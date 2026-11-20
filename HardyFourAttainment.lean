module

public import HardyMomentGap

@[expose] public section
/-! Three explicit real bivectors attain the three disjoint-pairing scores
in four positive Schmidt levels. -/
noncomputable section
open HardyMomentGap HardyFourPairing HardyTripleGap
namespace HardyFourAttainment

/-- Unit weights on each of the four edges crossing the chosen pairing. -/
private def crossSum (a b c d : ℝ) (p : Row → ℝ) : ℝ :=
  p (row a c) + p (row a d) + p (row b c) + p (row b d)

set_option maxHeartbeats 1600000 in
private theorem cross_identity {a b c d : ℝ} (ha : 0<a) (hb : 0<b) (hc : 0<c) (hd : 0<d) :
    let L := crossSum a b c d
    L Row.T2*L Row.J10 - L Row.T6*L Row.C + L Row.J6*L Row.T10 =
    (edge a b+edge c d)*(L Row.lower*L Row.upper) := by
  have hab : a^5+b^5 ≠ 0 := by positivity
  have hcd : c^5+d^5 ≠ 0 := by positivity
  dsimp [crossSum,row,edge]
  field_simp
  ring

/-- The three pairing values, in the same order as the omitted complementary minors. -/
def pairingScore (d : Vertex → ℝ) : Fin 3 → ℝ :=
  ![edge (d 0) (d 1) + edge (d 2) (d 3),edge (d 0) (d 2) + edge (d 1) (d 3),
    edge (d 0) (d 3) + edge (d 1) (d 2)]

/-- The nonzero entries of each witness have magnitude one. The minus sign in
the middle witness gives the alternating Plücker equation exactly. -/
def witness : Fin 3 → Fin 6 → ℂ := ![
  ![0,1,1,0,1,1],
  ![1,0,1,1,0,-1],
  ![1,1,0,1,1,0]]

def vertexWeights : Fin 3 → Fin 6 → ℝ := ![
  ![0,1,1,0,1,1],
  ![1,0,1,1,0,1],
  ![1,1,0,1,1,0]]

theorem witness_plucker (k : Fin 3) :
    witness k 0*witness k 3-witness k 1*witness k 4+witness k 2*witness k 5 = 0 := by
  fin_cases k <;> norm_num [witness]

theorem witness_nonzero (k : Fin 3) : witness k ≠ 0 := by
  intro h
  fin_cases k <;> first
    | simpa [witness] using congrFun h 0
    | simpa [witness] using congrFun h 1

theorem witness_squares (k : Fin 3) : (fun i => ‖witness k i‖^2) = vertexWeights k := by
  funext i
  fin_cases k <;> fin_cases i <;> norm_num [witness,vertexWeights]

private theorem row_swap (x y : ℝ) : row x y = row y x := by
  simp [row,mul_comm x y,add_comm]

private def order : Fin 3 → Fin 4 → Vertex :=
  ![![0,1,2,3],![0,2,1,3],![0,3,1,2]]

private theorem lin_vertex (d : Vertex → ℝ) (k : Fin 3) (p : Row → ℝ) :
    lin (vertexWeights k) (rows d) p =
    crossSum (d (order k 0)) (d (order k 1)) (d (order k 2)) (d (order k 3)) p := by
  fin_cases k <;> simp [lin,Fin.sum_univ_succ,vertexWeights,rows,crossSum,order,
    row_swap,add_comm,add_left_comm,add_assoc]

theorem vertex_ratio (d : Vertex → ℝ) (hd : ∀ i, 0<d i) (k : Fin 3) :
    momentN d (vertexWeights k) / momentB d (vertexWeights k) = pairingScore d k := by
  have hw (i : Fin 6) : 0 ≤ vertexWeights k i := by
    rw [←witness_squares]
    exact sq_nonneg _
  have hn : vertexWeights k ≠ 0 := by
    intro h
    fin_cases k <;> first
      | simpa [vertexWeights] using congrFun h 0
      | simpa [vertexWeights] using congrFun h 1
  apply (div_eq_iff (momentB_pos d hd _ hw hn).ne').mpr
  unfold momentN momentB
  simp only [lin_vertex]
  have hs : pairingScore d k =
      edge (d (order k 0)) (d (order k 1))+edge (d (order k 2)) (d (order k 3)) := by
    fin_cases k <;> rfl
  rw [hs]
  exact cross_identity (hd _) (hd _) (hd _) (hd _)

/-- Explicit column vectors giving these minors, so the witnesses come
directly from genuine two-planes. -/
def firstColumn : Fin 3 → Fin 4 → ℂ := ![![1,1,0,0],![1,0,1,0],![1,0,0,-1]]
def secondColumn : Fin 3 → Fin 4 → ℂ := ![![0,0,1,1],![0,1,0,1],![0,1,1,0]]

def sixMinors (u v : Fin 4 → ℂ) : Fin 6 → ℂ :=
  let det := fun i j => u i*v j-u j*v i
  ![det 0 1,det 0 2,det 0 3,det 2 3,det 1 3,det 1 2]

theorem witness_is_plane (k : Fin 3) : sixMinors (firstColumn k) (secondColumn k) = witness k := by
  funext i
  fin_cases k <;> fin_cases i <;> norm_num [sixMinors,firstColumn,secondColumn,witness]

/-- For any four positive Schmidt values, one of the three exhibited complex
bivectors attains the largest disjoint-pairing score in the actual moment ratio. -/
theorem matchingMax_attained (d : Vertex → ℝ) (hd : ∀ i, 0<d i) :
    ∃ w : Fin 6 → ℂ, w ≠ 0 ∧ w 0*w 3-w 1*w 4+w 2*w 5=0 ∧
      momentN d (fun i => ‖w i‖^2) / momentB d (fun i => ‖w i‖^2) = matchingMax d := by
  have ex : ∃ k : Fin 3, pairingScore d k = matchingMax d := by
    change ∃ k, pairingScore d k = max (pairingScore d 0) (max (pairingScore d 1) (pairingScore d 2))
    rcases le_total (pairingScore d 0) (max (pairingScore d 1) (pairingScore d 2)) with ht | ht
    · rw [max_eq_right ht]
      rcases le_total (pairingScore d 1) (pairingScore d 2) with hp | hp
      · exact ⟨2,(max_eq_right hp).symm⟩
      · exact ⟨1,(max_eq_left hp).symm⟩
    · exact ⟨0,(max_eq_left ht).symm⟩
  obtain ⟨k,hk⟩ := ex
  refine ⟨witness k,witness_nonzero k,witness_plucker k,?_⟩
  rw [witness_squares,vertex_ratio d hd,hk]

end HardyFourAttainment

#print axioms HardyFourAttainment.witness_is_plane
#print axioms HardyFourAttainment.matchingMax_attained
