module

public import HardyExtension.Definitions
public import HardyMomentGap
public import HardyBalancedPolynomial
public import HardyFourAttainment

@[expose] public section
/-! Four-level Hardy upper bound on the full complex Plücker quadric. -/
noncomputable section
namespace HardyFourSharp
open HardyMomentGap HardyFourPairing HardyBalancedPolynomial

def fifth (d : Four) : Four := fun i => d i^5

private def scalarRows (d : Four) (m : Six) (f : Fin 4 → Fin 4 → ℝ) :=
  m 0*(f 0 1/(d 0*d 1)^5) + m 1*(f 0 2/(d 0*d 2)^5) + m 2*(f 0 3/(d 0*d 3)^5) +
  m 3*(f 2 3/(d 2*d 3)^5) + m 4*(f 1 3/(d 1*d 3)^5) + m 5*(f 1 2/(d 1*d 2)^5)

private theorem clearing (d : Four) (hd : ∀ i, 0<d i) (m : Six) (f : Fin 4 → Fin 4 → ℝ) :
    sumRows (fifth d) m f = volume (fifth d)*scalarRows d m f := by
  have h0 := (hd 0).ne'
  have h1 := (hd 1).ne'
  have h2 := (hd 2).ne'
  have h3 := (hd 3).ne'
  dsimp [sumRows,volume,fifth,scalarRows]
  field_simp

private theorem read_rows (d : Four) (m : Six) (p : HardyMomentGap.Row → ℝ)
    (f : Fin 4 → Fin 4 → ℝ) (h : ∀ i j, p (row (d i) (d j)) = f i j/(d i*d j)^5) :
    lin m (rows d) p = scalarRows d m f := by
  simp [lin,rows,Fin.sum_univ_succ,h,scalarRows,add_assoc]

theorem physical_clearing (K : ℝ) (d : Four) (hd : ∀ i, 0<d i) (m : Six) :
    K*clearedB (fifth d) m-clearedN d (fifth d) m =
    (volume (fifth d))^2*(K*momentB d m-momentN d m) := by
  let t := fifth d
  have lower := read_rows d m HardyMomentGap.Row.lower (fun _ _ => 1) (fun _ _ => rfl)
  have upper := read_rows d m HardyMomentGap.Row.upper (fun i j => (t i*t j)^2) (by
    intro i j
    dsimp [row,t,fifth]
    have hi := (hd i).ne'
    have hj := (hd j).ne'
    field_simp)
  have j10 := read_rows d m HardyMomentGap.Row.J10 (fun i j => (t i*t j)^2) (by
    intro i j; dsimp [row,t,fifth]; ring)
  have t2 := read_rows d m HardyMomentGap.Row.T2 (fun i j => d i^2+d j^2) (fun _ _ => rfl)
  have t6 := read_rows d m HardyMomentGap.Row.T6 (fun i j => d i*t i+d j*t j) (by
    intro i j; dsimp [row,t,fifth]; ring)
  have c := read_rows d m HardyMomentGap.Row.C
    (fun i j => t i^2*d j*t j+t j^2*d i*t i) (by
      intro i j; dsimp [row,t,fifth]; ring)
  have j6 := read_rows d m HardyMomentGap.Row.J6 (fun i j => d i*t i*d j*t j) (by
    intro i j; dsimp [row,t,fifth]; ring)
  have t10 := read_rows d m HardyMomentGap.Row.T10 (fun i j => t i^2+t j^2) (by
    intro i j; dsimp [row,t,fifth]; ring)
  simp only [clearedB,clearedN,clearing d hd,momentB,momentN,lower,upper,j10,t2,t6,c,j6,t10]
  dsimp only [t]
  ring

def middle (m : Six) := HardyGapBalance.balanced (firstThree m) (oppositeThree m)

def triangle (g : Fin 3 → ℝ) : Prop :=
  g 0 ≤ g 1+g 2 ∧ g 1 ≤ g 0+g 2 ∧ g 2 ≤ g 0+g 1

/-- Bound in the six nonnegative squared minor coordinates, exactly on their
complex Plücker feasibility domain (the zero vector is excluded). -/
theorem four_level_ratio_le (d : Four) (hd : ∀ i, 0<d i) (m : Six)
    (hm : ∀ i, 0 ≤ m i) (hn : m≠0) (htri : triangle (middle m)) :
    momentN d m / momentB d m ≤ matchingMax d := by
  let g := middle m
  let x := (g 1+g 2-g 0)/2
  let y := (g 0+g 2-g 1)/2
  let z := (g 0+g 1-g 2)/2
  obtain ⟨h0,h1,h2⟩ := htri
  change g 0≤g 1+g 2 at h0
  change g 1≤g 0+g 2 at h1
  change g 2≤g 0+g 1 at h2
  have packed : balancedSix m = triangleMinors x y z := by
    change pack g g = _
    funext i
    fin_cases i <;> dsimp [pack,triangleMinors,x,y,z] <;> ring
  have h := balanced_nonneg d hd (matchingBound_max d) x y z
    (by dsimp [x]; linarith) (by dsimp [y]; linarith) (by dsimp [z]; linarith)
  change 0 ≤ matchingMax d*clearedB (fifth d) _-clearedN d (fifth d) _ at h
  rw [←packed,physical_clearing _ _ hd] at h
  have vol : 0 < volume (fifth d) := by
    dsimp [volume,fifth]; positivity [hd 0,hd 1,hd 2,hd 3]
  exact ratio_le_of_balanced_gap d hd (matchingBound_max d) m hm hn
    (nonneg_of_mul_nonneg_right h (sq_pos_of_pos vol))

/-- With complementary pairs 01|23,02|13,03|12, a decomposable bivector
obeys the three-term Plücker identity including its alternating sign. -/
def plucker (w : Fin 6 → ℂ) : Prop := w 0*w 3-w 1*w 4+w 2*w 5=0

theorem plucker_triangle (w : Fin 6 → ℂ) (hw : plucker w) :
    triangle (middle (squareMinors w)) := by
  have adj (x y : ℂ) : Real.sqrt (‖x‖^2*‖y‖^2) = ‖x*y‖ := by
    rw [←mul_pow,Real.sqrt_sq (mul_nonneg (norm_nonneg _) (norm_nonneg _)),norm_mul]
  have eqn : w 0*w 3+w 2*w 5=w 1*w 4 := by unfold plucker at hw; linear_combination hw
  simp [triangle,middle,squareMinors,HardyGapBalance.balanced,firstThree,oppositeThree,adj]
  simp only [← norm_mul]
  constructor
  · calc
      _ = ‖w 1*w 4-w 2*w 5‖ := by rw [←eqn,add_sub_cancel_right]
      _ ≤ _ := norm_sub_le _ _
  constructor
  · rw [←eqn]; exact norm_add_le _ _
  · calc
      _ = ‖w 1*w 4-w 0*w 3‖ := by rw [←eqn,add_sub_cancel_left]
      _ ≤ _ := (norm_sub_le _ _).trans_eq (add_comm _ _)

/-- The complex four-level moment score is at most the best disjoint pairing.
The inputs are any nonzero complex Plücker coordinates, without a reality,
repeated-spectrum, or integrality assumption. -/
theorem complex_four_level_bound (d : Four) (hd : ∀ i, 0<d i) (w : Fin 6 → ℂ)
    (hne : w≠0) (hw : plucker w) :
    momentN d (squareMinors w) / momentB d (squareMinors w) ≤ matchingMax d := by
  apply four_level_ratio_le d hd _ (fun i => sq_nonneg _) _ (plucker_triangle w hw)
  intro hz
  apply hne
  funext i
  have h : ‖w i‖^2=0 := congrFun hz i
  simpa using h

theorem frame_plucker (x y : Vertex → ℂ) : plucker (frameMinors x y) := by
  dsimp [plucker,frameMinors]
  ring

/-- No basis choice, reality hypothesis or restriction on the four distinct
levels is needed. A nonzero minor is the rank-two condition on the frame. -/
theorem complex_frame_bound {ρ : ℝ} (hρ : ρ^3=ρ+1)
    (d : Four) (hd : ∀ i, 0<d i) (x y : Vertex → ℂ) (hr : frameMinors x y≠0) :
    let m := squareMinors (frameMinors x y)
    momentN d m / momentB d m ≤ matchingMax d ∧
      matchingMax d ≤ ((8*ρ^2+ρ-11)/25)*(∑ i, d i^2) :=
  ⟨complex_four_level_bound d hd _ hr (frame_plucker x y),matchingMax_le_plastic hρ d hd⟩

/-- Sharp maximum, including attainment, over the full complex Plücker quadric. -/
theorem four_level_exact_maximum (d : Four) (hd : ∀ i, 0<d i) :
    IsGreatest {p : ℝ | ∃ w : Fin 6 → ℂ, w≠0 ∧ plucker w ∧
      momentN d (squareMinors w)/momentB d (squareMinors w)=p} (matchingMax d) := by
  constructor
  · exact HardyFourAttainment.matchingMax_attained d hd
  · rintro p ⟨w,hn,hp,rfl⟩
    exact complex_four_level_bound d hd w hn hp

end HardyFourSharp

#print axioms HardyFourSharp.complex_four_level_bound
#print axioms HardyFourSharp.complex_frame_bound
#print axioms HardyFourSharp.four_level_exact_maximum
