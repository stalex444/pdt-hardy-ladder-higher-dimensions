module

public import Mathlib.Analysis.Matrix.PosDef
public import Mathlib.Tactic

@[expose] public section
/-! Seven assignment patterns on an exceptional two-by-two spectral block. -/
noncomputable section
open Matrix
open scoped Matrix ComplexConjugate ComplexOrder
namespace HardyRepeated

abbrev Block := Matrix (Fin 2) (Fin 2) ℂ

/-- No exceptional match, exactly one of the four matches, or one of the two
perfect two-match patterns. -/
structure PatternWeights where
  empty : ℝ
  single : Fin 2 → Fin 2 → ℝ
  direct : ℝ
  crossed : ℝ

/-- The seven probabilities and their prescribed one- and two-match masses. -/
structure Certificate (m : Fin 2 → Fin 2 → ℝ) (q : ℝ) (w : PatternWeights) : Prop where
  empty_nonneg : 0 ≤ w.empty
  single_nonneg : ∀ i j, 0 ≤ w.single i j
  direct_nonneg : 0 ≤ w.direct
  crossed_nonneg : 0 ≤ w.crossed
  total : w.empty + (∑ i, ∑ j, w.single i j) + w.direct + w.crossed = 1
  marginal : ∀ i j, w.single i j + (if i=j then w.direct else w.crossed) = m i j
  double : w.direct + w.crossed = q

/-- Allocate at most the direct diagonal's two available marginals to the direct
matching; remaining double mass goes to the crossed matching. -/
def weights (m : Fin 2 → Fin 2 → ℝ) (q : ℝ) : PatternWeights :=
  let t := min q (min (m 0 0) (m 1 1))
  { empty := 1-(∑ i, ∑ j, m i j)+q
    single := fun i j => m i j - (if i=j then t else q-t)
    direct := t
    crossed := q-t }

theorem certificate (m : Fin 2 → Fin 2 → ℝ) (q : ℝ) (hm : ∀ i j, 0 ≤ m i j)
    (hq : 0 ≤ q) (hr : ∀ i, q ≤ m i 0 + m i 1)
    (hc : ∀ j, q ≤ m 0 j + m 1 j) (he : 0 ≤ 1-(∑ i, ∑ j, m i j)+q) :
    Certificate m q (weights m q) := by
  let t := min q (min (m 0 0) (m 1 1))
  have ht : 0 ≤ t := le_min hq (le_min (hm 0 0) (hm 1 1))
  have hs : t ≤ q := min_le_left _ _
  have ha : t ≤ m 0 0 := (min_le_right _ _).trans (min_le_left _ _)
  have hd : t ≤ m 1 1 := (min_le_right _ _).trans (min_le_right _ _)
  have hb : q - t ≤ m 0 1 := by
    dsimp [t]
    simp only [min_def]; split_ifs <;> linarith [hm 0 1, hr 0, hc 1]
  have hcc : q - t ≤ m 1 0 := by
    dsimp [t]
    simp only [min_def]; split_ifs <;> linarith [hm 1 0, hc 0, hr 1]
  refine ⟨he,?_,ht,sub_nonneg.mpr hs,?_,?_,?_⟩
  · intro i j
    change 0 ≤ m i j - (if i = j then t else q-t)
    apply sub_nonneg.mpr
    fin_cases i <;> fin_cases j <;> first | exact ha | exact hb | exact hcc | exact hd
  · simp [weights,Fin.sum_univ_two]; ring
  · intro i j; simp [weights]
  · dsimp [weights]; ring

/-- Squared overlaps on the four exceptional row-column pairs. -/
def marginal (C : Block) (i j : Fin 2) := Complex.normSq (C i j)

/-- Probability mass assigned to a double exceptional match. -/
def doubleMass (C : Block) := Complex.normSq C.det

private lemma gram_diag (C : Block) (i : Fin 2) :
    (C * Cᴴ) i i = (↑(marginal C i 0 + marginal C i 1) : ℂ) := by
  simp only [Matrix.mul_apply, Fin.sum_univ_two, Matrix.conjTranspose_apply, Complex.star_def,
    Complex.mul_conj, Complex.ofReal_add, marginal]

private lemma gram_det (C : Block) :
    (C * Cᴴ).det = (doubleMass C : ℂ) := by
  rw [Matrix.det_mul,Matrix.det_conjTranspose,Complex.star_def,Complex.mul_conj]
  rfl

/-- The zero-match mass is the determinant of the complementary two-dimensional Gram matrix. -/
theorem complementary_gram (C : Block) :
    (1 - C * Cᴴ).det = ((1 - (∑ i, ∑ j, marginal C i j) + doubleMass C : ℝ) : ℂ) := by
  let G := C * Cᴴ
  have he : (1-G).det = 1 - G 0 0 - G 1 1 + G.det := by
    simp [Matrix.det_fin_two, Matrix.sub_apply]; ring
  rw [he]
  dsimp only [G]
  rw [gram_diag,gram_diag,gram_det]
  push_cast; simp only [Fin.sum_univ_two]; ring

private lemma det_le_row_product (C : Block) :
    doubleMass C ≤ (marginal C 0 0 + marginal C 0 1) * (marginal C 1 0 + marginal C 1 1) := by
  let G := C * Cᴴ
  have hh : G.IsHermitian := Matrix.isHermitian_mul_conjTranspose_self C
  have hoff : G 1 0 = conj (G 0 1) := (hh.apply 1 0).symm
  have h := gram_det C
  change G.det = _ at h
  rw [Matrix.det_fin_two,hoff,Complex.mul_conj] at h
  dsimp only [G] at h
  rw [gram_diag,gram_diag] at h
  have hre := congrArg Complex.re h
  simp only [Complex.sub_re,← Complex.ofReal_mul,Complex.ofReal_re] at hre
  linarith [Complex.normSq_nonneg ((C*Cᴴ) 0 1)]

private theorem marginal_star (C : Block) (i j : Fin 2) :
    marginal Cᴴ i j = marginal C j i := by simp [marginal, Matrix.conjTranspose_apply]

private theorem doubleMass_star (C : Block) : doubleMass Cᴴ = doubleMass C := by
  simp [doubleMass, Matrix.det_conjTranspose]

private theorem row_le_one {C : Block} (h : (1-C*Cᴴ).PosSemidef) (i : Fin 2) :
    marginal C i 0 + marginal C i 1 ≤ 1 := by
  have he := (Complex.nonneg_iff.mp (h.diag_nonneg (i:=i))).1
  rw [Matrix.sub_apply, gram_diag] at he
  simpa using he

private theorem double_le_rows {C : Block} (h : (1-C*Cᴴ).PosSemidef) (i : Fin 2) :
    doubleMass C ≤ marginal C i 0 + marginal C i 1 := by
  have hn i j : 0 ≤ marginal C i j := Complex.normSq_nonneg _
  have h0 := row_le_one h 0
  have h1 := row_le_one h 1
  have hp := det_le_row_product C
  fin_cases i
  · exact hp.trans (mul_le_of_le_one_right (add_nonneg (hn 0 0) (hn 0 1)) h1)
  · exact hp.trans (mul_le_of_le_one_left (add_nonneg (hn 1 0) (hn 1 1)) h0)

/-- Every two-by-two contraction in the two-sided Gram formulation has a
nonnegative, normalized seven-pattern certificate. -/
theorem contraction_certificate (C : Block) (hrow : (1-C*Cᴴ).PosSemidef)
    (hcol : (1-Cᴴ*C).PosSemidef) :
    Certificate (marginal C) (doubleMass C) (weights (marginal C) (doubleMass C)) := by
  apply certificate
  · intro i j; exact Complex.normSq_nonneg _
  · exact Complex.normSq_nonneg _
  · exact double_le_rows hrow
  · intro j
    have hcol' : (1-Cᴴ*Cᴴᴴ).PosSemidef := by simpa using hcol
    simpa only [doubleMass_star,marginal_star] using double_le_rows hcol' j
  · have he := hrow.det_nonneg
    rw [complementary_gram] at he
    exact (Complex.nonneg_iff.mp he).1


/-- The exceptional block of the four-dimensional unitary overlap matrix is
two-sided contractive. Its two Gram complements are the Gram matrices of the
other entries in the exceptional rows and columns. -/
theorem unitary_block_contractive
    (W : Matrix.unitaryGroup (Fin 2 ⊕ Fin 2) ℂ) :
    let U : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) ℂ := W
    let C := U.toBlocks₁₁
    (1-C*Cᴴ).PosSemidef ∧ (1-Cᴴ*C).PosSemidef := by
  let U : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) ℂ := W
  let C := U.toBlocks₁₁
  let R := U.toBlocks₁₂
  let S := U.toBlocks₂₁
  have hl : U * Uᴴ = 1 := Matrix.mem_unitaryGroup_iff.mp W.property
  have hr : Uᴴ * U = 1 := Matrix.mem_unitaryGroup_iff'.mp W.property
  have hL : C*Cᴴ + R*Rᴴ = 1 := by
    ext i j
    have h := congrFun (congrFun hl (Sum.inl i)) (Sum.inl j)
    simpa [Matrix.mul_apply, Fintype.sum_sum_type, Matrix.one_apply, C, R, Matrix.toBlocks₁₁,
      Matrix.toBlocks₁₂, Matrix.conjTranspose_apply, Matrix.submatrix] using h
  have hR : Cᴴ*C + Sᴴ*S = 1 := by
    ext i j
    have h := congrFun (congrFun hr (Sum.inl i)) (Sum.inl j)
    simpa [Matrix.mul_apply, Fintype.sum_sum_type, Matrix.one_apply, C, S, Matrix.toBlocks₁₁,
      Matrix.toBlocks₂₁, Matrix.conjTranspose_apply, Matrix.submatrix] using h
  change (1-C*Cᴴ).PosSemidef ∧ (1-Cᴴ*C).PosSemidef
  have h1 : 1-C*Cᴴ = R*Rᴴ := by rw [← hL]; abel
  have h2 : 1-Cᴴ*C = Sᴴ*S := by rw [← hR]; abel
  rw [h1,h2]
  exact ⟨Matrix.posSemidef_self_mul_conjTranspose R, Matrix.posSemidef_conjTranspose_mul_self S⟩

theorem unitary_block_certificate (W : Matrix.unitaryGroup (Fin 2 ⊕ Fin 2) ℂ) :
    let C := (W.val).toBlocks₁₁
    Certificate (marginal C) (doubleMass C) (weights (marginal C) (doubleMass C)) :=
  contraction_certificate _ (unitary_block_contractive W).1 (unitary_block_contractive W).2


/-- Generating polynomial for the singleton and double exceptional minors; the
four independent variables weight exceptional rows and columns. -/
def generating (m : Fin 2 → Fin 2 → ℝ) (q : ℝ) (x y : Fin 2 → ℂ) : ℂ :=
  1 + (∑ i, ∑ j, (m i j:ℂ)*x i*y j) + (q:ℂ)*x 0*x 1*y 0*y 1

/-- Determinantal form of the four-variable minor polynomial. -/
theorem two_by_two_gram_pencil (C : Block) (x y : Fin 2 → ℂ) :
    (1 + diagonal x * C * diagonal y * Cᴴ).det = generating (marginal C) (doubleMass C) x y := by
  let G := diagonal x * C * diagonal y * Cᴴ
  have h1 : (1+G).det = 1 + G 0 0 + G 1 1 + G.det := by
    simp [Matrix.det_fin_two, Matrix.add_apply]; ring
  have hi (i : Fin 2) : G i i = (marginal C i 0 : ℂ)*x i*y 0 + (marginal C i 1 : ℂ)*x i*y 1 := by
    simp only [G, Matrix.mul_apply, Fin.sum_univ_two, Matrix.diagonal_apply, Matrix.conjTranspose_apply,
      Complex.star_def, marginal, Complex.normSq_eq_conj_mul_self]
    fin_cases i <;> norm_num <;> ring
  have hd : G.det = (doubleMass C : ℂ)*x 0*x 1*y 0*y 1 := by
    simp only [G, Matrix.det_mul,Matrix.det_diagonal,Fin.prod_univ_two,Matrix.det_conjTranspose,
      Complex.star_def,doubleMass,Complex.normSq_eq_conj_mul_self]
    ring
  rw [h1,hi,hi,hd]
  simp only [generating, Fin.sum_univ_two]
  ring

/-- The Gram polynomial is exactly the average matching polynomial. This
is stronger than matching the four singleton coefficients separately. -/
theorem certificate_polynomial {m q w} (h : Certificate m q w) (x y : Fin 2 → ℂ) :
    (w.empty:ℂ) + (∑ i, ∑ j, (w.single i j:ℂ)*(1+x i*y j)) +
      (w.direct:ℂ)*(1+x 0*y 0)*(1+x 1*y 1) +
      (w.crossed:ℂ)*(1+x 0*y 1)*(1+x 1*y 0) = generating m q x y := by
  have ht := congrArg Complex.ofReal h.total
  have h00 := congrArg Complex.ofReal (h.marginal 0 0)
  have h01 := congrArg Complex.ofReal (h.marginal 0 1)
  have h10 := congrArg Complex.ofReal (h.marginal 1 0)
  have h11 := congrArg Complex.ofReal (h.marginal 1 1)
  have hd := congrArg Complex.ofReal h.double
  norm_num [Fin.sum_univ_two] at ht h00 h01 h10 h11 hd
  simp only [generating, Fin.sum_univ_two]
  linear_combination ht + x 0*y 0*h00 + x 0*y 1*h01 + x 1*y 0*h10 +
    x 1*y 1*h11 + x 0*x 1*y 0*y 1*hd

/-- Four-dimensional unitary overlap directly gives a seven-pattern
probability law and a determinant identity valid for every set of variables. -/
theorem unitary_block_polynomial (W : Matrix.unitaryGroup (Fin 2 ⊕ Fin 2) ℂ) (x y : Fin 2 → ℂ) :
    let C := W.val.toBlocks₁₁
    let w := weights (marginal C) (doubleMass C)
    (1 + diagonal x * C * diagonal y * Cᴴ).det =
      (w.empty:ℂ) + (∑ i, ∑ j, (w.single i j:ℂ)*(1+x i*y j)) +
      (w.direct:ℂ)*(1+x 0*y 0)*(1+x 1*y 1) +
      (w.crossed:ℂ)*(1+x 0*y 1)*(1+x 1*y 0) := by
  exact (two_by_two_gram_pencil _ _ _).trans (certificate_polynomial (unitary_block_certificate W) x y).symm


def price (u v : ℝ) (i : Fin 4) : ℝ := if i=2 then u else if i=3 then v else 0

private def crossing (i j : Fin 4) : ℝ :=
  if (i=2 ∧ j=3) ∨ (i=3 ∧ j=2) then 1 else 0

/-- Pair costs for labels (a,a,b,c): equal values have zero cost, a-b costs u,
a-c costs v, and b-c costs w. -/
def pairCost (u v w : ℝ) (i j : Fin 4) : ℝ :=
  if i=j then 0 else if (i=2 ∧ j=3) ∨ (i=3 ∧ j=2) then w else price u v i + price u v j

private theorem cost_charge (u v w : ℝ) (hu : 0≤u) (hv : 0≤v) (i j : Fin 4) :
    pairCost u v w i j ≤ price u v i + price u v j + (w-u-v)*crossing i j := by
  fin_cases i <;> fin_cases j <;> norm_num [pairCost,price,crossing] <;> linarith

theorem affine_pair_bound (u v w k : ℝ) (hk : 0≤k) (hk' : k≤2) :
    k*w+(2-k)*(u+v) ≤ 2*max (u+v) w := by
  have hw := mul_le_mul_of_nonneg_left (le_max_right (u+v) w) hk
  have huv := mul_le_mul_of_nonneg_left (le_max_left (u+v) w) (sub_nonneg.mpr hk')
  linarith only [hw,huv]

/-- At most two matching edges can go straight between the exceptional labels.
The remaining edges charge each exceptional endpoint at most once. -/
theorem permutation_cost_le (u v w : ℝ) (hu : 0≤u) (hv : 0≤v) (σ : Equiv.Perm (Fin 4)) :
    (∑ i, pairCost u v w i (σ i))/2 ≤ max (u+v) w := by
  let k : ℝ := ∑ i, crossing i (σ i)
  have hkn : 0 ≤ k := Finset.sum_nonneg fun i _ => by dsimp only [crossing]; split <;> norm_num
  have hks : k ≤ 2 := by
    have h (i j : Fin 4) : crossing i j ≤ price 1 1 i := by
      fin_cases i <;> fin_cases j <;> norm_num [crossing,price]
    have ht := Finset.sum_le_sum (s:=Finset.univ) (fun i _ => h i (σ i))
    have hp : ∑ i, price 1 1 i = 2 := by norm_num [Fin.sum_univ_succ,price]
    exact ht.trans_eq hp
  have hp : ∑ i, price u v i = u+v := by simp [Fin.sum_univ_succ,price]
  have hc := Finset.sum_le_sum (s:=Finset.univ) (fun i _ => cost_charge u v w hu hv i (σ i))
  simp only [Finset.sum_add_distrib,← Finset.mul_sum,Equiv.sum_comp σ (price u v),hp] at hc
  have bound := affine_pair_bound u v w k hkn hks
  change _ ≤ u+v+(u+v)+(w-u-v)*k at hc
  linarith only [hc,bound]

/-- The maximum of the half-summed costs over all four-label permutations is
exactly the larger of u+v and w; explicit disjoint transpositions attain both. -/
theorem maximum_permutation_cost (u v w : ℝ) (hu : 0≤u) (hv : 0≤v) :
    IsGreatest (Set.range (fun σ : Equiv.Perm (Fin 4) => (∑ i, pairCost u v w i (σ i))/2))
      (max (u+v) w) := by
  constructor
  · rcases le_total (u+v) w with h|h
    · rw [max_eq_right h]
      refine ⟨Equiv.swap 2 3,?_⟩
      norm_num [Fin.sum_univ_succ, pairCost,price,Equiv.swap_apply_def]
    · rw [max_eq_left h]
      refine ⟨(Equiv.swap 0 2).trans (Equiv.swap 1 3),?_⟩
      norm_num [Fin.sum_univ_succ, pairCost,price,Equiv.swap_apply_def]; ring
  · rintro _ ⟨σ,rfl⟩
    exact permutation_cost_le u v w hu hv σ

end HardyRepeated
#print axioms HardyRepeated.certificate
#print axioms HardyRepeated.contraction_certificate

#print axioms HardyRepeated.unitary_block_certificate

#print axioms HardyRepeated.unitary_block_polynomial

#print axioms HardyRepeated.maximum_permutation_cost
