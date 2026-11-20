module

public import HardyExtension.Definitions
public import HardyPairBound
public import Mathlib.Tactic

@[expose] public section
/-! Rank-one copositivity in midpoint coordinates. The unbalanced
four-level minor gap reduces to this quadratic form on three labels. -/
noncomputable section
open Finset
namespace HardyTripleGap

def coefficient (K x y : ℝ) : ℝ :=
  (K-edge x y)*(x^5/y^5+y^5/x^5)-2*edge x y

/-- The adjacent-minor coefficient is exactly the cross coefficient of the
rank-one variance gap after multiplication by its two positive denominators. -/
theorem coefficient_eq {K x y : ℝ} (hx : 0 < x) (hy : 0 < y) :
    coefficient K x y =
      K*(x^5/y^5+y^5/x^5) - (y^5/x^3+x^5/y^3-2*x*y) := by
  have hs : x^5+y^5 ≠ 0 := by positivity
  unfold coefficient edge
  field_simp
  ring

variable {ι : Type*} [Fintype ι] [Nonempty ι]

/-- The rank-one gap is nonnegative for arbitrary nonnegative midpoint
weights as soon as each two-coordinate cost is at most K. -/
theorem rank_one_gap (d a : ι → ℝ) (hd : ∀ i, 0 < d i) (ha : ∀ i, 0 ≤ a i)
    {K : ℝ} (hK : 0 ≤ K) (hpair : ∀ i j, edge (d i) (d j) ≤ K) :
    0 ≤ K*(∑ i, a i/(d i)^5)*(∑ i, a i*(d i)^5)
      - (∑ i, a i/(d i)^3)*(∑ i, a i*(d i)^5) + (∑ i, a i*d i)^2 := by
  obtain ⟨t, ht⟩ := (HardyPairBound.common_multiplier_iff d hd (Real.sqrt K)).2 (by
    intro i j
    have den : 0 < d i^5+d j^5 := by positivity [hd i, hd j]
    apply (div_le_iff₀ den).mp
    have h := hpair i j
    unfold edge at h
    nlinarith [Real.sq_sqrt hK, Real.sqrt_nonneg K])
  have point (i : ι) : 0 ≤ a i/(d i)^5*(K-(d i-t*(d i)^5)^2) := by
    apply mul_nonneg (div_nonneg (ha i) (by positivity [hd i]))
    have hs := pow_le_pow_left₀ (abs_nonneg _) (ht i) 2
    rw [sq_abs, Real.sq_sqrt hK] at hs
    linarith
  have update (i : ι) :
      a i/(d i)^5*(K-(d i-t*(d i)^5)^2) =
        K*(a i/(d i)^5) - a i/(d i)^3 + (2*t)*(a i*d i) - t^2*(a i*(d i)^5) := by
    have hn := (hd i).ne'
    field_simp
    ring
  have combined := Finset.sum_nonneg (s:=Finset.univ) fun i _ => point i
  simp_rw [update] at combined
  rw [Finset.sum_sub_distrib, Finset.sum_add_distrib, Finset.sum_sub_distrib,
      ← Finset.mul_sum, ← Finset.mul_sum, ← Finset.mul_sum] at combined
  have mass : 0 ≤ ∑ i, a i*(d i)^5 :=
    Finset.sum_nonneg fun i _ => mul_nonneg (ha i) (pow_nonneg (hd i).le _)
  nlinarith only [mul_nonneg combined mass, sq_nonneg ((∑ i, a i*d i)-t*(∑ i, a i*(d i)^5))]

/-- The explicit three-edge quadratic is copositive, including zero weights. -/
theorem triple_gap (d a : Fin 3 → ℝ) (hd : ∀ i, 0 < d i) (ha : ∀ i, 0 ≤ a i)
    {K : ℝ} (hK : 0 ≤ K) (hpair : ∀ i j, edge (d i) (d j) ≤ K) :
    0 ≤ K*((a 0)^2+(a 1)^2+(a 2)^2)
      + coefficient K (d 0) (d 1)*a 0*a 1
      + coefficient K (d 0) (d 2)*a 0*a 2
      + coefficient K (d 1) (d 2)*a 1*a 2 := by
  have h := rank_one_gap d a hd ha hK hpair
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one] at h
  rw [coefficient_eq (hd 0) (hd 1), coefficient_eq (hd 0) (hd 2),
      coefficient_eq (hd 1) (hd 2)]
  apply h.trans_eq
  have h₀ := (hd 0).ne'
  have h₁ := (hd 1).ne'
  have h₂ := (hd 2).ne'
  norm_num at *
  field_simp
  ring

end HardyTripleGap

#print axioms HardyTripleGap.triple_gap
