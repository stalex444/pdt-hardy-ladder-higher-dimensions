module

public import Mathlib.Tactic
public import Mathlib.Analysis.Real.Sqrt

@[expose] public section
/-! Exact balancing of complementary minor pairs in the four-level Hardy gap. -/
noncomputable section
open Finset
namespace HardyGapBalance

/-- Sum over each unordered pair of indices once. -/
def edges {n : ℕ} (f : Fin n → Fin n → ℝ) : ℝ :=
  ∑ i, ∑ j ∈ Ioi i, f i j

/-- The gap quadratic for high and low complementary coordinates. Coefficients
on products in a single complementary pair are arbitrary. -/
def gap {n : ℕ} (K : ℝ) (dis : Fin n → ℝ) (c b : Fin n → Fin n → ℝ)
    (h l : Fin n → ℝ) : ℝ :=
  (∑ i, (K*(h i^2+l i^2) + dis i*(h i*l i))) +
  edges (fun i j => c i j*(h i*h j+l i*l j) + b i j*(h i*l j+l i*h j))

/-- The two complementary entries become equal at their geometric mean. -/
def balanced {n : ℕ} (h l : Fin n → ℝ) (i : Fin n) := Real.sqrt (h i*l i)

/-- Remainder of one pair of adjacent complementary blocks after extracting
the quadratic in the high-minus-low differences. -/
theorem adjacent_balance {h l H L : ℝ} (hh : 0≤h) (hl : 0≤l) (hH : 0≤H) (hL : 0≤L)
    (c b : ℝ) :
    c*(h*H+l*L)+b*(h*L+l*H) -
      (c*(Real.sqrt (h*l)*Real.sqrt (H*L)+Real.sqrt (h*l)*Real.sqrt (H*L)) +
       b*(Real.sqrt (h*l)*Real.sqrt (H*L)+Real.sqrt (h*l)*Real.sqrt (H*L))) =
    c*(h-l)*(H-L)+(c+b)*(Real.sqrt (h*L)-Real.sqrt (l*H))^2 := by
  have hx := Real.sq_sqrt (mul_nonneg hh hL)
  have hy := Real.sq_sqrt (mul_nonneg hl hH)
  have hxy : Real.sqrt (h*L)*Real.sqrt (l*H) = Real.sqrt (h*l)*Real.sqrt (H*L) := by
    rw [← Real.sqrt_mul (mul_nonneg hh hL),← Real.sqrt_mul (mul_nonneg hh hl)]
    congr 1
    ring
  linear_combination -(c+b)*hx - (c+b)*hy + (2*(c+b))*hxy

/-- Exact gap identity. It holds for any finite number of complementary pairs,
including the three pairs of a four-level rank-two plane. -/
theorem gap_difference {n : ℕ} (K : ℝ) (dis : Fin n → ℝ) (c b : Fin n → Fin n → ℝ)
    (h l : Fin n → ℝ) (hh : ∀ i, 0≤h i) (hl : ∀ i, 0≤l i) :
    gap K dis c b h l - gap K dis c b (balanced h l) (balanced h l) =
      K*(∑ i, (h i-l i)^2) + edges (fun i j => c i j*(h i-l i)*(h j-l j)) +
      edges (fun i j => (c i j+b i j)*(Real.sqrt (h i*l j)-Real.sqrt (l i*h j))^2) := by
  let g := balanced h l
  have hd :
      (∑ i, (K*(h i^2+l i^2)+dis i*(h i*l i))) -
      (∑ i, (K*(g i^2+g i^2)+dis i*(g i*g i))) = K*∑ i, (h i-l i)^2 := by
    rw [←sum_sub_distrib,mul_sum]
    apply sum_congr rfl
    intro i _
    have hi : g i^2 = h i*l i := Real.sq_sqrt (mul_nonneg (hh i) (hl i))
    linear_combination (-2*K-dis i)*hi
  have he :
      edges (fun i j => c i j*(h i*h j+l i*l j)+b i j*(h i*l j+l i*h j)) -
      edges (fun i j => c i j*(g i*g j+g i*g j)+b i j*(g i*g j+g i*g j)) =
      edges (fun i j => c i j*(h i-l i)*(h j-l j)) +
      edges (fun i j => (c i j+b i j)*(Real.sqrt (h i*l j)-Real.sqrt (l i*h j))^2) := by
    unfold edges
    rw [←sum_sub_distrib,←sum_add_distrib]
    apply sum_congr rfl
    intro i _
    rw [←sum_sub_distrib,←sum_add_distrib]
    apply sum_congr rfl
    intro j _
    exact adjacent_balance (hh i) (hl i) (hh j) (hl j) (c i j) (b i j)
  unfold gap
  change _ - ((_)+edges (fun i j => c i j*(g i*g j+g i*g j)+b i j*(g i*g j+g i*g j))) = _
  linarith

/-- The coefficient of an adjacent monomial for edge cost u and positive
fifth-power ratio r. -/
def coefficient (K u r : ℝ) := (K-u)*(r+r⁻¹)-2*u

private theorem reciprocal_gap {r : ℝ} (hr : 0 < r) : 0 ≤ r+r⁻¹-2 := by
  have h : 0 ≤ (r-1)^2/r := div_nonneg (sq_nonneg _) hr.le
  convert h using 1
  field_simp
  ring

/-- Opposite edge costs bounded by K give a nonnegative coefficient on the
square lost in balancing. -/
theorem opposite_coefficients_nonneg {K u v r s : ℝ} (hu : 0≤u) (hv : 0≤v)
    (hk : u+v≤K) (hr : 0<r) (hs : 0<s) : 0≤coefficient K u r + coefficient K v s := by
  unfold coefficient
  have hu' : 0 ≤ K-u := by linarith
  have hv' : 0 ≤ K-v := by linarith
  nlinarith [mul_nonneg hu' (reciprocal_gap hr),mul_nonneg hv' (reciprocal_gap hs)]

/-- A nonnegative difference-vector quadratic suffices to compare the original
gap to its balanced value. Only off-diagonal coefficient sums enter. -/
theorem balanced_le {n : ℕ} (K : ℝ) (dis : Fin n → ℝ) (c b : Fin n → Fin n → ℝ)
    (h l : Fin n → ℝ) (hh : ∀ i, 0≤h i) (hl : ∀ i, 0≤l i)
    (hadj : ∀ i j, i<j → 0≤c i j+b i j)
    (hquad : 0 ≤ K*(∑ i, (h i-l i)^2) + edges (fun i j => c i j*(h i-l i)*(h j-l j))) :
    gap K dis c b (balanced h l) (balanced h l) ≤ gap K dis c b h l := by
  apply sub_nonneg.mp
  rw [gap_difference K dis c b h l hh hl]
  refine add_nonneg hquad (sum_nonneg fun i _ => sum_nonneg fun j hj => ?_)
  exact mul_nonneg (hadj i j (mem_Ioi.mp hj)) (sq_nonneg _)

end HardyGapBalance

#print axioms HardyGapBalance.gap_difference
#print axioms HardyGapBalance.opposite_coefficients_nonneg
#print axioms HardyGapBalance.balanced_le
