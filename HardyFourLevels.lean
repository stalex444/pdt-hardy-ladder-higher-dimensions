module

public import Mathlib

@[expose] public section
/-! Algebraic steps of the real-plane reduction in FourLevels.md. -/
namespace HardyFourLevels
open Matrix

/-- The trace identity used to eliminate the inverse of a two-by-two Gram matrix,
in denominator-cleared form. -/
theorem trace_identity (M A : Matrix (Fin 2) (Fin 2) ℂ) :
    trace (M.adjugate * A ^ 2) =
    trace A * trace (M.adjugate * A) - A.det * trace M := by
  simp only [Matrix.adjugate_fin_two, Matrix.det_fin_two, sq, Matrix.trace_fin_two,
    Matrix.mul_apply, Fin.sum_univ_two]
  simp
  ring

/-- Along a segment of fixed marginals both numerator and denominator are affine.
A positive denominator bounds every score by the higher endpoint. -/
theorem endpoint_bounds_affine_ratio {n₀ n₁ d₀ d₁ s : ℝ} (h₀ : 0 < d₀) (h₁ : 0 < d₁)
    (hs : 0 ≤ s) (hs' : s ≤ 1) :
    ((1-s)*n₀+s*n₁)/((1-s)*d₀+s*d₁) ≤ max (n₀/d₀) (n₁/d₁) := by
  let m := max (n₀/d₀) (n₁/d₁)
  have a : n₀ ≤ m*d₀ := (div_le_iff₀ h₀).mp (le_max_left _ _)
  have b : n₁ ≤ m*d₁ := (div_le_iff₀ h₁).mp (le_max_right _ _)
  have ha := mul_le_mul_of_nonneg_left a (sub_nonneg.mpr hs')
  have hb := mul_le_mul_of_nonneg_left b hs
  have den : 0 < (1-s)*d₀+s*d₁ := by
    rcases eq_or_lt_of_le hs with h | h
    · rw [← h]; simpa using h₀
    · exact add_pos_of_nonneg_of_pos (mul_nonneg (sub_nonneg.mpr hs') h₀.le) (mul_pos h h₁)
  apply (div_le_iff₀ den).mpr
  change _ ≤ m*_
  linear_combination ha + hb

end HardyFourLevels

#print axioms HardyFourLevels.trace_identity
#print axioms HardyFourLevels.endpoint_bounds_affine_ratio
