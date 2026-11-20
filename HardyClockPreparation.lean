module

public import Mathlib

@[expose] public section
/-! Reachability of the two-step Hardy spectrum in the cubic dephasing channel.
The output is the reduced state of the qubit. Its eigenvalues are the squared
Schmidt coefficients across qubit / environment for a pure dilation. -/
namespace HardyClockPreparation

/-- The input diagonal is (w, 1-w) and its upper coherence is z.
One tick multiplies that coherence by s. -/
noncomputable def reduced (w : ℝ) (s z : ℂ) (n : ℕ) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![(w : ℂ), s^n*z; star (s^n*z), 1-(w : ℂ)]

def determinant (t w : ℝ) (n : ℕ) : ℝ := w*(1-w)*(1-t^n)

/-- Three consecutive density matrices determine the tick contraction from
their determinant increments whenever the first increment is nonzero. -/
theorem increment_law (t w : ℝ) (n : ℕ) :
    determinant t w (n+2) - determinant t w (n+1) =
      t*(determinant t w (n+1) - determinant t w n) := by
  simp only [determinant, pow_succ]
  ring

theorem det_reduced {w t : ℝ} {s z : ℂ} (n : ℕ)
    (hs : Complex.normSq s = t) (hz : Complex.normSq z = w*(1-w)) :
    (reduced w s z n).det = (determinant t w n : ℂ) := by
  simp only [reduced, Matrix.det_fin_two, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.of_apply, Matrix.cons_val_fin_one]
  rw [Complex.star_def, Complex.mul_conj, map_mul, map_pow, hs, hz]
  unfold determinant
  push_cast
  ring

open Polynomial

def HasHardySpectrum (t : ℝ) (A : Matrix (Fin 2) (Fin 2) ℂ) : Prop :=
  A.charpoly = (X - C (t : ℂ)) * (X - C (1-(t : ℂ)))

theorem spectrum_iff_determinant {t w : ℝ} {s z : ℂ} (n : ℕ)
    (hs : Complex.normSq s = t) (hz : Complex.normSq z = w*(1-w)) :
    HasHardySpectrum t (reduced w s z n) ↔ determinant t w n=t*(1-t) := by
  have htr : (reduced w s z n).trace = 1 := by
    rw [reduced, Matrix.trace_fin_two_of]
    ring
  unfold HasHardySpectrum
  rw [Matrix.charpoly_fin_two, htr, det_reduced n hs hz]
  constructor
  · intro h
    have h0 := congrArg (Polynomial.eval (0 : ℂ)) h
    simp at h0
    have hv : determinant t w n = -(t*(t-1)) := by exact_mod_cast h0
    linarith
  · intro h
    rw [h]
    push_cast
    simp only [map_mul, map_sub, map_one]
    ring

/-- In terms of t = 1/ρ, the plastic cubic is t³ + t² = 1. -/
theorem inverse_cubic {ρ : ℝ} (hpos : 0 < ρ) (h : ρ^3 = ρ+1) :
    ρ⁻¹^3 + ρ⁻¹^2 = 1 := by
  field_simp
  linarith

private theorem bounds {t : ℝ} (ht : 0 < t) (hc : t^3+t^2=1) :
    3/4 < t ∧ t < 1 := by
  constructor
  · by_contra! h
    have hsq := pow_le_pow_left₀ ht.le h 2
    have hcube := pow_le_pow_left₀ ht.le h 3
    norm_num at hsq hcube
    linarith
  · by_contra! h
    have hsq := pow_le_pow_left₀ (by norm_num : (0:ℝ) ≤ 1) h 2
    nlinarith [pow_pos ht 3]

private theorem fifth {t : ℝ} (hc : t^3+t^2=1) : t^5 = 1-t := by
  linear_combination (t^2-t+1)*hc

/-- No pure input can reach the Hardy determinant before five ticks. -/
theorem before_five {t : ℝ} (ht : 0<t) (hc : t^3+t^2=1) (w : ℝ)
    {n : ℕ} (hn : n<5) : determinant t w n < t*(1-t) := by
  obtain ⟨hlo,hhi⟩ := bounds ht hc
  have hpow : t^4 ≤ t^n := (pow_right_strictAnti₀ ht hhi).antitone (by omega)
  have hunit : t^n ≤ 1 := pow_le_one₀ ht.le hhi.le
  have hgap : t^4-(2*t-1)^2 = (1-t)*(3*t-2) := by
    linear_combination (t-1)*hc
  have hstrict := mul_pos (sub_pos.mpr hhi) (by linarith : 0<3*t-2)
  have hcap : w*(1-w) ≤ 1/4 := by nlinarith [sq_nonneg (w-1/2)]
  have hprod := mul_le_mul_of_nonneg_right hcap (sub_nonneg.mpr hunit)
  unfold determinant
  nlinarith

/-- The only two input populations reaching the target at the earliest
tick are the two symbol weights of the cubic capacity equation. -/
theorem fifth_iff {t : ℝ} (ht : 0<t) (hc : t^3+t^2=1) (w : ℝ) :
    determinant t w 5 = t*(1-t) ↔ w=t^2 ∨ w=t^3 := by
  have h5 := fifth hc
  have hfactor : (w-t^2)*(w-t^3) = w^2-w+(1-t) := by
    linear_combination -w*hc+h5
  unfold determinant
  rw [h5]
  constructor
  · intro h
    have heq : w*(1-w)=1-t := by
      apply mul_right_cancel₀ ht.ne'
      linear_combination h
    have hz : (w-t^2)*(w-t^3)=0 := by nlinarith
    simpa only [mul_eq_zero, sub_eq_zero] using hz
  · intro h
    have hz : (w-t^2)*(w-t^3)=0 := by
      simpa only [mul_eq_zero, sub_eq_zero] using h
    have heq : w*(1-w)=1-t := by nlinarith
    rw [heq]
    ring

/-- With either of those fixed input populations, only tick five attains
the target. Repeating the same reduced channel takes it past the target. -/
theorem only_fifth {t w : ℝ} (ht : 0<t) (hc : t^3+t^2=1)
    (hw : w=t^2 ∨ w=t^3) (n : ℕ) :
    determinant t w n=t*(1-t) ↔ n=5 := by
  have hhi := (bounds ht hc).2
  have h5 := (fifth_iff ht hc w).2 hw
  have hcoef : 0<w*(1-w) := by
    rcases hw with rfl|rfl
    · rw [show 1-t^2=t^3 by linarith]
      positivity
    · rw [show 1-t^3=t^2 by linarith]
      positivity
  constructor
  · intro h
    have heq := h.trans h5.symm
    have hdiff : 1-t^n=1-t^5 := mul_left_cancel₀ hcoef.ne' heq
    exact (pow_right_strictAnti₀ ht hhi).injective (by linarith)
  · rintro rfl
    exact h5

theorem first_tick_inputs {t w : ℝ} {s z : ℂ} (ht : 0<t) (hc : t^3+t^2=1)
    (hs : Complex.normSq s = t) (hz : Complex.normSq z = w*(1-w)) :
    (∀ n < 5, ¬ HasHardySpectrum t (reduced w s z n)) ∧
      (HasHardySpectrum t (reduced w s z 5) ↔ w=t^2 ∨ w=t^3) := by
  refine ⟨fun n hn h => (before_five ht hc w hn).ne ((spectrum_iff_determinant n hs hz).1 h), ?_⟩
  exact (spectrum_iff_determinant 5 hs hz).trans (fifth_iff ht hc w)

#print axioms det_reduced
#print axioms before_five
#print axioms fifth_iff
#print axioms only_fifth
#print axioms first_tick_inputs
#print axioms increment_law
end HardyClockPreparation
