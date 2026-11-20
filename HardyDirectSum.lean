module

public import HardyExtension.Definitions
public import HardyComplex

@[expose] public section
/-! An explicit pure higher-rank realization by matched orthogonal qubit sectors. -/
noncomputable section
namespace HardyDirectSum

open HardyComplex
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Both binary outcomes in one sector, in the order used by the Hardy ladder. -/
def outcome (v : Vec) (k : Fin 2) : Vec := ![v, perp v] k

private theorem outcome_inner (v : Vec) (hv : UnitRay v) (k l : Fin 2) :
    (∑ m, star (outcome v k m) * outcome v l m) = if k = l then 1 else 0 := by
  have h : (‖v 0‖ ^ 2 : ℂ) + (‖v 1‖ ^ 2 : ℂ) = 1 := by
    unfold UnitRay at hv
    exact_mod_cast hv
  fin_cases k <;> fin_cases l <;>
    simp [Fin.sum_univ_two, outcome, perp, Complex.conj_mul'] <;> first | exact h | linear_combination h | ring

/-- Each binary local measurement has a full square family of orthonormal
rays, indexed by sector and outcome. -/
theorem measurement_orthonormal (v : Vec) (hv : UnitRay v) (i j : ι) (k l : Fin 2) :
    (∑ p : ι × Fin 2, star (embedded i (outcome v k) p) * embedded j (outcome v l) p) =
      if (i,k) = (j,l) then 1 else 0 := by
  rw [Fintype.sum_prod_type, Finset.sum_eq_single i]
  · by_cases h : i = j
    · subst j
      simpa [embedded] using outcome_inner v hv k l
    · simp [embedded, h]
  · intro m _ hm
    simp [embedded, hm]
  · simp

private theorem sector_amp (w : ι → ℝ) (c d : ℝ) (i j : ι) (v z : Vec) :
    (∑ p : ι × Fin 2, (schmidt w c d p : ℂ) * embedded i v p * embedded j z p) =
      if i = j then (Real.sqrt (w i) : ℂ) * amp c d v z else 0 := by
  rw [Fintype.sum_prod_type]
  rw [Finset.sum_eq_single i]
  · by_cases h : i = j
    · subst j
      simp [schmidt, embedded, Fin.sum_univ_two, amp]
      ring
    · simp [embedded, h]
  · intro k _ hk
    simp [embedded, hk]
  · simp

/-- Every qubit joint outcome probability is preserved by the direct sum. -/
theorem event_lift (w : ι → ℝ) (hw : ∀ i, 0 ≤ w i) (hn : ∑ i, w i = 1)
    (c d : ℝ) (v z : Vec) :
    event (schmidt w c d) v z = ‖amp c d v z‖ ^ 2 := by
  unfold event
  simp_rw [sector_amp, apply_ite (fun x : ℂ => ‖x‖), norm_zero, ite_pow, zero_pow (by decide : 2 ≠ 0)]
  simp only [Finset.sum_ite_eq, Finset.mem_univ, ite_true, norm_mul, mul_pow,
    Complex.norm_real, Real.norm_eq_abs, sq_abs, Real.sq_sqrt (hw _)]
  rw [← Finset.sum_mul, hn, one_mul]

omit [DecidableEq ι] in
theorem normalized (w : ι → ℝ) (hw : ∀ i, 0 ≤ w i) (hn : ∑ i, w i = 1)
    {c d : ℝ} (hcd : c ^ 2 + d ^ 2 = 1) :
    ∑ p : ι × Fin 2, schmidt w c d p ^ 2 = 1 := by
  rw [Fintype.sum_prod_type]
  simpa [schmidt, Fin.sum_univ_two, mul_pow, Real.sq_sqrt (hw _), ← mul_add, hcd] using hn

theorem ladder_lift (w : ι → ℝ) (hw : ∀ i, 0 ≤ w i) (hn : ∑ i, w i = 1)
    {c d : ℝ} {a b : ℕ → Vec} (h : Ladder c d a b) :
    Lifted (schmidt w c d) a b (‖amp c d (a 2) (b 2)‖ ^ 2) := by
  refine ⟨h.unitA,h.unitB,?_,?_,?_,event_lift w hw hn ..⟩
  · simp [event_lift w hw hn,h.base]
  · intro k hk
    simp [event_lift w hw hn,h.stepA k hk]
  · intro k hk
    simp [event_lift w hw hn,h.stepB k hk]

private theorem num_pos : ∀ i, 0 < numerator i := by decide
private theorem num_inj : ∀ i j, numerator i = numerator j → i = j := by decide
private theorem num_gap : ∀ i j, numerator j ≤ 3 * numerator i ∨
    31 * numerator i ≤ 10 * numerator j := by decide

private theorem weights_pos (i : Fin 6) : 0 < weights i := by
  exact div_pos (by exact_mod_cast num_pos i) (by norm_num)

private theorem weights_sum : ∑ i, weights i = 1 := by
  norm_num [weights, numerator, Fin.sum_univ_succ]

private theorem weights_inj : Function.Injective weights := by
  intro i j h
  apply num_inj
  unfold weights at h
  have h' : (numerator i : ℝ) = numerator j := by linarith
  exact_mod_cast h'

/-- Rational separation suffices to distinguish cross-sector eigenvalues. -/
private theorem rho_four_interval {ρ : ℝ} (hρ : ρ^3 = ρ+1) :
    3 < ρ^4 ∧ ρ^4 < 31/10 := by
  have hp := HardyLadder.five_quarters_lt_of_cubic hρ
  have lo : 33/25 < ρ := by
    by_contra! h
    have prod := mul_nonneg (sub_nonneg.mpr h)
      (show 0 ≤ ρ^2 + 33/25*ρ + (33/25)^2 - 1 by nlinarith [sq_nonneg ρ])
    nlinarith
  have hi : ρ < 133/100 := by
    by_contra! h
    have prod := mul_nonneg (sub_nonneg.mpr h)
      (show 0 ≤ ρ^2 + 133/100*ρ + (133/100)^2 - 1 by nlinarith [sq_nonneg ρ])
    nlinarith
  have pow4 : ρ^4 = ρ^2 + ρ := by linear_combination ρ*hρ
  rw [pow4]
  constructor
  · nlinarith [mul_pos (sub_pos.mpr lo) (show 0 < ρ+33/25 by linarith)]
  · nlinarith [mul_pos (sub_pos.mpr hi) (show 0 < ρ+133/100 by linarith)]

private theorem no_cross {ρ : ℝ} (hρ : ρ^3 = ρ+1) (i j : Fin 6) :
    weights i * ρ⁻¹ ≠ weights j * ρ⁻¹^5 := by
  intro h
  have hp := HardyLadder.five_quarters_lt_of_cubic hρ
  have hn : ρ ≠ 0 := by linarith
  have hi : 0 < (numerator i : ℝ) := by exact_mod_cast num_pos i
  have e : (numerator i : ℝ) * ρ^4 = numerator j := by
    unfold weights at h
    field_simp [hn] at h
    nlinarith [h]
  obtain ⟨hlo,hhi⟩ := rho_four_interval hρ
  rcases num_gap i j with hsmall | hlarge
  · have hs : (numerator j : ℝ) ≤ 3 * numerator i := by exact_mod_cast hsmall
    linarith [mul_lt_mul_of_pos_left hlo hi]
  · have hs : 31 * (numerator i : ℝ) ≤ 10 * numerator j := by exact_mod_cast hlarge
    linarith [mul_lt_mul_of_pos_left hhi hi]

private theorem sq_zero (c d : ℝ) (i : Fin 6) :
    schmidt weights c d (i,0) ^ 2 = weights i * c^2 := by
  simp [schmidt, mul_pow, Real.sq_sqrt (weights_pos i).le]

private theorem sq_one (c d : ℝ) (i : Fin 6) :
    schmidt weights c d (i,1) ^ 2 = weights i * d^2 := by
  simp [schmidt, mul_pow, Real.sq_sqrt (weights_pos i).le]

private theorem weights_distinct {ρ c d : ℝ} (hρ : ρ^3 = ρ+1)
    (hc : 0 < c) (hd : 0 < d) (wc : c^2 = ρ⁻¹) (wd : d^2 = ρ⁻¹^5) :
    Function.Injective (fun p => schmidt weights c d p ^ 2) := by
  rintro ⟨i,k⟩ ⟨j,l⟩ h
  fin_cases k <;> fin_cases l
  · change schmidt weights c d (i,0) ^ 2 = schmidt weights c d (j,0) ^ 2 at h
    rw [sq_zero, sq_zero] at h
    have := weights_inj (mul_right_cancel₀ (pow_ne_zero 2 hc.ne') h)
    subst j
    rfl
  · change schmidt weights c d (i,0) ^ 2 = schmidt weights c d (j,1) ^ 2 at h
    rw [sq_zero, sq_one, wc, wd] at h
    exact (no_cross hρ i j h).elim
  · change schmidt weights c d (i,1) ^ 2 = schmidt weights c d (j,0) ^ 2 at h
    rw [sq_one, sq_zero, wc, wd] at h
    exact (no_cross hρ j i h.symm).elim
  · change schmidt weights c d (i,1) ^ 2 = schmidt weights c d (j,1) ^ 2 at h
    rw [sq_one, sq_one] at h
    have := weights_inj (mul_right_cancel₀ (pow_ne_zero 2 hd.ne') h)
    subst j
    rfl

/-- A normalized pure state on twelve local levels with twelve pairwise
distinct positive squared Schmidt coefficients attains the exact qubit value. -/
theorem twelve_level_attainment {ρ : ℝ} (hρ : ρ^3 = ρ+1) :
    ∃ (s : Fin 6 × Fin 2 → ℝ) (a b : ℕ → Vec),
      (∀ p, 0 < s p) ∧ (∑ p, s p ^ 2 = 1) ∧ Function.Injective (fun p => s p ^ 2) ∧
      (∀ i, s (i,0)^2 = weights i * ρ⁻¹ ∧ s (i,1)^2 = weights i * ρ⁻¹^5) ∧
      Lifted s a b ((8*ρ^2+ρ-11)/25) := by
  obtain ⟨c,d,hc,hd,hn,wc,wd,a,b,hl,hs⟩ := complex_attained hρ
  refine ⟨schmidt weights c d, a, b, ?_,
    normalized weights (fun i => (weights_pos i).le) weights_sum hn,
    weights_distinct hρ hc hd wc wd, ?_, ?_⟩
  · rintro ⟨i,k⟩
    have hp := Real.sqrt_pos.mpr (weights_pos i)
    fin_cases k
    · exact mul_pos hp hc
    · exact mul_pos hp hd
  · intro i
    simp [sq_zero, sq_one, wc, wd]
  · rw [← hs]
    exact ladder_lift weights (fun i => (weights_pos i).le) weights_sum hl

end HardyDirectSum

#print axioms HardyDirectSum.event_lift
#print axioms HardyDirectSum.twelve_level_attainment
