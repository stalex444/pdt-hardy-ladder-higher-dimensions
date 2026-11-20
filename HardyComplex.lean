module

public import HardyExtension.Definitions
public import HardyLadder

@[expose] public section
/-! The two-step Hardy ladder for complex rank-one measurements in Schmidt coordinates. -/
namespace HardyComplex
open Real
structure Ladder (c d : ℝ) (a b : ℕ → Vec) : Prop where
  unitA : ∀ k, UnitRay (a k)
  unitB : ∀ k, UnitRay (b k)
  base : amp c d (a 0) (b 0) = 0
  stepA : ∀ k < 2, amp c d (a (k+1)) (perp (b k)) = 0
  stepB : ∀ k < 2, amp c d (perp (a k)) (b (k+1)) = 0

private theorem collinear {u v x y : ℂ} (hn : x ≠ 0 ∨ y ≠ 0)
    (h : u * y = v * x) : ∃ e : ℂ, u = e*x ∧ v = e*y := by
  rcases hn with hx | hy
  · refine ⟨u/x, by field_simp, ?_⟩
    field_simp
    linear_combination -h
  · refine ⟨v/y, ?_, by field_simp⟩
    field_simp
    linear_combination h

private theorem step_ray {c d : ℝ} (hc : 0 < c) (hd : 0 < d)
    {v w : Vec} (hw : UnitRay w) (h : amp c d v (perp w) = 0) :
    ∃ e : ℂ, v 0 = e*((d:ℂ)*star (w 0)) ∧ v 1 = e*((c:ℂ)*star (w 1)) := by
  apply collinear
  · have hc' : (c:ℂ) ≠ 0 := by exact_mod_cast hc.ne'
    have hd' : (d:ℂ) ≠ 0 := by exact_mod_cast hd.ne'
    by_contra! hz
    simp [hc',hd'] at hz
    simp [UnitRay, hz.1, hz.2] at hw
  · change (c:ℂ)*v 0*(-star (w 1)) + (d:ℂ)*v 1*star (w 0) = 0 at h
    linear_combination -h

theorem amp_comm (c d : ℝ) (a b : Vec) : amp c d a b = amp c d b a := by
  unfold amp
  ring

/-- Destructive interference at one rung propagates with two different positive weights. -/
private theorem advance {c d s t : ℝ} (hc : 0<c) (hd : 0<d)
    {a b a' b' : Vec} (ha : UnitRay a) (hb : UnitRay b)
    (hz : amp s t a b = 0)
    (hA : amp c d a' (perp b) = 0) (hB : amp c d (perp a) b' = 0) :
    amp (s*c^2) (t*d^2) a' b' = 0 := by
  obtain ⟨e, he0, he1⟩ := step_ray hc hd hb hA
  rw [amp_comm] at hB
  obtain ⟨f, hf0, hf1⟩ := step_ray hc hd ha hB
  have h := congrArg (star : ℂ → ℂ) hz
  simp only [amp, star_add, star_mul, Complex.star_def, Complex.conj_ofReal, map_zero] at h
  unfold amp
  rw [he0,he1,hf0,hf1]
  push_cast
  simp only [Complex.star_def]
  linear_combination e*f*(c:ℂ)^2*(d:ℂ)^2*h

private theorem opposite_norm {x y : ℂ} {s t : ℝ} (hs : 0<s) (ht : 0<t)
    (h : (s:ℂ)*x + (t:ℂ)*y = 0) : ‖x+y‖^2 = (‖x‖-‖y‖)^2 := by
  have ht' : (t:ℂ) ≠ 0 := by exact_mod_cast ht.ne'
  have hy : y = -((s/t:ℝ):ℂ)*x := by
    push_cast
    field_simp
    linear_combination h
  rw [hy, show x + -((s/t : ℝ):ℂ)*x = ((1-s/t:ℝ):ℂ)*x by push_cast; ring]
  simp only [norm_mul, norm_neg, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (div_pos hs ht)]
  rw [mul_pow, sq_abs]
  ring

private noncomputable def angle (v : Vec) := Real.arccos ‖v 0‖

private theorem angle_cs {v : Vec} (hv : UnitRay v) :
    cos (angle v) = ‖v 0‖ ∧ sin (angle v) = ‖v 1‖ := by
  unfold UnitRay at hv
  have hle : ‖v 0‖ ≤ 1 := by nlinarith [norm_nonneg (v 0), sq_nonneg ‖v 1‖]
  constructor
  · exact Real.cos_arccos (by linarith [norm_nonneg (v 0)]) hle
  · rw [angle, Real.sin_arccos, show 1 - ‖v 0‖ ^ 2 = ‖v 1‖ ^ 2 by linarith,
        Real.sqrt_sq (norm_nonneg _)]

private theorem eq_norm_of_add_zero {x y : ℂ} (h : x+y=0) : ‖x‖ = ‖y‖ := by
  rw [eq_neg_of_add_eq_zero_left h, norm_neg]

private theorem component_norms {c d : ℝ} (hc : 0<c) (hd : 0<d) {v w : Vec}
    (h : amp c d v w = 0) : c*‖v 0‖*‖w 0‖ = d*‖v 1‖*‖w 1‖ := by
  simpa [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hc, abs_of_pos hd]
    using eq_norm_of_add_zero h

private structure RealCopy (c d : ℝ) (a b : ℕ → ℝ) (p : ℝ) : Prop where
  base : (c*cos (a 0)*cos (b 0) + d*sin (a 0)*sin (b 0))^2=0
  stepA : ∀ k < 2, (c*cos (a (k+1))*(-sin (b k)) + d*sin (a (k+1))*cos (b k))^2=0
  stepB : ∀ k < 2, (c*(-sin (a k))*cos (b (k+1)) + d*cos (a k)*sin (b (k+1)))^2=0
  success : (c*cos (a 2)*cos (b 2) + d*sin (a 2)*sin (b 2))^2=p

/-- Recover real settings for all five zeros and the success event, including coordinate axes. -/
private theorem real_copy {c d : ℝ} (hc : 0<c) (hd : 0<d) {a b : ℕ → Vec}
    (h : Ladder c d a b) : ∃ x y, RealCopy c d x y (‖amp c d (a 2) (b 2)‖^2) := by
  let x (k : ℕ) := if k=1 then -angle (a k) else angle (a k)
  let y (k : ℕ) := if k=1 then angle (b k) else -angle (b k)
  have ac := fun k => angle_cs (h.unitA k)
  have bc := fun k => angle_cs (h.unitB k)
  have h₀ := component_norms hc hd h.base
  have hA (k : ℕ) (hk : k<2) := component_norms hc hd (h.stepA k hk)
  have hB (k : ℕ) (hk : k<2) := component_norms hc hd (h.stepB k hk)
  simp [perp] at hA hB
  refine ⟨x,y,?_,?_,?_,?_⟩
  · simp [x,y,(ac _).1,(bc _).1,(ac _).2,(bc _).2]
    linarith
  · intro k hk
    have h' := hA k (by omega)
    interval_cases k <;> norm_num [x,y,(ac _).1,(bc _).1,(ac _).2,(bc _).2] at * <;> linarith
  · intro k hk
    have h' := hB k (by omega)
    interval_cases k <;> norm_num [x,y,(ac _).1,(bc _).1,(ac _).2,(bc _).2] at * <;> linarith
  · have h1 := advance hc hd (h.unitA 0) (h.unitB 0) h.base (h.stepA 0 (by decide)) (h.stepB 0 (by decide))
    have h2 := advance hc hd (h.unitA 1) (h.unitB 1) h1 (h.stepA 1 (by decide)) (h.stepB 1 (by decide))
    let u := (c:ℂ) * a 2 0 * b 2 0
    let v := (d:ℂ) * a 2 1 * b 2 1
    have hu : (((c^4:ℝ):ℂ))*u + (((d^4:ℝ):ℂ))*v = 0 := by
      unfold amp at h2
      dsimp [u,v]; push_cast at *
      linear_combination h2
    have hn := opposite_norm (x:=u) (y:=v) (by positivity : 0<c^4) (by positivity : 0<d^4) hu
    change _ = ‖u+v‖^2
    rw [hn]
    simp [x,y,u,v,(ac _).1,(bc _).1,(ac _).2,(bc _).2, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos hc, abs_of_pos hd]
    ring

/-- A one-coordinate (product) state has zero success under the five exact constraints. -/
private theorem product_zero (i : Fin 2) {a b : ℕ → Vec}
    (ua : ∀ k, UnitRay (a k)) (ub : ∀ k, UnitRay (b k))
    (base : a 0 i * b 0 i = 0)
    (sa : ∀ k < 2, a (k+1) i * perp (b k) i = 0)
    (sb : ∀ k < 2, perp (a k) i * b (k+1) i = 0) :
    a 2 i * b 2 i = 0 := by
  have force {v : Vec} (hv : UnitRay v) (hp : perp v i = 0) : v i ≠ 0 := by
    intro hz
    fin_cases i <;> simp [perp] at hp <;> simp_all [UnitRay]
  have A {k : ℕ} (hk : k<2) (hn : a (k+1) i ≠ 0) : b k i ≠ 0 :=
    force (ub k) ((mul_eq_zero.mp (sa k hk)).resolve_left hn)
  have B {k : ℕ} (hk : k<2) (hn : b (k+1) i ≠ 0) : a k i ≠ 0 :=
    force (ua k) ((mul_eq_zero.mp (sb k hk)).resolve_right hn)
  by_contra hn
  have na : a 2 i ≠ 0 := fun hz => hn (by rw [hz,zero_mul])
  have nb : b 2 i ≠ 0 := fun hz => hn (by rw [hz,mul_zero])
  exact (mul_ne_zero (B (k:=0) (by decide) (A (k:=1) (by decide) na))
    (A (k:=0) (by decide) (B (k:=1) (by decide) nb))) base

private theorem deficient {c d : ℝ} {a b : ℕ → Vec} (h : Ladder c d a b)
    (hc : c=0 ∨ d=0) : amp c d (a 2) (b 2) = 0 := by
  rcases hc with rfl | rfl
  · by_cases hd : d=0
    · simp [amp,hd]
    have hd' : (d:ℂ) ≠ 0 := by exact_mod_cast hd
    have hb := h.base
    have sa := h.stepA
    have sb := h.stepB
    simp only [amp, Complex.ofReal_zero, zero_mul, zero_add, mul_assoc, mul_eq_zero,
      hd', false_or] at hb sa sb ⊢
    exact mul_eq_zero.mp (product_zero 1 h.unitA h.unitB (mul_eq_zero.mpr hb)
      (fun k hk => mul_eq_zero.mpr (sa k hk)) (fun k hk => mul_eq_zero.mpr (sb k hk)))
  · by_cases hc : c=0
    · simp [amp,hc]
    have hc' : (c:ℂ) ≠ 0 := by exact_mod_cast hc
    have hb := h.base
    have sa := h.stepA
    have sb := h.stepB
    simp only [amp, Complex.ofReal_zero, zero_mul, add_zero, mul_assoc, mul_eq_zero,
      hc', false_or] at hb sa sb ⊢
    exact mul_eq_zero.mp (product_zero 0 h.unitA h.unitB (mul_eq_zero.mpr hb)
      (fun k hk => mul_eq_zero.mpr (sa k hk)) (fun k hk => mul_eq_zero.mpr (sb k hk)))

/-- The exact plastic-number ceiling, including Schmidt rank one. Equality forces the weights. -/
theorem schmidt_bound_and_weights {ρ c d : ℝ} (hρ : ρ^3=ρ+1)
    (hc : 0≤c) (hd : 0≤d) (hn : c^2+d^2=1) {a b : ℕ → Vec} (h : Ladder c d a b) :
    ‖amp c d (a 2) (b 2)‖^2 ≤ (8*ρ^2+ρ-11)/25 ∧
    (‖amp c d (a 2) (b 2)‖^2 = (8*ρ^2+ρ-11)/25 →
      (c^2=ρ⁻¹ ∧ d^2=ρ⁻¹^5) ∨ (c^2=ρ⁻¹^5 ∧ d^2=ρ⁻¹)) := by
  by_cases hp : c=0 ∨ d=0
  · have hr := HardyLadder.five_quarters_lt_of_cubic hρ
    have hp' : 0 < (8*ρ^2+ρ-11)/25 := by nlinarith [sq_nonneg (ρ-5/4)]
    rw [deficient h hp, norm_zero, zero_pow (by decide : 2≠0)]
    exact ⟨hp'.le, fun he => (ne_of_lt hp' he).elim⟩
  · push Not at hp
    have hc' := lt_of_le_of_ne hc (Ne.symm hp.1)
    have hd' := lt_of_le_of_ne hd (Ne.symm hp.2)
    obtain ⟨x,y,r⟩ := real_copy hc' hd' h
    rw [← r.success]
    exact ⟨HardyLadder.ladder_K2_le hρ hc' hd' hn x y r.base r.stepA r.stepB,
      HardyLadder.ladder_K2_weights_of_eq hρ hc' hd' hn x y r.base r.stepA r.stepB⟩

private noncomputable def realRay (x : ℝ) : Vec := ![(cos x:ℝ), (sin x:ℝ)]

private theorem realRay_unit (x : ℝ) : UnitRay (realRay x) := by
  change ‖((cos x:ℝ):ℂ)‖^2+‖((sin x:ℝ):ℂ)‖^2=1
  simp only [Complex.norm_real,Real.norm_eq_abs,sq_abs,Real.cos_sq_add_sin_sq]

/-- Real strategies embed into complex ones, so the exact upper bound is attained. -/
theorem complex_attained {ρ : ℝ} (hρ : ρ^3=ρ+1) :
    ∃ c d : ℝ, 0<c ∧ 0<d ∧ c^2+d^2=1 ∧ c^2=ρ⁻¹ ∧ d^2=ρ⁻¹^5 ∧
    ∃ a b, Ladder c d a b ∧ ‖amp c d (a 2) (b 2)‖^2=(8*ρ^2+ρ-11)/25 := by
  obtain ⟨c,d,hc,hd,hn,wc,wd,x,y,h0,hA,hB,hp⟩ := HardyLadder.ladder_K2_attained hρ
  refine ⟨c,d,hc,hd,hn,wc,wd,fun k => realRay (x k),fun k => realRay (y k),
    ⟨fun _ => realRay_unit _,fun _ => realRay_unit _,?_,?_,?_⟩,?_⟩
  · simp [amp, realRay]
    exact_mod_cast (pow_eq_zero_iff (by decide : 2≠0)).mp h0
  · intro k hk
    simp only [amp, realRay, perp, Matrix.cons_val_zero, Matrix.cons_val_one, Complex.star_def, Complex.conj_ofReal]
    exact_mod_cast (pow_eq_zero_iff (by decide : 2≠0)).mp (hA k hk)
  · intro k hk
    simp only [amp, realRay, perp, Matrix.cons_val_zero, Matrix.cons_val_one, Complex.star_def, Complex.conj_ofReal]
    exact_mod_cast (pow_eq_zero_iff (by decide : 2≠0)).mp (hB k hk)
  · simp only [amp,realRay, Matrix.cons_val_zero, Matrix.cons_val_one]
    norm_cast
    simpa [Complex.norm_real,Real.norm_eq_abs,sq_abs] using hp

end HardyComplex
