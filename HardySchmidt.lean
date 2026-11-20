module

public import Mathlib.Analysis.Matrix.PosDef
public import Mathlib.Tactic

@[expose] public section
/-! Schmidt reduction for two complex qubits in coefficient-matrix coordinates. -/
noncomputable section

open Matrix Complex
open scoped Matrix ComplexConjugate ComplexOrder

namespace HardySchmidt

abbrev M := Matrix (Fin 2) (Fin 2) ℂ
abbrev Vect := Fin 2 → ℂ

def ip (x y : Vect) : ℂ := conj (x 0) * y 0 + conj (x 1) * y 1

def perp (x : Vect) : Vect := ![-conj (x 1), conj (x 0)]

private lemma ip_perp (x : Vect) : ip x (perp x) = 0 := by
  simp [ip, perp]; ring

private lemma ip_flip (x y : Vect) : ip y x = conj (ip x y) := by
  simp [ip]; ring

private lemma ip_perp_perp (x : Vect) : ip (perp x) (perp x) = ip x x := by
  simp [ip, perp]; ring

private lemma col_gram (B : M) (i j : Fin 2) :
    ip (B.col i) (B.col j) = (Bᴴ * B) i j := by
  simp [ip, Matrix.mul_apply, Fin.sum_univ_two, Matrix.conjTranspose_apply,
    Matrix.col]

private lemma col_zero {x : Vect} (h : ip x x = 0) : x = 0 := by
  have he : (Complex.normSq (x 0) : ℂ) + Complex.normSq (x 1) = 0 := by
    simpa only [Complex.normSq_eq_conj_mul_self, ip] using h
  have hsum := congrArg Complex.re he
  simp only [Complex.add_re, Complex.ofReal_re, Complex.zero_re] at hsum
  have h₀ : x 0 = 0 := Complex.normSq_eq_zero.mp (by linarith [Complex.normSq_nonneg (x 0), Complex.normSq_nonneg (x 1)])
  have h₁ : x 1 = 0 := Complex.normSq_eq_zero.mp (by linarith [Complex.normSq_nonneg (x 0), Complex.normSq_nonneg (x 1)])
  funext i; fin_cases i <;> assumption

private def scaled (x : Vect) (s : ℝ) : Vect := fun i => x i / (s : ℂ)

private lemma ip_scaled (x y : Vect) (r s : ℝ) :
    ip (scaled x r) (scaled y s) = ip x y / ((r : ℂ) * s) := by
  simp [ip, scaled, div_eq_mul_inv]; ring

private lemma normalized {x : Vect} {s : ℝ} (hs : s ≠ 0)
    (h : ip x x = (s : ℂ)^2) : ip (scaled x s) (scaled x s) = 1 := by
  rw [ip_scaled, h, ← sq]
  exact div_self (pow_ne_zero _ (Complex.ofReal_ne_zero.mpr hs))

private lemma scaled_mul {s : ℝ} (hs : s ≠ 0) (x : Vect) (i : Fin 2) :
    scaled x s i * (s : ℂ) = x i :=
  div_mul_cancel₀ _ (Complex.ofReal_ne_zero.mpr hs)

private def columns (x y : Vect) : M := Matrix.of fun i j => (![x,y] : Fin 2 → Vect) j i

private lemma fromCols {x y : Vect} (hx : ip x x = 1) (hy : ip y y = 1)
    (hxy : ip x y = 0) : columns x y ∈ Matrix.unitaryGroup (Fin 2) ℂ := by
  apply Matrix.mem_unitaryGroup_iff'.mpr
  have hyx : ip y x = 0 := by rw [ip_flip, hxy, map_zero]
  ext i j
  change ((columns x y)ᴴ * columns x y) i j = _
  rw [← col_gram]
  fin_cases i <;> fin_cases j <;> first | exact hx | exact hy | exact hxy | exact hyx

/-- Complete the normalized nonzero columns to a unitary basis. The rank-one cases
use the explicit Hermitian perpendicular of the surviving column. -/
private lemma factor_columns (B : M) (s : Fin 2 → ℝ)
    (hn : ∀ j, ip (B.col j) (B.col j) = (s j : ℂ)^2)
    (ho : ip (B.col 0) (B.col 1) = 0)
    (hne : s 0 ≠ 0 ∨ s 1 ≠ 0) :
    ∃ U : Matrix.unitaryGroup (Fin 2) ℂ, B = (U : M) * Matrix.diagonal (fun j => (s j : ℂ)) := by
  suffices ∃ x y : Vect, ip x x = 1 ∧ ip y y = 1 ∧ ip x y = 0 ∧
      (∀ i, x i * s 0 = B i 0) ∧ (∀ i, y i * s 1 = B i 1) by
    obtain ⟨x,y,hx,hy,hxy,h₀,h₁⟩ := this
    refine ⟨⟨columns x y, fromCols hx hy hxy⟩, ?_⟩
    ext i j
    rw [Matrix.mul_diagonal]
    fin_cases j <;> first | exact (h₀ i).symm | exact (h₁ i).symm
  by_cases h₀ : s 0 = 0
  · have h₁ : s 1 ≠ 0 := hne.resolve_left (not_not_intro h₀)
    have hz := col_zero (x := B.col 0) (by rw [hn, h₀]; norm_num)
    let y := scaled (B.col 1) (s 1)
    have hy : ip y y = 1 := normalized h₁ (hn 1)
    exact ⟨perp y, y, (ip_perp_perp y).trans hy, hy,
      by rw [ip_flip, ip_perp, map_zero],
      fun i => by rw [h₀]; simpa using (congrFun hz i).symm,
      fun i => scaled_mul h₁ _ i⟩
  · let x := scaled (B.col 0) (s 0)
    have hx : ip x x = 1 := normalized h₀ (hn 0)
    by_cases h₁ : s 1 = 0
    · have hz := col_zero (x := B.col 1) (by rw [hn, h₁]; norm_num)
      exact ⟨x, perp x, hx, (ip_perp_perp x).trans hx, ip_perp x, fun i => scaled_mul h₀ _ i,
        fun i => by rw [h₁]; simpa using (congrFun hz i).symm⟩
    · exact ⟨x, scaled (B.col 1) (s 1), hx, normalized h₁ (hn 1),
        by rw [show x = scaled (B.col 0) (s 0) from rfl, ip_scaled, ho, zero_div],
        fun i => scaled_mul h₀ _ i, fun i => scaled_mul h₁ _ i⟩

/-- A normalized two-qubit coefficient matrix has nonnegative Schmidt coefficients.
The statement includes singular matrices and repeated singular values. -/
theorem exists_schmidt (C : M)
    (hC : ∑ i, ∑ j, Complex.normSq (C i j) = 1) :
    ∃ (s : Fin 2 → ℝ) (U V : Matrix.unitaryGroup (Fin 2) ℂ),
      (∀ i, 0 ≤ s i) ∧ s 0 ^ 2 + s 1 ^ 2 = 1 ∧
      C = (U : M) * Matrix.diagonal (fun i => (s i : ℂ)) * (V : M)ᴴ := by
  classical
  let G := Cᴴ * C
  have hp : G.PosSemidef := Matrix.posSemidef_conjTranspose_mul_self C
  let V := hp.1.eigenvectorUnitary
  let B := C * (V : M)
  let s (i : Fin 2) := Real.sqrt (hp.1.eigenvalues i)
  have hs (i : Fin 2) : s i ^ 2 = hp.1.eigenvalues i := Real.sq_sqrt (hp.eigenvalues_nonneg i)
  have hdiag : (V : M)ᴴ * G * (V : M) = diagonal (fun i => (hp.1.eigenvalues i : ℂ)) := by
    have hh := hp.1.conjStarAlgAut_star_eigenvectorUnitary
    rw [Unitary.conjStarAlgAut_star_apply] at hh
    convert hh using 1
    rw [RCLike.ofReal_eq_complex_ofReal]; rfl
  have hgram : Bᴴ * B = diagonal (fun i => (hp.1.eigenvalues i : ℂ)) := by
    simpa only [B, G, Matrix.conjTranspose_mul, Matrix.mul_assoc] using hdiag
  have hcov : (V : M) * (V : M)ᴴ = 1 := Matrix.mem_unitaryGroup_iff.mp V.property
  have ht : G.trace = 1 := by
    simp only [Fin.sum_univ_two] at hC
    have hh := congrArg Complex.ofReal hC
    simp only [Complex.ofReal_add, Complex.ofReal_one, Complex.normSq_eq_conj_mul_self] at hh
    simpa only [G, Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.conjTranspose_apply,
      Fin.sum_univ_two, Complex.star_def, add_add_add_comm] using hh
  have ht' := congrArg Matrix.trace hdiag
  rw [Matrix.trace_mul_cycle, hcov, one_mul, ht, Matrix.trace_diagonal, Fin.sum_univ_two] at ht'
  have hn : s 0 ^ 2 + s 1 ^ 2 = 1 := by
    rw [hs, hs]
    exact_mod_cast ht'.symm
  have hlen (j : Fin 2) : ip (B.col j) (B.col j) = (s j : ℂ)^2 := by
    rw [col_gram, hgram, Matrix.diagonal_apply_eq, ← Complex.ofReal_pow, hs]
  have horth : ip (B.col 0) (B.col 1) = 0 := by rw [col_gram, hgram]; simp
  have hnz : s 0 ≠ 0 ∨ s 1 ≠ 0 := by
    by_contra! hz; simp [hz.1,hz.2] at hn
  obtain ⟨U, hf⟩ := factor_columns B s hlen horth hnz
  refine ⟨s, U, V, fun i => Real.sqrt_nonneg _, hn, ?_⟩
  rw [← hf, show B = C * (V : M) from rfl, Matrix.mul_assoc, hcov, mul_one]

/-- Bilinear Born amplitude with the measurement coordinates taken as bras. -/
def amplitude (C : M) (v w : Vect) : ℂ := v ⬝ᵥ (C *ᵥ w)

/-- Exact amplitude identity in the local Schmidt bases. -/
theorem amplitude_change {C : M} {s : Fin 2 → ℝ}
    {U V : Matrix.unitaryGroup (Fin 2) ℂ}
    (hc : C = (U : M) * diagonal (fun i => (s i : ℂ)) * (V : M)ᴴ)
    (v w : Vect) :
    amplitude C v w =
      (s 0 : ℂ) * ((U : M)ᵀ *ᵥ v) 0 * ((V : M)ᴴ *ᵥ w) 0 +
      (s 1 : ℂ) * ((U : M)ᵀ *ᵥ v) 1 * ((V : M)ᴴ *ᵥ w) 1 := by
  rw [amplitude, hc, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec,
    Matrix.mulVec_transpose]
  simp only [dotProduct, Fin.sum_univ_two, Matrix.mulVec_diagonal]
  ring

private lemma ip_dot (x y : Vect) : ip x y = (star x) ⬝ᵥ y := by
  simp [ip, dotProduct, Fin.sum_univ_two]

theorem ip_change (T : Matrix.unitaryGroup (Fin 2) ℂ) (x y : Vect) :
    ip ((T : M) *ᵥ x) ((T : M) *ᵥ y) = ip x y := by
  rw [ip_dot, ip_dot, Matrix.star_mulVec, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec,
    show (T : M)ᴴ * (T : M) = 1 from Matrix.mem_unitaryGroup_iff'.mp T.property, Matrix.one_mulVec]

private lemma ip_one_iff (x : Vect) :
    ip x x = 1 ↔ ‖x 0‖^2 + ‖x 1‖^2 = 1 := by
  rw [ip, Complex.sq_norm, Complex.sq_norm, ← Complex.normSq_eq_conj_mul_self,
    ← Complex.normSq_eq_conj_mul_self, ← Complex.ofReal_add]
  exact Complex.ofReal_inj

theorem unit_change (T : Matrix.unitaryGroup (Fin 2) ℂ) {x : Vect}
    (h : ‖x 0‖^2 + ‖x 1‖^2 = 1) :
    ‖((T : M) *ᵥ x) 0‖^2 + ‖((T : M) *ᵥ x) 1‖^2 = 1 := by
  rw [← ip_one_iff, ip_change, ip_one_iff]; exact h

private lemma orthogonal_span {x y : Vect} (hn : ip x x = 1) (ho : ip x y = 0) :
    ∀ i, y i = ip (perp x) y * perp x i := by
  simp only [ip] at hn ho
  intro i
  fin_cases i <;> simp [perp, ip]
  · linear_combination -(y 0) * hn + (x 0) * ho
  · linear_combination -(y 1) * hn + (x 1) * ho

/-- Changing the measurement basis takes the complementary outcome to the
complement of the transported ray, up to a nonzero complex scalar. -/
theorem perp_change (T : Matrix.unitaryGroup (Fin 2) ℂ) {x : Vect}
    (h : ‖x 0‖^2 + ‖x 1‖^2 = 1) :
    ∃ k : ℂ, k ≠ 0 ∧ ∀ i, ((T : M) *ᵥ perp x) i = k * perp ((T : M) *ᵥ x) i := by
  let a := (T : M) *ᵥ x
  let b := (T : M) *ᵥ perp x
  have hx : ip x x = 1 := (ip_one_iff x).2 h
  have ha : ip a a = 1 := (ip_change _ _ _).trans hx
  have hb : ip b b = 1 := (ip_change _ _ _).trans ((ip_perp_perp x).trans hx)
  have ho : ip a b = 0 := (ip_change _ _ _).trans (ip_perp x)
  have he := orthogonal_span ha ho
  refine ⟨ip (perp a) b, ?_, he⟩
  intro hz
  have hzero : b = 0 := funext fun i => by simpa [hz] using he i
  simp [hzero, ip] at hb

end HardySchmidt
