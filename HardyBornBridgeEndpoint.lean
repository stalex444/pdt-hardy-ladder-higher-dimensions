module

public import HardyBornBridge
public import HardyRankOne

@[expose] public section
/-! Bessel's inequality for the actual rank-two Hardy endpoint. -/
noncomputable section
open Matrix HardyRankOne HardyFourPairing HardyBalancedPolynomial
namespace HardyBornBridge

private abbrev Space := EuclideanSpace ℂ (Fin 4)

private def column {k : ℕ} (X : Matrix (Fin 4) (Fin k) ℂ) (i : Fin k) : Space :=
  WithLp.toLp 2 (fun z => X z i)

private def frameOf {k : ℕ} (a : Fin k → Space) : Matrix (Fin 4) (Fin k) ℂ :=
  fun z i => a i z

private theorem column_frameOf {k : ℕ} (a : Fin k → Space) (i : Fin k) :
    column (frameOf a) i = a i := rfl

private def evolve (V : Frame) (d : Four) (k : ℕ) : Frame :=
  fun z i => (d z : ℂ)^k * V z i

private theorem column_evolve (V : Frame) (d : Four) (k : ℕ) (i : Fin 2) :
    column (evolve V d k) i = weighted d k (column V i) := by
  ext z
  change (d z : ℂ)^k * V z i = ((d z^k : ℝ) : ℂ) * V z i
  rw [Complex.ofReal_pow]

private theorem inner_column {k l : ℕ} (X : Matrix (Fin 4) (Fin k) ℂ)
    (Y : Matrix (Fin 4) (Fin l) ℂ) (i : Fin k) (j : Fin l) :
    inner ℂ (column X i) (column Y j) = (Xᴴ * Y) i j := by
  rw [EuclideanSpace.inner_eq_star_dotProduct]
  simp only [dotProduct, Matrix.mul_apply, Matrix.conjTranspose_apply, Pi.star_apply]
  apply Finset.sum_congr rfl
  intro z _
  exact mul_comm _ _

private theorem cross (V : Frame) (d : Four) (i j : ℕ) :
    (evolve V d i)ᴴ * evolve V d j = G V d (i+j) := by
  ext a b
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, evolve, G, gram,
    star_mul, star_pow, Complex.star_def, Complex.conj_ofReal, pow_add]
  apply Finset.sum_congr rfl
  intro z _
  ring

private theorem gram_orthonormal (a : Fin 2 → Space) (ha : Orthonormal ℂ a) :
    gram (frameOf a) 1 = 1 := by
  have matrixGram : gram (frameOf a) 1 = (frameOf a)ᴴ * frameOf a := by
    ext i j
    simp [gram, Matrix.mul_apply, Matrix.conjTranspose_apply]
  rw [matrixGram]
  ext i j
  rw [← inner_column, column_frameOf, column_frameOf, orthonormal_iff_ite.mp ha]
  rfl

private theorem squared_columns (X : Frame) :
    ∑ i, ‖column X i‖^2 = (Xᴴ * X).trace.re := by
  simp only [trace, diag, ← inner_column, inner_self_eq_norm_sq_to_K]
  simp [← Complex.ofReal_pow]

private theorem residual_trace (X W : Frame) (h : IsUnit (Wᴴ * W).det) :
    let H := Wᴴ * W
    let A := Wᴴ * X
    let Z := X - W * (H⁻¹ * A)
    (Zᴴ * Z).trace = (Xᴴ * X).trace - ((Xᴴ * W) * (H⁻¹ * A)).trace := by
  let H := Wᴴ * W
  let C := H⁻¹ * (Wᴴ * X)
  let Z := X - W * C
  change (Zᴴ * Z).trace = _ - ((Xᴴ * W) * C).trace
  have hz : Wᴴ * Z = 0 := by
    change Wᴴ * (X - W * (H⁻¹ * (Wᴴ * X))) = 0
    rw [Matrix.mul_sub, ← Matrix.mul_assoc, show Wᴴ * W = H from rfl,
      Matrix.mul_nonsing_inv_cancel_left _ _ h, sub_self]
  have hz' : Zᴴ * Z = Xᴴ * Z := by
    calc Zᴴ * Z = (Xᴴ - Cᴴ * Wᴴ) * Z := by
          rw [show Z = X - W*C from rfl, Matrix.conjTranspose_sub, Matrix.conjTranspose_mul]
         _ = Xᴴ * Z := by rw [Matrix.sub_mul, Matrix.mul_assoc, hz, Matrix.mul_zero, sub_zero]
  rw [hz']
  change (Xᴴ * (X-W*C)).trace = _
  rw [Matrix.mul_sub, ← Matrix.mul_assoc, Matrix.trace_sub]

/-- For a two-dimensional endpoint, the physical joint Born probability of any
orthonormal opposite endpoint obeying Hardy orthogonality is at most the best
pairing for the given Schmidt spectrum. -/
theorem rank_two_endpoint_le {s : ℕ} (d : Fin 4 → ℝ) (hd : ∀ i, 0<d i)
    (a : Fin 2 → EuclideanSpace ℂ (Fin 4)) (b : Fin s → EuclideanSpace ℂ (Fin 4))
    (ha : Orthonormal ℂ a) (hb : Orthonormal ℂ b)
    (hz : ∀ i j, inner ℂ (weighted d 5 (a i)) (b j)=0) :
    endpointScore d a b ≤ matchingMax d := by
  let V := frameOf a
  let X := evolve V d 1
  let W := evolve V d 5
  let Y := frameOf b
  let H := Wᴴ * W
  let C := H⁻¹ * (Wᴴ * X)
  let Z := X-W*C
  have hV : gram V 1 = 1 := gram_orthonormal a ha
  have hW : H = G V d 10 := cross V d 5 5
  have hdet : IsUnit H.det := by
    rw [hW, ← momentB_gram V hV d hd, isUnit_iff_ne_zero, Complex.ofReal_ne_zero]
    exact (midpoint_denominator_pos V hV d hd).ne'
  have hWY : Wᴴ * Y = 0 := by
    ext i j
    rw [← inner_column]
    exact (column_evolve V d 5 i) ▸ hz i j
  have projection : Zᴴ * Y = Xᴴ * Y := by
    change (X-W*C)ᴴ * Y = _
    rw [Matrix.conjTranspose_sub, Matrix.conjTranspose_mul, Matrix.sub_mul,
      Matrix.mul_assoc, hWY, Matrix.mul_zero, sub_zero]
  have hscore : endpointScore d a b ≤ ∑ i, ‖column Z i‖^2 := by
    apply Finset.sum_le_sum
    intro i _
    have same (j : Fin s) : ‖inner ℂ (weighted d 1 (a i)) (b j)‖ =
        ‖inner ℂ (b j) (column Z i)‖ := by
      rw [norm_inner_symm (b j) (column Z i)]
      change ‖inner ℂ (weighted d 1 (column V i)) (column Y j)‖ = ‖inner ℂ (column Z i) (column Y j)‖
      rw [← column_evolve, inner_column, inner_column, projection]
    simp_rw [same]
    exact hb.sum_inner_products_le (column Z i)
  have tr := residual_trace X W hdet
  change (Zᴴ*Z).trace = (Xᴴ*X).trace - ((Xᴴ*W)*(H⁻¹*(Wᴴ*X))).trace at tr
  have h1 : Xᴴ * X = G V d 2 := cross V d 1 1
  have h2 : Wᴴ * X = G V d 6 := cross V d 5 1
  have h3 : Xᴴ * W = G V d 6 := cross V d 1 5
  rw [h1,h2,h3,hW,Matrix.trace_mul_comm (G V d 6), Matrix.mul_assoc, ← sq] at tr
  exact hscore.trans (by rw [squared_columns, tr]; exact gram_residual_le_matching V hV d hd)

end HardyBornBridge

#print axioms HardyBornBridge.rank_two_endpoint_le
