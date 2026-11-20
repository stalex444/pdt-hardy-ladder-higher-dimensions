module

public import HardyFourLevels
public import HardyFourSharp

@[expose] public section
/-! Weighted Gram determinants for a two-dimensional terminal subspace in four
Schmidt coordinates. The six coefficients are squared minors of the frame. -/
noncomputable section
open Matrix
namespace HardyBornBridge

abbrev Frame := Matrix (Fin 4) (Fin 2) ℂ
abbrev Two := Matrix (Fin 2) (Fin 2) ℂ

/-- The compressed diagonal operator in frame coordinates. -/
def gram (V : Frame) (w : Fin 4 → ℂ) : Two :=
  fun i j => ∑ k, star (V k i) * w k * V k j

def minor (V : Frame) (i j : Fin 4) : ℂ :=
  V i 0 * V j 1 - V i 1 * V j 0

def mass (V : Frame) (i j : Fin 4) : ℝ := ‖minor V i j‖ ^ 2

def pairs {R : Type*} [Add R] (f : Fin 4 → Fin 4 → R) : R :=
  f 0 1 + f 0 2 + f 0 3 + f 2 3 + f 1 3 + f 1 2

private theorem cast_mass (V : Frame) (i j : Fin 4) :
    (mass V i j : ℂ) = star (minor V i j) * minor V i j := by
  rw [mass, Complex.sq_norm, Complex.normSq_eq_conj_mul_self]
  rfl

/-- Weighted Cauchy--Binet, in complementary-pair order. -/
theorem det_gram (V : Frame) (w : Fin 4 → ℂ) :
    (gram V w).det = pairs (fun i j => (mass V i j : ℂ) * (w i * w j)) := by
  simp only [Matrix.det_fin_two, gram, pairs, cast_mass, minor, Fin.sum_univ_four,
    star_sub, star_mul]
  ring

/-- Polarization of weighted Cauchy--Binet computes the mixed adjugate trace. -/
theorem mixed_gram (V : Frame) (a b : Fin 4 → ℂ) :
    ((gram V a).adjugate * gram V b).trace =
    pairs (fun i j => (mass V i j : ℂ) * (a i * b j + a j * b i)) := by
  have add_gram : gram V (a+b) = gram V a + gram V b := by
    ext i j
    simp [gram, mul_add, add_mul, Finset.sum_add_distrib]
  have polar (A B : Two) :
      (A.adjugate * B).trace = (A+B).det - A.det - B.det := by
    simp only [Matrix.adjugate_fin_two, Matrix.det_fin_two, Matrix.trace_fin_two,
      Matrix.mul_apply, Fin.sum_univ_two]
    simp
    ring
  rw [polar, ← add_gram, det_gram, det_gram, det_gram]
  simp only [pairs, Pi.add_apply]
  ring

/-- In an orthonormal frame the trace also depends just on the squared minors. -/
theorem trace_gram (V : Frame) (hV : gram V 1 = 1) (w : Fin 4 → ℂ) :
    (gram V w).trace = pairs (fun i j => (mass V i j : ℂ) * (w i + w j)) := by
  simpa [hV, add_comm] using mixed_gram V 1 w

open HardyMomentGap HardyFourSharp HardyFourPairing HardyBalancedPolynomial

def edges {R : Type*} (f : Fin 4 → Fin 4 → R) : Fin 6 → R :=
  ![f 0 1, f 0 2, f 0 3, f 2 3, f 1 3, f 1 2]

/-- Midpoint minor masses include the five applications of the Schmidt
operator split equally between the two endpoints. -/
def midpointMass (V : Frame) (d : Four) : Six :=
  edges (fun i j => mass V i j * (d i*d j)^5)

def sumMass (V : Frame) (f : Fin 4 → Fin 4 → ℝ) : ℝ :=
  pairs (fun i j => mass V i j * f i j)

def G (V : Frame) (d : Four) (k : ℕ) : Two :=
  gram V (fun i => (d i : ℂ)^k)

private theorem cast_sumMass (V : Frame) (f : Fin 4 → Fin 4 → ℝ) :
    (sumMass V f : ℂ) = pairs (fun i j => (mass V i j : ℂ) * (f i j : ℂ)) := by
  simp [sumMass, pairs]

theorem det_G (V : Frame) (d : Four) (k : ℕ) :
    (G V d k).det = (sumMass V (fun i j => (d i*d j)^k) : ℂ) := by
  simp [G, det_gram, cast_sumMass, mul_pow]

theorem trace_G (V : Frame) (hV : gram V 1 = 1) (d : Four) (k : ℕ) :
    (G V d k).trace = (sumMass V (fun i j => d i^k+d j^k) : ℂ) := by
  simp [G, trace_gram V hV, cast_sumMass]

theorem mixed_G (V : Frame) (d : Four) (k l : ℕ) :
    ((G V d k).adjugate * G V d l).trace =
      (sumMass V (fun i j => d i^k*d j^l+d j^k*d i^l) : ℂ) := by
  simp [G, mixed_gram, cast_sumMass]

private theorem read_mass (V : Frame) (d : Four) (hd : ∀ i, 0<d i)
    (p : Row → ℝ) (f : Fin 4 → Fin 4 → ℝ)
    (h : ∀ i j, p (row (d i) (d j)) = f i j/(d i*d j)^5) :
    lin (midpointMass V d) (rows d) p = sumMass V f := by
  have cancel (i j : Fin 4) :
      (mass V i j * (d i*d j)^5)*(f i j/(d i*d j)^5)=mass V i j*f i j := by
    field_simp [(hd i).ne', (hd j).ne']
  simp [lin, midpointMass, edges, rows, Fin.sum_univ_succ, h, cancel,
    sumMass, pairs, add_assoc]

private theorem mass_one (V : Frame) (hV : gram V 1 = 1) :
    sumMass V (fun _ _ => 1) = 1 := by
  have h := det_gram V 1
  rw [hV, Matrix.det_one] at h
  apply Complex.ofReal_injective
  simpa [cast_sumMass] using h.symm

theorem momentB_gram (V : Frame) (hV : gram V 1 = 1) (d : Four) (hd : ∀ i, 0<d i) :
    (momentB d (midpointMass V d) : ℂ) = (G V d 10).det := by
  have lo := read_mass V d hd Row.lower (fun _ _ => 1) (fun _ _ => rfl)
  have hi := read_mass V d hd Row.upper (fun i j => (d i*d j)^10) (by
    intro i j
    dsimp [HardyMomentGap.row]
    field_simp [(hd i).ne', (hd j).ne'])
  rw [momentB, lo, hi, mass_one V hV, one_mul, det_G]

theorem momentN_gram (V : Frame) (hV : gram V 1 = 1) (d : Four) (hd : ∀ i, 0<d i) :
    (momentN d (midpointMass V d) : ℂ) =
      (G V d 2).trace * (G V d 10).det -
        ((G V d 10).adjugate * G V d 6 ^ 2).trace := by
  rw [HardyFourLevels.trace_identity, momentN]
  rw [read_mass V d hd Row.T2 (fun i j => d i^2+d j^2) (fun _ _ => rfl),
      read_mass V d hd Row.J10 (fun i j => (d i*d j)^10) (fun _ _ => rfl),
      read_mass V d hd Row.T6 (fun i j => d i^6+d j^6) (fun _ _ => rfl),
      read_mass V d hd Row.C (fun i j => d i^10*d j^6+d j^10*d i^6) (fun _ _ => rfl),
      read_mass V d hd Row.J6 (fun i j => (d i*d j)^6) (fun _ _ => rfl),
      read_mass V d hd Row.T10 (fun i j => d i^10+d j^10) (fun _ _ => rfl)]
  simp only [trace_G V hV, det_G, mixed_G, Complex.ofReal_add, Complex.ofReal_sub,
    Complex.ofReal_mul]
  ring

/-- The midpoint frame distributes five steps of Schmidt evolution evenly. -/
def midpointColumn (V : Frame) (d : Four) (k : Fin 2) (i : Fin 4) : ℂ :=
  (Real.sqrt ((d i)^5) : ℂ) * V i k

def midpointMinors (V : Frame) (d : Four) : Fin 6 → ℂ :=
  frameMinors (midpointColumn V d 0) (midpointColumn V d 1)

theorem midpoint_squared (V : Frame) (d : Four) (hd : ∀ i, 0<d i) :
    squareMinors (midpointMinors V d) = midpointMass V d := by
  have h (i j : Fin 4) :
      ‖midpointColumn V d 0 i * midpointColumn V d 1 j -
        midpointColumn V d 0 j * midpointColumn V d 1 i‖ ^ 2 =
      mass V i j * (d i*d j)^5 := by
    have hfactor : midpointColumn V d 0 i * midpointColumn V d 1 j -
        midpointColumn V d 0 j * midpointColumn V d 1 i =
        (Real.sqrt ((d i)^5) : ℂ) * (Real.sqrt ((d j)^5) : ℂ) * minor V i j := by
      dsimp [midpointColumn, minor]
      ring
    rw [hfactor]
    simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (Real.sqrt_nonneg _), mul_pow, Real.sq_sqrt (pow_nonneg (hd i).le _),
      Real.sq_sqrt (pow_nonneg (hd j).le _), mass]
    ring
  funext k
  fin_cases k <;> apply h

private theorem midpoint_ne (V : Frame) (hV : gram V 1 = 1) (d : Four) (hd : ∀ i, 0<d i) :
    midpointMass V d ≠ 0 := by
  intro hz
  have lo := read_mass V d hd Row.lower (fun _ _ => 1) (fun _ _ => rfl)
  simp [hz, lin, mass_one V hV] at lo

theorem midpoint_denominator_pos (V : Frame) (hV : gram V 1 = 1) (d : Four) (hd : ∀ i, 0<d i) :
    0 < momentB d (midpointMass V d) := by
  apply momentB_pos d hd _ _ (midpoint_ne V hV d hd)
  intro i
  rw [← midpoint_squared V d hd]
  exact sq_nonneg _

/-- The inverse Gram correction is exactly the previously bounded real moment
quotient, for every orthonormal complex four-by-two frame. -/
theorem gram_residual_eq_moments (V : Frame) (hV : gram V 1 = 1) (d : Four)
    (hd : ∀ i, 0<d i) :
    (G V d 2).trace - ((G V d 10)⁻¹ * (G V d 6)^2).trace =
      ((momentN d (midpointMass V d) / momentB d (midpointMass V d) : ℝ) : ℂ) := by
  have hn : (momentB d (midpointMass V d) : ℂ) ≠ 0 := by
    exact_mod_cast (midpoint_denominator_pos V hV d hd).ne'
  rw [Complex.ofReal_div, momentN_gram V hV d hd, Matrix.inv_def,
    Ring.inverse_eq_inv, Matrix.smul_mul, Matrix.trace_smul, smul_eq_mul,
    ← momentB_gram V hV d hd]
  field_simp

/-- The actual inverse Gram correction obeys the optimal pairing bound. -/
theorem gram_residual_le_matching (V : Frame) (hV : gram V 1 = 1) (d : Four)
    (hd : ∀ i, 0<d i) :
    ((G V d 2).trace - ((G V d 10)⁻¹ * (G V d 6)^2).trace).re ≤ matchingMax d := by
  have hne : midpointMinors V d ≠ 0 := by
    intro hz
    apply midpoint_ne V hV d hd
    rw [← midpoint_squared V d hd, hz]
    funext i
    simp [squareMinors]
  rw [gram_residual_eq_moments V hV d hd, Complex.ofReal_re, ← midpoint_squared V d hd]
  exact complex_four_level_bound d hd _ hne (frame_plucker _ _)

end HardyBornBridge
