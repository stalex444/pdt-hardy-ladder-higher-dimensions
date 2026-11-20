module

public import HardyComplex
public import HardySchmidt

@[expose] public section
/-! The two-step Hardy experiment in arbitrary complex coefficient-matrix coordinates.
Each party has exactly three binary rank-one projective settings. -/
noncomputable section
open Matrix HardyComplex
open scoped Matrix

namespace HardyMatrix

abbrev M := HardySchmidt.M
abbrev Vec := HardySchmidt.Vect

/-- The five zero-probability events of the two-step ladder in the original local bases.
A Born amplitude vanishes exactly when its squared norm does. -/
structure Strategy (C : M) (a b : Fin 3 → Vec) : Prop where
  unitA : ∀ i, UnitRay (a i)
  unitB : ∀ i, UnitRay (b i)
  base : HardySchmidt.amplitude C (a 0) (b 0) = 0
  stepA : ∀ i : Fin 2, HardySchmidt.amplitude C (a i.succ) (perp (b i.castSucc)) = 0
  stepB : ∀ i : Fin 2, HardySchmidt.amplitude C (perp (a i.castSucc)) (b i.succ) = 0

private def setting (k : ℕ) : Fin 3 := ⟨min k 2, by omega⟩

/-- Transfer both outcomes of every measurement to Schmidt coordinates. Phases of
complementary rays cancel from the zero-amplitude constraints. -/
private theorem transport {C : M} {s : Fin 2 → ℝ} {U V : unitaryGroup (Fin 2) ℂ}
    (hC : C = (U:M) * diagonal (fun i => (s i:ℂ)) * (V:M)ᴴ)
    {a b : Fin 3 → Vec} (h : Strategy C a b) :
    ∃ x y, Ladder (s 0) (s 1) x y ∧
      HardySchmidt.amplitude C (a 2) (b 2) = amp (s 0) (s 1) (x 2) (y 2) := by
  let A := Matrix.UnitaryGroup.transpose U
  let B := star V
  let x (k : ℕ) := (A : M) *ᵥ a (setting k)
  let y (k : ℕ) := (B : M) *ᵥ b (setting k)
  have changeAmp (v w : Vec) : HardySchmidt.amplitude C v w =
      amp (s 0) (s 1) ((A : M) *ᵥ v) ((B : M) *ᵥ w) :=
    HardySchmidt.amplitude_change hC v w
  have az {v w : Vec} (hw : UnitRay w)
      (h0 : HardySchmidt.amplitude C v (perp w) = 0) :
      amp (s 0) (s 1) ((A : M) *ᵥ v) (perp ((B : M) *ᵥ w)) = 0 := by
    rw [changeAmp] at h0
    obtain ⟨t, ht, he⟩ := HardySchmidt.perp_change B hw
    change ∀ i, ((B:M) *ᵥ perp w) i = t * perp ((B:M) *ᵥ w) i at he
    unfold amp at *
    rw [he 0, he 1] at h0
    apply (mul_eq_zero.mp (show t * _ = 0 by linear_combination h0)).resolve_left ht
  have bz {v w : Vec} (hv : UnitRay v)
      (h0 : HardySchmidt.amplitude C (perp v) w = 0) :
      amp (s 0) (s 1) (perp ((A : M) *ᵥ v)) ((B : M) *ᵥ w) = 0 := by
    rw [changeAmp] at h0
    obtain ⟨t, ht, he⟩ := HardySchmidt.perp_change A hv
    change ∀ i, ((A:M) *ᵥ perp v) i = t * perp ((A:M) *ᵥ v) i at he
    unfold amp at *
    rw [he 0, he 1] at h0
    apply (mul_eq_zero.mp (show t * _ = 0 by linear_combination h0)).resolve_left ht
  refine ⟨x,y,⟨fun k => HardySchmidt.unit_change A (h.unitA _),
    fun k => HardySchmidt.unit_change B (h.unitB _), ?_, ?_, ?_⟩, changeAmp _ _⟩
  · exact (changeAmp (a 0) (b 0)).symm.trans h.base
  · intro k hk
    interval_cases k
    · exact az (h.unitB 0) (h.stepA 0)
    · exact az (h.unitB 1) (h.stepA 1)
  · intro k hk
    interval_cases k
    · exact bz (h.unitA 0) (h.stepB 0)
    · exact bz (h.unitA 1) (h.stepB 1)

/-- In any choice of complex local bases, the Hardy probability is at most the
plastic-number value. At equality the squared Schmidt coefficients are forced. -/
theorem bound_and_weights {ρ : ℝ} (hρ : ρ ^ 3 = ρ + 1) (C : M)
    (hC : ∑ i, ∑ j, Complex.normSq (C i j) = 1) {a b : Fin 3 → Vec}
    (h : Strategy C a b) :
    ‖HardySchmidt.amplitude C (a 2) (b 2)‖ ^ 2 ≤ (8*ρ^2+ρ-11)/25 ∧
    (‖HardySchmidt.amplitude C (a 2) (b 2)‖ ^ 2 = (8*ρ^2+ρ-11)/25 →
      ∃ (s : Fin 2 → ℝ) (U V : unitaryGroup (Fin 2) ℂ),
        (∀ i, 0 ≤ s i) ∧ C = (U:M) * diagonal (fun i => (s i:ℂ)) * (V:M)ᴴ ∧
        ((s 0^2 = ρ⁻¹ ∧ s 1^2 = ρ⁻¹^5) ∨ (s 0^2 = ρ⁻¹^5 ∧ s 1^2 = ρ⁻¹))) := by
  obtain ⟨s,U,V,hs,hn,hsv⟩ := HardySchmidt.exists_schmidt C hC
  obtain ⟨x,y,hl,ha⟩ := transport hsv h
  obtain ⟨hub,heq⟩ := schmidt_bound_and_weights hρ (hs 0) (hs 1) hn hl
  rw [ha]
  exact ⟨hub,fun he => ⟨s,U,V,hs,hsv,heq he⟩⟩

/-- A normalized complex matrix strategy reaches the same value. -/
theorem attained {ρ : ℝ} (hρ : ρ^3=ρ+1) :
    ∃ (C : M) (a b : Fin 3 → Vec), (∑ i, ∑ j, Complex.normSq (C i j)) = 1 ∧
      Strategy C a b ∧ ‖HardySchmidt.amplitude C (a 2) (b 2)‖ ^ 2 = (8*ρ^2+ρ-11)/25 := by
  obtain ⟨c,d,_,_,hn,_,_,a,b,hl,hp⟩ := complex_attained hρ
  let C : M := diagonal ![(c:ℂ),(d:ℂ)]
  have hd (v w : Vec) : HardySchmidt.amplitude C v w = amp c d v w := by
    simp only [HardySchmidt.amplitude,C,dotProduct,Fin.sum_univ_two, Matrix.mulVec_diagonal,
      Matrix.cons_val_zero, Matrix.cons_val_one, amp]
    ring
  refine ⟨C,fun i => a i.val,fun i => b i.val,?_,?_,?_⟩
  · simpa [C, Fin.sum_univ_two, Matrix.diagonal_apply, Complex.normSq_ofReal, sq] using hn
  · refine ⟨fun i => hl.unitA _, fun i => hl.unitB _, ?_, ?_, ?_⟩
    · rw [hd]; exact hl.base
    · intro i; rw [hd]; exact hl.stepA i.val i.isLt
    · intro i; rw [hd]; exact hl.stepB i.val i.isLt
  · rw [hd]; exact hp

#print axioms HardyMatrix.bound_and_weights
#print axioms HardyMatrix.attained
end HardyMatrix
