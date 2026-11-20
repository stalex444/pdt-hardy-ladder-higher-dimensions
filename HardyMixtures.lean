module

public import HardyExtension.Definitions
public import HardyEffects

@[expose] public section
/-! The exact-zero Hardy experiment on a finite ensemble. Each component is in
its own Schmidt coordinates, so its compressed effects and its support dimension
may vary. Only the ensemble probabilities are assumed to have the five zeros. -/
noncomputable section
namespace HardyMixtures
open Finset HardyEffects

private theorem Component.forbidden_nonneg (c : Component) (j : Forbidden) :
    0 ≤ c.forbidden j := by
  cases j <;> exact event_nonneg _ _ _

variable {ι : Type*} [Fintype ι]

private theorem component_zero {w f : ι → ℝ} (hw : ∀ i, 0 ≤ w i)
    (hf : ∀ i, 0 ≤ f i) (hz : average w f = 0) {i : ι} (hi : 0 < w i) :
    f i = 0 := by
  classical
  have h := Finset.single_le_sum (f := fun k => w k * f k)
    (fun k _ => mul_nonneg (hw k) (hf k)) (Finset.mem_univ i)
  change w i * f i ≤ average w f at h
  rw [hz] at h
  exact (mul_eq_zero.mp (le_antisymm h (mul_nonneg (hw i) (hf i)))).resolve_left hi.ne'

private theorem component_zeros {w : ι → ℝ} {c : ι → Component}
    (hw : ∀ i, 0 ≤ w i) (hz : ∀ j, average w (fun i => (c i).forbidden j) = 0)
    {i : ι} (hi : 0 < w i) (j : Forbidden) : (c i).forbidden j = 0 :=
  component_zero hw (fun k => (c k).forbidden_nonneg j) (hz j) hi

private theorem Component.bound {ρ : ℝ} (hρ : ρ ^ 3 = ρ + 1) (c : Component)
    (hr : c.rank ≤ 3) (hz : ∀ j, c.forbidden j = 0) :
    c.success ≤ (8*ρ^2+ρ-11)/25 :=
  three_level_effect_le (by simpa using hr) hρ c.positive c.normalized c.alice c.bob
    (hz .base) (fun k => hz (.left k)) (fun k => hz (.right k))

private theorem Component.strict_bound {ρ : ℝ} (hρ : ρ ^ 3 = ρ + 1) (c : Component)
    (hr : c.rank = 3) (hz : ∀ j, c.forbidden j = 0) :
    c.success < (8*ρ^2+ρ-11)/25 := by
  obtain ⟨n,d,hd,hs,A,B⟩ := c
  change n = 3 at hr
  subst n
  exact full_rank_qutrit_effect_lt hρ hd hs A B (hz .base)
    (fun k => hz (.left k)) (fun k => hz (.right k))

/-- With five exact ensemble zeros, a finite mixture of components of Schmidt
rank at most three obeys the sharp two-qubit bound. A positive-weight rank-three
component makes the inequality strict. Zero-weight components are unrestricted. -/
theorem three_level_mixture_bound {ρ : ℝ} (hρ : ρ ^ 3 = ρ + 1)
    (w : ι → ℝ) (hw : ∀ i, 0 ≤ w i) (hn : ∑ i, w i = 1)
    (c : ι → Component) (hr : ∀ i, 0 < w i → (c i).rank ≤ 3)
    (hz : ∀ j, average w (fun i => (c i).forbidden j) = 0) :
    average w (fun i => (c i).success) ≤ (8*ρ^2+ρ-11)/25 ∧
      ((∃ i, 0 < w i ∧ (c i).rank = 3) →
        average w (fun i => (c i).success) < (8*ρ^2+ρ-11)/25) := by
  classical
  let p := (8*ρ^2+ρ-11)/25
  have upper i : w i * (c i).success ≤ w i * p := by
    rcases (hw i).eq_or_lt with h | h
    · simp [← h]
    · exact mul_le_mul_of_nonneg_left
        ((c i).bound hρ (hr i h) (component_zeros hw hz h)) (hw i)
  have hsum : ∑ i, w i * p = p := by rw [← Finset.sum_mul, hn, one_mul]
  constructor
  · exact (Finset.sum_le_sum (fun i _ => upper i)).trans_eq hsum
  · rintro ⟨i, hi, hthree⟩
    have hlt : w i * (c i).success < w i * p := mul_lt_mul_of_pos_left
      ((c i).strict_bound hρ hthree (component_zeros hw hz hi)) hi
    exact (Finset.sum_lt_sum (fun k _ => upper k) ⟨i, Finset.mem_univ _, hlt⟩).trans_eq hsum

end HardyMixtures

#print axioms HardyMixtures.three_level_mixture_bound
