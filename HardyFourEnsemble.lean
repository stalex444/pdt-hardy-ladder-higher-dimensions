module

public import HardyFourMeasurements
public import HardyFourEquality
public import HardyMixtures

/-! A finite ensemble may have different Schmidt coordinates and compressed
binary effects in each component. Exact ensemble zeros imply component zeros. -/
@[expose] public section
noncomputable section
namespace HardyFourEnsemble
open HardyMixtures

private theorem component_bound {ρ : ℝ} (hρ : ρ^3 = ρ + 1) (c : Component)
    (hr : c.rank ≤ 4) (hz : ∀ j, c.forbidden j = 0) :
    c.success ≤ HardyFourEquality.plasticValue ρ := by
  obtain ⟨n, d, hd, hn, A, B⟩ := c
  change n ≤ 4 at hr
  by_cases h : n = 4
  · subst n
    have he := HardyFourMeasurements.four_level_effect_le hd A B (hz .base)
      (fun i => hz (.left i)) (fun i => hz (.right i))
    have hp := HardyFourPairing.matchingMax_le_plastic hρ d hd
    rw [hn, mul_one] at hp
    exact he.trans hp
  · exact HardyEffects.three_level_effect_le (by simp; omega) hρ hd hn A B
      (hz .base) (fun i => hz (.left i)) (fun i => hz (.right i))

/-- Finite mixtures of positive Schmidt spectra of size at most four obey the
plastic ceiling whenever their five averaged forbidden probabilities vanish. -/
theorem mixture_bound {ι : Type*} [Fintype ι] {ρ : ℝ} (hρ : ρ^3=ρ+1)
    (w : ι → ℝ) (hw : ∀ i, 0 ≤ w i) (hn : ∑ i, w i = 1)
    (c : ι → Component) (hr : ∀ i, 0 < w i → (c i).rank ≤ 4)
    (hz : ∀ j, average w (fun i => (c i).forbidden j) = 0) :
    average w (fun i => (c i).success) ≤ HardyFourEquality.plasticValue ρ := by
  classical
  have hnonneg (i : ι) (j : Forbidden) : 0 ≤ (c i).forbidden j := by
    cases j <;> exact HardyEffects.event_nonneg _ _ _
  have hzero (i : ι) (hi : 0 < w i) (j : Forbidden) : (c i).forbidden j = 0 := by
    have h := Finset.single_le_sum (f := fun k => w k * (c k).forbidden j)
      (fun k _ => mul_nonneg (hw k) (hnonneg k j)) (Finset.mem_univ i)
    change _ ≤ average w _ at h
    rw [hz j] at h
    exact (mul_eq_zero.mp (le_antisymm h (mul_nonneg (hw i) (hnonneg i j)))).resolve_left hi.ne'
  calc
    _ ≤ ∑ i, w i * HardyFourEquality.plasticValue ρ := by
      apply Finset.sum_le_sum
      intro i _
      rcases (hw i).eq_or_lt with h | h
      · simp [← h]
      · exact mul_le_mul_of_nonneg_left (component_bound hρ _ (hr i h) (hzero i h)) (hw i)
    _ = _ := by rw [← Finset.sum_mul, hn, one_mul]

end HardyFourEnsemble
