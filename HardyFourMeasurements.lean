module

public import HardyBornBridgeEndpoint
public import HardyEffects
public import HardyFourPairing

@[expose] public section
/-! Four positive Schmidt coefficients and six arbitrary binary measurements.
The bound uses the spectrum of the given state. -/
noncomputable section
namespace HardyFourMeasurements

open Finset HardyRankOne HardyFourPairing
abbrev Space := EuclideanSpace ℂ (Fin 4)

/-- The best scalar approximation on the four Schmidt coordinates is
bounded by the best disjoint matching, for every normalized endpoint ray. -/
theorem ray_le_matchingMax (d : Fin 4 → ℝ) (hd : ∀ i, 0 < d i)
    (u : Space) (hu : ‖u‖ = 1) : score d u ≤ matchingMax d := by
  let g (m : Fin 4 × Fin 4) :=
    (d m.1 * d m.2 ^ 5 - d m.2 * d m.1 ^ 5) / (d m.1 ^ 5 + d m.2 ^ 5)
  obtain ⟨m, _, hm⟩ := Finset.exists_max_image (univ : Finset (Fin 4 × Fin 4)) g univ_nonempty
  obtain ⟨t, ht⟩ := (HardyPairBound.common_multiplier_iff d hd (g m)).2 (fun i j =>
    (div_le_iff₀ (add_pos (pow_pos (hd i) 5) (pow_pos (hd j) 5))).mp (hm (i,j) (mem_univ _)))
  exact (residual_le hu ht).trans ((matching_costs (matchingBound_max d)).2 m.1 m.2)

/-- A four-level Schmidt state obeys the matching bound for every pair of
orthonormal endpoint families satisfying fifth-power orthogonality. -/
theorem four_level_endpoint_le {r s : ℕ} (d : Fin 4 → ℝ) (hd : ∀ i, 0 < d i)
    (a : Fin r → Space) (b : Fin s → Space) (ha : Orthonormal ℂ a) (hb : Orthonormal ℂ b)
    (hz : ∀ i j, inner ℂ (weighted d 5 (a i)) (b j) = 0) :
    endpointScore d a b ≤ matchingMax d := by
  have hr : r + s ≤ 4 := by simpa using endpoint_rank_sum hd a b ha hb hz
  have cases : r = 0 ∨ s = 0 ∨ r = 1 ∨ s = 1 ∨ r = 2 := by omega
  rcases cases with rfl | rfl | rfl | rfl | rfl
  · simpa [endpointScore] using (matching_costs (matchingBound_max d)).1
  · simpa [endpointScore] using (matching_costs (matchingBound_max d)).1
  · have hsym (j : Fin s) : inner ℂ (weighted d 5 (b j)) (a 0) = 0 := by
      rw [weighted_selfadjoint, inner_eq_zero_symm]
      exact hz 0 j
    have hswap (j : Fin s) : ‖inner ℂ (weighted d 1 (a 0)) (b j)‖ =
        ‖inner ℂ (weighted d 1 (b j)) (a 0)‖ := by
      rw [weighted_selfadjoint, norm_inner_symm]
    simp only [endpointScore, Fin.sum_univ_one, hswap]
    exact (family_le_score d (a 0) b hb hsym).trans (ray_le_matchingMax d hd _ (ha.norm_eq_one _))
  · simp only [endpointScore, Fin.sum_univ_one]
    exact (family_le_score d (b 0) a ha (fun i => hz i 0)).trans
      (ray_le_matchingMax d hd _ (hb.norm_eq_one _))
  · exact HardyBornBridge.rank_two_endpoint_le d hd a b ha hb hz

/-- The upper bound for all six projective measurements, at fixed spectrum,
with no restriction on the ranks of individual projectors. -/
theorem four_level_projective_le (d : Fin 4 → ℝ) (hd : ∀ i, 0 < d i)
    (A B : Fin 3 → Submodule ℂ Space)
    (base : event d (A 0) (B 0) = 0)
    (left : ∀ i : Fin 2, event d (A i.succ) (B i.castSucc)ᗮ = 0)
    (right : ∀ i : Fin 2, event d (A i.castSucc)ᗮ (B i.succ) = 0) :
    event d (A 2) (B 2) ≤ matchingMax d :=
  four_level_endpoint_le d hd _ _ (outcome_orthonormal _) (outcome_orthonormal _)
    (fun i j => five_zeros_force_endpoint base left right
      ((stdOrthonormalBasis ℂ (A 2) i).property) ((stdOrthonormalBasis ℂ (B 2) j).property))

/-- Four positive Schmidt coefficients and arbitrary binary effects. The five
forbidden probabilities alone imply the fixed-spectrum terminal bound. -/
theorem four_level_effect_le {d : Fin 4 → ℝ} (hd : ∀ i, 0 < d i)
    (A B : Fin 3 → HardyEffects.Effect (Fin 4))
    (base : HardyEffects.event d (A 0) (B 0) = 0)
    (left : ∀ i : Fin 2, HardyEffects.event d (A i.succ) (B i.castSucc).complement = 0)
    (right : ∀ i : Fin 2, HardyEffects.event d (A i.castSucc).complement (B i.succ) = 0) :
    HardyEffects.event d (A 2) (B 2) ≤ matchingMax d :=
  (HardyEffects.event_le_active d (A 2) (B 2)).trans
    (four_level_endpoint_le d hd _ _ (HardyEffects.orthonormal_active _)
      (HardyEffects.orthonormal_active _)
      (fun i j => HardyEffects.five_zeros_force_endpoint base left right
        (HardyEffects.active_mem _ i) (HardyEffects.active_mem _ j)))

/-- Normalized four-level states obey the same absolute bound as qubits. -/
theorem four_level_effect_le_plastic {ρ : ℝ} (hρ : ρ ^ 3 = ρ + 1)
    {d : Fin 4 → ℝ} (hd : ∀ i, 0 < d i) (hn : ∑ i, d i ^ 2 = 1)
    (A B : Fin 3 → HardyEffects.Effect (Fin 4))
    (base : HardyEffects.event d (A 0) (B 0) = 0)
    (left : ∀ i : Fin 2, HardyEffects.event d (A i.succ) (B i.castSucc).complement = 0)
    (right : ∀ i : Fin 2, HardyEffects.event d (A i.castSucc).complement (B i.succ) = 0) :
    HardyEffects.event d (A 2) (B 2) ≤ (8*ρ^2+ρ-11)/25 := by
  refine (four_level_effect_le hd A B base left right).trans ?_
  simpa [hn] using matchingMax_le_plastic hρ d hd

end HardyFourMeasurements

#print axioms HardyFourMeasurements.four_level_effect_le
#print axioms HardyFourMeasurements.four_level_effect_le_plastic
