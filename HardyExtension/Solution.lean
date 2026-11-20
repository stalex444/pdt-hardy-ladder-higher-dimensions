module

public import HardyFourEquality
public import HardyFourEnsemble
public import HardyFourWitness
public import HardyDirectSum

@[expose] public section
noncomputable section
open Finset


namespace HardyExtension
open HardyFourPairing HardyMomentGap HardyFourSharp HardyFourEquality
open HardyRankOne HardyEffects HardyComplex HardyDirectSum HardyMixtures

/-- Exact maximum over all rank-two complex frames. -/
theorem four_level_frame_maximum (d : Fin 4 → ℝ) (hd : ∀ i, 0 < d i) :
    IsGreatest {p : ℝ | ∃ x y : Fin 4 → ℂ, frameMinors x y ≠ 0 ∧
      (let m := squareMinors (frameMinors x y); momentN d m / momentB d m) = p}
      (matchingMax d) := by
  constructor
  · have ex : ∃ k : Fin 3, HardyFourAttainment.pairingScore d k = matchingMax d := by
      let f := HardyFourAttainment.pairingScore d
      change ∃ k, f k = max (f 0) (max (f 1) (f 2))
      rcases le_total (f 0) (max (f 1) (f 2)) with h | h
      · rw [max_eq_right h]
        rcases le_total (f 1) (f 2) with h' | h'
        · exact ⟨2, (max_eq_right h').symm⟩
        · exact ⟨1, (max_eq_left h').symm⟩
      · exact ⟨0, (max_eq_left h).symm⟩
    obtain ⟨k, hk⟩ := ex
    refine ⟨HardyFourAttainment.firstColumn k, HardyFourAttainment.secondColumn k, ?_, ?_⟩
    · change HardyFourAttainment.sixMinors _ _ ≠ 0
      rw [HardyFourAttainment.witness_is_plane]
      exact HardyFourAttainment.witness_nonzero k
    · change momentN d (squareMinors (HardyFourAttainment.sixMinors _ _)) /
          momentB d (squareMinors (HardyFourAttainment.sixMinors _ _)) = matchingMax d
      rw [HardyFourAttainment.witness_is_plane]
      unfold squareMinors
      rw [HardyFourAttainment.witness_squares, HardyFourAttainment.vertex_ratio d hd, hk]
  · rintro v ⟨x, y, hn, rfl⟩
    exact HardyFourSharp.complex_four_level_bound d hd _ hn (HardyFourSharp.frame_plucker x y)

/-- Plastic ceiling for the best matching. -/
theorem four_level_ceiling {ρ : ℝ} (hρ : ρ^3 = ρ+1) (d : Fin 4 → ℝ) (hd : ∀ i, 0 < d i) :
    matchingMax d ≤ plasticValue ρ * (∑ i, d i^2) := HardyFourPairing.matchingMax_le_plastic hρ d hd

/-- Necessary and sufficient spectral pairing for equality. -/
theorem four_level_equality {ρ : ℝ} (hρ : ρ^3=ρ+1) (d : Vertex → ℝ) (hd : ∀ i, 0<d i) :
    matchingMax d = plasticValue ρ*(∑ i, d i^2) ↔ PlasticPairing ρ d := HardyFourEquality.matchingMax_eq_iff hρ d hd

/-- All binary effects through Schmidt rank three. -/
theorem three_level_effect_bound {ι : Type*} [Fintype ι] (hdim : Fintype.card ι ≤ 3) {ρ : ℝ} (hρ : ρ^3=ρ+1)
    {d : ι → ℝ} (hd : ∀ i, 0 < d i) (hs : ∑ i, d i^2=1) (A B : Fin 3 → Effect ι)
    (base : HardyEffects.event d (A 0) (B 0)=0)
    (left : ∀ i : Fin 2, HardyEffects.event d (A i.succ) (B i.castSucc).complement=0)
    (right : ∀ i : Fin 2, HardyEffects.event d (A i.castSucc).complement (B i.succ)=0) :
    HardyEffects.event d (A 2) (B 2) ≤ (8*ρ^2+ρ-11)/25 := HardyEffects.three_level_effect_le hdim hρ hd hs A B base left right

/-- Strict inequality at full Schmidt rank three. -/
theorem full_rank_three_strict {ρ : ℝ} (hρ : ρ^3=ρ+1) {d : Fin 3 → ℝ}
    (hd : ∀ i, 0 < d i) (hs : ∑ i, d i^2=1) (A B : Fin 3 → Effect (Fin 3))
    (base : HardyEffects.event d (A 0) (B 0)=0)
    (left : ∀ i : Fin 2, HardyEffects.event d (A i.succ) (B i.castSucc).complement=0)
    (right : ∀ i : Fin 2, HardyEffects.event d (A i.castSucc).complement (B i.succ)=0) :
    HardyEffects.event d (A 2) (B 2) < (8*ρ^2+ρ-11)/25 := HardyEffects.full_rank_qutrit_effect_lt hρ hd hs A B base left right

/-- Rank-one endpoint in any finite dimension. -/
theorem rank_one_endpoint {ι : Type*} [Fintype ι] {ρ : ℝ} (hρ : ρ^3=ρ+1) {d : ι → ℝ}
    (hd : ∀ i, 0 ≤ d i) (hs : ∑ i, d i^2=1)
    {u : EuclideanSpace ℂ ι} (hu : ‖u‖=1) : score d u ≤ (8*ρ^2+ρ-11)/25 := HardyRankOne.score_le hρ hd hs hu

/-- Codimension-one endpoint in any finite dimension. -/
theorem codimension_one_endpoint {ι : Type*} [Fintype ι] {κ : Type*} [Fintype κ] {ρ : ℝ} (hρ : ρ^3=ρ+1)
    {d : ι → ℝ} (hd : ∀ i, 0 ≤ d i) (hs : ∑ i, d i^2=1)
    {u : EuclideanSpace ℂ ι} (hu : ‖u‖=1) (v : κ → EuclideanSpace ℂ ι)
    (hv : Orthonormal ℂ v) (hz : ∀ j, inner ℂ (weighted d 5 (v j)) u = 0) :
    ∑ j, ‖inner ℂ (weighted d 1 (v j)) u‖^2 ≤ (8*ρ^2+ρ-11)/25 := HardyRankOne.codimension_one_le hρ hd hs hu v hv hz

/-- Preservation of all qubit joint probabilities under finite sector lifting. -/
theorem sector_outcome_probability {ι : Type*} [Fintype ι] [DecidableEq ι] (w : ι → ℝ) (hw : ∀ i, 0 ≤ w i) (hn : ∑ i, w i = 1)
    (c d : ℝ) (v z : Vec) :
    HardyDirectSum.event (schmidt w c d) v z = ‖amp c d v z‖ ^ 2 := HardyDirectSum.event_lift w hw hn c d v z

/-- Twelve distinct Schmidt weights attain the same success. -/
theorem twelve_level_attainment {ρ : ℝ} (hρ : ρ^3 = ρ+1) :
    ∃ (s : Fin 6 × Fin 2 → ℝ) (a b : ℕ → Vec),
      (∀ p, 0 < s p) ∧ (∑ p, s p ^ 2 = 1) ∧ Function.Injective (fun p => s p ^ 2) ∧
      (∀ i, s (i,0)^2 = weights i * ρ⁻¹ ∧ s (i,1)^2 = weights i * ρ⁻¹^5) ∧
      Lifted s a b ((8*ρ^2+ρ-11)/25) := HardyDirectSum.twelve_level_attainment hρ

/-- Sharp matching upper bound for six arbitrary binary effects. -/
theorem four_level_measurement_bound {d : Fin 4 → ℝ} (hd : ∀ i, 0 < d i)
    (A B : Fin 3 → HardyEffects.Effect (Fin 4))
    (base : HardyEffects.event d (A 0) (B 0) = 0)
    (left : ∀ i : Fin 2, HardyEffects.event d (A i.succ) (B i.castSucc).complement = 0)
    (right : ∀ i : Fin 2, HardyEffects.event d (A i.castSucc).complement (B i.succ) = 0) :
    HardyEffects.event d (A 2) (B 2) ≤ matchingMax d := HardyFourMeasurements.four_level_effect_le hd A B base left right

/-- Plastic ceiling for finite ensembles through Schmidt rank four. -/
theorem four_level_mixture_bound {ι : Type*} [Fintype ι] {ρ : ℝ} (hρ : ρ^3=ρ+1)
    (w : ι → ℝ) (hw : ∀ i, 0 ≤ w i) (hn : ∑ i, w i = 1)
    (c : ι → Component) (hr : ∀ i, 0 < w i → (c i).rank ≤ 4)
    (hz : ∀ j, average w (fun i => (c i).forbidden j) = 0) :
    average w (fun i => (c i).success) ≤ HardyFourEquality.plasticValue ρ := HardyFourEnsemble.mixture_bound hρ w hw hn c hr hz

/-- Exact maximum for all six binary measurements at a fixed four-level spectrum. -/
theorem four_level_measurement_maximum (d : Fin 4 → ℝ) (hd : ∀ i, 0 < d i) :
    IsGreatest (HardyFixedState.successSet d) (matchingMax d) := by
  constructor
  · exact HardyFourWitness.four_level_effect_attainment d hd
  · rintro p ⟨A, B, h0, hA, hB, rfl⟩
    exact HardyFourMeasurements.four_level_effect_le hd A B h0 hA hB

/-- Spectra admitting equality in the original six-measurement experiment. -/
theorem four_level_measurement_equality {ρ : ℝ} (hρ : ρ^3 = ρ+1) (d : Fin 4 → ℝ) (hd : ∀ i, 0 < d i) :
    plasticValue ρ * (∑ i, d i^2) ∈ HardyFixedState.successSet d ↔ PlasticPairing ρ d := by
  have hmax := four_level_measurement_maximum d hd
  rw [← HardyFourEquality.matchingMax_eq_iff hρ d hd]
  constructor
  · intro ha
    exact le_antisymm (HardyFourPairing.matchingMax_le_plastic hρ d hd) (hmax.2 ha)
  · intro he
    rw [← he]
    exact hmax.1

end HardyExtension
