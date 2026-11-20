module

public import HardyExtension.Definitions
public import HardyFourSharp

@[expose] public section
/-! The exact four-level spectral condition for attaining the plastic Hardy ceiling. -/
noncomputable section
open Finset HardyFourPairing HardyTripleGap
namespace HardyFourEquality

private theorem edge_swap (x y : ℝ) : edge x y = edge y x := by
  unfold edge; rw [add_comm (x^5) (y^5)]; ring

private theorem ordered_edge {ρ x y : ℝ} (hρ : ρ^3=ρ+1) (hx : 0<x) (hxy : x<y) :
    edge x y = plasticValue ρ*(x^2+y^2) ↔ x/y=ρ⁻¹^2 := by
  have hy := hx.trans hxy
  have hs : x^2+y^2 ≠ 0 := by positivity
  have hden : x^5+y^5 ≠ 0 := by positivity
  have hi : edge x y = HardyLadder.ladderValue 2 (x/y)*(x^2+y^2) := by
    unfold edge HardyLadder.ladderValue
    norm_num only
    field_simp
    ring
  rw [hi]
  have eqv : HardyLadder.ladderValue 2 (x/y)*(x^2+y^2)=plasticValue ρ*(x^2+y^2) ↔
      HardyLadder.ladderValue 2 (x/y)=plasticValue ρ :=
    ⟨mul_right_cancel₀ hs,fun h => congrArg (fun z : ℝ => z*(x^2+y^2)) h⟩
  exact eqv.trans (HardyLadder.hardy_K2_eq_iff_inv_sq hρ (div_pos hx hy)
    ((div_lt_one hy).mpr hxy))

/-- Scalar equality for unordered positive Schmidt coefficients. A repeated
value gives a zero edge and cannot itself be a saturating pair. -/
theorem edge_eq_iff {ρ x y : ℝ} (hρ : ρ^3=ρ+1) (hx : 0<x) (hy : 0<y) :
    edge x y = plasticValue ρ*(x^2+y^2) ↔ PlasticPair ρ x y := by
  unfold PlasticPair
  rcases lt_trichotomy x y with h | h | h
  · rw [min_eq_left h.le,max_eq_right h.le]
    exact ordered_edge hρ hx h
  · subst y
    have hp : 0 < plasticValue ρ := HardyLadder.value_pos hρ
    have hval := HardyLadder.inv_sq_mem_Ioo hρ
    have hs : 0 < plasticValue ρ*(x^2+x^2) := by positivity
    simp only [min_self,max_self,div_self hx.ne',edge,sub_self,zero_div,zero_pow (by decide : 2≠0)]
    exact iff_of_false (Ne.symm hs.ne') (Ne.symm hval.2.ne)
  · rw [min_eq_right h.le,max_eq_left h.le,edge_swap x y,add_comm (x^2) (y^2)]
    exact ordered_edge hρ hy h

private theorem two_edge_eq_iff {ρ x y z w : ℝ} (hρ : ρ^3=ρ+1)
    (hx : 0<x) (hy : 0<y) (hz : 0<z) (hw : 0<w) :
    edge x y + edge z w = plasticValue ρ*(x^2+y^2+z^2+w^2) ↔
      PlasticPair ρ x y ∧ PlasticPair ρ z w := by
  rw [←edge_eq_iff hρ hx hy,←edge_eq_iff hρ hz hw]
  have hp : edge x y ≤ plasticValue ρ*(x^2+y^2) := HardyPairBound.pair_bound hρ hx hy
  have hq : edge z w ≤ plasticValue ρ*(z^2+w^2) := HardyPairBound.pair_bound hρ hz hw
  constructor
  · intro h
    exact ⟨by linarith only [h,hp,hq], by linarith only [h,hp,hq]⟩
  · rintro ⟨h₁,h₂⟩
    rw [h₁,h₂]; ring

private theorem max_three_eq {a b c M : ℝ} (h : max a (max b c) ≤ M) :
    max a (max b c)=M ↔ a=M ∨ b=M ∨ c=M := by
  constructor
  · intro e
    rcases le_total a (max b c) with h₁ | h₁
    · rw [max_eq_right h₁] at e
      rcases le_total b c with h₂ | h₂
      · exact Or.inr (Or.inr ((max_eq_right h₂).symm.trans e))
      · exact Or.inr (Or.inl ((max_eq_left h₂).symm.trans e))
    · exact Or.inl ((max_eq_left h₁).symm.trans e)
  · intro he
    apply le_antisymm h
    rcases he with rfl | rfl | rfl
    · exact le_max_left _ _
    · exact (le_max_left _ _).trans (le_max_right _ _)
    · exact (le_max_right _ _).trans (le_max_right _ _)

/-- On four positive levels, the global plastic ceiling is reached precisely
when one perfect matching realizes the scalar equality on both its edges. -/
theorem matchingMax_eq_iff {ρ : ℝ} (hρ : ρ^3=ρ+1) (d : Vertex → ℝ) (hd : ∀ i, 0<d i) :
    matchingMax d = plasticValue ρ*(∑ i, d i^2) ↔ PlasticPairing ρ d := by
  have h := matchingMax_le_plastic hρ d hd
  change matchingMax d ≤ plasticValue ρ*_ at h
  rw [matchingMax,max_three_eq h,Fin.sum_univ_four]
  have h₁ := two_edge_eq_iff hρ (hd 0) (hd 1) (hd 2) (hd 3)
  have h₂ := two_edge_eq_iff hρ (hd 0) (hd 2) (hd 1) (hd 3)
  have h₃ := two_edge_eq_iff hρ (hd 0) (hd 3) (hd 1) (hd 2)
  rw [show d 0^2+d 2^2+d 1^2+d 3^2=d 0^2+d 1^2+d 2^2+d 3^2 by ring] at h₂
  rw [show d 0^2+d 3^2+d 1^2+d 2^2=d 0^2+d 1^2+d 2^2+d 3^2 by ring] at h₃
  exact or_congr h₁ (or_congr h₂ h₃)

open HardyMomentGap HardyFourSharp

/-- A nonzero complex Plücker witness attains the plastic ceiling exactly for
the spectra in the disjoint-pair characterization. -/
theorem plastic_attainable_iff {ρ : ℝ} (hρ : ρ^3=ρ+1) (d : Vertex → ℝ) (hd : ∀ i, 0<d i) :
    (∃ w : Fin 6 → ℂ, w≠0 ∧ plucker w ∧
      momentN d (squareMinors w)/momentB d (squareMinors w)=plasticValue ρ*(∑ i, d i^2)) ↔
    PlasticPairing ρ d := by
  rw [←matchingMax_eq_iff hρ d hd]
  constructor
  · rintro ⟨w,hw,hp,he⟩
    exact le_antisymm (matchingMax_le_plastic hρ d hd)
      (he ▸ complex_four_level_bound d hd w hw hp)
  · intro he
    rw [←he]
    exact HardyFourAttainment.matchingMax_attained d hd

end HardyFourEquality

#print axioms HardyFourEquality.matchingMax_eq_iff
#print axioms HardyFourEquality.plastic_attainable_iff
