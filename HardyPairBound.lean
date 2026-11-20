module

public import HardyLadder

@[expose] public section
/-! Exact scalar ingredients for the one-dimensional endpoint in the higher-dimensional proof. -/
namespace HardyPairBound
open Finset

/-- The error of the best scalar fit on two Schmidt values is bounded by the
plastic Hardy probability times the total weight of those two coordinates. -/
theorem pair_bound {ρ x y : ℝ} (hρ : ρ^3=ρ+1) (hx : 0<x) (hy : 0<y) :
    ((x*y^5-y*x^5)/(x^5+y^5))^2 ≤ ((8*ρ^2+ρ-11)/25)*(x^2+y^2) := by
  have identity : ((x*y^5-y*x^5)/(x^5+y^5))^2 =
      HardyLadder.ladderValue 2 (y/x) * (x^2+y^2) := by
    unfold HardyLadder.ladderValue
    norm_num only
    field_simp
    ring
  rw [identity]
  exact mul_le_mul_of_nonneg_right (HardyLadder.ladderValue_two_le hρ (div_pos hy hx)) (by positivity)

/-- A finite spectrum admits one real approximating multiplier exactly when
every pair of its scalar approximation intervals overlaps. -/
theorem common_multiplier_iff {ι : Type*} [Fintype ι] [Nonempty ι] (d : ι → ℝ)
    (hd : ∀ i, 0 < d i) (e : ℝ) :
    (∃ t : ℝ, ∀ i, |d i-t*(d i)^5| ≤ e) ↔
    (∀ i j, d i*(d j)^5-d j*(d i)^5 ≤ e*((d i)^5+(d j)^5)) := by
  classical
  have eqv (t : ℝ) (i : ι) : |d i-t*(d i)^5| ≤ e ↔
      (d i-e)/(d i)^5 ≤ t ∧ t ≤ (d i+e)/(d i)^5 := by
    rw [abs_le, div_le_iff₀ (pow_pos (hd i) 5), le_div_iff₀ (pow_pos (hd i) 5)]
    constructor <;> rintro ⟨h1,h2⟩ <;> constructor <;> linarith
  have pair (i j : ι) : (d i-e)/(d i)^5 ≤ (d j+e)/(d j)^5 ↔
      d i*(d j)^5-d j*(d i)^5 ≤ e*((d i)^5+(d j)^5) := by
    rw [div_le_div_iff₀ (pow_pos (hd i) 5) (pow_pos (hd j) 5)]
    constructor <;> intro h <;> linarith only [h]
  constructor
  · rintro ⟨t,ht⟩ i j
    exact (pair i j).mp (((eqv t i).mp (ht i)).1.trans ((eqv t j).mp (ht j)).2)
  · intro h
    obtain ⟨m, _, hm⟩ := Finset.exists_max_image (univ : Finset ι)
      (fun i => (d i-e)/(d i)^5) univ_nonempty
    exact ⟨_, fun i => (eqv _ i).mpr ⟨hm i (mem_univ i), (pair m i).mpr (h m i)⟩⟩

end HardyPairBound

#print axioms HardyPairBound.pair_bound
#print axioms HardyPairBound.common_multiplier_iff
