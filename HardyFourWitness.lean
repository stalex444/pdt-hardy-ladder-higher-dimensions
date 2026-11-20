module

public import HardyEffects
public import HardyFourPairing

/-! Attainment by binary effects at every prescribed positive four-level spectrum. -/
@[expose] public section
noncomputable section
namespace HardyFourWitness
open Finset Real HardyTripleGap HardyFourPairing HardyEffects

/-- The two outcomes of a real projective setting. -/
def rot (a : ℝ) : Fin 2 → Fin 2 → ℝ :=
  ![![cos a, sin a], ![-sin a, cos a]]

def pairProbability (x y a b : ℝ) (i j : Fin 2) : ℝ :=
  (x * rot a i 0 * rot b j 0 + y * rot a i 1 * rot b j 1)^2

private theorem pair_scale (s c e a b : ℝ) (i j : Fin 2) :
    pairProbability (s*c) (s*e) a b i j = s^2 * pairProbability c e a b i j := by
  unfold pairProbability
  ring

private theorem normalized_edge (x y : ℝ) (hx : 0<x) (hy : 0<y) {s : ℝ}
    (hs : s^2=x^2+y^2) :
    s^2 * HardyLadder.ladderValue 2 (y/x) = edge x y := by
  have hn : x^5+y^5 ≠ 0 := by positivity
  rw [hs]
  norm_num [HardyLadder.ladderValue,edge]
  field_simp
  ring

/-- The optimal qubit pairing rescales with its Schmidt norm. -/
theorem pair_attained (x y : ℝ) (hx : 0<x) (hy : 0<y) :
    ∃ a b : ℕ → ℝ, pairProbability x y (a 0) (b 0) 0 0 = 0 ∧
      (∀ k < 2, pairProbability x y (a (k+1)) (b k) 0 1 = 0) ∧
      (∀ k < 2, pairProbability x y (a k) (b (k+1)) 1 0 = 0) ∧
      pairProbability x y (a 2) (b 2) 0 0 = edge x y := by
  let s := Real.sqrt (x^2+y^2)
  have pos : 0<s := Real.sqrt_pos.mpr (by positivity)
  have hs : s^2=x^2+y^2 := Real.sq_sqrt (by positivity)
  have hnorm : (x/s)^2 + (y/s)^2 = 1 := by
    rw [div_pow,div_pow,←add_div,←hs,div_self (pow_ne_zero _ pos.ne')]
  obtain ⟨a,b,h0,hA,hB,hp⟩ := HardyLadder.ladder_prob_attained 2 (div_pos hx pos) (div_pos hy pos) hnorm
  have scale (u v : ℝ) (i j : Fin 2) :
      pairProbability x y u v i j = s^2 * pairProbability (x/s) (y/s) u v i j := by
    convert pair_scale s (x/s) (y/s) u v i j using 2 <;> field_simp
  refine ⟨a,b,?_,?_,?_,?_⟩
  · rw [scale, show pairProbability (x/s) (y/s) (a 0) (b 0) 0 0 = 0 from h0,mul_zero]
  · intro k hk
    rw [scale,show pairProbability (x/s) (y/s) (a (k+1)) (b k) 0 1 = 0 from hA k hk,mul_zero]
  · intro k hk
    rw [scale,show pairProbability (x/s) (y/s) (a k) (b (k+1)) 1 0 = 0 from hB k hk,mul_zero]
  · rw [scale,show pairProbability (x/s) (y/s) (a 2) (b 2) 0 0 = _ from hp,
      div_div_div_cancel_right₀ pos.ne', normalized_edge x y hx hy hs]

/-- Rows 0 and 2 form one outcome, and 1 and 3 form its complement. -/
def blocks (a b : ℝ) : Fin 4 → Fin 4 → ℝ :=
  ![![cos a, sin a, 0, 0], ![-sin a, cos a, 0, 0],
    ![0, 0, cos b, sin b], ![0, 0, -sin b, cos b]]

/-- The permutation assigns the two pairs to their Schmidt coordinates. -/
def vec (e : Equiv.Perm (Fin 4)) (a b : ℝ) (l : Fin 4) : Space (Fin 4) :=
  WithLp.toLp 2 fun t => (blocks a b l (e.symm t) : ℂ)

theorem vec_orthonormal (e : Equiv.Perm (Fin 4)) (a b : ℝ) :
    Orthonormal ℂ (vec e a b) := by
  rw [orthonormal_iff_ite]
  intro i j
  rw [EuclideanSpace.inner_eq_star_dotProduct]
  unfold dotProduct
  rw [←Equiv.sum_comp e]
  simp only [vec, Pi.star_apply, PiLp.toLp_apply, Equiv.symm_apply_apply, Complex.star_def,
    Complex.conj_ofReal, ←Complex.ofReal_mul, ←Complex.ofReal_sum]
  fin_cases i <;> fin_cases j <;> simp [blocks, Fin.sum_univ_four, ←sq,
    Real.cos_sq_add_sin_sq, Real.sin_sq_add_cos_sq] <;> ring

def basis (e : Equiv.Perm (Fin 4)) (a b : ℝ) : OrthonormalBasis (Fin 4) ℂ (Space (Fin 4)) :=
  let h := vec_orthonormal e a b
  (basisOfOrthonormalOfCardEqFinrank h (by simp [Space])).toOrthonormalBasis (by simpa using h)

private theorem basis_apply (e : Equiv.Perm (Fin 4)) (a b : ℝ) (l : Fin 4) :
    basis e a b l = vec e a b l := by
  simp [basis, Module.Basis.coe_toOrthonormalBasis]

def effect (e : Equiv.Perm (Fin 4)) (a b : ℝ) (i : Fin 2) : Effect (Fin 4) where
  basis := basis e a b
  weight := ![if i=0 then 1 else 0, if i=1 then 1 else 0,
              if i=0 then 1 else 0, if i=1 then 1 else 0]
  nonneg j := by fin_cases i <;> fin_cases j <;> norm_num
  le_one j := by fin_cases i <;> fin_cases j <;> norm_num

private theorem effect_complement (e : Equiv.Perm (Fin 4)) (a b : ℝ) :
    (effect e a b 0).complement = effect e a b 1 := by
  unfold effect Effect.complement
  congr 1
  funext j
  fin_cases j <;> norm_num [effect,Effect.complement]

private theorem entry_blocks (d : Fin 4 → ℝ) (e : Equiv.Perm (Fin 4)) (a b c f : ℝ)
    (m n : Fin 2) (i j : Fin 4) :
    entry d (effect e a b m) (effect e c f n) i j =
      (∑ k : Fin 4, (d (e k) * blocks a b i k) * blocks c f j k)^2 := by
  unfold entry
  change ‖inner ℂ (HardyRankOne.weighted d 1 (basis e a b i)) (basis e c f j)‖^2 = _
  rw [basis_apply,basis_apply,EuclideanSpace.inner_eq_star_dotProduct]
  unfold dotProduct
  rw [←Equiv.sum_comp e]
  simp [HardyRankOne.weighted,vec,←Complex.ofReal_sum,←Complex.ofReal_mul,mul_comm,
    mul_left_comm,Real.norm_eq_abs]

/-- The actual double spectral sum has two contributions, one from each paired sector. -/
theorem event_blocks (d : Fin 4 → ℝ) (e : Equiv.Perm (Fin 4)) (a b c f : ℝ)
    (m n : Fin 2) :
    event d (effect e a b m) (effect e c f n) =
      pairProbability (d (e 0)) (d (e 1)) a c m n +
      pairProbability (d (e 2)) (d (e 3)) b f m n := by
  unfold event
  simp_rw [entry_blocks]
  fin_cases m <;> fin_cases n <;> simp [Fin.sum_univ_four,effect,blocks,pairProbability,rot]

private theorem matching_permutation (d : Fin 4 → ℝ) :
    ∃ e : Equiv.Perm (Fin 4), edge (d (e 0)) (d (e 1)) + edge (d (e 2)) (d (e 3)) = matchingMax d := by
  unfold matchingMax
  rcases le_total (edge (d 0) (d 1) + edge (d 2) (d 3))
    (max (edge (d 0) (d 2) + edge (d 1) (d 3)) (edge (d 0) (d 3) + edge (d 1) (d 2))) with h | h
  · rw [max_eq_right h]
    rcases le_total (edge (d 0) (d 2) + edge (d 1) (d 3))
      (edge (d 0) (d 3) + edge (d 1) (d 2)) with hh | hh
    · rw [max_eq_right hh]
      refine ⟨(Equiv.swap (1 : Fin 4) 3).trans (Equiv.swap 1 2), ?_⟩
      rfl
    · rw [max_eq_left hh]
      exact ⟨Equiv.swap (1 : Fin 4) 2, rfl⟩
  · rw [max_eq_left h]
    exact ⟨Equiv.refl _, rfl⟩

/-- At any fixed four-level Schmidt spectrum, explicit local binary projectors
achieve the best of the three disjoint pairings with all five forbidden probabilities zero.
For an unnormalized spectrum the Born weights have the same quadratic scaling. -/
theorem four_level_effect_attainment (d : Fin 4 → ℝ) (hd : ∀ i, 0 < d i) :
    ∃ A B : Fin 3 → Effect (Fin 4),
      event d (A 0) (B 0) = 0 ∧
      (∀ i : Fin 2, event d (A i.succ) (B i.castSucc).complement = 0) ∧
      (∀ i : Fin 2, event d (A i.castSucc).complement (B i.succ) = 0) ∧
      event d (A 2) (B 2) = matchingMax d := by
  obtain ⟨e,he⟩ := matching_permutation d
  obtain ⟨a,b,h0,hA,hB,ht⟩ := pair_attained _ _ (hd (e 0)) (hd (e 1))
  obtain ⟨u,v,h1,hU,hV,hw⟩ := pair_attained _ _ (hd (e 2)) (hd (e 3))
  refine ⟨fun k => effect e (a k.val) (u k.val) 0,
    fun k => effect e (b k.val) (v k.val) 0,?_,?_,?_,?_⟩
  · simp only [event_blocks, Fin.val_zero,h0,h1,add_zero]
  · intro i
    simp only [effect_complement,event_blocks,Fin.val_castSucc,Fin.val_succ,hA i.val i.isLt,hU i.val i.isLt,add_zero]
  · intro i
    simp only [effect_complement,event_blocks,Fin.val_castSucc,Fin.val_succ,hB i.val i.isLt,hV i.val i.isLt,add_zero]
  · simpa only [event_blocks,show (2 : Fin 3).val = 2 from rfl,ht,hw] using he

end HardyFourWitness

#print axioms HardyFourWitness.four_level_effect_attainment

