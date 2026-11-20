module

public import HardyExtension.Definitions
public import HardyRankOne

@[expose] public section
/-! Binary effects in spectral coordinates. Positive-support rounding converts the
five Hardy zeros to constraints on projective supports without averaging over
six independent random settings. A zero weight is allowed at every setting. -/
noncomputable section
namespace HardyEffects
open Finset
open HardyRankOne (weighted)

variable {ι : Type*} [Fintype ι]
open scoped Classical

theorem event_nonneg (d : ι → ℝ) (A B : Effect ι) : 0 ≤ event d A B :=
  Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ =>
    mul_nonneg (mul_nonneg (A.nonneg i) (B.nonneg j)) (sq_nonneg _)

/-- Support of the outcome-one effect. -/
def Effect.support (A : Effect ι) : Submodule ℂ (Space ι) :=
  Submodule.span ℂ (Set.range (fun i : {j // 0 < A.weight j} => A.basis i.val))

private theorem basis_mem (A : Effect ι) {i} (h : 0 < A.weight i) :
    A.basis i ∈ A.support := Submodule.subset_span ⟨⟨i,h⟩,rfl⟩

/-- Every vector in the kernel of the outcome-one effect lies in the positive
support of the complementary effect. -/
theorem support_orthogonal_le_complement (A : Effect ι) : A.supportᗮ ≤ A.complement.support := by
  intro x hx
  rw [← A.basis.sum_repr' x]
  apply Submodule.sum_mem
  intro i _
  by_cases h : 0 < A.weight i
  · have h0 := (Submodule.mem_orthogonal _ _).mp hx _ (basis_mem A h)
    simp [h0]
  · have hz : A.weight i = 0 := le_antisymm (le_of_not_gt h) (A.nonneg i)
    have hp : 0 < A.complement.weight i := by simp [Effect.complement,hz]
    exact A.complement.support.smul_mem _ (basis_mem A.complement hp)

private theorem zero_entry {d : ι → ℝ} {A B : Effect ι} (he : event d A B=0) {i j : ι}
    (hi : 0 < A.weight i) (hj : 0 < B.weight j) :
    inner ℂ (weighted d 1 (A.basis i)) (B.basis j) = 0 := by
  let f i j := (A.weight i*B.weight j) * entry d A B i j
  have hf i j : 0 ≤ f i j := mul_nonneg (mul_nonneg (A.nonneg i) (B.nonneg j)) (sq_nonneg _)
  have h1 := Finset.single_le_sum (f := fun i => ∑ j, f i j)
    (fun i _ => Finset.sum_nonneg fun j _ => hf i j) (Finset.mem_univ i)
  have h2 := Finset.single_le_sum (f := f i) (fun j _ => hf i j) (Finset.mem_univ j)
  change _ ≤ event d A B at h1
  have hz := le_antisymm (by simpa only [he] using h2.trans h1) (hf i j)
  have hp : A.weight i * B.weight j ≠ 0 := (mul_pos hi hj).ne'
  have hz' : entry d A B i j = 0 := (mul_eq_zero.mp hz).resolve_left hp
  exact norm_eq_zero.mp ((pow_eq_zero_iff (by decide : 2≠0)).mp hz')

private def diag (d : ι → ℝ) : Space ι →ₗ[ℂ] Space ι where
  toFun := weighted d 1
  map_add' x y := by
    ext i
    exact mul_add _ _ _
  map_smul' c x := by
    ext i
    change ((d i^1:ℝ):ℂ) * (c*x i) = c*(((d i^1:ℝ):ℂ)*x i)
    ring

private theorem zero_on_support {d : ι → ℝ} {A B : Effect ι} (he : event d A B=0)
    {x y : Space ι} (hx : x ∈ A.support) (hy : y ∈ B.support) :
    inner ℂ (weighted d 1 x) y = 0 := by
  have h : Submodule.IsOrtho (A.support.map (diag d)) B.support := by
    rw [Effect.support,Submodule.map_span]
    apply Submodule.isOrtho_span.mpr
    rintro _ ⟨_,⟨i,rfl⟩,rfl⟩ _ ⟨j,rfl⟩
    exact zero_entry he i.property j.property
  exact (Submodule.isOrtho_iff_inner_eq.mp h) _ ⟨x,hx,rfl⟩ _ hy

private theorem projective_zero {d : ι → ℝ} {S T : Submodule ℂ (Space ι)}
    (h : ∀ x ∈ S, ∀ y ∈ T, inner ℂ (weighted d 1 x) y = 0) :
    HardyRankOne.event d S T = 0 := by
  unfold HardyRankOne.event HardyRankOne.endpointScore
  apply Finset.sum_eq_zero
  intro i _
  apply Finset.sum_eq_zero
  intro j _
  have hz := h _ (stdOrthonormalBasis ℂ S i).property _ (stdOrthonormalBasis ℂ T j).property
  change ‖inner ℂ (weighted d 1 ((stdOrthonormalBasis ℂ S i : S) : Space ι))
    ((stdOrthonormalBasis ℂ T j : T) : Space ι)‖^2 = 0
  rw [hz]; simp

/-- The original five effect probabilities imply the endpoint orthogonality for
every pair of rays in the positive terminal supports. -/
theorem five_zeros_force_endpoint {d : ι → ℝ} {A B : Fin 3 → Effect ι}
    (base : event d (A 0) (B 0)=0)
    (left : ∀ i : Fin 2, event d (A i.succ) (B i.castSucc).complement=0)
    (right : ∀ i : Fin 2, event d (A i.castSucc).complement (B i.succ)=0)
    {x y : Space ι} (hx : x ∈ (A 2).support) (hy : y ∈ (B 2).support) :
    inner ℂ (weighted d 5 x) y = 0 := by
  apply HardyRankOne.five_zeros_force_endpoint
    (A:=fun i => (A i).support) (B:=fun i => (B i).support) _ _ _ hx hy
  · exact projective_zero fun _ h1 _ h2 => zero_on_support base h1 h2
  · intro i
    exact projective_zero fun _ h1 _ h2 => zero_on_support (left i) h1
      (support_orthogonal_le_complement _ h2)
  · intro i
    exact projective_zero fun _ h1 _ h2 => zero_on_support (right i)
      (support_orthogonal_le_complement _ h1) h2


abbrev Active (A : Effect ι) := {i // 0 < A.weight i}

def activeRay (A : Effect ι) (j : Fin (Fintype.card (Active A))) : Space ι :=
  A.basis ((Fintype.equivFin (Active A)).symm j).val

theorem orthonormal_active (A : Effect ι) : Orthonormal ℂ (activeRay A) :=
  A.basis.orthonormal.comp _ <| Subtype.val_injective.comp (Fintype.equivFin (Active A)).symm.injective

theorem active_mem (A : Effect ι) (i) : activeRay A i ∈ A.support :=
  basis_mem A ((Fintype.equivFin (Active A)).symm i).property

private theorem sum_on_active (A : Effect ι) (f : ι → ℝ) (hz : ∀ i, A.weight i = 0 → f i = 0) :
    ∑ i, f i = ∑ i : Active A, f i.val := by
  have h := Fintype.sum_subtype_add_sum_subtype (fun i => 0 < A.weight i) f
  have ho : ∀ i : {i // ¬ 0 < A.weight i}, f i.val = 0 :=
    fun i => hz i (le_antisymm (le_of_not_gt i.property) (A.nonneg i))
  simpa only [ho, Finset.sum_const_zero, add_zero] using h.symm

/-- Raising all positive eigenvalues to one can only raise the terminal probability. -/
theorem event_le_active (d : ι → ℝ) (A B : Effect ι) :
    event d A B ≤ HardyRankOne.endpointScore d (activeRay A) (activeRay B) := by
  let f i j := (A.weight i * B.weight j) * entry d A B i j
  change ∑ i, ∑ j, f i j ≤ _
  rw [sum_on_active A (fun i => ∑ j, f i j) (fun i hi => by simp [f,hi])]
  calc
    _ = ∑ i : Active A, ∑ j : Active B, f i.val j.val := by
      apply Finset.sum_congr rfl
      intro i _
      exact sum_on_active B (f i.val) (fun j hj => by simp [f,hj])
    _ ≤ ∑ i : Active A, ∑ j : Active B, entry d A B i j := by
      apply Finset.sum_le_sum; intro i _
      apply Finset.sum_le_sum; intro j _
      have hw : A.weight i * B.weight j ≤ 1 := by
        simpa using mul_le_mul (A.le_one i) (B.le_one j) (B.nonneg j) (zero_le_one : (0:ℝ) ≤ 1)
      simpa [f] using mul_le_mul_of_nonneg_right hw (show 0 ≤ entry d A B i j from sq_nonneg _)
    _ = _ := by
      unfold HardyRankOne.endpointScore
      rw [← (Fintype.equivFin (Active A)).symm.sum_comp]
      apply Finset.sum_congr rfl; intro i _
      exact ((Fintype.equivFin (Active B)).symm.sum_comp _).symm

theorem three_level_effect_le (hdim : Fintype.card ι ≤ 3) {ρ : ℝ} (hρ : ρ^3=ρ+1)
    {d : ι → ℝ} (hd : ∀ i, 0 < d i) (hs : ∑ i, d i^2=1) (A B : Fin 3 → Effect ι)
    (base : event d (A 0) (B 0)=0)
    (left : ∀ i : Fin 2, event d (A i.succ) (B i.castSucc).complement=0)
    (right : ∀ i : Fin 2, event d (A i.castSucc).complement (B i.succ)=0) :
    event d (A 2) (B 2) ≤ (8*ρ^2+ρ-11)/25 := by
  refine (event_le_active d (A 2) (B 2)).trans
    (HardyRankOne.three_level_endpoint_le hdim hρ hd hs _ _
      (orthonormal_active _) (orthonormal_active _) ?_)
  exact fun i j => five_zeros_force_endpoint base left right (active_mem _ i) (active_mem _ j)

theorem full_rank_qutrit_effect_lt {ρ : ℝ} (hρ : ρ^3=ρ+1) {d : Fin 3 → ℝ}
    (hd : ∀ i, 0 < d i) (hs : ∑ i, d i^2=1) (A B : Fin 3 → Effect (Fin 3))
    (base : event d (A 0) (B 0)=0)
    (left : ∀ i : Fin 2, event d (A i.succ) (B i.castSucc).complement=0)
    (right : ∀ i : Fin 2, event d (A i.castSucc).complement (B i.succ)=0) :
    event d (A 2) (B 2) < (8*ρ^2+ρ-11)/25 := by
  refine (event_le_active d (A 2) (B 2)).trans_lt
    (HardyRankOne.three_level_endpoint_lt hρ hd hs _ _
      (orthonormal_active _) (orthonormal_active _) ?_)
  exact fun i j => five_zeros_force_endpoint base left right (active_mem _ i) (active_mem _ j)

open Matrix
open scoped Matrix ComplexOrder

/-- Eigenvalues of an arbitrary binary effect matrix lie in the unit interval.
Conjugating the complementary positive operator into the same basis gives the upper bound. -/
theorem eigenvalue_le_one [DecidableEq ι] (M : Matrix ι ι ℂ) (hp : M.PosSemidef)
    (hc : (1-M).PosSemidef) (i : ι) : hp.1.eigenvalues i ≤ 1 := by
  let U := hp.1.eigenvectorUnitary
  let V : Matrix ι ι ℂ := U
  have hu : Vᴴ * V = 1 := Matrix.mem_unitaryGroup_iff'.mp U.property
  have hm := hp.1.conjStarAlgAut_star_eigenvectorUnitary
  rw [Unitary.conjStarAlgAut_star_apply] at hm
  have he : Vᴴ * M * V = diagonal (RCLike.ofReal ∘ hp.1.eigenvalues) := hm
  have hpos := hc.conjTranspose_mul_mul_same V
  rw [mul_sub,mul_one,sub_mul,hu,he] at hpos
  have h := Complex.nonneg_iff.mp (hpos.diag_nonneg (i:=i))
  simpa [Matrix.sub_apply, RCLike.ofReal_eq_complex_ofReal] using h.1

/-- Every Hermitian effect matrix with positive semidefinite effect and complement
defines an admissible spectral effect. The basis is supplied by the spectral theorem. -/
def Effect.ofMatrix [DecidableEq ι] (M : Matrix ι ι ℂ) (hp : M.PosSemidef)
    (hc : (1-M).PosSemidef) : Effect ι where
  basis := hp.1.eigenvectorBasis
  weight := hp.1.eigenvalues
  nonneg := hp.eigenvalues_nonneg
  le_one := eigenvalue_le_one M hp hc

/-- Reconstruct the effect matrix from its complex orthonormal eigenvectors and weights. -/
def Effect.toMatrix [DecidableEq ι] (A : Effect ι) : Matrix ι ι ℂ :=
  let U := Matrix.of fun i j => A.basis j i
  U * diagonal (fun i => (A.weight i : ℂ)) * Uᴴ

/-- Spectral conversion preserves the original effect matrix, including repeated
and boundary eigenvalues. -/
theorem Effect.toMatrix_ofMatrix [DecidableEq ι] (M : Matrix ι ι ℂ) (hp : M.PosSemidef)
    (hc : (1-M).PosSemidef) : (Effect.ofMatrix M hp hc).toMatrix = M := by
  let U : Matrix ι ι ℂ := hp.1.eigenvectorUnitary
  have he : (Matrix.of fun i j => hp.1.eigenvectorBasis j i) = U := by
    ext i j; rfl
  have ht := hp.1.spectral_theorem
  rw [Unitary.conjStarAlgAut_apply, RCLike.ofReal_eq_complex_ofReal] at ht
  unfold Effect.toMatrix
  change (Matrix.of fun i j => hp.1.eigenvectorBasis j i) *
    diagonal (fun i => (hp.1.eigenvalues i : ℂ)) * _ = M
  rw [he]
  exact ht.symm

end HardyEffects

#print axioms HardyEffects.three_level_effect_le
#print axioms HardyEffects.full_rank_qutrit_effect_lt

#print axioms HardyEffects.Effect.toMatrix_ofMatrix
