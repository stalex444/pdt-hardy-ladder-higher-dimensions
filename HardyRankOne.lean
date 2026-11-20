module

public import HardyExtension.Definitions
public import HardyPairBound
public import Mathlib.Analysis.InnerProductSpace.Projection.Basic
public import Mathlib.Analysis.InnerProductSpace.PiL2

@[expose] public section
/-! Rank-one endpoints in arbitrary finite complex Schmidt spaces. We use actual
Hilbert norms and orthogonal projections, including spectra with zero entries. -/
noncomputable section
open Finset
open scoped ComplexConjugate
namespace HardyRankOne

variable {ι : Type*} [Fintype ι]

theorem residual_le {d : ι → ℝ} {u : EuclideanSpace ℂ ι} (hu : ‖u‖ = 1)
    {t e : ℝ} (h : ∀ i, |d i - t * d i ^ 5| ≤ e) :
    score d u ≤ e^2 := by
  let v := weighted d 1 u
  let w := weighted d 5 u
  let K := Submodule.span ℂ {w}
  have hv : (t:ℂ) • w ∈ K := K.smul_mem _ (Submodule.subset_span (Set.mem_singleton _))
  have hmin : ‖v - K.starProjection v‖ ≤ ‖v - (t:ℂ) • w‖ := by
    rw [Submodule.starProjection_minimal]
    exact ciInf_le ⟨0,fun _ ⟨i,hi⟩ => hi ▸ norm_nonneg _⟩ (⟨_,hv⟩ : K)
  change ‖v - K.starProjection v‖ ^ 2 ≤ e^2
  refine (pow_le_pow_left₀ (norm_nonneg _) hmin 2).trans ?_
  rw [EuclideanSpace.norm_sq_eq]
  calc
    _ ≤ ∑ i, e^2 * ‖u i‖^2 := by
      apply Finset.sum_le_sum
      intro i _
      have hcoord : (v - (t:ℂ) • w) i = ((d i - t*d i^5 : ℝ):ℂ) * u i := by
        change ((d i ^ 1 : ℝ):ℂ)*u i - (t:ℂ)*(((d i ^ 5 : ℝ):ℂ)*u i) = _
        push_cast; ring
      rw [hcoord, norm_mul, mul_pow, Complex.norm_real, Real.norm_eq_abs]
      exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (abs_nonneg _) (h i) 2) (sq_nonneg _)
    _ = e^2 := by rw [← Finset.mul_sum, ← EuclideanSpace.norm_sq_eq, hu]; ring

/-- Either the rank-one score vanishes or one pair of distinct positive Schmidt
coordinates pays for it. This retains the pair weight, which makes strictness at
Schmidt rank ≥ 3 immediate. -/
theorem pair_controls_score {ρ : ℝ} (hρ : ρ^3=ρ+1) {d : ι → ℝ}
    (hd : ∀ i, 0 ≤ d i) (hs : ∑ i, d i ^ 2 = 1)
    {u : EuclideanSpace ℂ ι} (hu : ‖u‖=1) :
    score d u = 0 ∨ ∃ i j : ι, i ≠ j ∧ 0 < d i ∧ 0 < d j ∧
      score d u ≤ ((8*ρ^2+ρ-11)/25) * (d i^2+d j^2) := by
  classical
  have hp : ∃ i, 0 < d i := by
    by_contra! h
    have hz : ∀ i, d i = 0 := fun i => le_antisymm (h i) (hd i)
    simp [hz] at hs
  let I := {i : ι // 0 < d i}
  let _ : Nonempty I := by obtain ⟨i,hi⟩ := hp; exact ⟨⟨i,hi⟩⟩
  let g (m : I × I) := (d m.1.val * d m.2.val^5 - d m.2.val * d m.1.val^5) /
      (d m.1.val^5 + d m.2.val^5)
  obtain ⟨m,_,hm⟩ := Finset.exists_max_image (univ : Finset (I × I)) g univ_nonempty
  have hg (i j : I) : g (i,j) ≤ g m := hm _ (mem_univ _)
  have hnn : 0 ≤ g m := by simpa [g] using hg m.1 m.1
  have hfit : ∃ t : ℝ, ∀ i : I, |d i - t*(d i)^5| ≤ g m := by
    apply (HardyPairBound.common_multiplier_iff (fun i : I => d i) (fun i => i.property) (g m)).2
    intro i j
    exact (div_le_iff₀ (add_pos (pow_pos i.property 5) (pow_pos j.property 5))).mp (hg i j)
  obtain ⟨t,ht⟩ := hfit
  have haul (i : ι) : |d i - t*d i^5| ≤ g m := by
    by_cases hi : 0 < d i
    · exact ht ⟨i,hi⟩
    · have hz : d i = 0 := le_antisymm (le_of_not_gt hi) (hd i)
      simpa [hz] using hnn
  have hres := residual_le hu haul
  by_cases hij : m.1.val = m.2.val
  · left
    have hh : g m = 0 := by simp [g,hij]
    rw [hh] at hres
    exact le_antisymm (by simpa using hres) (sq_nonneg _)
  · exact Or.inr ⟨m.1.val,m.2.val,hij,m.1.property,m.2.property,
      hres.trans (HardyPairBound.pair_bound hρ m.1.property m.2.property)⟩

private theorem plastic_positive {ρ : ℝ} (hρ : ρ^3=ρ+1) : 0 < (8*ρ^2+ρ-11)/25 := by
  have hr := HardyLadder.five_quarters_lt_of_cubic hρ
  nlinarith [sq_nonneg (ρ-5/4)]

/-- The squared norm of the residual orthogonal to `D^5 u` is at most the
plastic Hardy value for every normalized Schmidt spectrum and unit ray. -/
theorem score_le {ρ : ℝ} (hρ : ρ^3=ρ+1) {d : ι → ℝ}
    (hd : ∀ i, 0 ≤ d i) (hs : ∑ i, d i^2=1)
    {u : EuclideanSpace ℂ ι} (hu : ‖u‖=1) : score d u ≤ (8*ρ^2+ρ-11)/25 := by
  classical
  rcases pair_controls_score hρ hd hs hu with hz | ⟨i,j,hij,_,_,h⟩
  · rw [hz]; exact (plastic_positive hρ).le
  · have hsum := Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ ({i,j} : Finset ι))
        (fun k _ _ => sq_nonneg (d k))
    rw [hs] at hsum
    have hb : d i ^ 2 + d j ^ 2 ≤ 1 := by simpa [hij] using hsum
    simpa using h.trans (mul_le_mul_of_nonneg_left hb (plastic_positive hρ).le)

/-- With positive Schmidt coefficients at three different indices (repeated values
are allowed), every rank-one endpoint gives strictly less than the optimum. -/
theorem score_lt_of_three {ρ : ℝ} (hρ : ρ^3=ρ+1) {d : ι → ℝ}
    (hd : ∀ i, 0 ≤ d i) (hs : ∑ i, d i^2=1)
    {u : EuclideanSpace ℂ ι} (hu : ‖u‖=1) {i₀ i₁ i₂ : ι}
    (h01 : i₀ ≠ i₁) (h02 : i₀ ≠ i₂) (h12 : i₁ ≠ i₂)
    (h₀ : 0 < d i₀) (h₁ : 0 < d i₁) (h₂ : 0 < d i₂) :
    score d u < (8*ρ^2+ρ-11)/25 := by
  classical
  rcases pair_controls_score hρ hd hs hu with hz | ⟨i,j,hij,_,_,h⟩
  · rw [hz]; exact plastic_positive hρ
  · have hex : ∃ k, k ≠ i ∧ k ≠ j ∧ 0 < d k := by
      by_contra! hn
      have get (k : ι) (hk : 0 < d k) : k = i ∨ k = j := by
        by_contra! hh; exact hk.not_ge (hn k hh.1 hh.2)
      rcases get i₀ h₀ with rfl | rfl <;> rcases get i₁ h₁ with rfl | rfl <;>
        rcases get i₂ h₂ with rfl | rfl <;> simp_all
    obtain ⟨k,hki,hkj,hk⟩ := hex
    have hsum := Finset.sum_le_sum_of_subset_of_nonneg
      (Finset.subset_univ ({k,i,j} : Finset ι)) (fun l _ _ => sq_nonneg (d l))
    rw [hs] at hsum
    have hb : d i ^ 2 + d j ^ 2 < 1 := by
      simp [hki,hkj,hij] at hsum
      nlinarith [sq_pos_of_pos hk]
    simpa using h.trans_lt (mul_lt_mul_of_pos_left hb (plastic_positive hρ))

/-- Measurement amplitudes against a real diagonal Schmidt operator are unchanged
when the operator is moved to the opposite side of the complex inner product. -/
theorem weighted_selfadjoint (d : ι → ℝ) (k : ℕ) (x y : EuclideanSpace ℂ ι) :
    inner ℂ (weighted d k x) y = inner ℂ x (weighted d k y) := by
  simp only [EuclideanSpace.inner_eq_star_dotProduct, dotProduct, Pi.star_apply]
  apply Finset.sum_congr rfl
  intro i _
  change y i * star (((d i^k:ℝ):ℂ) * x i) = (((d i^k:ℝ):ℂ) * y i) * star (x i)
  rw [star_mul, Complex.star_def, Complex.conj_ofReal]
  ring

/-- The opposite endpoint may have any number of orthonormal outcomes provided
its directions obey the Hardy condition against the single complementary ray.
This gives the codimension-one case on exchanging the two endpoints. -/
theorem family_le_score {κ : Type*} [Fintype κ] (d : ι → ℝ)
    (u : EuclideanSpace ℂ ι) (v : κ → EuclideanSpace ℂ ι) (hv : Orthonormal ℂ v)
    (hz : ∀ j, inner ℂ (weighted d 5 (v j)) u = 0) :
    ∑ j, ‖inner ℂ (weighted d 1 (v j)) u‖^2 ≤ score d u := by
  let x := weighted d 1 u
  let K := Submodule.span ℂ {weighted d 5 u}
  have ho (j : κ) : v j ∈ Kᗮ := Submodule.mem_orthogonal_singleton_iff_inner_left.mpr
    ((weighted_selfadjoint d 5 (v j) u).symm.trans (hz j))
  have hproj (j : κ) : inner ℂ (v j) (K.starProjection x) = 0 :=
    (Submodule.mem_orthogonal' _ _).mp (ho j) _ (K.starProjection_apply_mem x)
  have hid (j : κ) : inner ℂ (weighted d 1 (v j)) u = inner ℂ (v j) (x - K.starProjection x) := by
    rw [inner_sub_right,hproj,sub_zero]
    exact weighted_selfadjoint d 1 (v j) u
  simp_rw [hid]
  exact hv.sum_inner_products_le (x - K.starProjection x)

/-- Finite-dimensional codimension-one endpoint bound in Born-amplitude form. -/
theorem codimension_one_le {κ : Type*} [Fintype κ] {ρ : ℝ} (hρ : ρ^3=ρ+1)
    {d : ι → ℝ} (hd : ∀ i, 0 ≤ d i) (hs : ∑ i, d i^2=1)
    {u : EuclideanSpace ℂ ι} (hu : ‖u‖=1) (v : κ → EuclideanSpace ℂ ι)
    (hv : Orthonormal ℂ v) (hz : ∀ j, inner ℂ (weighted d 5 (v j)) u = 0) :
    ∑ j, ‖inner ℂ (weighted d 1 (v j)) u‖^2 ≤ (8*ρ^2+ρ-11)/25 :=
  (family_le_score d u v hv hz).trans (score_le hρ hd hs hu)


private def diagonalMap (d : ι → ℝ) (k : ℕ) : EuclideanSpace ℂ ι →ₗ[ℂ] EuclideanSpace ℂ ι where
  toFun := weighted d k
  map_add' x y := by
    ext i
    change ((d i ^ k:ℝ):ℂ) * (x i + y i) = _
    exact mul_add _ _ _
  map_smul' c x := by
    ext i
    change ((d i ^ k:ℝ):ℂ) * (c * x i) = c * (((d i ^ k:ℝ):ℂ)*x i)
    ring

/-- The Hardy orthogonality constraints limit the sum of the two endpoint ranks. -/
theorem endpoint_rank_sum {r s : ℕ} {d : ι → ℝ} (hd : ∀ i, 0 < d i)
    (a : Fin r → EuclideanSpace ℂ ι) (b : Fin s → EuclideanSpace ℂ ι)
    (ha : Orthonormal ℂ a) (hb : Orthonormal ℂ b)
    (hz : ∀ i j, inner ℂ (weighted d 5 (a i)) (b j) = 0) :
    r + s ≤ Fintype.card ι := by
  classical
  let T := diagonalMap d 5
  have hinj : Function.Injective T := by
    intro v w he
    ext i
    have hi := congrArg (fun (z : EuclideanSpace ℂ ι) => z i) he
    change ((d i ^ 5 : ℝ):ℂ) * v i = ((d i ^ 5 : ℝ):ℂ) * w i at hi
    exact mul_left_cancel₀ (Complex.ofReal_ne_zero.mpr (pow_pos (hd i) 5).ne') hi
  have hli : LinearIndependent ℂ (T ∘ a) := ha.linearIndependent.map' T
    (LinearMap.ker_eq_bot.mpr hinj)
  have horth : Submodule.IsOrtho (Submodule.span ℂ (Set.range (T ∘ a)))
      (Submodule.span ℂ (Set.range b)) := by
    apply Submodule.isOrtho_span.mpr
    rintro _ ⟨i,rfl⟩ _ ⟨j,rfl⟩
    exact hz i j
  have hdim := Submodule.finrank_add_finrank_le_of_disjoint horth.disjoint
  simpa [finrank_span_eq_card hli,finrank_span_eq_card hb.linearIndependent,
    finrank_euclideanSpace] using hdim

/-- Probability summed over orthonormal bases of both outcome-one endpoint spaces. -/
def endpointScore {r s : ℕ} (d : ι → ℝ) (a : Fin r → EuclideanSpace ℂ ι)
    (b : Fin s → EuclideanSpace ℂ ι) : ℝ :=
  ∑ i, ∑ j, ‖inner ℂ (weighted d 1 (a i)) (b j)‖ ^ 2

private theorem swap_inner (d : ι → ℝ) (k : ℕ) (x y : EuclideanSpace ℂ ι) :
    ‖inner ℂ (weighted d k x) y‖ = ‖inner ℂ (weighted d k y) x‖ := by
  rw [weighted_selfadjoint, norm_inner_symm]

/-- On Schmidt support of size at most three the two endpoint spaces must have a
zero or one-dimensional member. In the latter case Bessel's inequality reduces
the sum of *all* endpoint probabilities to one genuine projected residual. -/
theorem endpoint_reduces_to_ray {r s : ℕ} (hdim : Fintype.card ι ≤ 3)
    {d : ι → ℝ} (hd : ∀ i, 0 < d i) (a : Fin r → EuclideanSpace ℂ ι)
    (b : Fin s → EuclideanSpace ℂ ι) (ha : Orthonormal ℂ a) (hb : Orthonormal ℂ b)
    (hz : ∀ i j, inner ℂ (weighted d 5 (a i)) (b j) = 0) :
    endpointScore d a b = 0 ∨ ∃ u : EuclideanSpace ℂ ι, ‖u‖ = 1 ∧
      endpointScore d a b ≤ score d u := by
  have hdim' := (endpoint_rank_sum hd a b ha hb hz).trans hdim
  have cases : r=0 ∨ s=0 ∨ r=1 ∨ s=1 := by omega
  rcases cases with rfl | rfl | rfl | rfl
  · left; simp [endpointScore]
  · left; simp [endpointScore]
  · right
    refine ⟨a 0,ha.norm_eq_one _,?_⟩
    simp only [endpointScore,Fin.sum_univ_one]
    have hsym (j : Fin s) : inner ℂ (weighted d 5 (b j)) (a 0) = 0 := by
      rw [weighted_selfadjoint,inner_eq_zero_symm]
      exact hz 0 j
    simp_rw [swap_inner d 1 (a 0)]
    exact family_le_score d (a 0) b hb hsym
  · right
    refine ⟨b 0,hb.norm_eq_one _,?_⟩
    simp only [endpointScore,Fin.sum_univ_one]
    exact family_le_score d (b 0) a ha (fun i => hz i 0)

/-- The full reduced endpoint objective for up to three positive Schmidt
coefficients and arbitrary ranks of both projective endpoints. -/
theorem three_level_endpoint_le {r s : ℕ} (hdim : Fintype.card ι ≤ 3)
    {ρ : ℝ} (hρ : ρ^3=ρ+1) {d : ι → ℝ} (hd : ∀ i, 0 < d i)
    (hs : ∑ i, d i^2=1) (a : Fin r → EuclideanSpace ℂ ι)
    (b : Fin s → EuclideanSpace ℂ ι) (ha : Orthonormal ℂ a) (hb : Orthonormal ℂ b)
    (hz : ∀ i j, inner ℂ (weighted d 5 (a i)) (b j) = 0) :
    endpointScore d a b ≤ (8*ρ^2+ρ-11)/25 := by
  rcases endpoint_reduces_to_ray hdim hd a b ha hb hz with h | ⟨u,hu,h⟩
  · rw [h]; exact (plastic_positive hρ).le
  · exact h.trans (score_le hρ (fun i => (hd i).le) hs hu)

/-- The normalized three-positive-coefficient objective is strictly below the
optimum for each fixed full-Schmidt-rank pure qutrit state. -/
theorem three_level_endpoint_lt {r s : ℕ} {ρ : ℝ} (hρ : ρ^3=ρ+1)
    {d : Fin 3 → ℝ} (hd : ∀ i, 0 < d i) (hs : ∑ i, d i^2=1)
    (a : Fin r → EuclideanSpace ℂ (Fin 3)) (b : Fin s → EuclideanSpace ℂ (Fin 3))
    (ha : Orthonormal ℂ a) (hb : Orthonormal ℂ b)
    (hz : ∀ i j, inner ℂ (weighted d 5 (a i)) (b j) = 0) :
    endpointScore d a b < (8*ρ^2+ρ-11)/25 := by
  rcases endpoint_reduces_to_ray (by simp) hd a b ha hb hz with h | ⟨u,hu,h⟩
  · rw [h]; exact plastic_positive hρ
  · exact h.trans_lt (score_lt_of_three hρ (fun i => (hd i).le) hs hu
      (i₀:=0) (i₁:=1) (i₂:=2) (by decide) (by decide) (by decide) (hd 0) (hd 1) (hd 2))


private abbrev E (ι : Type*) := EuclideanSpace ℂ ι

/-- Orthonormal coordinates of a projective outcome subspace in Schmidt space. -/
def outcomeBasis (S : Submodule ℂ (EuclideanSpace ℂ ι)) :
    Fin (Module.finrank ℂ S) → EuclideanSpace ℂ ι :=
  fun i => (stdOrthonormalBasis ℂ S i : S)

theorem outcome_orthonormal (S : Submodule ℂ (EuclideanSpace ℂ ι)) :
    Orthonormal ℂ (outcomeBasis S) :=
  (stdOrthonormalBasis ℂ S).orthonormal.comp_linearIsometry S.subtypeₗᵢ

/-- The joint Born probability of two projective subspace outcomes on a pure
Schmidt state. Bob's subspace coordinates here are conjugated in the Schmidt basis. -/
def event (d : ι → ℝ) (S T : Submodule ℂ (EuclideanSpace ℂ ι)) : ℝ :=
  endpointScore d (outcomeBasis S) (outcomeBasis T)

private theorem event_zero {d : ι → ℝ} {S T : Submodule ℂ (E ι)} (h : event d S T=0)
    {x y : E ι} (hx : x ∈ S) (hy : y ∈ T) : inner ℂ (weighted d 1 x) y = 0 := by
  have hz (i j) : inner ℂ (weighted d 1 (outcomeBasis S i)) (outcomeBasis T j) = 0 := by
    have ha := Finset.single_le_sum (f := fun i => ∑ j,
      ‖inner ℂ (weighted d 1 (outcomeBasis S i)) (outcomeBasis T j)‖^2)
      (fun i _ => Finset.sum_nonneg fun _ _ => sq_nonneg _) (Finset.mem_univ i)
    have hb := Finset.single_le_sum (f := fun j =>
      ‖inner ℂ (weighted d 1 (outcomeBasis S i)) (outcomeBasis T j)‖^2)
        (fun j _ => sq_nonneg _) (Finset.mem_univ j)
    change _ ≤ event d S T at ha
    rw [h] at ha
    exact norm_eq_zero.mp (by nlinarith [hb.trans ha] )
  have expansion (Z : Submodule ℂ (E ι)) (v : E ι) (hv : v ∈ Z) :
      ∃ c : Fin (Module.finrank ℂ Z) → ℂ, ∑ i, c i • outcomeBasis Z i = v := by
    let z : Z := ⟨v,hv⟩
    let e := stdOrthonormalBasis ℂ Z
    refine ⟨fun i => e.repr z i, ?_⟩
    exact (show ∑ i, e.repr z i • outcomeBasis Z i = Z.subtype z by
      simpa only [map_sum, map_smul, Submodule.subtype_apply, outcomeBasis, e] using
        congrArg Z.subtype (e.sum_repr z))
  obtain ⟨c,hc⟩ := expansion S x hx
  obtain ⟨f,hf⟩ := expansion T y hy
  change inner ℂ (diagonalMap d 1 x) y = 0
  rw [← hc,← hf]
  simp only [map_sum, map_smul, sum_inner, inner_sum, inner_smul_left, inner_smul_right]
  have hall (i j) : inner ℂ ((diagonalMap d 1) (outcomeBasis S i)) (outcomeBasis T j) = 0 := hz i j
  simp only [hall,mul_zero,Finset.sum_const_zero]

omit [Fintype ι] in
private theorem weighted_add (d : ι → ℝ) (k l : ℕ) (u : E ι) :
    weighted d k (weighted d l u) = weighted d (k+l) u := by
  ext i
  change ((d i^k:ℝ):ℂ) * (((d i^l:ℝ):ℂ) * u i) = ((d i^(k+l):ℝ):ℂ) * u i
  rw [pow_add, Complex.ofReal_mul, mul_assoc]

/-- The five original zero-probability conditions on binary projective
measurements force the fifth-power orthogonality used by the dimension bound. -/
theorem five_zeros_force_endpoint {d : ι → ℝ}
    {A B : Fin 3 → Submodule ℂ (EuclideanSpace ℂ ι)}
    (base : event d (A 0) (B 0) = 0)
    (left : ∀ i : Fin 2, event d (A i.succ) (B i.castSucc)ᗮ = 0)
    (right : ∀ i : Fin 2, event d (A i.castSucc)ᗮ (B i.succ) = 0)
    {x y : EuclideanSpace ℂ ι} (hx : x ∈ A 2) (hy : y ∈ B 2) :
    inner ℂ (weighted d 5 x) y = 0 := by
  have l (i : Fin 2) {u : E ι} (hu : u ∈ A i.succ) :
      weighted d 1 u ∈ B i.castSucc := by
    rw [← (B i.castSucc).orthogonal_orthogonal]
    exact (Submodule.mem_orthogonal' _ _).mpr fun v hv => event_zero (left i) hu hv
  have r (i : Fin 2) {v : E ι} (hv : v ∈ B i.succ) :
      weighted d 1 v ∈ A i.castSucc := by
    rw [← (A i.castSucc).orthogonal_orthogonal]
    exact (Submodule.mem_orthogonal _ _).mpr fun u hu =>
      (weighted_selfadjoint d 1 u v).symm.trans (event_zero (right i) hu hv)
  have ha := r 0 (l 1 hx)
  have hb := l 0 (r 1 hy)
  have he := event_zero base ha hb
  rw [← weighted_selfadjoint,← weighted_selfadjoint] at he
  simpa only [weighted_add] using he

/-- End-to-end Hardy bound for pure positive-Schmidt states on a support of
dimension ≤3 and arbitrary projective ranks at all six measurements. -/
theorem three_level_projective_le (hdim : Fintype.card ι ≤ 3)
    {ρ : ℝ} (hρ : ρ^3=ρ+1) {d : ι → ℝ} (hd : ∀ i, 0 < d i)
    (hs : ∑ i, d i^2=1) (A B : Fin 3 → Submodule ℂ (EuclideanSpace ℂ ι))
    (base : event d (A 0) (B 0) = 0)
    (left : ∀ i : Fin 2, event d (A i.succ) (B i.castSucc)ᗮ = 0)
    (right : ∀ i : Fin 2, event d (A i.castSucc)ᗮ (B i.succ) = 0) :
    event d (A 2) (B 2) ≤ (8*ρ^2+ρ-11)/25 :=
  three_level_endpoint_le hdim hρ hd hs _ _ (outcome_orthonormal _) (outcome_orthonormal _)
    (fun i j => five_zeros_force_endpoint base left right
      ((stdOrthonormalBasis ℂ (A 2) i).property) ((stdOrthonormalBasis ℂ (B 2) j).property))

theorem full_rank_qutrit_projective_lt {ρ : ℝ} (hρ : ρ^3=ρ+1)
    {d : Fin 3 → ℝ} (hd : ∀ i, 0 < d i) (hs : ∑ i, d i^2=1)
    (A B : Fin 3 → Submodule ℂ (EuclideanSpace ℂ (Fin 3)))
    (base : event d (A 0) (B 0) = 0)
    (left : ∀ i : Fin 2, event d (A i.succ) (B i.castSucc)ᗮ = 0)
    (right : ∀ i : Fin 2, event d (A i.castSucc)ᗮ (B i.succ) = 0) :
    event d (A 2) (B 2) < (8*ρ^2+ρ-11)/25 :=
  three_level_endpoint_lt hρ hd hs _ _ (outcome_orthonormal _) (outcome_orthonormal _)
    (fun i j => five_zeros_force_endpoint base left right
      ((stdOrthonormalBasis ℂ (A 2) i).property) ((stdOrthonormalBasis ℂ (B 2) j).property))

end HardyRankOne

#print axioms HardyRankOne.score_le
#print axioms HardyRankOne.score_lt_of_three

#print axioms HardyRankOne.codimension_one_le

#print axioms HardyRankOne.three_level_endpoint_le
#print axioms HardyRankOne.three_level_endpoint_lt

#print axioms HardyRankOne.three_level_projective_le
#print axioms HardyRankOne.full_rank_qutrit_projective_lt
