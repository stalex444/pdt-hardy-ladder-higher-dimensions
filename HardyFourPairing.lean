module

public import HardyExtension.Definitions
public import HardyTripleGap
public import HardyGapBalance

@[expose] public section
/-! Balancing all six minors for four positive Schmidt coefficients. The three
complementary pairs are (01,23), (02,13), and (03,12). -/
noncomputable section
open Finset HardyTripleGap HardyGapBalance
namespace HardyFourPairing

abbrev PairIndex := Fin 3
abbrev Key := Vertex × Vertex

/-- Three disjoint-matching scores bound all six individual costs. -/
def MatchingBound (K : ℝ) (d : Vertex → ℝ) : Prop :=
  edge (d 0) (d 1) + edge (d 2) (d 3) ≤ K ∧
  edge (d 0) (d 2) + edge (d 1) (d 3) ≤ K ∧
  edge (d 0) (d 3) + edge (d 1) (d 2) ≤ K

private theorem edge_swap (x y : ℝ) : edge x y = edge y x := by
  unfold edge
  rw [add_comm (x^5) (y^5)]
  ring

private theorem coeff_swap (K x y : ℝ) :
    HardyTripleGap.coefficient K x y = HardyTripleGap.coefficient K y x := by
  unfold HardyTripleGap.coefficient
  rw [edge_swap x y]
  ring

theorem matching_costs {K : ℝ} {d : Vertex → ℝ} (hm : MatchingBound K d) :
    0 ≤ K ∧ ∀ i j, edge (d i) (d j) ≤ K := by
  obtain ⟨h01,h02,h03⟩ := hm
  have nn (i j : Vertex) : 0 ≤ edge (d i) (d j) := sq_nonneg _
  have hk : 0≤K := (add_nonneg (nn 0 1) (nn 2 3)).trans h01
  have small (i j : Vertex) (hij : i≤j) : edge (d i) (d j) ≤ K := by
    fin_cases i <;> fin_cases j <;>
      first
      | exact absurd hij (by decide)
      | simpa [edge] using hk
      | exact (le_add_of_nonneg_right (nn 2 3)).trans h01
      | exact (le_add_of_nonneg_left (nn 0 1)).trans h01
      | exact (le_add_of_nonneg_right (nn 1 3)).trans h02
      | exact (le_add_of_nonneg_left (nn 0 2)).trans h02
      | exact (le_add_of_nonneg_right (nn 1 2)).trans h03
      | exact (le_add_of_nonneg_left (nn 0 3)).trans h03
  refine ⟨hk,fun i j => ?_⟩
  rcases le_total i j with h | h
  · exact small i j h
  · rw [edge_swap]; exact small j i h

def key (i j : Vertex) : Key := (min i j,max i j)

def front (i j : PairIndex) := key i.succ j.succ
def back (i j : PairIndex) : Key :=
  if front i j = (1,2) then (0,3) else if front i j = (1,3) then (0,2) else (0,1)

/-- A minor from each complementary pair gives either a common-center star or a
triangle. These are the three labels of the resulting rank-one inequality. -/
def labels (f : PairIndex → Bool) : PairIndex → Vertex :=
  if f 0 = f 1 then
    if f 1 = f 2 then ![1,2,3] else ![2,1,0]
  else if f 0 = f 2 then ![3,0,1] else ![0,3,2]

/-- Exhaustive certificate covering all eight high-side choices. -/
private theorem eight_orientations : ∀ (f : PairIndex → Bool) (i j : PairIndex), i<j →
    (if f i = f j then front i j else back i j) = key (labels f i) (labels f j) := by
  decide

def coeffKey (K : ℝ) (d : Vertex → ℝ) (k : Key) :=
  HardyTripleGap.coefficient K (d k.1) (d k.2)

private theorem coeff_key (K : ℝ) (d : Vertex → ℝ) (i j : Vertex) :
    coeffKey K d (key i j) = HardyTripleGap.coefficient K (d i) (d j) := by
  rcases le_total i j with h | h
  · simp [key,coeffKey,min_eq_left h,max_eq_right h]
  · simpa [key,coeffKey,min_eq_right h,max_eq_left h] using coeff_swap K (d j) (d i)

private def aligned {n : ℕ} (f : Fin n → Bool) (c b : Fin n → Fin n → ℝ) (i j : Fin n) :=
  if f i = f j then c i j else b i j

private def swapSide {n : ℕ} (f : Fin n → Bool) (u v : Fin n → ℝ) (i : Fin n) :=
  if f i then v i else u i

private theorem orient_gap {n : ℕ} (K : ℝ) (dis : Fin n → ℝ)
    (c b : Fin n → Fin n → ℝ) (f : Fin n → Bool) (u v : Fin n → ℝ) :
    gap K dis (aligned f c b) (aligned f b c) (swapSide f u v) (swapSide f v u) =
    gap K dis c b u v := by
  unfold gap
  congr 1
  · apply sum_congr rfl
    intro i _
    cases h : f i <;> simp [swapSide,h]
    all_goals ring
  · unfold edges
    apply sum_congr rfl
    intro i _
    apply sum_congr rfl
    intro j _
    cases hi : f i <;> cases hj : f j <;> simp [swapSide,aligned,hi,hj] <;> ring

private theorem edges_three (f : PairIndex → PairIndex → ℝ) :
    edges f = f 0 1 + f 0 2 + f 1 2 := by
  have h₀ : Ioi (0:PairIndex) = {1,2} := by decide
  have h₁ : Ioi (1:PairIndex) = {2} := by decide
  have h₂ : Ioi (2:PairIndex) = ∅ := by decide
  simp [edges,Fin.sum_univ_three,h₀,h₁,h₂]

def frontCoeff (K : ℝ) (d : Vertex → ℝ) (i j : PairIndex) := coeffKey K d (front i j)
def backCoeff (K : ℝ) (d : Vertex → ℝ) (i j : PairIndex) := coeffKey K d (back i j)

private theorem align_coeff (K : ℝ) (d : Vertex → ℝ) (f : PairIndex → Bool)
    (i j : PairIndex) (hij : i < j) :
    aligned f (frontCoeff K d) (backCoeff K d) i j =
    HardyTripleGap.coefficient K (d (labels f i)) (d (labels f j)) := by
  have he := congrArg (coeffKey K d) (eight_orientations f i j hij)
  rw [coeff_key] at he
  by_cases hf : f i = f j
  · simpa only [aligned,ite_eq_left hf,frontCoeff] using he
  · simpa only [aligned,ite_eq_right hf,backCoeff] using he

private theorem difference_copositive {K : ℝ} (d : Vertex → ℝ) (hd : ∀ i, 0<d i)
    (hm : MatchingBound K d) (f : PairIndex → Bool)
    (a : PairIndex → ℝ) (ha : ∀ i, 0≤a i) :
    0 ≤ K*(∑ i, a i^2) + edges
        (fun i j => aligned f (frontCoeff K d) (backCoeff K d) i j*a i*a j) := by
  obtain ⟨hk,hpair⟩ := matching_costs hm
  have h := triple_gap (fun i => d (labels f i)) a (fun i => hd _) ha hk (fun i j => hpair _ _)
  rw [Fin.sum_univ_three,edges_three,align_coeff K d f 0 1 (by decide),
    align_coeff K d f 0 2 (by decide),align_coeff K d f 1 2 (by decide)]
  linarith only [h]

private theorem positive_pair_coeff {K x y u v : ℝ}
    (hx : 0<x) (hy : 0<y) (hu : 0<u) (hv : 0<v) (h : edge x y + edge u v ≤ K) :
    0≤ HardyTripleGap.coefficient K x y + HardyTripleGap.coefficient K u v := by
  have hcomp := opposite_coefficients_nonneg (sq_nonneg ((x*y^5-y*x^5)/(x^5+y^5)))
    (sq_nonneg ((u*v^5-v*u^5)/(u^5+v^5))) h
    (show 0 < x^5/y^5 by positivity) (show 0 < u^5/v^5 by positivity)
  simpa only [HardyGapBalance.coefficient,HardyTripleGap.coefficient,edge,inv_div] using hcomp

private theorem adjacent_nonneg {K : ℝ} (d : Vertex → ℝ) (hd : ∀ i, 0<d i)
    (hm : MatchingBound K d) (f : PairIndex → Bool)
    (i j : PairIndex) (hij : i<j) :
    0 ≤ aligned f (frontCoeff K d) (backCoeff K d) i j +
      aligned f (backCoeff K d) (frontCoeff K d) i j := by
  obtain ⟨h01,h02,h03⟩ := hm
  have hcost : edge (d (front i j).1) (d (front i j).2) +
      edge (d (back i j).1) (d (back i j).2) ≤ K := by
    fin_cases i <;> fin_cases j <;>
      first
      | exact absurd hij (by decide)
      | exact (add_comm _ _).le.trans h01
      | exact (add_comm _ _).le.trans h02
      | exact (add_comm _ _).le.trans h03
  have hc := positive_pair_coeff (hd _) (hd _) (hd _) (hd _) hcost
  by_cases hf : f i = f j
  · simpa only [aligned,ite_eq_left hf,frontCoeff,backCoeff,coeffKey] using hc
  · simp only [aligned,ite_eq_right hf,frontCoeff,backCoeff,coeffKey]
    rwa [add_comm]

/-- The raw six midpoint minor weights are grouped as (01,02,03) and their
opposites (23,13,12). Each group's entries can vanish. -/
def rawGap (K : ℝ) (d : Vertex → ℝ) (dis u v : PairIndex → ℝ) : ℝ :=
  gap K dis (frontCoeff K d) (backCoeff K d) u v

/-- Explicit coefficient table of the six-coordinate quadratic, with the
complementary ordering above. Here Cij is the physical cost coefficient for
the two labels that differ between the indicated minor pair. -/
theorem rawGap_explicit (K : ℝ) (d : Vertex → ℝ) (dis u v : PairIndex → ℝ) :
    let C := fun i j => HardyTripleGap.coefficient K (d i) (d j)
    let diag := fun i => K*(u i^2+v i^2)+dis i*(u i*v i)
    rawGap K d dis u v = diag 0 + diag 1 + diag 2 +
      ((C 1 2*(u 0*u 1+v 0*v 1) + C 0 3*(u 0*v 1+v 0*u 1)) +
       (C 1 3*(u 0*u 2+v 0*v 2) + C 0 2*(u 0*v 2+v 0*u 2)) +
       (C 2 3*(u 1*u 2+v 1*v 2) + C 0 1*(u 1*v 2+v 1*u 2))) := by
  rw [rawGap,gap,Fin.sum_univ_three,edges_three]
  rfl

/-- Balancing each minor with its opposite cannot increase the physical gap.
The three disjoint-matching inequalities are the only cost assumptions. -/
theorem raw_balanced_le {K : ℝ} (d : Vertex → ℝ) (hd : ∀ i, 0<d i)
    (hm : MatchingBound K d) (dis u v : PairIndex → ℝ) (hu : ∀ i, 0≤u i)
    (hv : ∀ i, 0≤v i) :
    rawGap K d dis (balanced u v) (balanced u v) ≤ rawGap K d dis u v := by
  let f (i : PairIndex) : Bool := decide (u i < v i)
  let h := swapSide f u v
  let l := swapSide f v u
  have hp (i : PairIndex) : 0 ≤ h i ∧ 0 ≤ l i ∧ l i ≤ h i := by
    by_cases hx : u i < v i
    · simpa [h,l,swapSide,f,hx] using And.intro (hv i) (And.intro (hu i) hx.le)
    · simpa [h,l,swapSide,f,hx] using And.intro (hu i) (And.intro (hv i) (le_of_not_gt hx))
  have he : balanced h l = balanced u v := by
    funext i
    cases hi : f i <;> simp [balanced,h,l,swapSide,hi,mul_comm]
  have hsame (g : PairIndex → ℝ) : swapSide f g g = g := by funext i; simp [swapSide]
  have result := balanced_le K dis (aligned f (frontCoeff K d) (backCoeff K d))
    (aligned f (backCoeff K d) (frontCoeff K d)) h l (fun i => (hp i).1) (fun i => (hp i).2.1)
    (adjacent_nonneg d hd hm f) (difference_copositive d hd hm f
      (fun i => h i-l i) (fun i => sub_nonneg.mpr (hp i).2.2))
  rw [he] at result
  have hbase := orient_gap K dis (frontCoeff K d) (backCoeff K d) f (balanced u v) (balanced u v)
  rw [hsame] at hbase
  rw [hbase] at result
  exact result.trans_eq (orient_gap K dis (frontCoeff K d) (backCoeff K d) f u v)

theorem matchingBound_max (d : Vertex → ℝ) : MatchingBound (matchingMax d) d :=
  ⟨le_max_left _ _,(le_max_left _ _).trans (le_max_right _ _),
    (le_max_right _ _).trans (le_max_right _ _)⟩

theorem raw_balanced_le_matchingMax (d : Vertex → ℝ) (hd : ∀ i, 0<d i)
    (dis u v : PairIndex → ℝ) (hu : ∀ i, 0≤u i) (hv : ∀ i, 0≤v i) :
    rawGap (matchingMax d) d dis (balanced u v) (balanced u v) ≤
      rawGap (matchingMax d) d dis u v :=
  raw_balanced_le d hd (matchingBound_max d) dis u v hu hv

/-- The sharp scalar inequality pays for each disjoint pair by its Schmidt
weight, so the normalized disjoint-pairing score is at most the plastic value. -/
theorem matchingMax_le_plastic {ρ : ℝ} (hρ : ρ^3=ρ+1)
    (d : Vertex → ℝ) (hd : ∀ i, 0<d i) :
    matchingMax d ≤ ((8*ρ^2+ρ-11)/25)*(∑ i, d i^2) := by
  let p := (8*ρ^2+ρ-11)/25
  have h (i j : Vertex) : edge (d i) (d j) ≤ p*(d i^2+d j^2) :=
    HardyPairBound.pair_bound hρ (hd i) (hd j)
  change matchingMax d ≤ p*_
  rw [matchingMax,Fin.sum_univ_four]
  refine max_le ?_ (max_le ?_ ?_)
  · nlinarith only [h 0 1,h 2 3]
  · nlinarith only [h 0 2,h 1 3]
  · nlinarith only [h 0 3,h 1 2]

end HardyFourPairing

#print axioms HardyFourPairing.raw_balanced_le

#print axioms HardyFourPairing.matchingMax_le_plastic
