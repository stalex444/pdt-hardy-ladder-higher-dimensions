module

public import Mathlib

@[expose] public section
noncomputable section
open Finset

namespace HardyTripleGap

def edge (x y : ℝ) : ℝ := ((x*y^5-y*x^5)/(x^5+y^5))^2

end HardyTripleGap
namespace HardyFourPairing

abbrev Vertex := Fin 4
open HardyTripleGap
def matchingMax (d : Vertex → ℝ) : ℝ :=
  max (edge (d 0) (d 1) + edge (d 2) (d 3))
    (max (edge (d 0) (d 2) + edge (d 1) (d 3))
         (edge (d 0) (d 3) + edge (d 1) (d 2)))

end HardyFourPairing
namespace HardyBalancedPolynomial

abbrev Four := Fin 4 → ℝ

abbrev Six := Fin 6 → ℝ

end HardyBalancedPolynomial
namespace HardyMomentGap

open HardyFourPairing
structure Row where
  lower : ℝ
  upper : ℝ
  T2 : ℝ
  J10 : ℝ
  T6 : ℝ
  C : ℝ
  J6 : ℝ
  T10 : ℝ

def row (x y : ℝ) : Row where
  lower := 1/(x*y)^5
  upper := (x*y)^5
  T2 := (x^2+y^2)/(x*y)^5
  J10 := (x*y)^10/(x*y)^5
  T6 := (x^6+y^6)/(x*y)^5
  C := (x^10*y^6+y^10*x^6)/(x*y)^5
  J6 := (x*y)^6/(x*y)^5
  T10 := (x^10+y^10)/(x*y)^5

def rows (d : Vertex → ℝ) : Fin 6 → Row :=
  ![row (d 0) (d 1),row (d 0) (d 2),row (d 0) (d 3),
    row (d 2) (d 3),row (d 1) (d 3),row (d 1) (d 2)]

def lin (m : Fin 6 → ℝ) (R : Fin 6 → Row) (p : Row → ℝ) := ∑ i, m i*p (R i)

def momentB (d : Vertex → ℝ) (m : Fin 6 → ℝ) :=
  lin m (rows d) Row.lower * lin m (rows d) Row.upper

def momentN (d : Vertex → ℝ) (m : Fin 6 → ℝ) :=
  lin m (rows d) Row.T2 * lin m (rows d) Row.J10 -
  lin m (rows d) Row.T6 * lin m (rows d) Row.C +
  lin m (rows d) Row.J6 * lin m (rows d) Row.T10

end HardyMomentGap
namespace HardyFourSharp

open HardyBalancedPolynomial HardyFourPairing
def squareMinors (w : Fin 6 → ℂ) : Six := fun i => ‖w i‖^2

def frameMinors (x y : Vertex → ℂ) : Fin 6 → ℂ :=
  let det := fun i j => x i*y j-x j*y i
  ![det 0 1,det 0 2,det 0 3,det 2 3,det 1 3,det 1 2]

end HardyFourSharp
namespace HardyFourEquality

open HardyFourPairing
def plasticValue (ρ : ℝ) := (8*ρ^2+ρ-11)/25

def PlasticPair (ρ x y : ℝ) : Prop := min x y / max x y = ρ⁻¹^2

def PlasticPairing (ρ : ℝ) (d : Vertex → ℝ) : Prop :=
  (PlasticPair ρ (d 0) (d 1) ∧ PlasticPair ρ (d 2) (d 3)) ∨
  (PlasticPair ρ (d 0) (d 2) ∧ PlasticPair ρ (d 1) (d 3)) ∨
  (PlasticPair ρ (d 0) (d 3) ∧ PlasticPair ρ (d 1) (d 2))

end HardyFourEquality
namespace HardyRankOne

variable {ι : Type*} [Fintype ι]
def weighted (d : ι → ℝ) (k : ℕ) (u : EuclideanSpace ℂ ι) : EuclideanSpace ℂ ι :=
  WithLp.toLp 2 fun i => (d i ^ k : ℝ) * u i

def score (d : ι → ℝ) (u : EuclideanSpace ℂ ι) : ℝ :=
  let K := Submodule.span ℂ {weighted d 5 u}
  ‖weighted d 1 u - K.starProjection (weighted d 1 u)‖ ^ 2

end HardyRankOne
namespace HardyEffects

abbrev Space (ι : Type*) := EuclideanSpace ℂ ι

structure Effect (ι : Type*) [Fintype ι] where
  basis : OrthonormalBasis ι ℂ (Space ι)
  weight : ι → ℝ
  nonneg : ∀ i, 0 ≤ weight i
  le_one : ∀ i, weight i ≤ 1
variable {ι : Type*} [Fintype ι]
open scoped Classical
open HardyRankOne (weighted)
def Effect.complement (A : Effect ι) : Effect ι where
  basis := A.basis
  weight i := 1-A.weight i
  nonneg i := sub_nonneg.mpr (A.le_one i)
  le_one i := by linarith [A.nonneg i]

def entry (d : ι → ℝ) (A B : Effect ι) (i j : ι) : ℝ :=
  ‖inner ℂ (weighted d 1 (A.basis i)) (B.basis j)‖^2

def event (d : ι → ℝ) (A B : Effect ι) : ℝ :=
  ∑ i, ∑ j, (A.weight i * B.weight j) * entry d A B i j

end HardyEffects
namespace HardyComplex

abbrev Vec := Fin 2 → ℂ

def UnitRay (v : Vec) : Prop := ‖v 0‖ ^ 2 + ‖v 1‖ ^ 2 = 1

noncomputable def perp (v : Vec) : Vec := ![-star (v 1), star (v 0)]

noncomputable def amp (c d : ℝ) (v w : Vec) : ℂ :=
  (c : ℂ) * v 0 * w 0 + (d : ℂ) * v 1 * w 1

end HardyComplex
namespace HardyDirectSum

open HardyComplex
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
def schmidt (w : ι → ℝ) (c d : ℝ) (p : ι × Fin 2) : ℝ :=
  Real.sqrt (w p.1) * (![c, d] : Fin 2 → ℝ) p.2

def embedded (i : ι) (v : Vec) (p : ι × Fin 2) : ℂ :=
  if p.1 = i then v p.2 else 0

def event (s : ι × Fin 2 → ℝ) (v z : Vec) : ℝ :=
  ∑ i : ι, ∑ j : ι, ‖∑ p : ι × Fin 2, (s p : ℂ) * embedded i v p * embedded j z p‖ ^ 2

structure Lifted (s : ι × Fin 2 → ℝ) (a b : ℕ → Vec) (success : ℝ) : Prop where
  unitA : ∀ k, UnitRay (a k)
  unitB : ∀ k, UnitRay (b k)
  base : event s (a 0) (b 0) = 0
  stepA : ∀ k < 2, event s (a (k+1)) (perp (b k)) = 0
  stepB : ∀ k < 2, event s (perp (a k)) (b (k+1)) = 0
  terminal : event s (a 2) (b 2) = success

def numerator : Fin 6 → ℕ := ![1, 2, 3, 5, 7, 11]

def weights (i : Fin 6) : ℝ := numerator i / 29

end HardyDirectSum
namespace HardyMixtures

open HardyEffects
structure Component where
  rank : ℕ
  d : Fin rank → ℝ
  positive : ∀ i, 0 < d i
  normalized : ∑ i, d i ^ 2 = 1
  alice : Fin 3 → Effect (Fin rank)
  bob : Fin 3 → Effect (Fin rank)
inductive Forbidden where
  | base
  | left (step : Fin 2)
  | right (step : Fin 2)
def Component.forbidden (c : Component) : Forbidden → ℝ
  | .base => event c.d (c.alice 0) (c.bob 0)
  | .left k => event c.d (c.alice k.succ) (c.bob k.castSucc).complement
  | .right k => event c.d (c.alice k.castSucc).complement (c.bob k.succ)

def Component.success (c : Component) : ℝ := event c.d (c.alice 2) (c.bob 2)
variable {ι : Type*} [Fintype ι]
def average (w f : ι → ℝ) : ℝ := ∑ i, w i * f i

end HardyMixtures
namespace HardyFixedState

open HardyEffects

/-- Attainable terminal Born scores with three binary settings on each side.
For a normalized spectrum these scores are probabilities. -/
def successSet (d : Fin 4 → ℝ) : Set ℝ :=
  {p | ∃ A B : Fin 3 → Effect (Fin 4),
    event d (A 0) (B 0) = 0 ∧
    (∀ i : Fin 2, event d (A i.succ) (B i.castSucc).complement = 0) ∧
    (∀ i : Fin 2, event d (A i.castSucc).complement (B i.succ) = 0) ∧
    event d (A 2) (B 2) = p}

end HardyFixedState

namespace HardyExtension
open HardyFourPairing HardyMomentGap HardyFourSharp HardyFourEquality
open HardyRankOne HardyEffects HardyComplex HardyDirectSum HardyMixtures

/-- Exact maximum over all rank-two complex frames. -/
theorem four_level_frame_maximum (d : Fin 4 → ℝ) (hd : ∀ i, 0 < d i) :
    IsGreatest {p : ℝ | ∃ x y : Fin 4 → ℂ, frameMinors x y ≠ 0 ∧
      (let m := squareMinors (frameMinors x y); momentN d m / momentB d m) = p}
      (matchingMax d) := by sorry

/-- Plastic ceiling for the best matching. -/
theorem four_level_ceiling {ρ : ℝ} (hρ : ρ^3 = ρ+1) (d : Fin 4 → ℝ) (hd : ∀ i, 0 < d i) :
    matchingMax d ≤ plasticValue ρ * (∑ i, d i^2) := by sorry

/-- Necessary and sufficient spectral pairing for equality. -/
theorem four_level_equality {ρ : ℝ} (hρ : ρ^3=ρ+1) (d : Vertex → ℝ) (hd : ∀ i, 0<d i) :
    matchingMax d = plasticValue ρ*(∑ i, d i^2) ↔ PlasticPairing ρ d := by sorry

/-- All binary effects through Schmidt rank three. -/
theorem three_level_effect_bound {ι : Type*} [Fintype ι] (hdim : Fintype.card ι ≤ 3) {ρ : ℝ} (hρ : ρ^3=ρ+1)
    {d : ι → ℝ} (hd : ∀ i, 0 < d i) (hs : ∑ i, d i^2=1) (A B : Fin 3 → Effect ι)
    (base : HardyEffects.event d (A 0) (B 0)=0)
    (left : ∀ i : Fin 2, HardyEffects.event d (A i.succ) (B i.castSucc).complement=0)
    (right : ∀ i : Fin 2, HardyEffects.event d (A i.castSucc).complement (B i.succ)=0) :
    HardyEffects.event d (A 2) (B 2) ≤ (8*ρ^2+ρ-11)/25 := by sorry

/-- Strict inequality at full Schmidt rank three. -/
theorem full_rank_three_strict {ρ : ℝ} (hρ : ρ^3=ρ+1) {d : Fin 3 → ℝ}
    (hd : ∀ i, 0 < d i) (hs : ∑ i, d i^2=1) (A B : Fin 3 → Effect (Fin 3))
    (base : HardyEffects.event d (A 0) (B 0)=0)
    (left : ∀ i : Fin 2, HardyEffects.event d (A i.succ) (B i.castSucc).complement=0)
    (right : ∀ i : Fin 2, HardyEffects.event d (A i.castSucc).complement (B i.succ)=0) :
    HardyEffects.event d (A 2) (B 2) < (8*ρ^2+ρ-11)/25 := by sorry

/-- Rank-one endpoint in any finite dimension. -/
theorem rank_one_endpoint {ι : Type*} [Fintype ι] {ρ : ℝ} (hρ : ρ^3=ρ+1) {d : ι → ℝ}
    (hd : ∀ i, 0 ≤ d i) (hs : ∑ i, d i^2=1)
    {u : EuclideanSpace ℂ ι} (hu : ‖u‖=1) : score d u ≤ (8*ρ^2+ρ-11)/25 := by sorry

/-- Codimension-one endpoint in any finite dimension. -/
theorem codimension_one_endpoint {ι : Type*} [Fintype ι] {κ : Type*} [Fintype κ] {ρ : ℝ} (hρ : ρ^3=ρ+1)
    {d : ι → ℝ} (hd : ∀ i, 0 ≤ d i) (hs : ∑ i, d i^2=1)
    {u : EuclideanSpace ℂ ι} (hu : ‖u‖=1) (v : κ → EuclideanSpace ℂ ι)
    (hv : Orthonormal ℂ v) (hz : ∀ j, inner ℂ (weighted d 5 (v j)) u = 0) :
    ∑ j, ‖inner ℂ (weighted d 1 (v j)) u‖^2 ≤ (8*ρ^2+ρ-11)/25 := by sorry

/-- Preservation of all qubit joint probabilities under finite sector lifting. -/
theorem sector_outcome_probability {ι : Type*} [Fintype ι] [DecidableEq ι] (w : ι → ℝ) (hw : ∀ i, 0 ≤ w i) (hn : ∑ i, w i = 1)
    (c d : ℝ) (v z : Vec) :
    HardyDirectSum.event (schmidt w c d) v z = ‖amp c d v z‖ ^ 2 := by sorry

/-- Twelve distinct Schmidt weights attain the same success. -/
theorem twelve_level_attainment {ρ : ℝ} (hρ : ρ^3 = ρ+1) :
    ∃ (s : Fin 6 × Fin 2 → ℝ) (a b : ℕ → Vec),
      (∀ p, 0 < s p) ∧ (∑ p, s p ^ 2 = 1) ∧ Function.Injective (fun p => s p ^ 2) ∧
      (∀ i, s (i,0)^2 = weights i * ρ⁻¹ ∧ s (i,1)^2 = weights i * ρ⁻¹^5) ∧
      Lifted s a b ((8*ρ^2+ρ-11)/25) := by sorry

/-- Sharp matching upper bound for six arbitrary binary effects. -/
theorem four_level_measurement_bound {d : Fin 4 → ℝ} (hd : ∀ i, 0 < d i)
    (A B : Fin 3 → HardyEffects.Effect (Fin 4))
    (base : HardyEffects.event d (A 0) (B 0) = 0)
    (left : ∀ i : Fin 2, HardyEffects.event d (A i.succ) (B i.castSucc).complement = 0)
    (right : ∀ i : Fin 2, HardyEffects.event d (A i.castSucc).complement (B i.succ) = 0) :
    HardyEffects.event d (A 2) (B 2) ≤ matchingMax d := by sorry

/-- Plastic ceiling for finite ensembles through Schmidt rank four. -/
theorem four_level_mixture_bound {ι : Type*} [Fintype ι] {ρ : ℝ} (hρ : ρ^3=ρ+1)
    (w : ι → ℝ) (hw : ∀ i, 0 ≤ w i) (hn : ∑ i, w i = 1)
    (c : ι → Component) (hr : ∀ i, 0 < w i → (c i).rank ≤ 4)
    (hz : ∀ j, average w (fun i => (c i).forbidden j) = 0) :
    average w (fun i => (c i).success) ≤ HardyFourEquality.plasticValue ρ := by sorry

/-- Exact maximum for all six binary measurements at a fixed four-level spectrum. -/
theorem four_level_measurement_maximum (d : Fin 4 → ℝ) (hd : ∀ i, 0 < d i) :
    IsGreatest (HardyFixedState.successSet d) (matchingMax d) := by sorry

/-- Spectra admitting equality in the original six-measurement experiment. -/
theorem four_level_measurement_equality {ρ : ℝ} (hρ : ρ^3 = ρ+1) (d : Fin 4 → ℝ) (hd : ∀ i, 0 < d i) :
    plasticValue ρ * (∑ i, d i^2) ∈ HardyFixedState.successSet d ↔ PlasticPairing ρ d := by sorry

end HardyExtension
