module

public import HardyExtension.Definitions
public import HardyFourPairing

@[expose] public section
/-! A polynomial certificate on the Plücker triangle of balanced midpoint
minors. Denominators are cleared before checking the degree-two identity. -/
noncomputable section
namespace HardyBalancedPolynomial
open HardyTripleGap HardyFourPairing

/-- Two oriented scalar edges. Entries n/s and m/t are the signed roots. -/
structure Roots where
  n : ℝ
  s : ℝ
  m : ℝ
  t : ℝ

def Roots.lead (r : Roots) := r.s*r.t
def Roots.weightedSum (r : Roots) := r.n*r.t+r.m*r.s
def Roots.productNum (r : Roots) := r.n*r.m
def Roots.energy (r : Roots) := (r.n*r.t)^2+(r.m*r.s)^2
def Roots.score (r : Roots) := (r.n/r.s)^2+(r.m/r.t)^2
def mixed (r s : Roots) := r.weightedSum*s.weightedSum-r.lead*s.productNum-s.lead*r.productNum

theorem vertex_nonneg {K : ℝ} (r : Roots) (hs : 0<r.s) (ht : 0<r.t) (hk : r.score≤K) :
    0≤K*r.lead^2-r.energy := by
  have he : r.score*r.lead^2 = r.energy := by
    unfold Roots.score Roots.lead Roots.energy
    field_simp
  rw [←he, ←sub_mul]
  exact mul_nonneg (sub_nonneg.mpr hk) (sq_nonneg _)

theorem mixed_nonneg {K : ℝ} (r s : Roots) (hr : 0<r.lead) (hs : 0<s.lead)
    (h₁ : 0≤K*r.lead^2-r.energy) (h₂ : 0≤K*s.lead^2-s.energy) :
    0≤K*r.lead*s.lead-mixed r s := by
  have ident : (K*r.lead*s.lead-mixed r s)*(2*r.lead*s.lead) =
      (K*r.lead^2-r.energy)*s.lead^2+(K*s.lead^2-s.energy)*r.lead^2+
      (r.weightedSum*s.lead-s.weightedSum*r.lead)^2 := by
    unfold mixed Roots.weightedSum Roots.lead Roots.productNum Roots.energy
    ring
  have h := add_nonneg (add_nonneg (mul_nonneg h₁ (sq_nonneg s.lead))
    (mul_nonneg h₂ (sq_nonneg r.lead))) (sq_nonneg (r.weightedSum*s.lead-s.weightedSum*r.lead))
  rw [←ident] at h
  exact nonneg_of_mul_nonneg_left h (by positivity)

def oriented (d t : Four) (i j k l : Fin 4) : Roots where
  n := d i*t j-d j*t i
  s := t i+t j
  m := d k*t l-d l*t k
  t := t k+t l

def volume (t : Four) := t 0*t 1*t 2*t 3

/-- q times the common product of all four metric entries, in order
01,02,03,23,13,12. Unlike normalized minors these have no divisors. -/
def sumRows (t : Four) (m : Six) (f : Fin 4 → Fin 4 → ℝ) :=
  m 0*t 2*t 3*f 0 1 + m 1*t 1*t 3*f 0 2 + m 2*t 1*t 2*f 0 3 +
  m 3*t 0*t 1*f 2 3 + m 4*t 0*t 2*f 1 3 + m 5*t 0*t 3*f 1 2

def clearedN (d t : Four) (m : Six) :=
  let row := sumRows t m
  row (fun i j => d i^2+d j^2) * row (fun i j => (t i*t j)^2) -
  row (fun i j => d i*t i+d j*t j) *
    row (fun i j => t i^2*d j*t j+t j^2*d i*t i) +
  row (fun i j => d i*t i*d j*t j)*row (fun i j => t i^2+t j^2)

def clearedB (t : Four) (m : Six) :=
  sumRows t m (fun _ _ => 1)*sumRows t m (fun i j => (t i*t j)^2)

def triangleMinors (x y z : ℝ) : Six := ![y+z,x+z,x+y,y+z,x+z,x+y]

/-- All six coefficients of the balanced score polynomial. Different pairs
of matchings use a common orientation across their respective bipartition. -/
theorem balanced_polynomial (K : ℝ) (d t : Four) (x y z : ℝ) :
    let a := oriented d t 0 1 3 2
    let b := oriented d t 0 2 3 1
    let a' := oriented d t 0 1 2 3
    let c := oriented d t 0 3 2 1
    let b' := oriented d t 0 2 1 3
    let c' := oriented d t 0 3 1 2
    K*clearedB t (triangleMinors x y z)-clearedN d t (triangleMinors x y z) =
    volume t*(x^2*(K*a.lead^2-a.energy) + y^2*(K*b.lead^2-b.energy) +
      z^2*(K*c.lead^2-c.energy) + 2*x*y*(K*a.lead*b.lead-mixed a b) +
      2*x*z*(K*a'.lead*c.lead-mixed a' c) + 2*y*z*(K*b'.lead*c'.lead-mixed b' c')) := by
  dsimp [clearedN,clearedB,sumRows,triangleMinors,volume,oriented,mixed,
    Roots.lead,Roots.energy,Roots.productNum,Roots.weightedSum]
  ring

private theorem edge_swap (a b : ℝ) : edge a b = edge b a := by
  unfold edge
  rw [add_comm (a^5) (b^5), div_pow, div_pow]
  ring

/-- Positivity on the full Plücker triangle, even when all its inequalities
are strict. Only the three disjoint pairing inequalities are required. -/
theorem balanced_nonneg {K : ℝ} (d : Four) (hd : ∀ i, 0<d i)
    (hk : MatchingBound K d) (x y z : ℝ) (hx : 0≤x) (hy : 0≤y) (hz : 0≤z) :
    let t := fun i => d i^5
    0 ≤ K*clearedB t (triangleMinors x y z)-clearedN d t (triangleMinors x y z) := by
  let t : Four := fun i => d i^5
  have dt (i : Fin 4) : 0<t i := pow_pos (hd i) _
  have vol : 0<volume t := by unfold volume; positivity [dt 0,dt 1,dt 2,dt 3]
  obtain ⟨hA,hB,hC⟩ := hk
  let r := oriented d t
  have pos (i j k l : Fin 4) : 0 < (r i j k l).lead := mul_pos
    (add_pos (dt i) (dt j)) (add_pos (dt k) (dt l))
  have v (i j k l : Fin 4) (h : edge (d i) (d j)+edge (d k) (d l)≤K) :
      0≤K*(r i j k l).lead^2-(r i j k l).energy :=
    vertex_nonneg _ (add_pos (dt i) (dt j)) (add_pos (dt k) (dt l)) h
  have va := v 0 1 3 2 (by rwa [edge_swap (d 3) (d 2)])
  have vb := v 0 2 3 1 (by rwa [edge_swap (d 3) (d 1)])
  have va' := v 0 1 2 3 hA
  have vc := v 0 3 2 1 (by rwa [edge_swap (d 2) (d 1)])
  have vb' := v 0 2 1 3 hB
  have vc' := v 0 3 1 2 hC
  have ab := mixed_nonneg _ _ (pos 0 1 3 2) (pos 0 2 3 1) va vb
  have ac := mixed_nonneg _ _ (pos 0 1 2 3) (pos 0 3 2 1) va' vc
  have bc := mixed_nonneg _ _ (pos 0 2 1 3) (pos 0 3 1 2) vb' vc'
  change 0≤K*clearedB t _-clearedN d t _
  rw [balanced_polynomial]
  apply mul_nonneg vol.le
  exact add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg
    (mul_nonneg (sq_nonneg x) va) (mul_nonneg (sq_nonneg y) vb))
    (mul_nonneg (sq_nonneg z) vc)) (mul_nonneg (by positivity) ab))
    (mul_nonneg (by positivity) ac)) (mul_nonneg (by positivity) bc)

end HardyBalancedPolynomial

#print axioms HardyBalancedPolynomial.balanced_polynomial
#print axioms HardyBalancedPolynomial.balanced_nonneg
