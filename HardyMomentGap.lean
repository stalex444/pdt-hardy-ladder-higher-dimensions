module

public import HardyExtension.Definitions
public import HardyFourPairing

@[expose] public section
/-! Moment expansion for the Hardy two-plane objective on four Schmidt levels.
All six minor weights are midpoint squared minors, ordered 01,02,03,23,13,12. -/
noncomputable section
open Finset HardyFourPairing HardyTripleGap
namespace HardyMomentGap

def directed (K : ℝ) (a b : Row) : ℝ :=
  K*a.lower*b.upper - a.T2*b.J10 + a.T6*b.C - a.J6*b.T10

def polar (K : ℝ) (a b : Row) : ℝ := directed K a b + directed K b a

private theorem row_swap (x y : ℝ) : row x y = row y x := by
  simp [row,mul_comm x y,add_comm]

/-- A single nonzero minor contributes K times its square to the gap. -/
theorem diagonal_coefficient (K : ℝ) {x y : ℝ} (hx : 0<x) (hy : 0<y) :
    directed K (row x y) (row x y) = K := by
  simp only [directed,row]
  field_simp
  ring

/-- A common vertex cancels completely from the adjacent-minor coefficient. -/
theorem adjacent_coefficient (K : ℝ) {z x y : ℝ} (hz : 0<z) (hx : 0<x) (hy : 0<y) :
    polar K (row z x) (row z y) = HardyTripleGap.coefficient K x y := by
  rw [HardyTripleGap.coefficient_eq hx hy]
  simp only [polar,directed,row]
  field_simp
  ring

private theorem polar_swap (K : ℝ) (a b : Row) : polar K a b = polar K b a := add_comm _ _

/-- The three disjoint coefficients are determined by polarizing the actual
numerator and denominator. -/
def physicalDisjoint (K : ℝ) (d : Vertex → ℝ) : PairIndex → ℝ :=
  ![polar K (rows d 0) (rows d 3),polar K (rows d 1) (rows d 4),
    polar K (rows d 2) (rows d 5)]

def firstThree (m : Fin 6 → ℝ) : PairIndex → ℝ := ![m 0,m 1,m 2]
def oppositeThree (m : Fin 6 → ℝ) : PairIndex → ℝ := ![m 3,m 4,m 5]

private theorem product_expand (m : Fin 6 → ℝ) (R : Fin 6 → Row) (f g : Row → ℝ) :
    lin m R f * lin m R g = ∑ i, ∑ j, (m i*m j)*(f (R i)*g (R j)) := by
  simp only [lin]
  rw [sum_mul]
  apply sum_congr rfl
  intro i _
  rw [mul_sum]
  apply sum_congr rfl
  intro j _
  ring

private theorem gap_sum (K : ℝ) (d : Vertex → ℝ) (m : Fin 6 → ℝ) :
    K*momentB d m - momentN d m = ∑ i, ∑ j, m i*m j*directed K (rows d i) (rows d j) := by
  simp only [momentB,momentN,product_expand,mul_sum]
  simp_rw [←sum_sub_distrib,←sum_add_distrib]
  rw [←sum_sub_distrib]
  apply sum_congr rfl
  intro i _
  rw [←sum_sub_distrib]
  apply sum_congr rfl
  intro j _
  unfold directed; ring

/-- Homogeneous quadratic expansion into six diagonals and fifteen unordered
cross terms. This is independent of the moment formulas. -/
private theorem expand_six (K : ℝ) (R : Fin 6 → Row) (m : Fin 6 → ℝ) :
    (∑ i, ∑ j, m i*m j*directed K (R i) (R j)) =
      directed K (R 0) (R 0)*m 0^2 +
      directed K (R 1) (R 1)*m 1^2 +
      directed K (R 2) (R 2)*m 2^2 +
      directed K (R 3) (R 3)*m 3^2 +
      directed K (R 4) (R 4)*m 4^2 +
      directed K (R 5) (R 5)*m 5^2 +
      polar K (R 0) (R 1)*m 0*m 1 +
      polar K (R 0) (R 2)*m 0*m 2 +
      polar K (R 0) (R 3)*m 0*m 3 +
      polar K (R 0) (R 4)*m 0*m 4 +
      polar K (R 0) (R 5)*m 0*m 5 +
      polar K (R 1) (R 2)*m 1*m 2 +
      polar K (R 1) (R 3)*m 1*m 3 +
      polar K (R 1) (R 4)*m 1*m 4 +
      polar K (R 1) (R 5)*m 1*m 5 +
      polar K (R 2) (R 3)*m 2*m 3 +
      polar K (R 2) (R 4)*m 2*m 4 +
      polar K (R 2) (R 5)*m 2*m 5 +
      polar K (R 3) (R 4)*m 3*m 4 +
      polar K (R 3) (R 5)*m 3*m 5 +
      polar K (R 4) (R 5)*m 4*m 5 := by
  simp only [Fin.sum_univ_six,polar]
  ring

/-- The six-variable physical moment gap is exactly the quadratic used in the
balancing theorem. Minor weights may be arbitrary real numbers. -/
theorem moment_gap_eq_rawGap (K : ℝ) (d : Vertex → ℝ) (hd : ∀ i, 0<d i) (m : Fin 6 → ℝ) :
    K*momentB d m - momentN d m =
    rawGap K d (physicalDisjoint K d) (firstThree m) (oppositeThree m) := by
  have diag (i : Fin 6) : directed K (rows d i) (rows d i) = K := by
    fin_cases i <;> exact diagonal_coefficient K (hd _) (hd _)
  have h01 : polar K (rows d 0) (rows d 1) = HardyTripleGap.coefficient K (d 1) (d 2) := by
    change polar K (row (d 0) (d 1)) (row (d 0) (d 2)) = _
    exact adjacent_coefficient K (hd 0) (hd 1) (hd 2)
  have h02 : polar K (rows d 0) (rows d 2) = HardyTripleGap.coefficient K (d 1) (d 3) := by
    change polar K (row (d 0) (d 1)) (row (d 0) (d 3)) = _
    exact adjacent_coefficient K (hd 0) (hd 1) (hd 3)
  have h04 : polar K (rows d 0) (rows d 4) = HardyTripleGap.coefficient K (d 0) (d 3) := by
    change polar K (row (d 0) (d 1)) (row (d 1) (d 3)) = _
    rw [row_swap (d 0) (d 1)]
    exact adjacent_coefficient K (hd 1) (hd 0) (hd 3)
  have h05 : polar K (rows d 0) (rows d 5) = HardyTripleGap.coefficient K (d 0) (d 2) := by
    change polar K (row (d 0) (d 1)) (row (d 1) (d 2)) = _
    rw [row_swap (d 0) (d 1)]
    exact adjacent_coefficient K (hd 1) (hd 0) (hd 2)
  have h12 : polar K (rows d 1) (rows d 2) = HardyTripleGap.coefficient K (d 2) (d 3) := by
    change polar K (row (d 0) (d 2)) (row (d 0) (d 3)) = _
    exact adjacent_coefficient K (hd 0) (hd 2) (hd 3)
  have h13 : polar K (rows d 1) (rows d 3) = HardyTripleGap.coefficient K (d 0) (d 3) := by
    change polar K (row (d 0) (d 2)) (row (d 2) (d 3)) = _
    rw [row_swap (d 0) (d 2)]
    exact adjacent_coefficient K (hd 2) (hd 0) (hd 3)
  have h15 : polar K (rows d 1) (rows d 5) = HardyTripleGap.coefficient K (d 0) (d 1) := by
    change polar K (row (d 0) (d 2)) (row (d 1) (d 2)) = _
    rw [row_swap (d 0) (d 2)]
    rw [row_swap (d 1) (d 2)]
    exact adjacent_coefficient K (hd 2) (hd 0) (hd 1)
  have h23 : polar K (rows d 2) (rows d 3) = HardyTripleGap.coefficient K (d 0) (d 2) := by
    change polar K (row (d 0) (d 3)) (row (d 2) (d 3)) = _
    rw [row_swap (d 0) (d 3)]
    rw [row_swap (d 2) (d 3)]
    exact adjacent_coefficient K (hd 3) (hd 0) (hd 2)
  have h24 : polar K (rows d 2) (rows d 4) = HardyTripleGap.coefficient K (d 0) (d 1) := by
    change polar K (row (d 0) (d 3)) (row (d 1) (d 3)) = _
    rw [row_swap (d 0) (d 3)]
    rw [row_swap (d 1) (d 3)]
    exact adjacent_coefficient K (hd 3) (hd 0) (hd 1)
  have h34 : polar K (rows d 3) (rows d 4) = HardyTripleGap.coefficient K (d 1) (d 2) := by
    change polar K (row (d 2) (d 3)) (row (d 1) (d 3)) = _
    rw [row_swap (d 2) (d 3)]
    rw [row_swap (d 1) (d 3)]
    rw [polar_swap]
    exact adjacent_coefficient K (hd 3) (hd 1) (hd 2)
  have h35 : polar K (rows d 3) (rows d 5) = HardyTripleGap.coefficient K (d 1) (d 3) := by
    change polar K (row (d 2) (d 3)) (row (d 1) (d 2)) = _
    rw [row_swap (d 1) (d 2)]
    rw [polar_swap]
    exact adjacent_coefficient K (hd 2) (hd 1) (hd 3)
  have h45 : polar K (rows d 4) (rows d 5) = HardyTripleGap.coefficient K (d 2) (d 3) := by
    change polar K (row (d 1) (d 3)) (row (d 1) (d 2)) = _
    rw [polar_swap]
    exact adjacent_coefficient K (hd 1) (hd 2) (hd 3)
  rw [gap_sum,expand_six,rawGap_explicit]
  simp only [diag,h01,h02,h04,h05,h12,h13,h15,h23,h24,h34,h35,h45]
  change _ =
    (K*(m 0^2+m 3^2) + polar K (rows d 0) (rows d 3)*(m 0*m 3)) +
    (K*(m 1^2+m 4^2) + polar K (rows d 1) (rows d 4)*(m 1*m 4)) +
    (K*(m 2^2+m 5^2) + polar K (rows d 2) (rows d 5)*(m 2*m 5)) +
    ((HardyTripleGap.coefficient K (d 1) (d 2)*(m 0*m 1+m 3*m 4) +
      HardyTripleGap.coefficient K (d 0) (d 3)*(m 0*m 4+m 3*m 1)) +
     (HardyTripleGap.coefficient K (d 1) (d 3)*(m 0*m 2+m 3*m 5) +
      HardyTripleGap.coefficient K (d 0) (d 2)*(m 0*m 5+m 3*m 2)) +
     (HardyTripleGap.coefficient K (d 2) (d 3)*(m 1*m 2+m 4*m 5) +
      HardyTripleGap.coefficient K (d 0) (d 1)*(m 1*m 5+m 4*m 2)))
  ring

/-- Package the first three minors and their opposite partners. -/
def pack (u v : PairIndex → ℝ) : Fin 6 → ℝ := ![u 0,u 1,u 2,v 0,v 1,v 2]

theorem firstThree_pack (u v : PairIndex → ℝ) : firstThree (pack u v) = u := by
  funext i
  fin_cases i <;> rfl

theorem oppositeThree_pack (u v : PairIndex → ℝ) : oppositeThree (pack u v) = v := by
  funext i
  fin_cases i <;> rfl

def balancedSix (m : Fin 6 → ℝ) : Fin 6 → ℝ :=
  let g := HardyGapBalance.balanced (firstThree m) (oppositeThree m)
  pack g g

/-- Balancing all three opposing minor pairs decreases the denominator-cleared
physical gap for every nonnegative array, including arrays with zero entries. -/
theorem moment_gap_balanced_le {K : ℝ} (d : Vertex → ℝ) (hd : ∀ i, 0<d i)
    (hm : MatchingBound K d) (m : Fin 6 → ℝ) (hn : ∀ i, 0 ≤ m i) :
    K*momentB d (balancedSix m) - momentN d (balancedSix m) ≤
    K*momentB d m - momentN d m := by
  rw [moment_gap_eq_rawGap K d hd,moment_gap_eq_rawGap K d hd]
  simp only [balancedSix,firstThree_pack,oppositeThree_pack]
  apply raw_balanced_le d hd hm
  · intro i
    fin_cases i <;> exact hn _
  · intro i
    fin_cases i <;> exact hn _

/-- The actual denominator is positive as soon as one nonnegative midpoint
minor weight is positive. No individual minor needs to be inverted. -/
theorem momentB_pos (d : Vertex → ℝ) (hd : ∀ i, 0<d i) (m : Fin 6 → ℝ)
    (hm : ∀ i, 0 ≤ m i) (hn : m ≠ 0) : 0 < momentB d m := by
  have hrow (x y : ℝ) (hx : 0<x) (hy : 0<y) : 0 < (row x y).lower ∧ 0 < (row x y).upper :=
    ⟨div_pos zero_lt_one (pow_pos (mul_pos hx hy) _),pow_pos (mul_pos hx hy) _⟩
  have hs (i : Fin 6) : 0 < (rows d i).lower ∧ 0 < (rows d i).upper := by
    fin_cases i <;> exact hrow _ _ (hd _) (hd _)
  obtain ⟨i,hi⟩ : ∃ i, 0 < m i := by
    by_contra! h
    exact hn (funext fun i => le_antisymm (h i) (hm i))
  have hlin (f : Row → ℝ) (hf : ∀ j, 0<f (rows d j)) : 0 < lin m (rows d) f := by
    exact (mul_pos hi (hf i)).trans_le (single_le_sum
      (fun j _ => mul_nonneg (hm j) (hf j).le) (mem_univ i))
  exact mul_pos (hlin _ (fun j => (hs j).1)) (hlin _ (fun j => (hs j).2))

/-- A balanced physical gap certificate gives the original unbalanced moment
ratio bound on every nonzero nonnegative minor array. -/
theorem ratio_le_of_balanced_gap {K : ℝ} (d : Vertex → ℝ) (hd : ∀ i, 0<d i)
    (hk : MatchingBound K d) (m : Fin 6 → ℝ) (hm : ∀ i, 0 ≤ m i) (hn : m ≠ 0)
    (hb : 0 ≤ K*momentB d (balancedSix m)-momentN d (balancedSix m)) :
    momentN d m / momentB d m ≤ K := by
  apply (div_le_iff₀ (momentB_pos d hd m hm hn)).mpr
  exact sub_nonneg.mp (hb.trans (moment_gap_balanced_le d hd hk m hm))

end HardyMomentGap

#print axioms HardyMomentGap.moment_gap_eq_rawGap

#print axioms HardyMomentGap.ratio_le_of_balanced_gap
