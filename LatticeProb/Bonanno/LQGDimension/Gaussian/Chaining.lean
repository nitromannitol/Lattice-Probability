/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGDimension.Gaussian.Chaining at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGDimension.Gaussian.MaxInequality

/-!
# A periodic 4-adic tree majorant for the distance `√|s - t|`

This file contains the "chaining" input used for the finiteness of `a₁`: a Gaussian family
indexed by the real line whose canonical distance dominates `√|s - t|` at scales below `1`, and
whose expected supremum over *any* finite set is bounded by a universal constant.

The construction is a majorizing tree.  At level `j ≤ J` the real line is cut into cells of
length `4^{-j}`, identified modulo `2` (so there are `2·4^j` cells: `treeCell j t`).  The
vector of `t` has weight `2^{-j}` on the coordinate `(j, treeCell j t)` (`treeCoord`).

* `abs_sub_lt_of_treeCell_eq`: if `|s - t| < 1` and `s, t` share the cell at level `j`, then
  `|s - t| < 4^{-j}`.
* `abs_sub_le_two_mul_sum_sq_treeCoord`: if `4^{-J} ≤ |s - t| < 1`, then
  `|s - t| ≤ 2 ∑_i (treeCoord J s i - treeCoord J t i)²`.
* `sum_treeCoord_mul_inner_le`, `integral_treeMax_le`: for vectors `e i` of norm at most `1`
  in a Euclidean space with its standard Gaussian vector `x`,
  `∑_i treeCoord J t i ⟪e i, x⟫ ≤ treeMax J e x` for every `t`, and `E treeMax J e ≤ 12`,
  uniformly in `J`.  The proof uses the Gaussian maximal inequality at each level
  (`2·4^j` terms) and `∑_j 2^{-j} · 3 (j + 1) ≤ 12`.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Real
open scoped RealInnerProductSpace

namespace LQGDimension.Tree

/-- The index set of the periodic 4-adic tree of depth `J`: a level `j ≤ J` and one of the
`2·4^j` cells of that level. -/
abbrev TreeIdx (J : ℕ) : Type := Σ j : Fin (J + 1), Fin (2 * 4 ^ (j : ℕ))

/-- The cell of `t` at level `j`: `⌊4^j t⌋ mod 2·4^j`. -/
def treeCell (j : ℕ) (t : ℝ) : Fin (2 * 4 ^ j) :=
  ⟨(⌊t * 4 ^ j⌋ % ((2 * 4 ^ j : ℕ) : ℤ)).toNat, by
    have hpos : (0 : ℤ) < ((2 * 4 ^ j : ℕ) : ℤ) := by positivity
    have h1 := Int.emod_nonneg ⌊t * 4 ^ j⌋ hpos.ne'
    have h2 := Int.emod_lt_of_pos ⌊t * 4 ^ j⌋ hpos
    generalize ⌊t * 4 ^ j⌋ % ((2 * 4 ^ j : ℕ) : ℤ) = y at h1 h2 ⊢
    omega⟩

/-- Two points at distance `< 1` in the same cell of level `j` are at distance `< 4^{-j}`. -/
theorem abs_sub_lt_of_treeCell_eq {j : ℕ} {s t : ℝ} (hst : |s - t| < 1)
    (h : treeCell j s = treeCell j t) : |s - t| < 1 / 4 ^ j := by
  have hm : (0 : ℤ) < ((2 * 4 ^ j : ℕ) : ℤ) := by positivity
  set a := ⌊s * 4 ^ j⌋ with ha
  set b := ⌊t * 4 ^ j⌋ with hb
  have hmod : a % ((2 * 4 ^ j : ℕ) : ℤ) = b % ((2 * 4 ^ j : ℕ) : ℤ) := by
    have := congrArg Fin.val h
    simp only [treeCell] at this
    have h1 := Int.emod_nonneg a hm.ne'
    have h2 := Int.emod_nonneg b hm.ne'
    rw [← ha, ← hb] at this
    omega
  have hdvd : ((2 * 4 ^ j : ℕ) : ℤ) ∣ b - a := Int.ModEq.dvd hmod
  have h4 : (0 : ℝ) < 4 ^ j := by positivity
  have hsa := Int.floor_le (s * 4 ^ j)
  have hsa' := Int.lt_floor_add_one (s * 4 ^ j)
  have htb := Int.floor_le (t * 4 ^ j)
  have htb' := Int.lt_floor_add_one (t * 4 ^ j)
  rw [← ha] at hsa hsa'
  rw [← hb] at htb htb'
  have hdiff : |s * 4 ^ j - t * 4 ^ j| < 4 ^ j := by
    rw [← sub_mul, abs_mul, abs_of_pos h4]
    nlinarith
  rw [abs_lt] at hdiff
  have h1 : ((a - b : ℤ) : ℝ) < ((4 ^ j : ℕ) : ℝ) + 1 := by push_cast; linarith
  have h2 : ((b - a : ℤ) : ℝ) < ((4 ^ j : ℕ) : ℝ) + 1 := by push_cast; linarith
  have h1' : a - b < ((4 ^ j : ℕ) : ℤ) + 1 := by exact_mod_cast h1
  have h2' : b - a < ((4 ^ j : ℕ) : ℤ) + 1 := by exact_mod_cast h2
  have hpos : (1 : ℤ) ≤ ((4 ^ j : ℕ) : ℤ) := by
    have : 1 ≤ 4 ^ j := Nat.one_le_pow _ _ (by norm_num)
    exact_mod_cast this
  have hm' : ((2 * 4 ^ j : ℕ) : ℤ) = 2 * ((4 ^ j : ℕ) : ℤ) := by push_cast; ring
  have hab : |b - a| < ((2 * 4 ^ j : ℕ) : ℤ) := by
    rw [hm', abs_lt]
    constructor <;> omega
  have hba : b - a = 0 := Int.eq_zero_of_abs_lt_dvd hdvd hab
  have hab' : (a : ℝ) = b := by exact_mod_cast (by omega : a = b)
  rw [hab'] at hsa hsa'
  have : |s * 4 ^ j - t * 4 ^ j| < 1 := by
    rw [abs_lt]
    constructor <;> linarith
  rw [← sub_mul, abs_mul, abs_of_pos h4] at this
  rw [lt_div_iff₀ h4]
  linarith

/-- The coordinates of the tree vector of `t`: weight `2^{-j}` on `(j, treeCell j t)`. -/
def treeCoord (J : ℕ) (t : ℝ) (i : TreeIdx J) : ℝ :=
  if i.2 = treeCell i.1 t then (1 / 2 : ℝ) ^ (i.1 : ℕ) else 0

/-- **Tree domination of `|s - t|`**: if `4^{-J} ≤ |s - t| < 1`, then
`|s - t| ≤ 2 ∑_i (treeCoord J s i - treeCoord J t i)²`. -/
theorem abs_sub_le_two_mul_sum_sq_treeCoord {J : ℕ} {s t : ℝ} (hJ : 1 / 4 ^ J ≤ |s - t|)
    (h1 : |s - t| < 1) :
    |s - t| ≤ 2 * ∑ i : TreeIdx J, (treeCoord J s i - treeCoord J t i) ^ 2 := by
  classical
  have hJne : treeCell J s ≠ treeCell J t := fun h =>
    absurd (abs_sub_lt_of_treeCell_eq h1 h) (not_lt.2 hJ)
  have hex : ∃ j, treeCell j s ≠ treeCell j t := ⟨J, hJne⟩
  set j₀ := Nat.find hex with hj₀def
  have hj₀ : treeCell j₀ s ≠ treeCell j₀ t := Nat.find_spec hex
  have hj₀J : j₀ ≤ J := Nat.find_min' hex hJne
  have hlt : |s - t| < 4 / 4 ^ j₀ := by
    rcases Nat.eq_zero_or_pos j₀ with h0 | hpos
    · rw [h0]
      norm_num
      linarith
    · have heq : treeCell (j₀ - 1) s = treeCell (j₀ - 1) t := by
        by_contra hne
        exact Nat.find_min hex (by omega : j₀ - 1 < j₀) hne
      have := abs_sub_lt_of_treeCell_eq h1 heq
      have h4 : (4 : ℝ) ^ j₀ = 4 * 4 ^ (j₀ - 1) := by
        rw [← pow_succ']
        congr 1
        omega
      rw [h4]
      calc |s - t| < 1 / 4 ^ (j₀ - 1) := this
        _ = 4 / (4 * 4 ^ (j₀ - 1)) := by field_simp
  have hsum : 2 / 4 ^ j₀ ≤ ∑ i : TreeIdx J, (treeCoord J s i - treeCoord J t i) ^ 2 := by
    rw [Fintype.sum_sigma]
    have hle := Finset.single_le_sum
      (f := fun j : Fin (J + 1) => ∑ m : Fin (2 * 4 ^ (j : ℕ)),
        (treeCoord J s ⟨j, m⟩ - treeCoord J t ⟨j, m⟩) ^ 2)
      (fun j _ => Finset.sum_nonneg fun _ _ => sq_nonneg _)
      (Finset.mem_univ (⟨j₀, by omega⟩ : Fin (J + 1)))
    refine le_trans ?_ hle
    have hpair := Finset.sum_le_sum_of_subset_of_nonneg
      (f := fun m : Fin (2 * 4 ^ j₀) =>
        (treeCoord J s ⟨⟨j₀, by omega⟩, m⟩ - treeCoord J t ⟨⟨j₀, by omega⟩, m⟩) ^ 2)
      (Finset.subset_univ {treeCell j₀ s, treeCell j₀ t}) (fun _ _ _ => sq_nonneg _)
    refine le_trans ?_ hpair
    rw [Finset.sum_pair hj₀]
    simp only [treeCoord, ↓reduceIte, hj₀, hj₀.symm]
    have hq : ((1 / 2 : ℝ) ^ j₀) ^ 2 = 1 / 4 ^ j₀ := by
      rw [← pow_mul, mul_comm, pow_mul, one_div_pow, one_div_pow]
      norm_num
    simp only [sub_zero, zero_sub, neg_sq, hq]
    ring_nf
    exact le_rfl
  have h42 : (4 : ℝ) / 4 ^ j₀ = 2 * (2 / 4 ^ j₀) := by ring
  linarith

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

/-- The maximum over the cells of level `j` of `⟪e (j, m), x⟫`. -/
def levelMax (J : ℕ) (e : TreeIdx J → E) (j : Fin (J + 1)) (x : E) : ℝ :=
  ⨆ m : (Finset.univ : Finset (Fin (2 * 4 ^ (j : ℕ)))), ⟪e ⟨j, m⟩, x⟫

/-- The tree bound `∑_j 2^{-j} max_m ⟪e (j, m), x⟫`. -/
def treeMax (J : ℕ) (e : TreeIdx J → E) (x : E) : ℝ :=
  ∑ j : Fin (J + 1), (1 / 2 : ℝ) ^ (j : ℕ) * levelMax J e j x

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
/-- Pointwise domination of the tree process by `treeMax`. -/
theorem sum_treeCoord_mul_inner_le (J : ℕ) (e : TreeIdx J → E) (t : ℝ) (x : E) :
    ∑ i : TreeIdx J, treeCoord J t i * ⟪e i, x⟫ ≤ treeMax J e x := by
  rw [Fintype.sum_sigma]
  refine Finset.sum_le_sum fun j _ => ?_
  simp only [treeCoord, ite_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  exact le_ciSup (f := fun m : (Finset.univ : Finset (Fin (2 * 4 ^ (j : ℕ)))) => ⟪e ⟨j, m⟩, x⟫)
    (Set.finite_range _).bddAbove ⟨treeCell j t, Finset.mem_univ _⟩

/-- Each level maximum has expectation at most `3 (j + 1)`. -/
theorem integral_levelMax_le (J : ℕ) (e : TreeIdx J → E) (he : ∀ i, ‖e i‖ ≤ 1)
    (j : Fin (J + 1)) (hint : Integrable (levelMax J e j) (stdGaussian E)) :
    ∫ x, levelMax J e j x ∂stdGaussian E ≤ 3 * ((j : ℕ) + 1) := by
  have h := GaussianMax.integral_iSup_inner_le (Finset.univ : Finset (Fin (2 * 4 ^ (j : ℕ))))
    Finset.univ_nonempty (fun m => e ⟨j, m⟩) (σ := 1) one_pos (fun m _ => he _) hint
  refine h.trans ?_
  rw [Finset.card_univ, Fintype.card_fin]
  push_cast
  rw [Real.log_mul (by norm_num) (by positivity), Real.log_pow]
  have h2 := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
  have h4 := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 4)
  have hj : (0 : ℝ) ≤ (j : ℕ) := by positivity
  nlinarith

/-- `∑_{j < n} 2^{-j} (j + 1) = 4 - 2 (n + 2) 2^{-n}`. -/
theorem sum_range_half_pow_mul (n : ℕ) :
    ∑ j ∈ Finset.range n, (1 / 2 : ℝ) ^ j * ((j : ℝ) + 1) = 4 - 2 * ((n : ℝ) + 2) * (1 / 2) ^ n := by
  induction n with
  | zero => norm_num
  | succ n ih =>
    rw [Finset.sum_range_succ, ih, pow_succ]
    push_cast
    ring

omit [BorelSpace E] in
theorem integrable_treeMax (J : ℕ) (e : TreeIdx J → E)
    (hint : ∀ j, Integrable (levelMax J e j) (stdGaussian E)) :
    Integrable (treeMax J e) (stdGaussian E) :=
  integrable_finsetSum _ fun j _ => (hint j).const_mul _

/-- **Expected supremum of the tree process**: `E treeMax J e ≤ 12`, uniformly in `J`. -/
theorem integral_treeMax_le (J : ℕ) (e : TreeIdx J → E) (he : ∀ i, ‖e i‖ ≤ 1)
    (hint : ∀ j, Integrable (levelMax J e j) (stdGaussian E)) :
    ∫ x, treeMax J e x ∂stdGaussian E ≤ 12 := by
  unfold treeMax
  rw [integral_finsetSum _ fun j _ => (hint j).const_mul _]
  simp only [integral_const_mul]
  calc ∑ j : Fin (J + 1), (1 / 2 : ℝ) ^ (j : ℕ) * ∫ x, levelMax J e j x ∂stdGaussian E
      ≤ ∑ j : Fin (J + 1), (1 / 2 : ℝ) ^ (j : ℕ) * (3 * ((j : ℕ) + 1)) :=
        Finset.sum_le_sum fun j _ =>
          mul_le_mul_of_nonneg_left (integral_levelMax_le J e he j (hint j)) (by positivity)
    _ = 3 * ∑ j ∈ Finset.range (J + 1), (1 / 2 : ℝ) ^ j * ((j : ℝ) + 1) := by
        rw [Finset.mul_sum, Fin.sum_univ_eq_sum_range
          (fun j => (1 / 2 : ℝ) ^ j * (3 * ((j : ℝ) + 1)))]
        refine Finset.sum_congr rfl fun j _ => ?_
        ring
    _ ≤ 12 := by
        rw [sum_range_half_pow_mul]
        have : 0 ≤ 2 * (((J + 1 : ℕ) : ℝ) + 2) * (1 / 2 : ℝ) ^ (J + 1) := by positivity
        linarith

end LQGDimension.Tree
