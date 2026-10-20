/-
Adapted from Leonardo Bonanno’s formalizations:
https://github.com/leobon12/lean-formalizations
Source: LQGMetric/Metric/Midpoint.lean.
-/
import Mathlib.Topology.Order.IntermediateValue
import LatticeProb.Topology.Length.LengthSpace

/-!
# Approximate midpoints and dyadic points

* `IsApproxMidpoint ε x y z`: `z` is an `ε`-midpoint between `x` and `y`, i.e.
  `d(x, z) ≤ d(x, y)/2 + ε` and `d(y, z) ≤ d(x, y)/2 + ε`.
* `HasApproxMidpoints X`: any two points of `X` have an `ε`-midpoint for every `ε > 0`.
* `hasApproxMidpoints_of_isLengthSpace`: every length space has `ε`-midpoints.
* `dyadicPts x y m n k`: the level-`n` dyadic points of the midpoint construction, for a midpoint
  selector `m`. Consecutive level-`n` points are at most `(d(x, y) + ε) / 2ⁿ` apart, and the
  level-`n` points satisfy `d(dyadicPts n k, dyadicPts n l) ≤ (l - k)(d(x, y) + ε)/2ⁿ`, provided
  the selector chooses `ε / (4 · 4ⁿ)`-midpoints at level `n`.

Sources: Petrunin, *Pure metric geometry* (arXiv:2007.09846), the definition of `ε`-midpoints;
Burago–Burago–Ivanov, *A course in metric geometry* (2001), §2.4.3–2.4.4, Lemma 2.4.10.
-/

open Set Filter Topology
open scoped ENNReal NNReal

namespace LatticeProb.MetricGeometry

section Defs

variable {X : Type*} [PseudoMetricSpace X]

/-- `z` is an `ε`-midpoint between `x` and `y` (Petrunin, *Pure metric geometry*; Burago–Burago–Ivanov Lemma 2.4.10
uses the equivalent two-sided form). -/
def IsApproxMidpoint (ε : ℝ) (x y z : X) : Prop :=
  dist x z ≤ dist x y / 2 + ε ∧ dist y z ≤ dist x y / 2 + ε

/-- Any two points have an `ε`-midpoint for every `ε > 0`. -/
def HasApproxMidpoints (X : Type*) [PseudoMetricSpace X] : Prop :=
  ∀ x y : X, ∀ ε : ℝ, 0 < ε → ∃ z, IsApproxMidpoint ε x y z

/-- **Burago–Burago–Ivanov Lemma 2.4.10**: a length space has `ε`-midpoints. -/
theorem hasApproxMidpoints_of_isLengthSpace (hX : IsLengthSpace X) : HasApproxMidpoints X := by
  intro x y ε hε
  obtain ⟨γ, hγ⟩ := hX x y ε hε
  set D := dist x y
  have hf : ContinuousOn (fun t => dist x (γ.extend t)) (Icc 0 1) :=
    (continuous_const.dist γ.continuous_extend).continuousOn
  obtain ⟨t, ht, hft⟩ := intermediate_value_Icc zero_le_one hf
    (show D / 2 ∈ Icc (dist x (γ.extend 0)) (dist x (γ.extend 1)) by
      simp only [Path.extend_zero, Path.extend_one, dist_self]
      exact ⟨by positivity, by linarith [dist_nonneg (x := x) (y := y)]⟩)
  refine ⟨γ.extend t, le_add_of_le_of_nonneg (le_of_eq hft) hε.le, ?_⟩
  simp only at hft
  have h1 := edist_le_curveLength γ.extend ht.1
  have h2 := edist_le_curveLength γ.extend ht.2
  rw [Path.extend_zero] at h1
  rw [Path.extend_one] at h2
  have hsum : edist x (γ.extend t) + edist (γ.extend t) y ≤ edist x y + ENNReal.ofReal ε := by
    refine (add_le_add h1 h2).trans ?_
    rw [curveLength_add _ ht.1 ht.2]
    exact hγ
  rw [edist_dist, edist_dist, edist_dist, hft, ← ENNReal.ofReal_add dist_nonneg hε.le,
    show D + ε = D / 2 + (D / 2 + ε) by ring,
    ENNReal.ofReal_add (by positivity) (by positivity)] at hsum
  have := (ENNReal.add_le_add_iff_left ENNReal.ofReal_ne_top).1 hsum
  rw [ENNReal.ofReal_le_ofReal_iff (by positivity)] at this
  rwa [dist_comm]

end Defs

section Dyadic

variable {X : Type*}

/-- The level-`n` dyadic points of the midpoint construction, for a midpoint selector `m`
(`m n a b` is the point chosen between `a` and `b` at level `n + 1`). -/
def dyadicPts (x y : X) (m : ℕ → X → X → X) : ℕ → ℕ → X
  | 0, k => if k = 0 then x else y
  | n + 1, k => if k % 2 = 0 then dyadicPts x y m n (k / 2)
      else m n (dyadicPts x y m n (k / 2)) (dyadicPts x y m n (k / 2 + 1))

variable {x y : X} {m : ℕ → X → X → X}

/-- The point of index `0` at level `n` is `x`. -/
theorem dyadicPts_zero (n : ℕ) : dyadicPts x y m n 0 = x := by
  induction n with
  | zero => simp [dyadicPts]
  | succ n ih => simp [dyadicPts, ih]

/-- The point of index `2ⁿ` at level `n` is `y`. -/
theorem dyadicPts_two_pow (n : ℕ) : dyadicPts x y m n (2 ^ n) = y := by
  induction n with
  | zero => simp [dyadicPts]
  | succ n ih =>
    simp only [dyadicPts, pow_succ, Nat.mul_mod_left, ite_true]
    rwa [Nat.mul_div_cancel _ two_pos]

/-- Even-indexed points at level `n + 1` are the points of the same index at level `n`. -/
theorem dyadicPts_two_mul (n k : ℕ) : dyadicPts x y m (n + 1) (2 * k) = dyadicPts x y m n k := by
  simp [dyadicPts]

/-- Odd-indexed points at level `n + 1` are the points chosen by `m` between the neighbouring
points at level `n`. -/
theorem dyadicPts_two_mul_add_one (n k : ℕ) : dyadicPts x y m (n + 1) (2 * k + 1) =
    m n (dyadicPts x y m n k) (dyadicPts x y m n (k + 1)) := by
  have h1 : (2 * k + 1) % 2 = 1 := by omega
  have h2 : (2 * k + 1) / 2 = k := by omega
  simp [dyadicPts, h1, h2]

/-- Consecutive level-`n` points are `≤ (d(x,y) + ε)/2ⁿ − ε/4ⁿ` apart. -/
theorem dist_dyadicPts_succ_le [PseudoMetricSpace X] {ε : ℝ}
    (hm : ∀ n a b, IsApproxMidpoint (ε / (4 * ((2 : ℝ) ^ n) ^ 2)) a b (m n a b)) :
    ∀ n k, k < 2 ^ n → dist (dyadicPts x y m n k) (dyadicPts x y m n (k + 1)) ≤
      (dist x y + ε) / 2 ^ n - ε / ((2 : ℝ) ^ n) ^ 2 := by
  intro n
  induction n with
  | zero =>
    intro k hk
    obtain rfl : k = 0 := by simpa using hk
    simp [dyadicPts]
  | succ n ih =>
    intro k hk
    have key : ∀ j, j < 2 ^ n → ∀ w z : X, dist w z ≤
        dist (dyadicPts x y m n j) (dyadicPts x y m n (j + 1)) / 2 +
          ε / (4 * ((2 : ℝ) ^ n) ^ 2) →
        dist w z ≤ (dist x y + ε) / 2 ^ (n + 1) - ε / ((2 : ℝ) ^ (n + 1)) ^ 2 := by
      intro j hj w z hz
      refine hz.trans (le_of_le_of_eq (add_le_add_left (div_le_div_of_nonneg_right
        (ih j hj) two_pos.le) _) ?_)
      rw [pow_succ]
      field_simp
      ring
    rcases Nat.even_or_odd' k with ⟨j, rfl | rfl⟩
    · have hj : j < 2 ^ n := by rw [pow_succ] at hk; omega
      rw [dyadicPts_two_mul, dyadicPts_two_mul_add_one]
      exact key j hj _ _ (hm n _ _).1
    · have hj : j < 2 ^ n := by rw [pow_succ] at hk; omega
      rw [dyadicPts_two_mul_add_one, show 2 * j + 1 + 1 = 2 * (j + 1) by ring,
        dyadicPts_two_mul, dist_comm]
      exact key j hj _ _ (hm n _ _).2

variable [PseudoMetricSpace X] {ε : ℝ}

/-- Consecutive level-`n` points are at most `(d(x, y) + ε) / 2ⁿ` apart. -/
theorem dist_dyadicPts_succ_le' (hε : 0 ≤ ε)
    (hm : ∀ n a b, IsApproxMidpoint (ε / (4 * ((2 : ℝ) ^ n) ^ 2)) a b (m n a b))
    (n k : ℕ) (hk : k < 2 ^ n) :
    dist (dyadicPts x y m n k) (dyadicPts x y m n (k + 1)) ≤ (dist x y + ε) / 2 ^ n :=
  (dist_dyadicPts_succ_le hm n k hk).trans (sub_le_self _ (by positivity))

/-- Triangle inequality along level `n`: `d(dyadicPts n k, dyadicPts n l) ≤ (l − k)(d(x,y)+ε)/2ⁿ`
for `k ≤ l ≤ 2ⁿ`. -/
theorem dist_dyadicPts_le (hε : 0 ≤ ε)
    (hm : ∀ n a b, IsApproxMidpoint (ε / (4 * ((2 : ℝ) ^ n) ^ 2)) a b (m n a b))
    (n : ℕ) {k l : ℕ} (hkl : k ≤ l) (hl : l ≤ 2 ^ n) :
    dist (dyadicPts x y m n k) (dyadicPts x y m n l) ≤
      ((l : ℝ) - k) * ((dist x y + ε) / 2 ^ n) := by
  refine (dist_le_Ico_sum_dist (dyadicPts x y m n) hkl).trans ?_
  calc ∑ i ∈ Finset.Ico k l, dist (dyadicPts x y m n i) (dyadicPts x y m n (i + 1))
      ≤ ∑ _i ∈ Finset.Ico k l, (dist x y + ε) / 2 ^ n :=
        Finset.sum_le_sum fun i hi =>
          dist_dyadicPts_succ_le' hε hm n i (by simp only [Finset.mem_Ico] at hi; omega)
    _ = _ := by rw [Finset.sum_const, Nat.card_Ico, nsmul_eq_mul, Nat.cast_sub hkl]

end Dyadic

/-- The floor of `2a` is `2⌊a⌋` or `2⌊a⌋ + 1` for `a ≥ 0`. -/
theorem floor_two_mul_eq_or (a : ℝ) (ha : 0 ≤ a) :
    ⌊2 * a⌋₊ = 2 * ⌊a⌋₊ ∨ ⌊2 * a⌋₊ = 2 * ⌊a⌋₊ + 1 := by
  have h1 : 2 * ⌊a⌋₊ ≤ ⌊2 * a⌋₊ := Nat.le_floor (by push_cast; linarith [Nat.floor_le ha])
  have h2 : ⌊2 * a⌋₊ < 2 * ⌊a⌋₊ + 2 :=
    (Nat.floor_lt (by positivity)).2 (by push_cast; linarith [Nat.lt_floor_add_one a])
  omega

/-- For `t ≤ 1`, the floor of `t · 2ⁿ` is at most `2ⁿ`. -/
theorem floor_mul_two_pow_le {t : ℝ} (ht : t ≤ 1) (n : ℕ) : ⌊t * 2 ^ n⌋₊ ≤ 2 ^ n :=
  Nat.floor_le_of_le (by push_cast; have := pow_pos (two_pos (α := ℝ)) n; nlinarith)

/-! ### Nonvacuity examples -/

namespace MidpointExample

/-- On `ℝ` the midpoint `(x + y) / 2` is an `ε`-midpoint for every `ε ≥ 0`. -/
theorem isApproxMidpoint_real_midpoint (ε : ℝ) (hε : 0 ≤ ε) (x y : ℝ) :
    IsApproxMidpoint ε x y ((x + y) / 2) := by
  have h1 : dist x ((x + y) / 2) = dist x y / 2 := by
    rw [Real.dist_eq, Real.dist_eq, show x - (x + y) / 2 = (x - y) / 2 by ring, abs_div, abs_two]
  have h2 : dist y ((x + y) / 2) = dist x y / 2 := by
    rw [Real.dist_eq, Real.dist_eq, show y - (x + y) / 2 = -((x - y) / 2) by ring, abs_neg,
      abs_div, abs_two]
  exact ⟨h1.le.trans (le_add_of_nonneg_right hε), h2.le.trans (le_add_of_nonneg_right hε)⟩

/-- `HasApproxMidpoints ℝ` holds, so the conclusion of `hasApproxMidpoints_of_isLengthSpace`
is not vacuous. -/
example : HasApproxMidpoints ℝ :=
  fun x y ε hε => ⟨(x + y) / 2, isApproxMidpoint_real_midpoint ε hε.le x y⟩

/-- The midpoint hypothesis of the dyadic distance bounds is satisfiable on `ℝ`, with selector
`m n a b = (a + b) / 2`. -/
example (ε : ℝ) (hε : 0 ≤ ε) :
    ∀ (n : ℕ) (a b : ℝ), IsApproxMidpoint (ε / (4 * ((2 : ℝ) ^ n) ^ 2)) a b ((a + b) / 2) :=
  fun n a b => isApproxMidpoint_real_midpoint _ (div_nonneg hε (by positivity)) a b

end MidpointExample

end LatticeProb.MetricGeometry
