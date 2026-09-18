/- Adapted from nitromannitol/Parking-Sharpness, Apache-2.0. -/
/-
The weighted-Jensen geometric-tail lemma: a bound on the `p`-th power of a finite sum of
nonnegative reals, in terms of the SAME power of its individual terms weighted by a geometric
factor that grows with the index, for an arbitrary nonnegative real sequence.  Paired with the
geometric ratio `jensenRatio p := 2 ^ (-1 / (p - 1))`, chosen so that `(jensenRatio p) ^ (1 - p)
= 2` exactly, which is the standard choice turning a per-level geometric decay of ratio `1/2`
into an overall summable weighted series.  Both pieces are pure real-analysis (`Real.rpow`
arithmetic and Mathlib's weighted power-mean inequality).

The proof of the main bound: for weights `w_k := (1 - r) * r ^ k / (1 - r ^ (N + 1))` on
`Finset.range (N + 1)` (which sum to `1` by the finite geometric series identity),
`Real.rpow_arith_mean_le_arith_mean_rpow` applied to `z_k := x_k / w_k` gives `(∑ x_k) ^ p ≤ ∑
w_k ^ (1 - p) * x_k ^ p`.  Since `w_k ≥ (1 - r) * r ^ k` (dividing a positive quantity by
`1 - r ^ (N + 1) ∈ (0, 1]` only increases it) and `1 - p ≤ 0`, `Real.rpow_le_rpow_of_nonpos`
reverses this to `w_k ^ (1 - p) ≤ ((1 - r) * r ^ k) ^ (1 - p) = (1 - r) ^ (1 - p) * r ^ (k * (1 -
p))`, giving the stated bound.  The bound is UNIFORM IN `N`: no summability of `x` is assumed or
needed.
-/
import Mathlib

noncomputable section

namespace LatticeProb.WeightedJensen

open Finset

/-! ### The Jensen ratio -/

/-- **The geometric ratio used to weight the Jensen inequality.**  Chosen so that
`(jensenRatio p) ^ (1 - p) = 2` exactly. -/
def jensenRatio (p : ℝ) : ℝ := (2 : ℝ) ^ (-(1 : ℝ) / (p - 1))

theorem jensenRatio_pos (p : ℝ) : 0 < jensenRatio p :=
  Real.rpow_pos_of_pos (by norm_num) _

theorem jensenRatio_lt_one {p : ℝ} (hp : 1 < p) : jensenRatio p < 1 := by
  unfold jensenRatio
  refine Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) ?_
  have hp1 : (0 : ℝ) < p - 1 := by linarith
  exact div_neg_of_neg_of_pos (by norm_num) hp1

theorem jensenRatio_rpow_one_sub {p : ℝ} (hp : 1 < p) :
    (jensenRatio p) ^ (1 - p) = 2 := by
  unfold jensenRatio
  rw [← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
  have hp1 : p - 1 ≠ 0 := by linarith
  have hexp : -(1 : ℝ) / (p - 1) * (1 - p) = 1 := by
    field_simp
    ring
  rw [hexp, Real.rpow_one]

/-- **The overall geometric decay ratio, `θ(p) = 2 ^ (3 - p / 4)`, is below `1` for `p > 12`.**
This is the standard normalization for combining a per-level decay rate `4^m (1/2^m)^{p/4}`
(a dyadic-scale Kolmogorov moment bound) with the weighted-Jensen ratio `r ^ (1 - p)` at
`r := jensenRatio p`. -/
theorem jensenRatio_rpow_one_sub_mul_lt_one {p : ℝ} (hp : 12 < p) :
    (jensenRatio p) ^ (1 - p) * 4 * (2 : ℝ) ^ (-(p / 4)) < 1 := by
  have hval : (2:ℝ) * 4 * (2:ℝ) ^ (-(p/4)) = (2:ℝ) ^ (3 - p/4) := by
    have h8 : (2:ℝ) * 4 = (2:ℝ) ^ (3:ℝ) := by
      rw [show (3:ℝ) = ((3:ℕ):ℝ) by norm_num, Real.rpow_natCast]
      norm_num
    rw [h8, ← Real.rpow_add (by norm_num : (0:ℝ) < 2)]
    congr 1
  rw [jensenRatio_rpow_one_sub (by linarith : (1:ℝ) < p), hval]
  calc (2:ℝ) ^ (3 - p/4) < (2:ℝ) ^ (0:ℝ) :=
        (Real.rpow_lt_rpow_left_iff (by norm_num : (1:ℝ) < 2)).mpr (by linarith)
    _ = 1 := Real.rpow_zero 2

/-! ### The weighted-Jensen bound -/

/-- **The weighted-Jensen geometric bound.**  For any nonnegative sequence `x`, any `p ≥ 1`,
and any geometric ratio `r ∈ (0, 1)`, the `p`-th power of the sum of the first `N + 1` terms of
`x` is bounded by a GEOMETRICALLY WEIGHTED sum of the `p`-th powers of the individual terms,
uniformly in `N`. -/
theorem rpow_sum_range_le_geometric_weighted_sum (N : ℕ) (x : ℕ → ℝ) (hx : ∀ k, 0 ≤ x k)
    (p : ℝ) (hp : 1 ≤ p) (r : ℝ) (hr0 : 0 < r) (hr1 : r < 1) :
    (∑ k ∈ Finset.range (N + 1), x k) ^ p ≤
      (1 - r) ^ (1 - p) * ∑ k ∈ Finset.range (N + 1), r ^ ((k : ℝ) * (1 - p)) * (x k) ^ p := by
  have hr1' : r ≠ 1 := hr1.ne
  have hrpow_lt : r ^ (N + 1) < 1 := pow_lt_one₀ hr0.le hr1 (Nat.succ_ne_zero N)
  have hrpow_nonneg : (0 : ℝ) ≤ r ^ (N + 1) := by positivity
  have hden_pos : (0 : ℝ) < 1 - r ^ (N + 1) := by linarith
  set D : ℝ := 1 - r ^ (N + 1) with hDdef
  set w : ℕ → ℝ := fun k => (1 - r) * r ^ k / D with hwdef
  have h1r_pos : (0 : ℝ) < 1 - r := by linarith
  have hw_pos : ∀ k, 0 < w k := by
    intro k
    rw [hwdef]
    positivity
  have h1rp1_pos : (0 : ℝ) < 1 - r ^ (N + 1) := by linarith
  have hw_sum : ∑ k ∈ Finset.range (N + 1), w k = 1 := by
    have hgeom : ∑ k ∈ Finset.range (N + 1), r ^ k = (1 - r ^ (N + 1)) / (1 - r) := by
      rw [geom_sum_eq hr1']
      rw [div_eq_div_iff (sub_ne_zero.mpr hr1') h1r_pos.ne']
      ring
    calc ∑ k ∈ Finset.range (N + 1), w k
        = ∑ k ∈ Finset.range (N + 1), (1 - r) / D * r ^ k := by
          refine Finset.sum_congr rfl fun k _ => ?_
          rw [hwdef]; ring
      _ = (1 - r) / D * ∑ k ∈ Finset.range (N + 1), r ^ k := by rw [Finset.mul_sum]
      _ = (1 - r) / D * ((1 - r ^ (N + 1)) / (1 - r)) := by rw [hgeom]
      _ = 1 := by
          rw [hDdef]
          field_simp [h1r_pos.ne', h1rp1_pos.ne']
  set z : ℕ → ℝ := fun k => x k / w k with hzdef
  have hz_nonneg : ∀ k ∈ Finset.range (N + 1), 0 ≤ z k := by
    intro k _
    exact div_nonneg (hx k) (hw_pos k).le
  have hw_nonneg : ∀ k ∈ Finset.range (N + 1), 0 ≤ w k := fun k _ => (hw_pos k).le
  have hmain := Real.rpow_arith_mean_le_arith_mean_rpow (Finset.range (N + 1)) w z
    hw_nonneg hw_sum hz_nonneg hp
  have hwz : ∀ k ∈ Finset.range (N + 1), w k * z k = x k := by
    intro k _
    rw [hzdef]
    exact mul_div_cancel₀ (x k) (hw_pos k).ne'
  have hsum_eq : ∑ k ∈ Finset.range (N + 1), w k * z k = ∑ k ∈ Finset.range (N + 1), x k :=
    Finset.sum_congr rfl hwz
  rw [hsum_eq] at hmain
  have hstep : ∀ k ∈ Finset.range (N + 1), w k * z k ^ p = (w k) ^ (1 - p) * (x k) ^ p := by
    intro k _
    rw [hzdef, Real.div_rpow (hx k) (hw_pos k).le]
    rw [show (w k) ^ (1 - p) = (w k) / (w k) ^ p by
      rw [Real.rpow_sub (hw_pos k), Real.rpow_one]]
    field_simp
  rw [Finset.sum_congr rfl hstep] at hmain
  refine hmain.trans ?_
  have hbound : ∀ k ∈ Finset.range (N + 1),
      (w k) ^ (1 - p) * (x k) ^ p ≤
        (1 - r) ^ (1 - p) * r ^ ((k : ℝ) * (1 - p)) * (x k) ^ p := by
    intro k _
    have hle : (1 - r) * r ^ k ≤ w k := by
      rw [hwdef]
      rw [le_div_iff₀ hden_pos]
      have hDle1 : D ≤ 1 := by rw [hDdef]; linarith
      have hpos : (0 : ℝ) ≤ (1 - r) * r ^ k := by positivity
      nlinarith [hpos, hDle1]
    have hpos1 : (0 : ℝ) < (1 - r) * r ^ k := by positivity
    have hp1 : 1 - p ≤ 0 := by linarith
    have hrw : (w k) ^ (1 - p) ≤ ((1 - r) * r ^ k) ^ (1 - p) :=
      Real.rpow_le_rpow_of_nonpos hpos1 hle hp1
    have hexpand : ((1 - r) * r ^ k) ^ (1 - p) =
        (1 - r) ^ (1 - p) * r ^ ((k : ℝ) * (1 - p)) := by
      rw [Real.mul_rpow h1r_pos.le (by positivity : (0:ℝ) ≤ r ^ k)]
      congr 1
      rw [← Real.rpow_natCast r k, ← Real.rpow_mul hr0.le]
    rw [hexpand] at hrw
    exact mul_le_mul_of_nonneg_right hrw (Real.rpow_nonneg (hx k) p)
  calc ∑ k ∈ Finset.range (N + 1), (w k) ^ (1 - p) * (x k) ^ p
      ≤ ∑ k ∈ Finset.range (N + 1), (1 - r) ^ (1 - p) * r ^ ((k : ℝ) * (1 - p)) * (x k) ^ p :=
        Finset.sum_le_sum hbound
    _ = (1 - r) ^ (1 - p) * ∑ k ∈ Finset.range (N + 1), r ^ ((k : ℝ) * (1 - p)) * (x k) ^ p := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun k _ => ?_
        ring

end LatticeProb.WeightedJensen

end
