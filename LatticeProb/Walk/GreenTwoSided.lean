/-
Two-sided bounds for the killed Green function of a box in `ℤ^d` (all `d ≥ 1`).

Normalization: `Graph.killedGreenReal (lattice d) B x y = (∑' k, killedHeat k x y) / (2d)`
(`Network.killedGreenReal_eq_tsum`), i.e. expected visits to `y` before leaving `B`, over `2d`.

UPPER BOUND (`killedGreenReal_le_box`).  For `B ⊆ box L` and `x ≠ y`, `r = |x - y|_1`:
    g_B(x,y) ≤ C (L+1)^2 (r^{-d} + (L+1)^{-d}).
Route (time domain, no potential kernel, uniform in `d`):
* `killedHeat ≤ heat = srwHeat (x - y)`; the Gaussian bound `srwHeat_gaussian` gives the uniform
  off-diagonal bound `srwHeat k w ≤ C r^{-d}` for `|w|_1 ≥ r` (the sup over `k` of
  `k^{-d/2} e^{-r^2/(8(k+2d))}` is `≍ r^{-d}`).  Head `k < N`: `≤ N C r^{-d}`.
* `N := K (L+1)^2`: `survival N x ≤ |B| sup_w srwHeat N w ≤ (2L+1)^d C N^{-d/2} ≤ 1/2`; the
  library's `Network.sum_range_survival_le` gives `∑_k survival k x ≤ 2N`.
* Killed Chapman–Kolmogorov: `killedHeat (k + N) x y ≤ survival k x · sup_z srwHeat N (z - y)`.
  Tail `≤ 2N · C N^{-d/2}`.
For the Harnack application (`L = 2R-1`, `r ≥ R/2`) this is `≲ R^{2-d}` in every `d ≥ 1`.

LOWER BOUND (`killedGreenReal_ge_box`).  For `m ≤ Kρ`, `box (m+ρ) ⊆ B`, `x, y ∈ box m`:
    g_B(x,y) ≥ c(K) ρ^{2-d}.
(True in `d = 1` by the explicit interval Green function `2(x-a)(b-y)/(b-a) ≥ ρ/(2(K+2))`,
in `d = 2` as `g ≥ c > 0`, in `d ≥ 3` as `c ρ^{2-d}`.)
Route (lazy walk, to avoid parity):
* `lazyKilled B r x y` is the killed lazy kernel, a binomial mixture of `killedHeat`
  (`lazyKilled_eq_binom`), hence `∑_{r ∈ T} lazyKilled r ≤ 2 ∑_k killedHeat k` (the library's
  `hasSum_binomWeight`).
* Free lazy near-diagonal lower bound `Q^n δ₀(w) ≥ c₀ s^{-d}` for `s² ≤ n ≤ 2s²`, `|w|_1 ≤ s`:
  the coordinate-schedule formula `iterate_delta0_eq`, the 1D local CLT
  `exists_srwHeat_one_sub_gauss_le_int` (with `srwHeat_one_two_mul`), and Chebyshev on the counts.
* Killed version: `lazyKilled n a b ≥ Q^n δ₀(a-b) - sup_{j ≤ n, z ∉ B} Q^j δ₀(z-b)`, and the
  sup is `≤ C (Ms)^{-d}` (binomial mixture `iterate_delta0_eq_binom` plus the off-diagonal bound).
* Chaining along `N = O_K(1)` cubes of side `≍ s ≍ ρ` from `x` to `y` (Chapman–Kolmogorov
  lower bound), at every time `N n`, `n ∈ [s², 2s²]`: `s²` times each `≳ s^{-d}`.
* Small `ρ`: a monotone lattice path inside `box m` gives `killedHeat ℓ x y ≥ (2d)^{-ℓ}`.

The proof was written by the library's proof fleet from a statement-owned decomposition and
verified by the library gates.
-/
import LatticeProb.Site
import LatticeProb.Graph.Zd
import LatticeProb.Graph.ExitDecomp
import LatticeProb.Network.Killed
import LatticeProb.Network.KilledGreen
import LatticeProb.Walk.SRWGaussBound
import LatticeProb.Walk.GreenIdentity
import LatticeProb.Walk.Decomp
import LatticeProb.Walk.LocalCLTOne
import LatticeProb.Walk.SRWOneDim
import LatticeProb.Walk.LocalCLT
import LatticeProb.Walk.ExitBox

open Finset
open scoped Classical

namespace LatticeProb

namespace GreenTwoSided

variable {d : ℕ}

/-! ### A. Kernels on the lattice -/

-- unfold LatticeProb.walkOp, nbrSum; Finset.sum_congr; `z + unit i - y = z - y + unit i`
-- (add_sub_right_comm), same with `-`  (sub_right_comm).
/-- The averaging operator commutes with translation: `walkOp` of the `y`-shift of `f` at `x`
equals `walkOp f` at `x - y`. -/
private theorem walkOp_shift (f : Site d → ℝ) (x y : Site d) :
    LatticeProb.walkOp (fun z => f (z - y)) x = LatticeProb.walkOp f (x - y) := by
  simp only [LatticeProb.walkOp, LatticeProb.nbrSum]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  rw [show x + unit i - y = x - y + unit i from by abel,
      show x - unit i - y = x - y - unit i from by abel]


-- Induction on k generalizing x.  k = 0: Graph.heat def (`if x = y`), srwHeat_zero, sub_eq_zero.
-- k+1: Graph.Zd.heat_succ_walkOp, IH under the binder (funext), walkOp_shift, srwHeat_succ.
/-- The free heat kernel on the lattice is translation invariant: `Graph.heat` from `x` to `y` in
`k` steps equals the simple random walk kernel `srwHeat` at `x - y`. -/
private theorem heat_eq_srwHeat_sub (k : ℕ) (x y : Site d) :
    Graph.heat (lattice d) k x y = srwHeat d k (x - y) := by
  induction k generalizing x with
  | zero =>
    rw [srwHeat_zero]
    dsimp only [Graph.heat]
    by_cases h : x = y
    · subst h; simp
    · simp [h, sub_ne_zero.mpr h]
  | succ k ih =>
    rw [Graph.heat_succ, srwHeat_succ, Graph.Zd.walkOp_eq]
    simp only [ih]
    rw [walkOp_shift]


-- Graph.heat_eq_killedHeat_add_exitHeat C y k x, Graph.exitHeat_nonneg, heat_eq_srwHeat_sub;
-- linarith.
/-- The heat kernel killed on leaving any set `C` is dominated by the free heat kernel:
`killedHeat C k x y ≤ srwHeat d k (x - y)`. -/
private theorem killedHeat_le_srwHeat_sub (C : Set (Site d)) (k : ℕ) (x y : Site d) :
    Graph.killedHeat (lattice d) C k x y ≤ srwHeat d k (x - y) := by
  have h := Graph.heat_eq_killedHeat_add_exitHeat (G := lattice d) C y k x
  have hnn := Graph.exitHeat_nonneg (G := lattice d) C y k x
  have h2 := heat_eq_srwHeat_sub k x y
  linarith


-- unfold LatticeProb.walkOp, nbrSum; Finset.sum_div, ← Finset.sum_add_distrib, Finset.sum_comm.
/-- `walkOp` commutes with a finite sum over an index set: the average of a sum of functions is
the sum of the averages. -/
private theorem walkOp_sum {ι : Type*} (s : Finset ι) (F : ι → Site d → ℝ) (x : Site d) :
    LatticeProb.walkOp (fun w => ∑ z ∈ s, F z w) x = ∑ z ∈ s, LatticeProb.walkOp (F z) x := by
  simp only [walkOp, nbrSum_eq_sum_dir, Finset.sum_div]
  rw [Finset.sum_comm]


-- walkOp (c * f) = c * walkOp f:  unfold walkOp, nbrSum; Finset.mul_sum; ring.
/-- `walkOp` commutes with right multiplication by a constant. -/
private theorem walkOp_mul_const (c : ℝ) (f : Site d → ℝ) (x : Site d) :
    LatticeProb.walkOp (fun w => f w * c) x = LatticeProb.walkOp f x * c := by
  unfold LatticeProb.walkOp LatticeProb.nbrSum
  rw [Finset.sum_congr rfl (fun i _ => by ring : ∀ i ∈ Finset.univ,
    ((fun w => f w * c) (x + unit i) + (fun w => f w * c) (x - unit i))
      = (f (x + unit i) + f (x - unit i)) * c)]
  rw [← Finset.sum_mul]
  ring


-- Killed Chapman–Kolmogorov.  Induction on m generalizing x.
-- m = 0: Network.killedHeat_zero; Finset.sum_ite_eq; if x ∉ B the left side is 0 by
--   Network.killedHeat_of_source_not_mem.
-- m+1: rewrite `m + 1 + n = (m + n) + 1` (omega), Graph.Zd.killedHeat_succ_walkOp on both sides,
--   IH under the binder, walkOp_sum, walkOp_mul_const, split `if x ∈ B` (Finset.sum_ite_irrel or
--   by_cases).
/-- Killed Chapman-Kolmogorov: `killedHeat (m + n) x y` factors as a sum over the killing set `B`
of `killedHeat m x z * killedHeat n z y`. -/
private theorem killedHeat_add_eq_sum_mul (B : Finset (Site d)) (m n : ℕ) (x y : Site d) :
    Graph.killedHeat (lattice d) (B : Set (Site d)) (m + n) x y
      = ∑ z ∈ B, Graph.killedHeat (lattice d) (B : Set (Site d)) m x z
          * Graph.killedHeat (lattice d) (B : Set (Site d)) n z y := by
  classical
  induction m generalizing x with
  | zero =>
      rw [Nat.zero_add]
      by_cases hx : x ∈ B
      · have h1 : x ∈ (B : Set (Site d)) := hx
        simp only [Network.killedHeat_zero, if_pos h1, ite_mul, one_mul, zero_mul,
          Finset.sum_ite_eq, if_pos hx]
      · have h0 : ¬ (x ∈ (B : Set (Site d))) := hx
        rw [Network.killedHeat_of_source_not_mem (G := lattice d) h0 n y]
        exact (Finset.sum_eq_zero (fun z _ => by
          simp only [Network.killedHeat_zero, if_neg h0, zero_mul])).symm
  | succ m ih =>
      rw [Nat.succ_add]
      by_cases hx : x ∈ B
      · have h1 : x ∈ (B : Set (Site d)) := hx
        simp only [Graph.Zd.killedHeat_succ_walkOp, if_pos h1]
        simp only [ih]
        rw [walkOp_sum B (fun z w => Graph.killedHeat (lattice d) (B : Set (Site d)) m w z
              * Graph.killedHeat (lattice d) (B : Set (Site d)) n z y) x]
        exact Finset.sum_congr rfl (fun z _ => walkOp_mul_const _ _ x)
      · have h0 : ¬ (x ∈ (B : Set (Site d))) := hx
        rw [Graph.Zd.killedHeat_succ_walkOp (B : Set (Site d)) (m + n) x y, if_neg h0]
        exact (Finset.sum_eq_zero (fun z _ => by
          rw [Graph.Zd.killedHeat_succ_walkOp (B : Set (Site d)) m x z, if_neg h0,
            zero_mul])).symm


-- killedHeat_add_eq_sum_mul; Finset.sum_le_sum with mul_le_mul_of_nonneg_left
-- (Network.killedHeat_nonneg);
-- ← Finset.sum_mul; unfold Network.survival.
/-- If `killedHeat n z y ≤ S` for every `z ∈ B`, then `killedHeat (k + n) x y ≤ Network.survival
B k x * S`. -/
private theorem killedHeat_add_le_survival_mul (B : Finset (Site d)) (k n : ℕ) (x y : Site d)
    (S : ℝ)
    (hS : ∀ z ∈ B, Graph.killedHeat (lattice d) (B : Set (Site d)) n z y ≤ S) :
    Graph.killedHeat (lattice d) (B : Set (Site d)) (k + n) x y
      ≤ Network.survival (lattice d) B k x * S := by
  rw [killedHeat_add_eq_sum_mul B k n x y]
  calc ∑ z ∈ B, Graph.killedHeat (lattice d) (B : Set (Site d)) k x z
          * Graph.killedHeat (lattice d) (B : Set (Site d)) n z y
      ≤ ∑ z ∈ B, Graph.killedHeat (lattice d) (B : Set (Site d)) k x z * S :=
        Finset.sum_le_sum fun z hz =>
          mul_le_mul_of_nonneg_left (hS z hz) (Network.killedHeat_nonneg _ k x z)
    _ = (∑ z ∈ B, Graph.killedHeat (lattice d) (B : Set (Site d)) k x z) * S :=
        (Finset.sum_mul B _ S).symm
    _ = Network.survival (lattice d) B k x * S := rfl


/-! ### B. Pointwise heat-kernel bounds -/

-- y^{d/2} ≤ 1 + y^d for y ≥ 0: if y ≤ 1 then Real.rpow_le_one; else
-- Real.rpow_le_rpow_of_exponent_le (d/2 ≤ d) and Real.rpow_natCast.
/-- For `y ≥ 0`, the half-power `y ^ (d / 2)` is bounded by `1 + y ^ d`. -/
private theorem rpow_half_le_one_add_pow (y : ℝ) (hy : 0 ≤ y) : y ^ ((d : ℝ) / 2) ≤ 1 + y ^ d := by
  have hd : (0:ℝ) ≤ (d:ℝ) := Nat.cast_nonneg d
  rcases le_total y 1 with hy1 | hy1
  · have h1 : y ^ ((d:ℝ)/2) ≤ 1 := Real.rpow_le_one hy hy1 (by linarith)
    have h2 : (0:ℝ) ≤ y ^ d := pow_nonneg hy d
    linarith
  · have h1 : y ^ ((d:ℝ)/2) ≤ y ^ (d:ℝ) :=
      Real.rpow_le_rpow_of_exponent_le hy1 (by linarith)
    rw [Real.rpow_natCast] at h1
    have h2 : (0:ℝ) ≤ y ^ d := pow_nonneg hy d
    linarith


-- (1 + y^d) e^{-y} ≤ 1 + d!:  e^{-y} ≤ 1 (Real.exp_le_one_iff) and
-- y^d ≤ d! e^y (Real.pow_div_factorial_le_exp, div_le_iff₀), Real.exp_neg, mul_inv_cancel₀.
/-- For `y ≥ 0`, `(1 + y ^ d) * Real.exp (-y) ≤ 1 + d!`. -/
private theorem one_add_pow_mul_exp_neg_le (y : ℝ) (hy : 0 ≤ y) :
    (1 + y ^ d) * Real.exp (-y) ≤ 1 + (d.factorial : ℝ) := by
  nlinarith [mul_le_mul_of_nonneg_right
      ((div_le_iff₀ (Nat.cast_pos.mpr (Nat.factorial_pos d))).mp
        (Real.pow_div_factorial_le_exp y hy d)) (Real.exp_nonneg (-y)),
    Real.exp_le_one_iff.mpr (neg_nonpos.mpr hy),
    (by rw [← Real.exp_add, add_neg_cancel, Real.exp_zero] : Real.exp y * Real.exp (-y) = 1)]


-- With y := ρ²/(8u): u^{-d/2} = 8^{d/2} ρ^{-d} y^{d/2} (Real.rpow_neg, Real.div_rpow,
-- Real.rpow_natCast, Real.sqrt_eq_rpow ...), then rpow_half_le_one_add_pow,
-- one_add_pow_mul_exp_neg_le, 8^{d/2} ≤ 8^d.  SPLIT?
/-- A Gaussian-times-power bound: `u ^ (-d/2) * exp (-ρ²/(8u)) ≤ 8^d (1 + d!) / ρ^d` for `u, ρ >
0`. -/
private theorem rpow_neg_half_mul_exp_le_div_pow (u ρ : ℝ) (hu : 0 < u) (hρ : 0 < ρ) :
    u ^ (-(d : ℝ) / 2) * Real.exp (-ρ ^ 2 / (8 * u))
      ≤ 8 ^ d * (1 + (d.factorial : ℝ)) / ρ ^ d := by
  have hu_nn : (0 : ℝ) ≤ u := le_of_lt hu
  have hρ_nn : (0 : ℝ) ≤ ρ := le_of_lt hρ
  have h8nn : (0 : ℝ) ≤ 8 := (by norm_num)
  have hρd_pos : (0 : ℝ) < ρ ^ d := pow_pos hρ d
  have hρ2_nn : (0 : ℝ) ≤ ρ ^ 2 := (by positivity)
  have h3 : (ρ ^ 2) ^ ((d : ℝ) / 2) = ρ ^ d := (by
    rw [← Real.rpow_natCast ρ d, ← Real.rpow_natCast ρ 2, ← Real.rpow_mul hρ_nn]
    congr 1
    push_cast
    ring)
  rw [le_div_iff₀ hρd_pos]
  simp only [neg_div]
  set y : ℝ := ρ ^ 2 / (8 * u) with hydef
  have hy_nn : (0 : ℝ) ≤ y := (by rw [hydef]; positivity)
  have hu_pow_pos : (0 : ℝ) < u ^ ((d : ℝ) / 2) := Real.rpow_pos_of_pos hu _
  have huy : 8 * u * y = ρ ^ 2 := (by
    rw [hydef]; field_simp)
  have h8y : 8 * y = ρ ^ 2 / u := (by
    rw [hydef]; field_simp)
  have hA : (8 : ℝ) ^ ((d : ℝ) / 2) * y ^ ((d : ℝ) / 2) = (8 * y) ^ ((d : ℝ) / 2) :=
    (Real.mul_rpow h8nn hy_nn).symm
  have hBC : (8 * y) ^ ((d : ℝ) / 2) = ρ ^ d / u ^ ((d : ℝ) / 2) := (
    by rw [h8y, Real.div_rpow hρ2_nn hu_nn, h3])
  have hAy : (8 : ℝ) ^ ((d : ℝ) / 2) * y ^ ((d : ℝ) / 2) = ρ ^ d / u ^ ((d : ℝ) / 2) := (
    by rw [hA, hBC])
  have hkey : u ^ (-((d : ℝ) / 2)) * ρ ^ d = (8 : ℝ) ^ ((d : ℝ) / 2) * y ^ ((d : ℝ) / 2) := (
    by rw [Real.rpow_neg hu_nn, hAy, inv_mul_eq_div])
  have hL : u ^ (-((d : ℝ) / 2)) * Real.exp (-y) * ρ ^ d
      = (8 : ℝ) ^ ((d : ℝ) / 2) * (y ^ ((d : ℝ) / 2) * Real.exp (-y)) := (
    by rw [mul_assoc, mul_comm (Real.exp (-y)) (ρ ^ d), ← mul_assoc, hkey, mul_assoc])
  rw [hL]
  have hg : y ^ ((d : ℝ) / 2) * Real.exp (-y) ≤ 1 + (d.factorial : ℝ) :=
    le_trans (mul_le_mul_of_nonneg_right (rpow_half_le_one_add_pow y hy_nn) (Real.exp_nonneg _))
      (one_add_pow_mul_exp_neg_le y hy_nn)
  have hd2 : (d : ℝ) / 2 ≤ (d : ℝ) := (by
    have h : (0 : ℝ) ≤ (d : ℝ) := Nat.cast_nonneg d
    linarith)
  have h8le : (8 : ℝ) ^ ((d : ℝ) / 2) ≤ (8 : ℝ) ^ d :=
    le_trans (Real.rpow_le_rpow_of_exponent_le (by norm_num) hd2)
      (le_of_eq (Real.rpow_natCast 8 d))
  refine le_trans (mul_le_mul_of_nonneg_left hg (Real.rpow_nonneg h8nn _)) ?_
  exact mul_le_mul_of_nonneg_right h8le (by positivity)


-- k + 2d ≤ (1 + 2d) k for k ≥ 1; Real.rpow_le_rpow on exponent d/2, then Real.rpow_neg /
-- inv_le_inv₀; Real.mul_rpow.
/-- For `k ≥ 1`, `k ^ (-d/2) ≤ (1 + 2d) ^ (d/2) * (k + 2d) ^ (-d/2)`, absorbing an additive shift
of `2d` at the cost of a constant. -/
private theorem rpow_neg_half_le_rpow_neg_half_add (k : ℕ) (hk : 1 ≤ k) :
    (k : ℝ) ^ (-(d : ℝ) / 2)
      ≤ (1 + 2 * (d : ℝ)) ^ ((d : ℝ) / 2) * ((k : ℝ) + 2 * d) ^ (-(d : ℝ) / 2) := by
  have hk1 : (1 : ℝ) ≤ (k : ℝ) := (by exact_mod_cast hk)
  have hd0 : (0 : ℝ) ≤ (d : ℝ) := Nat.cast_nonneg d
  have hu : (0 : ℝ) < (k : ℝ) := lt_of_lt_of_le zero_lt_one hk1
  have hv : (0 : ℝ) < (k : ℝ) + 2 * (d : ℝ) := (by positivity)
  have hA : (0 : ℝ) < 1 + 2 * (d : ℝ) := (by positivity)
  have hD : (0 : ℝ) ≤ (d : ℝ) / 2 := (by positivity)
  have hD2 : -(d : ℝ) / 2 = -((d : ℝ) / 2) := (by ring)
  have hvv : (k : ℝ) + 2 * (d : ℝ) ≤ (1 + 2 * (d : ℝ)) * (k : ℝ) :=
    (by nlinarith [hd0, hk1, mul_nonneg hd0 (sub_nonneg.mpr hk1)])
  have hstep : ((k : ℝ) + 2 * (d : ℝ)) ^ ((d : ℝ) / 2)
      ≤ (1 + 2 * (d : ℝ)) ^ ((d : ℝ) / 2) * (k : ℝ) ^ ((d : ℝ) / 2) :=
    Real.mul_rpow hA.le hu.le ▸ Real.rpow_le_rpow hv.le hvv hD
  have hL : ((k : ℝ) ^ ((d : ℝ) / 2))⁻¹ = 1 / ((k : ℝ) ^ ((d : ℝ) / 2)) :=
    inv_eq_one_div _
  have hR : (1 + 2 * (d : ℝ)) ^ ((d : ℝ) / 2) * (((k : ℝ) + 2 * (d : ℝ)) ^ ((d : ℝ) / 2))⁻¹
      = (1 + 2 * (d : ℝ)) ^ ((d : ℝ) / 2) / ((k : ℝ) + 2 * (d : ℝ)) ^ ((d : ℝ) / 2) :=
    (div_eq_mul_inv _ _).symm
  rw [hD2]
  rw [Real.rpow_neg hu.le ((d : ℝ) / 2), Real.rpow_neg hv.le ((d : ℝ) / 2)]
  rw [hL, hR, div_le_div_iff₀ (Real.rpow_pos_of_pos hu _) (Real.rpow_pos_of_pos hv _)]
  simp only [one_mul]
  exact hstep


-- Uniform off-diagonal bound.  C := 3^d greenConst d (1+2d)^{d/2} 8^d (1+d!) + 1.
-- k = 0: srwHeat_zero, w ≠ 0 since graphNorm w ≥ 1 (graphNorm_eq_zero_iff).
-- k ≥ 1: srwHeat_gaussian hd, rpow_neg_half_le_rpow_neg_half_add, rpow_neg_half_mul_exp_le_div_pow
-- (u = k + 2d, ρ = graphNorm w),
-- then 1/(graphNorm w)^d ≤ 1/r^d (pow_le_pow_left₀, one_div_le_one_div_of_le).  SPLIT?
/-- Implementation lemma for `srwHeat_le_div_pow_of_le_graphNorm`: produces the uniform
off-diagonal Gaussian bound `srwHeat d k w ≤ C / r ^ d` whenever `1 ≤ r ≤ graphNorm w`. -/
private theorem srwHeat_le_div_pow_of_le_graphNorm' (hd : 1 ≤ d) :
    ∃ C : ℝ, 0 < C ∧ ∀ (k : ℕ) (w : Site d) (r : ℕ), 1 ≤ r → r ≤ graphNorm w →
      srwHeat d k w ≤ C / (r : ℝ) ^ d := by
  have hd0 : 0 < d := hd
  have hdpos : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd0
  have hA : (0 : ℝ) ≤ 1 + 2 * (d : ℝ) := by positivity
  have hB : (0 : ℝ) ≤ (1 + 2 * (d : ℝ)) ^ ((d : ℝ) / 2) := Real.rpow_nonneg hA _
  have hAB : (0 : ℝ) ≤ 3 ^ d * greenConst d :=
    mul_nonneg (pow_nonneg (by norm_num : (0 : ℝ) ≤ 3) d) (greenConst_nonneg d)
  have hM : (0 : ℝ) ≤ 8 ^ d * (1 + (d.factorial : ℝ)) :=
    mul_nonneg (pow_nonneg (by norm_num : (0 : ℝ) ≤ 8) d) (by positivity)
  have hABM : (0 : ℝ) ≤ 3 ^ d * greenConst d * (1 + 2 * (d : ℝ)) ^ ((d : ℝ) / 2)
      * (8 ^ d * (1 + (d.factorial : ℝ))) := mul_nonneg (mul_nonneg hAB hB) hM
  have hCpos : 0 < 3 ^ d * greenConst d * (1 + 2 * (d : ℝ)) ^ ((d : ℝ) / 2)
      * (8 ^ d * (1 + (d.factorial : ℝ))) + 1 :=
    lt_of_le_of_lt hABM (lt_add_one _)
  refine ⟨_, hCpos, ?_⟩
  intro k w r hr1 hrw
  have hrpos : (0 : ℝ) < (r : ℝ) := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hr1)
  have hRpos : (0 : ℝ) < (r : ℝ) ^ d := pow_pos hrpos d
  rcases Nat.eq_zero_or_pos k with hk | hk
  · subst hk
    rw [srwHeat_zero]
    by_cases hw : w = 0
    · subst hw
      rw [graphNorm_zero] at hrw
      exfalso
      omega
    · rw [if_neg hw]
      exact div_nonneg (by linarith) (le_of_lt hRpos)
  · have hk1 : 1 ≤ k := hk
    have h11 := rpow_neg_half_le_rpow_neg_half_add (d := d) k hk1
    have hg := srwHeat_gaussian (d := d) hd0 hk1 w
    have hu0 : (0 : ℝ) < (k : ℝ) + 2 * (d : ℝ) :=
      add_pos_of_nonneg_of_pos (Nat.cast_nonneg k) (by linarith)
    have hwpos : (0 : ℝ) < (graphNorm w : ℝ) := by
      exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one (le_trans hr1 hrw))
    have hrw' : (r : ℝ) ≤ (graphNorm w : ℝ) := by exact_mod_cast hrw
    have hpow : (r : ℝ) ^ d ≤ (graphNorm w : ℝ) ^ d :=
      pow_le_pow_left₀ (le_of_lt hrpos) hrw' d
    have h10 := rpow_neg_half_mul_exp_le_div_pow (d := d) ((k : ℝ) + 2 * (d : ℝ)) (graphNorm w : ℝ)
        hu0 hwpos
    have hMle : 8 ^ d * (1 + (d.factorial : ℝ)) / (graphNorm w : ℝ) ^ d
        ≤ 8 ^ d * (1 + (d.factorial : ℝ)) / (r : ℝ) ^ d :=
      div_le_div_of_nonneg_left hM hRpos hpow
    have hkey : srwHeat d k w
        ≤ 3 ^ d * greenConst d * (1 + 2 * (d : ℝ)) ^ ((d : ℝ) / 2)
          * (8 ^ d * (1 + (d.factorial : ℝ))) / (r : ℝ) ^ d := by
      have hstep3 : Real.exp (-(graphNorm w : ℝ) ^ 2 / (8 * ((k : ℝ) + 2 * (d : ℝ))))
            * (k : ℝ) ^ (-((d : ℝ)) / 2)
          ≤ Real.exp (-(graphNorm w : ℝ) ^ 2 / (8 * ((k : ℝ) + 2 * (d : ℝ))))
            * ((1 + 2 * (d : ℝ)) ^ ((d : ℝ) / 2)
              * ((k : ℝ) + 2 * (d : ℝ)) ^ (-((d : ℝ)) / 2)) :=
        mul_le_mul_of_nonneg_left h11 (Real.exp_nonneg _)
      calc srwHeat d k w
          ≤ 3 ^ d * greenConst d * (k : ℝ) ^ (-((d : ℝ)) / 2)
            * Real.exp (-(graphNorm w : ℝ) ^ 2 / (8 * ((k : ℝ) + 2 * (d : ℝ)))) := hg
        _ = 3 ^ d * greenConst d *
            (Real.exp (-(graphNorm w : ℝ) ^ 2 / (8 * ((k : ℝ) + 2 * (d : ℝ))))
              * (k : ℝ) ^ (-((d : ℝ)) / 2)) := by ring
        _ ≤ 3 ^ d * greenConst d *
            (Real.exp (-(graphNorm w : ℝ) ^ 2 / (8 * ((k : ℝ) + 2 * (d : ℝ))))
              * ((1 + 2 * (d : ℝ)) ^ ((d : ℝ) / 2)
                * ((k : ℝ) + 2 * (d : ℝ)) ^ (-((d : ℝ)) / 2))) :=
              mul_le_mul_of_nonneg_left hstep3 hAB
        _ = 3 ^ d * greenConst d * (1 + 2 * (d : ℝ)) ^ ((d : ℝ) / 2)
              * (((k : ℝ) + 2 * (d : ℝ)) ^ (-((d : ℝ)) / 2)
                * Real.exp (-(graphNorm w : ℝ) ^ 2 / (8 * ((k : ℝ) + 2 * (d : ℝ))))) := by ring
        _ ≤ 3 ^ d * greenConst d * (1 + 2 * (d : ℝ)) ^ ((d : ℝ) / 2)
              * (8 ^ d * (1 + (d.factorial : ℝ)) / (graphNorm w : ℝ) ^ d) :=
              mul_le_mul_of_nonneg_left h10 (mul_nonneg hAB hB)
        _ ≤ 3 ^ d * greenConst d * (1 + 2 * (d : ℝ)) ^ ((d : ℝ) / 2)
              * (8 ^ d * (1 + (d.factorial : ℝ)) / (r : ℝ) ^ d) :=
              mul_le_mul_of_nonneg_left hMle (mul_nonneg hAB hB)
        _ = 3 ^ d * greenConst d * (1 + 2 * (d : ℝ)) ^ ((d : ℝ) / 2)
              * (8 ^ d * (1 + (d.factorial : ℝ))) / (r : ℝ) ^ d := by ring
    rw [add_div]
    have hone : (0 : ℝ) ≤ 1 / (r : ℝ) ^ d := by positivity
    linarith

/-- The uniform off-diagonal Gaussian heat-kernel bound: there is `C > 0` with `srwHeat d k w ≤ C
/ r ^ d` for all `k`, whenever `1 ≤ r ≤ graphNorm w`. -/
private theorem srwHeat_le_div_pow_of_le_graphNorm (hd : 1 ≤ d) :
    ∃ C : ℝ, 0 < C ∧ ∀ (k : ℕ) (w : Site d) (r : ℕ), 1 ≤ r → r ≤ graphNorm w →
      srwHeat d k w ≤ C / (r : ℝ) ^ d := by
  exact srwHeat_le_div_pow_of_le_graphNorm' hd


-- On-diagonal: srwHeat_gaussian with Real.exp_le_one_iff (the exponent is ≤ 0);
-- C := 3^d greenConst d + 1 (greenConst_nonneg).
/-- The on-diagonal Gaussian heat-kernel bound: there is `C > 0` with `srwHeat d k w ≤ C * k ^
(-d/2)` for all `k ≥ 1` and all `w`. -/
private theorem srwHeat_le_mul_rpow_neg_half (hd : 1 ≤ d) :
    ∃ C : ℝ, 0 < C ∧ ∀ (k : ℕ), 1 ≤ k → ∀ w : Site d,
      srwHeat d k w ≤ C * (k : ℝ) ^ (-(d : ℝ) / 2) := by
  have hd0 : 0 < d := hd
  have hA : (0 : ℝ) ≤ 3 ^ d * greenConst d := mul_nonneg (pow_nonneg (by
    norm_num : (0:ℝ) ≤ 3) d) (greenConst_nonneg d)
  refine ⟨3 ^ d * greenConst d + 1, by linarith, ?_⟩
  intro k hk w
  have hpow : (0 : ℝ) ≤ (k : ℝ) ^ (-(d : ℝ) / 2) := Real.rpow_nonneg (Nat.cast_nonneg k) _
  have hg := srwHeat_gaussian (d := d) hd0 hk w
  have hexp : Real.exp (-(graphNorm w : ℝ) ^ 2 / (8 * ((k : ℝ) + 2 * (d : ℝ)))) ≤ 1 :=
      Real.exp_le_one_iff.mpr (div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (sq_nonneg _)) (by
    positivity))
  have hstep : 3 ^ d * greenConst d * (k : ℝ) ^ (-(d : ℝ) / 2) * Real.exp
      (-(graphNorm w : ℝ) ^ 2 / (8 * ((k : ℝ) + 2 * (d : ℝ)))) ≤ 3 ^ d * greenConst d * (k : ℝ) ^
          (-(d : ℝ) / 2) := (by
    have h := mul_le_mul_of_nonneg_left hexp (mul_nonneg hA hpow)
    simpa using h)
  have hfin : 3 ^ d * greenConst d * (k : ℝ) ^ (-(d : ℝ) / 2) ≤ (3 ^ d * greenConst d + 1) * (k : ℝ)
      ^ (-(d : ℝ) / 2) := (by
    nlinarith [hpow])
  exact le_trans (le_trans hg hstep) hfin


/-! ### C. The upper bound -/

-- Finset.card_le_card into originBox d L (membership: originBox, Fintype.mem_piFinset,
-- Finset.mem_Icc, abs_le from `z ∈ box d L`), card_originBox'; Nat.cast_le, push_cast.
/-- A set contained in `box d L` has at most `(2L + 1) ^ d` elements. -/
private theorem card_le_two_mul_add_one_pow (L : ℕ) (B : Finset (Site d))
    (hB : ∀ z ∈ B, z ∈ box d L) :
    (B.card : ℝ) ≤ (2 * (L : ℝ) + 1) ^ d := by
  refine le_trans (Nat.cast_le.mpr ((Finset.card_le_card ?_).trans (le_of_eq (card_originBox' L))))
      (le_of_eq ?_)
  · intro z hz
    exact Fintype.mem_piFinset.mpr fun i => Finset.mem_Icc.mpr (abs_le.mp (hB z hz i))
  · push_cast
    rfl


-- unfold Network.survival; Finset.sum_le_sum with killedHeat_le_srwHeat_sub and
-- srwHeat_le_mul_rpow_neg_half (k ≥ 1);
-- Finset.sum_const, nsmul_eq_mul.
/-- The survival probability at time `k ≥ 1` is at most `|B| * (C * k ^ (-d/2))`, given the
on-diagonal heat-kernel bound with constant `C`. -/
private theorem survival_le_card_mul_rpow_neg_half (_unused_hd : 1 ≤ d) (C : ℝ)
    (hC : ∀ (k : ℕ), 1 ≤ k → ∀ w : Site d, srwHeat d k w ≤ C * (k : ℝ) ^ (-(d : ℝ) / 2))
    (B : Finset (Site d)) (k : ℕ) (hk : 1 ≤ k) (x : Site d) :
    Network.survival (lattice d) B k x ≤ (B.card : ℝ) * (C * (k : ℝ) ^ (-(d : ℝ) / 2)) := by
  rw [Network.survival]
  exact le_trans
      (Finset.sum_le_sum (fun v _ => le_trans (killedHeat_le_srwHeat_sub (B : Set (Site d)) k x v)
          (hC k hk (x - v))))
    (le_of_eq (by rw [Finset.sum_const, nsmul_eq_mul]))


-- Arithmetic: choose K with (K:ℝ)^{d/2} ≥ 2 · 3^d · C (e.g. K := ⌈(2·3^d·C)^2⌉₊ + 1, so
-- K^{d/2} ≥ K^{1/2} ≥ 2·3^d·C as d ≥ 1).  Then ((K (L+1)^2 : ℕ) : ℝ)^{-d/2}
-- = K^{-d/2} (L+1)^{-d} (Real.mul_rpow, Real.rpow_natCast, Real.rpow_mul), and
-- (2L+1)^d ≤ 3^d (L+1)^d.  SPLIT?
/-- There is `K ≥ 1` with `(2 * 3^d * C) * K ^ (-d/2) ≤ 1`, the arithmetic input to the
survival-below-a-half bound. -/
private theorem exists_nat_rpow_neg_half_mul_le_one (hd : 1 ≤ d) (C : ℝ) (hC : 0 < C) :
    ∃ K : ℕ, 1 ≤ K ∧ (2 * 3 ^ d * C) * (K : ℝ) ^ (-(d : ℝ) / 2) ≤ 1 := by
  have hA0 : (0 : ℝ) ≤ 2 * 3 ^ d * C :=
    mul_nonneg (mul_nonneg (by norm_num) (pow_nonneg (by norm_num : (0:ℝ) ≤ 3) d)) hC.le
  obtain ⟨m, hm⟩ := exists_nat_ge ((2 * 3 ^ d * C) ^ 2)
  refine ⟨m + 1, by omega, ?_⟩
  have hK1 : (1 : ℝ) ≤ ((m + 1 : ℕ) : ℝ) := by
    exact_mod_cast Nat.le_add_left 1 m
  have hKpos : (0 : ℝ) < ((m + 1 : ℕ) : ℝ) := lt_of_lt_of_le one_pos hK1
  have hm1 : ((m : ℕ) : ℝ) ≤ (((m + 1 : ℕ)) : ℝ) := by push_cast; linarith
  have hsq : (2 * 3 ^ d * C) ^ 2 ≤ ((m + 1 : ℕ) : ℝ) := by linarith
  have hstep1 : 2 * 3 ^ d * C ≤ Real.sqrt (((m + 1 : ℕ) : ℝ)) := by
    rw [← Real.sqrt_sq hA0]
    exact Real.sqrt_le_sqrt hsq
  have hstep2 : Real.sqrt (((m + 1 : ℕ) : ℝ)) ≤ ((m + 1 : ℕ) : ℝ) ^ ((d : ℝ) / 2) := by
    rw [Real.sqrt_eq_rpow]
    apply Real.rpow_le_rpow_of_exponent_le hK1
    have hd1 : (1 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
    linarith
  have hKge : 2 * 3 ^ d * C ≤ ((m + 1 : ℕ) : ℝ) ^ ((d : ℝ) / 2) := le_trans hstep1 hstep2
  have ht_nonneg : (0 : ℝ) ≤ ((m + 1 : ℕ) : ℝ) ^ (-(d : ℝ) / 2) :=
    Real.rpow_nonneg hKpos.le _
  calc (2 * 3 ^ d * C) * ((m + 1 : ℕ) : ℝ) ^ (-(d : ℝ) / 2)
      ≤ (((m + 1 : ℕ) : ℝ) ^ ((d : ℝ) / 2)) * ((m + 1 : ℕ) : ℝ) ^ (-(d : ℝ) / 2) :=
        mul_le_mul_of_nonneg_right hKge ht_nonneg
    _ = 1 := by
        rw [← Real.rpow_add hKpos ((d : ℝ) / 2) (-(d : ℝ) / 2)]
        rw [show (d : ℝ) / 2 + -(d : ℝ) / 2 = 0 by ring, Real.rpow_zero]

/-- Once `K` satisfies the bound from `exists_nat_rpow_neg_half_mul_le_one`, `(2L+1)^d * (C *
(K(L+1)^2) ^ (-d/2)) ≤ 1/2` for every `L`. -/
private theorem two_mul_add_one_pow_mul_rpow_neg_half_le_half (C : ℝ) (K : ℕ) (hK : 1 ≤ K)
    (hC : 0 < C)
    (hKineq : (2 * 3 ^ d * C) * (K : ℝ) ^ (-(d : ℝ) / 2) ≤ 1) :
    ∀ L : ℕ, (2 * (L : ℝ) + 1) ^ d
      * (C * (((K * (L + 1) ^ 2 : ℕ) : ℝ)) ^ (-(d : ℝ) / 2)) ≤ 1 / 2 := by
  intro L
  have hKpos : (0 : ℝ) < (K : ℝ) := by exact_mod_cast hK
  have hPpos : (0 : ℝ) < (L : ℝ) + 1 := by positivity
  have hPpowpos : (0 : ℝ) < ((L : ℝ) + 1) ^ d := pow_pos hPpos d
  have hPnn : (0 : ℝ) ≤ 2 * (L : ℝ) + 1 := by positivity
  have h2L : 2 * (L : ℝ) + 1 ≤ 3 * ((L : ℝ) + 1) := by linarith
  have hratio : (2 * (L : ℝ) + 1) ^ d * ((L : ℝ) + 1) ^ (-(d : ℝ)) ≤ 3 ^ d := by
    rw [Real.rpow_neg hPpos.le d, Real.rpow_natCast]
    calc (2 * (L : ℝ) + 1) ^ d * (((L : ℝ) + 1) ^ d)⁻¹
        ≤ (3 * ((L : ℝ) + 1)) ^ d * (((L : ℝ) + 1) ^ d)⁻¹ :=
          mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hPnn h2L d) (inv_nonneg.2 hPpowpos.le)
      _ = 3 ^ d := by
          rw [mul_pow, mul_assoc, mul_inv_cancel₀ (ne_of_gt hPpowpos), mul_one]
  have hcast : (((K * (L + 1) ^ 2 : ℕ) : ℝ)) = (K : ℝ) * ((L : ℝ) + 1) ^ 2 := by
    push_cast; ring
  have htK : (0 : ℝ) ≤ C * (K : ℝ) ^ (-(d : ℝ) / 2) :=
    mul_nonneg hC.le (Real.rpow_nonneg hKpos.le _)
  rw [hcast]
  have hdec : ((K : ℝ) * ((L : ℝ) + 1) ^ 2) ^ (-(d : ℝ) / 2)
      = (K : ℝ) ^ (-(d : ℝ) / 2) * ((L : ℝ) + 1) ^ (-(d : ℝ)) := by
    rw [Real.mul_rpow hKpos.le (pow_nonneg hPpos.le 2)]
    rw [← Real.rpow_natCast ((L : ℝ) + 1) 2]
    rw [← Real.rpow_mul hPpos.le]
    rw [show ((2 : ℕ) : ℝ) * (-(d : ℝ) / 2) = -(d : ℝ) by push_cast; ring]
  rw [hdec]
  calc (2 * (L : ℝ) + 1) ^ d * (C * ((K : ℝ) ^ (-(d : ℝ) / 2) * ((L : ℝ) + 1) ^ (-(d : ℝ))))
      = ((2 * (L : ℝ) + 1) ^ d * ((L : ℝ) + 1) ^ (-(d : ℝ)))
          * (C * (K : ℝ) ^ (-(d : ℝ) / 2)) := by ring
    _ ≤ 3 ^ d * (C * (K : ℝ) ^ (-(d : ℝ) / 2)) := mul_le_mul_of_nonneg_right hratio htK
    _ = ((2 * 3 ^ d * C) * (K : ℝ) ^ (-(d : ℝ) / 2)) / 2 := by ring
    _ ≤ 1 / 2 := div_le_div_of_nonneg_right hKineq (by norm_num)

/-- There is `K ≥ 1` such that `(2L+1)^d * (C * (K(L+1)^2) ^ (-d/2)) ≤ 1/2` for every `L`,
combining `exists_nat_rpow_neg_half_mul_le_one` and
`two_mul_add_one_pow_mul_rpow_neg_half_le_half`. -/
private theorem exists_nat_survival_bound_le_half (hd : 1 ≤ d) (C : ℝ) (hC : 0 < C) :
    ∃ K : ℕ, 1 ≤ K ∧ ∀ L : ℕ,
      (2 * (L : ℝ) + 1) ^ d * (C * (((K * (L + 1) ^ 2 : ℕ) : ℝ)) ^ (-(d : ℝ) / 2)) ≤ 1 / 2 := by
  obtain ⟨K, hKn, hKineq⟩ := exists_nat_rpow_neg_half_mul_le_one hd C hC
  exact ⟨K, hKn, two_mul_add_one_pow_mul_rpow_neg_half_le_half C K hKn hC hKineq⟩


-- srwHeat_le_mul_rpow_neg_half, exists_nat_survival_bound_le_half,
-- survival_le_card_mul_rpow_neg_half at k = K (L+1)^2 (≥ 1), card_le_two_mul_add_one_pow,
-- mul_le_mul_of_nonneg_right.
/-- There is `K ≥ 1` such that the survival probability at time `K(L+1)^2` is at most `1/2` for
every box radius `L` and every set `B ⊆ box d L`. -/
private theorem exists_nat_survival_le_half (hd : 1 ≤ d) :
    ∃ K : ℕ, 1 ≤ K ∧ ∀ (L : ℕ) (B : Finset (Site d)), (∀ z ∈ B, z ∈ box d L) → ∀ x : Site d,
      Network.survival (lattice d) B (K * (L + 1) ^ 2) x ≤ 1 / 2 := by
  obtain ⟨C, hCpos, hC⟩ := srwHeat_le_mul_rpow_neg_half hd
  obtain ⟨K', hK'1, hK'⟩ := exists_nat_survival_bound_le_half hd C hCpos
  refine ⟨K', hK'1, ?_⟩
  intro L B hB x
  have h1 : 1 ≤ (L + 1) ^ 2 := Nat.one_le_pow 2 (L + 1) (Nat.succ_pos L)
  have hKL : 1 ≤ K' * (L + 1) ^ 2 := Nat.mul_le_mul hK'1 h1
  have h15 := survival_le_card_mul_rpow_neg_half hd C hC B (K' * (L + 1) ^ 2) hKL x
  have h14 := card_le_two_mul_add_one_pow L B hB
  have h16 := hK' L
  have hnn : 0 ≤ C * (((K' * (L + 1) ^ 2 : ℕ) : ℝ)) ^ (-(d : ℝ) / 2) :=
    mul_nonneg (le_of_lt hCpos) (Real.rpow_nonneg (Nat.cast_nonneg _) _)
  calc Network.survival (lattice d) B (K' * (L + 1) ^ 2) x
      ≤ (B.card : ℝ) * (C * (((K' * (L + 1) ^ 2 : ℕ) : ℝ)) ^ (-(d : ℝ) / 2)) := h15
    _ ≤ (2 * (L : ℝ) + 1) ^ d
          * (C * (((K' * (L + 1) ^ 2 : ℕ) : ℝ)) ^ (-(d : ℝ) / 2)) :=
        mul_le_mul_of_nonneg_right h14 hnn
    _ ≤ 1 / 2 := h16


-- Network.sum_range_survival_le (hN : 0 < N) (θ := 1/2): N / (1 - 1/2) = 2N (norm_num).
/-- If the survival probability at time `N > 0` is uniformly at most `1/2`, then the partial sums
of survival over any range are at most `2N`, by `Network.sum_range_survival_le`. -/
private theorem sum_range_survival_le_two_mul (B : Finset (Site d)) (N : ℕ) (hN : 0 < N)
    (h : ∀ x : Site d, Network.survival (lattice d) B N x ≤ 1 / 2) (x : Site d) (n : ℕ) :
    ∑ k ∈ Finset.range n, Network.survival (lattice d) B k x ≤ 2 * (N : ℝ) := by
  have h1 := Network.sum_range_survival_le (G := lattice d) (C := B) (N := N)
      (θ := (1/2 : ℝ)) hN (by norm_num) (by norm_num) h x n
  rw [show ((N : ℝ)) / (1 - (1/2 : ℝ)) = 2 * ((N : ℝ)) by ring] at h1
  exact h1


-- Tail: termwise killedHeat_add_le_survival_mul with S := C N^{-d/2} (hS from
-- killedHeat_le_srwHeat_sub + hC at N),
-- ← Finset.sum_mul, sum_range_survival_le_two_mul, mul_le_mul_of_nonneg_right (S ≥ 0:
-- Real.rpow_nonneg).
/-- The tail sum `∑_{k<n} killedHeat (k+N) x y` is at most `2N * (C * N ^ (-d/2))`, given the
on-diagonal bound and the survival bound at time `N`. -/
private theorem sum_range_killedHeat_add_le_two_mul_rpow_neg_half (_unused_hd : 1 ≤ d) (C : ℝ)
    (hC : ∀ (k : ℕ), 1 ≤ k → ∀ w : Site d, srwHeat d k w ≤ C * (k : ℝ) ^ (-(d : ℝ) / 2))
    (B : Finset (Site d)) (N : ℕ) (hN : 0 < N)
    (h : ∀ x : Site d, Network.survival (lattice d) B N x ≤ 1 / 2) (x y : Site d) (n : ℕ) :
    ∑ k ∈ Finset.range n, Graph.killedHeat (lattice d) (B : Set (Site d)) (k + N) x y
      ≤ 2 * (N : ℝ) * (C * (N : ℝ) ^ (-(d : ℝ) / 2)) := by
  have hN1 : 1 ≤ N := hN
  have hCnn : (0 : ℝ) ≤ C :=
    le_trans (srwHeat_nonneg (d := d) 1 x) (by simpa using hC 1 le_rfl x)
  have hSnn : 0 ≤ C * (N : ℝ) ^ (-(d : ℝ) / 2) :=
    mul_nonneg hCnn (Real.rpow_nonneg (Nat.cast_nonneg N) _)
  have hS : ∀ z ∈ B, Graph.killedHeat (lattice d) (B : Set (Site d)) N z y
      ≤ C * (N : ℝ) ^ (-(d : ℝ) / 2) := fun z _ =>
    le_trans (killedHeat_le_srwHeat_sub (B : Set (Site d)) N z y) (hC N hN1 (z - y))
  exact le_trans
    (le_trans
      (Finset.sum_le_sum fun k _ => killedHeat_add_le_survival_mul B k N x y _ (fun z hz => hS z
          hz))
      (le_of_eq (Finset.sum_mul _ _ _).symm))
    (mul_le_mul_of_nonneg_right (sum_range_survival_le_two_mul B N hN h x n) hSnn)


-- Head: termwise killedHeat_le_srwHeat_sub and the off-diagonal hC with r := graphNorm (x - y)
-- (≥ 1 by graphNorm_eq_zero_iff, sub_eq_zero); Finset.sum_le_card_nsmul / sum_const, card_range.
/-- The head sum `∑_{k<N} killedHeat k x y` is at most `N * (C / graphNorm (x - y) ^ d)`, from
the off-diagonal heat-kernel bound. -/
private theorem sum_range_killedHeat_le_mul_div_pow (C : ℝ)
    (hC : ∀ (k : ℕ) (w : Site d) (r : ℕ), 1 ≤ r → r ≤ graphNorm w → srwHeat d k w ≤ C / (r : ℝ) ^ d)
    (B : Finset (Site d)) (N : ℕ) (x y : Site d) (hxy : x ≠ y) :
    ∑ k ∈ Finset.range N, Graph.killedHeat (lattice d) (B : Set (Site d)) k x y
      ≤ (N : ℝ) * (C / (graphNorm (x - y) : ℝ) ^ d) := by
  refine le_trans (b := ∑ k ∈ Finset.range N, C / (graphNorm (x - y) : ℝ) ^ d) ?_ ?_
  · exact Finset.sum_le_sum
      (fun k _ => le_trans (killedHeat_le_srwHeat_sub (B : Set (Site d)) k x y)
      (hC k (x - y) (graphNorm (x - y))
        (Nat.one_le_iff_ne_zero.mpr (fun h => sub_ne_zero.mpr hxy (graphNorm_eq_zero_iff.mp h)))
        le_rfl))
  · rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]


-- NeZero d; q ∉ B from Infinite.exists_notMem_finset (Graph.Zd.latticeInfinite);
-- Network.killedGreenReal_eq_tsum (Graph.Zd.latticeConnected d) B hq x y; Graph.Zd.degree_eq,
-- push_cast.
/-- The killed Green function equals the total mass of `killedHeat` divided by `2d`:
`killedGreenReal B x y = (∑' k, killedHeat k x y) / (2d)`. -/
private theorem killedGreenReal_eq_tsum_killedHeat_div (hd : 1 ≤ d) (B : Finset (Site d))
    (x y : Site d) :
    Graph.killedGreenReal (lattice d) (B : Set (Site d)) x y
      = (∑' k : ℕ, Graph.killedHeat (lattice d) (B : Set (Site d)) k x y) / (2 * (d : ℝ)) := by
  haveI : NeZero d := ⟨by omega⟩
  obtain ⟨q, hq⟩ := Infinite.exists_notMem_finset B
  rw [Network.killedGreenReal_eq_tsum (Graph.Zd.latticeConnected d) B hq x y]
  rw [Graph.Zd.degree_eq]
  push_cast
  ring


-- Real.tsum_le_of_sum_range_le (Network.killedHeat_nonneg): for each n, the range-n partial sum
-- ≤ range (N + n) partial sum (Finset.sum_le_sum_of_subset_of_nonneg, range_mono) and
-- Finset.sum_range_add splits it into head + ∑_{k<n} killedHeat (N + k) (add_comm to k + N).
/-- If the head sum up to `N` is at most `H` and every tail sum from `N` is at most `T`, the full
series `∑' k, killedHeat k x y` is at most `H + T`. -/
private theorem tsum_killedHeat_le_add_of_sum_range_le (B : Finset (Site d)) (N : ℕ) (x y : Site d)
    (H T : ℝ)
    (hH : ∑ k ∈ Finset.range N, Graph.killedHeat (lattice d) (B : Set (Site d)) k x y ≤ H)
    (hT : ∀ n, ∑ k ∈ Finset.range n, Graph.killedHeat (lattice d) (B : Set (Site d)) (k + N) x y ≤
        T) :
    ∑' k : ℕ, Graph.killedHeat (lattice d) (B : Set (Site d)) k x y ≤ H + T := by
  refine Real.tsum_le_of_sum_range_le
    (fun k => Network.killedHeat_nonneg (B : Set (Site d)) k x y) (fun n => ?_)
  have hT0 : (0:ℝ) ≤ T := (by simpa using hT 0)
  by_cases hn : n ≤ N
  · have h1 : ∑ k ∈ Finset.range n, Graph.killedHeat (lattice d) (B : Set (Site d)) k x y
        ≤ ∑ k ∈ Finset.range N, Graph.killedHeat (lattice d) (B : Set (Site d)) k x y :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono hn)
        (fun i _ _ => Network.killedHeat_nonneg (B : Set (Site d)) i x y)
    linarith
  · have hle : N ≤ n := Nat.le_of_not_le hn
    have hsplit : ∑ k ∈ Finset.range n, Graph.killedHeat (lattice d) (B : Set (Site d)) k x y
        = (∑ k ∈ Finset.range N, Graph.killedHeat (lattice d) (B : Set (Site d)) k x y)
          + (∑ k ∈ Finset.range (n - N),
              Graph.killedHeat (lattice d) (B : Set (Site d)) (k + N) x y) := (by
      nth_rewrite 1 [← Nat.add_sub_of_le hle]
      rw [Finset.sum_range_add]
      congr 1
      exact Finset.sum_congr rfl (fun k _ => by rw [Nat.add_comm]))
    linarith [hH, hT (n - N)]


-- Arithmetic with N = K (L+1)^2:  N · C₁ / r^d ≤ K C₁ (L+1)^2 / r^d  and
-- 2 N · C₂ N^{-d/2} = 2 C₂ K^{1-d/2} (L+1)^{2-d} ≤ 2 C₂ K (L+1)^2 / (L+1)^d  (K ≥ 1,
-- Real.rpow_natCast, Real.mul_rpow, Real.rpow_le_rpow_of_exponent_le).  SPLIT?
/-- Arithmetic combination of the head and tail bounds at `N = K(L+1)^2` into the single estimate
`K(C₁+2C₂)(L+1)^2 (1/r^d + 1/(L+1)^d)`. -/
private theorem two_mul_add_one_sq_mul_rpow_neg_half_le (C₁ C₂ : ℝ) (hC₁ : 0 < C₁) (hC₂ : 0 < C₂)
    (K L : ℕ) (hK : 1 ≤ K)
    (r : ℝ) (hr : 0 < r) :
    ((K * (L + 1) ^ 2 : ℕ) : ℝ) * (C₁ / r ^ d)
        + 2 * ((K * (L + 1) ^ 2 : ℕ) : ℝ)
          * (C₂ * (((K * (L + 1) ^ 2 : ℕ) : ℝ)) ^ (-(d : ℝ) / 2))
      ≤ (K : ℝ) * (C₁ + 2 * C₂) * ((L : ℝ) + 1) ^ 2 * (1 / r ^ d + 1 / ((L : ℝ) + 1) ^ d) := by
  set N : ℝ := ((K * (L + 1) ^ 2 : ℕ) : ℝ) with hNdef
  have hK0 : (0:ℝ) ≤ (K:ℝ) := Nat.cast_nonneg K
  have hK1 : (1:ℝ) ≤ (K:ℝ) :=by exact_mod_cast hK
  have hL1 : (0:ℝ) < (L:ℝ) + 1 :=by
    have hL0 : (0:ℝ) ≤ (L:ℝ) := Nat.cast_nonneg L
    linarith
  have hbase2 : (0:ℝ) ≤ ((L:ℝ)+1)^2 := pow_nonneg (le_of_lt hL1) 2
  have hN : N = (K:ℝ) * ((L:ℝ)+1)^2 :=by rw [hNdef]; push_cast; ring
  have hNnn : 0 ≤ N :=by rw [hN]; exact mul_nonneg hK0 hbase2
  have hpowd : 0 < ((L:ℝ)+1)^d := pow_pos hL1 d
  have hdivpos : 0 < 1 / ((L:ℝ)+1)^d := one_div_pos.mpr hpowd
  have hz : -(d:ℝ)/2 ≤ 0 :=by
    have hd0 : (0:ℝ) ≤ (d:ℝ) := Nat.cast_nonneg d
    linarith
  have hkey : N ^ (-(d:ℝ)/2) ≤ 1 / ((L:ℝ)+1)^d :=by
    rw [hN, Real.mul_rpow hK0 hbase2]
    have hKle : (K:ℝ)^(-(d:ℝ)/2) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hK1 hz
    have h2 : (((L:ℝ)+1)^2)^(-(d:ℝ)/2) = 1 / ((L:ℝ)+1)^d :=by
      have e1 : (((L:ℝ)+1)^2)^(-(d:ℝ)/2) = (((L:ℝ)+1)^((2:ℕ):ℝ))^(-(d:ℝ)/2) :=by
        rw [Real.rpow_natCast]
      rw [e1, ← Real.rpow_mul (le_of_lt hL1) ((2:ℕ):ℝ) (-(d:ℝ)/2)]
      rw [show (((2:ℕ):ℝ) * (-(d:ℝ)/2)) = -(d:ℝ) by push_cast; ring]
      rw [Real.rpow_neg (le_of_lt hL1), Real.rpow_natCast, one_div]
    rw [h2]
    calc (K:ℝ)^(-(d:ℝ)/2) * (1/((L:ℝ)+1)^d)
        ≤ 1 * (1/((L:ℝ)+1)^d) := mul_le_mul_of_nonneg_right hKle (le_of_lt hdivpos)
      _ = 1 / ((L:ℝ)+1)^d := one_mul _
  have h1 : N * (C₁ / r^d) ≤ (K:ℝ) * (C₁ + 2*C₂) * ((L:ℝ)+1)^2 * (1/r^d) :=by
    have hC : C₁ / r^d ≤ (C₁ + 2*C₂) * (1/r^d) :=by
      rw [mul_one_div]
      exact div_le_div_of_nonneg_right (by linarith) (le_of_lt (pow_pos hr d))
    calc N * (C₁ / r^d) = (K:ℝ) * ((L:ℝ)+1)^2 * (C₁/r^d) :=by rw [hN]
      _ ≤ (K:ℝ) * ((L:ℝ)+1)^2 * ((C₁+2*C₂) * (1/r^d)) :=
          mul_le_mul_of_nonneg_left hC (mul_nonneg hK0 hbase2)
      _ = (K:ℝ) * (C₁ + 2*C₂) * ((L:ℝ)+1)^2 * (1/r^d) :=by ring
  have h2' : 2 * N * (C₂ * N ^ (-(d:ℝ)/2))
      ≤ (K:ℝ) * (C₁ + 2*C₂) * ((L:ℝ)+1)^2 * (1/((L:ℝ)+1)^d) :=by
    have hS : C₂ * N ^ (-(d:ℝ)/2) ≤ C₂ * (1/((L:ℝ)+1)^d) :=
      mul_le_mul_of_nonneg_left hkey (le_of_lt hC₂)
    calc 2 * N * (C₂ * N ^ (-(d:ℝ)/2))
        ≤ 2 * N * (C₂ * (1/((L:ℝ)+1)^d)) :=
          mul_le_mul_of_nonneg_left hS (mul_nonneg (by norm_num) hNnn)
      _ = (K:ℝ) * ((L:ℝ)+1)^2 * (1/((L:ℝ)+1)^d) * (2*C₂) :=by rw [hN]; ring
      _ ≤ (K:ℝ) * ((L:ℝ)+1)^2 * (1/((L:ℝ)+1)^d) * (C₁+2*C₂) :=
          mul_le_mul_of_nonneg_left (by linarith)
            (mul_nonneg (mul_nonneg hK0 hbase2) (le_of_lt hdivpos))
      _ = (K:ℝ) * (C₁ + 2*C₂) * ((L:ℝ)+1)^2 * (1/((L:ℝ)+1)^d) :=by ring
  calc N * (C₁ / r^d) + 2 * N * (C₂ * N ^ (-(d:ℝ)/2))
      ≤ (K:ℝ) * (C₁ + 2*C₂) * ((L:ℝ)+1)^2 * (1/r^d)
        + (K:ℝ) * (C₁ + 2*C₂) * ((L:ℝ)+1)^2 * (1/((L:ℝ)+1)^d) := add_le_add h1 h2'
    _ = (K:ℝ) * (C₁ + 2*C₂) * ((L:ℝ)+1)^2 * (1/r^d + 1/((L:ℝ)+1)^d) :=by ring


-- C := K (C₁ + 2 C₂) / (2d) with C₁ from srwHeat_le_div_pow_of_le_graphNorm, C₂ from
-- srwHeat_le_mul_rpow_neg_half, K from exists_nat_survival_le_half;
-- killedGreenReal_eq_tsum_killedHeat_div, tsum_killedHeat_le_add_of_sum_range_le with
-- sum_range_killedHeat_le_mul_div_pow (N := K (L+1)^2) and
-- sum_range_killedHeat_add_le_two_mul_rpow_neg_half, two_mul_add_one_sq_mul_rpow_neg_half_le,
-- div_le_div_of_nonneg_right.
/-- For `B` contained in `box d L` and `x ≠ y`, the killed Green function satisfies `g_B(x,y) ≤
C(L+1)^2 (r^{-d} + (L+1)^{-d})` with `r = graphNorm (x-y)`, uniformly in `d ≥ 1`. -/
theorem killedGreenReal_le_box (hd : 1 ≤ d) :
    ∃ C : ℝ, 0 < C ∧ ∀ (L : ℕ) (B : Finset (Site d)), (∀ z ∈ B, z ∈ box d L) →
      ∀ x y : Site d, x ≠ y →
        Graph.killedGreenReal (lattice d) (B : Set (Site d)) x y
          ≤ C * ((L : ℝ) + 1) ^ 2 * (1 / (graphNorm (x - y) : ℝ) ^ d + 1 / ((L : ℝ) + 1) ^ d) := by
  obtain ⟨C₁, hC₁pos, hC₁⟩ := srwHeat_le_div_pow_of_le_graphNorm hd
  obtain ⟨C₂, hC₂pos, hC₂⟩ := srwHeat_le_mul_rpow_neg_half hd
  obtain ⟨K, hK1, hK⟩ := exists_nat_survival_le_half hd
  have hd0 : 0 < d := hd
  have hdpos : (0 : ℝ) < (d : ℝ) := Nat.cast_pos.mpr hd0
  have hd2pos : (0 : ℝ) < 2 * (d : ℝ) := mul_pos (by norm_num) hdpos
  have hK0 : 0 < K := hK1
  have hKpos : (0 : ℝ) < (K : ℝ) := Nat.cast_pos.mpr hK0
  have hSum : (0 : ℝ) < C₁ + 2 * C₂ := add_pos hC₁pos (mul_pos (by norm_num) hC₂pos)
  refine ⟨(K : ℝ) * (C₁ + 2 * C₂) / (2 * (d : ℝ)), div_pos (mul_pos hKpos hSum) hd2pos, ?_⟩
  intro L B hB x y hxy
  have hNpos : 0 < K * (L + 1) ^ 2 := Nat.mul_pos hK0 (pow_pos (Nat.succ_pos L) 2)
  have hsurv : ∀ x : Site d, Network.survival (lattice d) B (K * (L + 1) ^ 2) x ≤ 1 / 2 :=
    fun x => hK L B hB x
  have hH := sum_range_killedHeat_le_mul_div_pow C₁ hC₁ B (K * (L + 1) ^ 2) x y hxy
  have hT : ∀ n, ∑ k ∈ Finset.range n,
      Graph.killedHeat (lattice d) (B : Set (Site d)) (k + K * (L + 1) ^ 2) x y
        ≤ 2 * ((K * (L + 1) ^ 2 : ℕ) : ℝ)
            * (C₂ * (((K * (L + 1) ^ 2 : ℕ) : ℝ)) ^ (-(d : ℝ) / 2)) :=
    fun n => sum_range_killedHeat_add_le_two_mul_rpow_neg_half hd C₂ hC₂ B (K * (L + 1) ^ 2) hNpos
        hsurv x y n
  have htsum := tsum_killedHeat_le_add_of_sum_range_le B (K * (L + 1) ^ 2) x y _ _ hH hT
  have hgn0 : 0 < graphNorm (x - y) := (by
    rcases Nat.eq_zero_or_pos (graphNorm (x - y)) with h | h
    · exact absurd (graphNorm_eq_zero_iff.mp h) (sub_ne_zero.mpr hxy)
    · exact h)
  have hr : (0 : ℝ) < (graphNorm (x - y) : ℝ) := Nat.cast_pos.mpr hgn0
  have h23 := two_mul_add_one_sq_mul_rpow_neg_half_le (d := d) C₁ C₂ hC₁pos hC₂pos K L hK1
      (graphNorm (x - y) : ℝ) hr
  have hgr : Graph.killedGreenReal (lattice d) (B : Set (Site d)) x y
      ≤ ((K : ℝ) * (C₁ + 2 * C₂) / (2 * (d : ℝ))) * ((L : ℝ) + 1) ^ 2
          * (1 / (graphNorm (x - y) : ℝ) ^ d + 1 / ((L : ℝ) + 1) ^ d) := (by
    rw [killedGreenReal_eq_tsum_killedHeat_div hd B x y]
    calc (∑' k : ℕ, Graph.killedHeat (lattice d) (B : Set (Site d)) k x y) / (2 * (d : ℝ))
        ≤ (((K * (L + 1) ^ 2 : ℕ) : ℝ) * (C₁ / (graphNorm (x - y) : ℝ) ^ d)
            + 2 * ((K * (L + 1) ^ 2 : ℕ) : ℝ)
                * (C₂ * (((K * (L + 1) ^ 2 : ℕ) : ℝ)) ^ (-(d : ℝ) / 2))) / (2 * (d : ℝ)) :=
          div_le_div_of_nonneg_right htsum (le_of_lt hd2pos)
      _ ≤ ((K : ℝ) * (C₁ + 2 * C₂) * ((L : ℝ) + 1) ^ 2
              * (1 / (graphNorm (x - y) : ℝ) ^ d + 1 / ((L : ℝ) + 1) ^ d)) / (2 * (d : ℝ)) :=
          div_le_div_of_nonneg_right h23 (le_of_lt hd2pos)
      _ = ((K : ℝ) * (C₁ + 2 * C₂) / (2 * (d : ℝ))) * ((L : ℝ) + 1) ^ 2
            * (1 / (graphNorm (x - y) : ℝ) ^ d + 1 / ((L : ℝ) + 1) ^ d) := (by ring_nf))
  exact hgr


/-! ### D. The killed lazy walk -/

/-- The kernel of the lazy walk (`Q`, library `LatticeProb.Q`) killed on leaving `B`:
`lazyKilled B r x y = P_x(lazy walk stays in B up to time r, X_r = y)`. -/
noncomputable def lazyKilled (B : Finset (Site d)) : ℕ → Site d → Site d → ℝ
  | 0 => fun x y => if x ∈ B then (if x = y then 1 else 0) else 0
  | r + 1 => fun x y => if x ∈ B then
      lazyKilled B r x y / 2 + (∑ a : Dir d, lazyKilled B r (x + dirVec a) y) / (4 * (d : ℝ))
    else 0

-- Induction on r generalizing x; positivity (Finset.sum_nonneg) in both branches.
/-- `lazyKilled B r x y` is nonnegative for every `r`, by induction using positivity of a sum of
nonnegative terms. -/
private theorem lazyKilled_nonneg (B : Finset (Site d)) (r : ℕ) (x y : Site d) : 0 ≤ lazyKilled B r
    x y := by
  induction r generalizing x with
  | zero =>
      simp only [lazyKilled]
      split_ifs <;> norm_num
  | succ n ih =>
      simp only [lazyKilled]
      split_ifs with hx
      · have h1 : 0 ≤ lazyKilled B n x y / 2 := div_nonneg (ih x) (by norm_num)
        have h2 : 0 ≤ (∑ a : Dir d, lazyKilled B n (x + dirVec a) y) / (4 * (d : ℝ)) :=
          div_nonneg (Finset.sum_nonneg fun a _ => ih _) (by positivity)
        linarith
      · exact le_refl 0


-- cases r; unfold lazyKilled; if_neg.
/-- `lazyKilled B r x y = 0` whenever the first argument `x` is not in `B`. -/
private theorem lazyKilled_eq_zero_of_not_mem_left (B : Finset (Site d)) (r : ℕ) {x : Site d}
    (hx : x ∉ B) (y : Site d) :
    lazyKilled B r x y = 0 := by
  cases r with
  | zero => simp [lazyKilled, hx]
  | succ r => simp [lazyKilled, hx]


-- Induction on r generalizing x: r = 0 forces x = y ∈ B; step: every term vanishes by IH.
/-- `lazyKilled B r x y = 0` whenever the second argument `y` is not in `B`. -/
private theorem lazyKilled_eq_zero_of_not_mem_right (B : Finset (Site d)) (r : ℕ) (x : Site d)
    {y : Site d} (hy : y ∉ B) :
    lazyKilled B r x y = 0 := by
  induction r generalizing x with
  | zero =>
      simp only [lazyKilled]
      split_ifs with hx hxy
      · exact absurd (hxy ▸ hx) hy
      · rfl
      · rfl
  | succ r ih =>
      simp only [lazyKilled]
      split_ifs with hx
      · simp [ih]
      · rfl


-- Chapman–Kolmogorov, induction on m generalizing x (as killedHeat_add_eq_sum_mul):
-- m = 0: Finset.sum_ite_eq, lazyKilled_eq_zero_of_not_mem_left when x ∉ B.
-- m+1: `m + 1 + n = (m + n) + 1`, unfold lazyKilled, IH at x and at each x + dirVec a,
-- Finset.sum_div, Finset.sum_comm, Finset.sum_add_distrib, add_mul, Finset.sum_mul.  SPLIT?
/-- Chapman-Kolmogorov for the lazy killed kernel: `lazyKilled B (m+n) x y = ∑_{z ∈ B} lazyKilled
B m x z * lazyKilled B n z y`. -/
private theorem lazyKilled_add_eq_sum_mul (B : Finset (Site d)) (m n : ℕ) (x y : Site d) :
    lazyKilled B (m + n) x y = ∑ z ∈ B, lazyKilled B m x z * lazyKilled B n z y := by
  induction m generalizing x with
  | zero =>
      rw [Nat.zero_add]
      simp only [lazyKilled.eq_1]
      by_cases hx : x ∈ B
      · simp only [if_pos hx, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq]
      · simp only [if_neg hx, zero_mul, Finset.sum_const_zero]
        exact lazyKilled_eq_zero_of_not_mem_left B n hx y
  | succ m ih =>
      rw [Nat.add_right_comm]
      simp only [lazyKilled.eq_2]
      rw [ih x]
      by_cases hx : x ∈ B
      · simp only [if_pos hx]
        simp only [ih]
        rw [Finset.sum_comm, Finset.sum_div, Finset.sum_div]
        have hR :
            (∑ z ∈ B, (lazyKilled B m x z / 2 + (∑ a : Dir d, lazyKilled B m (x + dirVec a) z) / (4
                *
                    (d : ℝ))) * lazyKilled B n z y) = (∑ z ∈ B, (lazyKilled B m x z * lazyKilled B n
                        z y / 2 +
                            (∑ a : Dir d, lazyKilled B m (x + dirVec a) z * lazyKilled B n z y) /
                                (4 * (d : ℝ)))) :=
          Finset.sum_congr rfl (fun z _ => by
            rw [add_mul, div_mul_eq_mul_div, div_mul_eq_mul_div, Finset.sum_mul])
        rw [hR, Finset.sum_add_distrib]
      · simp [hx, Finset.sum_const_zero]


-- lazyKilled_add_eq_sum_mul; ∑ over S = ∑ over S ∩ B (lazyKilled_eq_zero_of_not_mem_right kills z ∉
-- B: Finset.sum_filter /
-- Finset.sum_subset) ≤ ∑ over B (Finset.sum_le_sum_of_subset_of_nonneg, lazyKilled_nonneg).
/-- For any `S`, `∑_{z ∈ S} lazyKilled B m x z * lazyKilled B n z y ≤ lazyKilled B (m+n) x y`,
since restricting the Chapman-Kolmogorov sum to `S` only shrinks it. -/
private theorem sum_lazyKilled_mul_le_lazyKilled_add (B : Finset (Site d)) (m n : ℕ) (x y : Site d)
    (S : Finset (Site d)) :
    ∑ z ∈ S, lazyKilled B m x z * lazyKilled B n z y ≤ lazyKilled B (m + n) x y := by
  classical
  rw [lazyKilled_add_eq_sum_mul]
  have h1 : ∑ z ∈ S, lazyKilled B m x z * lazyKilled B n z y
      ≤ ∑ z ∈ S ∪ B, lazyKilled B m x z * lazyKilled B n z y :=
    Finset.sum_le_sum_of_subset_of_nonneg Finset.subset_union_left
      (fun z _ _ => mul_nonneg (lazyKilled_nonneg B m x z) (lazyKilled_nonneg B n z y))
  have h2 : ∑ z ∈ B, lazyKilled B m x z * lazyKilled B n z y
      = ∑ z ∈ S ∪ B, lazyKilled B m x z * lazyKilled B n z y :=
    Finset.sum_subset Finset.subset_union_right (fun z _ hzB => by
      rw [lazyKilled_eq_zero_of_not_mem_left B n hzB y, mul_zero])
  linarith


-- Comparison with the free lazy kernel.  Claim D_r(x) := Q^[r] δ₀(x - y) - lazyKilled r x y ≤ S,
-- induction on r generalizing x.  x ∉ B: lazyKilled = 0 (lazyKilled_eq_zero_of_not_mem_left), use
-- hS at j = r.
-- x ∈ B, r = 0: δ₀ - δ = 0 ≤ S.  x ∈ B, r+1: Function.iterate_succ_apply', unfold Q (library
-- `Q f x = f x/2 + (∑ a, f (x + dirVec a))/(4d)`), `x - y + dirVec a = (x + dirVec a) - y`
-- (add_sub_right_comm), D_{r+1}(x) = D_r(x)/2 + ∑_a D_r(x+a)/(4d) ≤ S/2 + (2d)S/(4d) = S
-- (Fintype.card (Dir d) = 2d: Fintype.card_prod, Fintype.card_fin, Fintype.card_bool).  SPLIT?
/-- Unfolds `lazyKilled B 0 x y` to its defining `if`-expression. -/
private theorem lazyKilled_zero_eq {d : ℕ} (B : Finset (Site d)) (x y : Site d) :
    lazyKilled B 0 x y = (if x ∈ B then (if x = y then (1 : ℝ) else 0) else 0) := rfl

/-- Unfolds `lazyKilled B (r+1) x y` to its defining recursive `if`-expression. -/
private theorem lazyKilled_succ_eq {d : ℕ} (B : Finset (Site d)) (r : ℕ) (x y : Site d) :
    lazyKilled B (r + 1) x y = (if x ∈ B then lazyKilled B r x y / 2
      + (∑ a : Dir d, lazyKilled B r (x + dirVec a) y) / (4 * (d : ℝ)) else 0) := rfl

/-- One step of the lazy walk operator `Q` applied to `delta0`: `Q^[r+1] delta0 x = Q^[r] delta0
x / 2 + (∑_a Q^[r] delta0 (x + dirVec a)) / (4d)`. -/
private theorem iterate_Q_succ_delta0_eq {d : ℕ} (r : ℕ) (x : Site d) :
    Q^[r + 1] (delta0 : Site d → ℝ) x = Q^[r] (delta0 : Site d → ℝ) x / 2
      + (∑ a : Dir d, Q^[r] (delta0 : Site d → ℝ) (x + dirVec a)) / (4 * (d : ℝ)) := by
  rw [Function.iterate_succ_apply']
  rfl

/-- Reindexes the neighbour sum of `Q^[r] delta0` at `(x-y) + dirVec a` as `(x + dirVec a) - y`. -/
private theorem sum_iterate_Q_delta0_sub_add_eq {d : ℕ} (r : ℕ) (x y : Site d) :
    (∑ a : Dir d, Q^[r] (delta0 : Site d → ℝ) ((x - y) + dirVec a))
      = ∑ a : Dir d, Q^[r] (delta0 : Site d → ℝ) ((x + dirVec a) - y) :=
  Finset.sum_congr rfl fun a _ => by rw [← add_sub_right_comm]

/-- Implementation lemma for `le_lazyKilled_of_forall_le`: if `Q^[j] delta0 (z-y) ≤ S` for all `j
≤ r` and `z ∉ B`, then `Q^[r] delta0 (x-y) - S ≤ lazyKilled B r x y`. -/
private theorem le_lazyKilled_of_forall_le' (hd : 1 ≤ d) (B : Finset (Site d)) (y : Site d) (S : ℝ)
    (hS0 : 0 ≤ S) :
    ∀ r : ℕ, (∀ j ≤ r, ∀ z : Site d, z ∉ B → Q^[j] (delta0 : Site d → ℝ) (z - y) ≤ S) →
      ∀ x : Site d, Q^[r] (delta0 : Site d → ℝ) (x - y) - S ≤ lazyKilled B r x y := by
  intro r
  induction r with
  | zero =>
    intro hS' x
    by_cases hx : x ∈ B
    · rw [lazyKilled_zero_eq, if_pos hx]
      simp only [Function.iterate_zero, id_eq]
      have hδ : delta0 (x - y) ≤ (if x = y then (1 : ℝ) else 0) := by
        by_cases hxy : x = y
        · rw [sub_eq_zero.mpr hxy, if_pos hxy]
          simp [delta0]
        · rw [if_neg hxy]
          have hne : x - y ≠ 0 := fun h => hxy (sub_eq_zero.mp h)
          simp [delta0, hne]
      linarith
    · rw [lazyKilled_zero_eq, if_neg hx]
      simp only [Function.iterate_zero, id_eq]
      have h0 : delta0 (x - y) ≤ S := by
        simpa only [Function.iterate_zero, id_eq] using hS' 0 le_rfl x hx
      linarith
  | succ r ih =>
    intro hS' x
    have ih' : ∀ z : Site d, Q^[r] (delta0 : Site d → ℝ) (z - y) - S ≤ lazyKilled B r z y :=
      fun z => ih (fun j hj z hz => hS' j (Nat.le_succ_of_le hj) z hz) z
    by_cases hx : x ∈ B
    · rw [lazyKilled_succ_eq, if_pos hx]
      rw [iterate_Q_succ_delta0_eq, sum_iterate_Q_delta0_sub_add_eq r x y]
      have h1 : Q^[r] (delta0 : Site d → ℝ) (x - y) / 2 - lazyKilled B r x y / 2 ≤ S / 2 := by
        linarith [ih' x]
      have hsum : ∑ a : Dir d, Q^[r] (delta0 : Site d → ℝ) ((x + dirVec a) - y)
          ≤ ∑ a : Dir d, (lazyKilled B r (x + dirVec a) y + S) :=
        Finset.sum_le_sum fun a _ => by linarith [ih' (x + dirVec a)]
      have hsum2 : ∑ a : Dir d, (lazyKilled B r (x + dirVec a) y + S)
          = (∑ a : Dir d, lazyKilled B r (x + dirVec a) y) + 2 * (d : ℝ) * S := by
        rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_prod,
          Fintype.card_fin, Fintype.card_bool, nsmul_eq_mul]
        push_cast
        ring
      have hpos : (0 : ℝ) < 4 * (d : ℝ) := by
        have hdpos : (0 : ℝ) < (d : ℝ) := by exact_mod_cast (show 0 < d by omega)
        positivity
      have h2 : (∑ a : Dir d, Q^[r] (delta0 : Site d → ℝ) ((x + dirVec a) - y))
            / (4 * (d : ℝ))
          - (∑ a : Dir d, lazyKilled B r (x + dirVec a) y) / (4 * (d : ℝ)) ≤ S / 2 := by
        rw [← sub_div, div_le_iff₀ hpos]
        rw [show S / 2 * (4 * (d : ℝ)) = 2 * (d : ℝ) * S by ring]
        linarith
      linarith
    · rw [lazyKilled_succ_eq, if_neg hx]
      have h0 : Q^[r + 1] (delta0 : Site d → ℝ) (x - y) ≤ S := hS' (r + 1) le_rfl x hx
      linarith

/-- Comparison with the free lazy kernel: if the free kernel is at most `S` off `B` up to time
`r`, then `Q^[r] delta0 (x-y) - S ≤ lazyKilled B r x y`. -/
private theorem le_lazyKilled_of_forall_le (hd : 1 ≤ d) (B : Finset (Site d)) (y : Site d) (S : ℝ)
    (hS0 : 0 ≤ S)
    (r : ℕ) (hS : ∀ j ≤ r, ∀ z : Site d, z ∉ B → Q^[j] (delta0 : Site d → ℝ) (z - y) ≤ S)
    (x : Site d) :
    Q^[r] (delta0 : Site d → ℝ) (x - y) - S ≤ lazyKilled B r x y := by
  exact le_lazyKilled_of_forall_le' hd B y S hS0 r hS x


-- Binomial mixture.  Induction on r generalizing x, modelled on the library's
-- iterate_delta0_eq_binom (walkOp_binom, pascal_sum_srwHeat): Pascal (Nat.choose_succ_succ,
-- Finset.sum_range_succ'), Graph.Zd.killedHeat_succ_walkOp, LatticeProb.walkOp = nbrSum/(2d)
-- and LocalCLT.sum_dir_eq_sum_unit (Dir-sum = nbrSum); if x ∉ B both sides are 0
-- (Network.killedHeat_of_source_not_mem, lazyKilled_eq_zero_of_not_mem_left).  SPLIT?
/-- `walkOp (c * g) = c * walkOp g`, the scalar-multiplication case of linearity of the averaging
operator. -/
private theorem walkOp_const_mul_eq (c : ℝ) (g : Site d → ℝ) (x : Site d) :
    LatticeProb.walkOp (fun z => c * g z) x = c * LatticeProb.walkOp g x := by
  simp only [walkOp_eq_sum_dir]
  rw [← mul_div_assoc, Finset.mul_sum]

/-- Pascal's rule rewritten as a splitting identity for the weighted sum `∑_{k<r+2} C(r+1,k) f k`
into two sums over `range (r+1)` at `f k` and `f (k+1)`. -/
private theorem sum_range_choose_succ_eq_add (f : ℕ → ℝ) (r : ℕ) :
    ∑ k ∈ Finset.range (r + 1 + 1), ((r + 1).choose k : ℝ) * f k
      = ∑ k ∈ Finset.range (r + 1), (r.choose k : ℝ) * f k
        + ∑ k ∈ Finset.range (r + 1), (r.choose k : ℝ) * f (k + 1) := by
  have h1 : ∑ k ∈ Finset.range (r + 1 + 1), ((r + 1).choose k : ℝ) * f k
      = ∑ k ∈ Finset.range (r + 1), ((r + 1).choose (k + 1) : ℝ) * f (k + 1)
        + ((r + 1).choose 0 : ℝ) * f 0 :=
    Finset.sum_range_succ' (fun k => ((r + 1).choose k : ℝ) * f k) (r + 1)
  have h2 : ∑ k ∈ Finset.range (r + 1), ((r + 1).choose (k + 1) : ℝ) * f (k + 1)
      = ∑ k ∈ Finset.range (r + 1), (r.choose k : ℝ) * f (k + 1)
        + ∑ k ∈ Finset.range (r + 1), (r.choose (k + 1) : ℝ) * f (k + 1) := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Nat.choose_succ_succ]
    push_cast
    ring
  have h3 : ∑ k ∈ Finset.range (r + 1), (r.choose k : ℝ) * f k
      = ∑ k ∈ Finset.range r, (r.choose (k + 1) : ℝ) * f (k + 1) + (r.choose 0 : ℝ) * f 0 :=
    Finset.sum_range_succ' (fun k => (r.choose k : ℝ) * f k) r
  have h4 : ∑ k ∈ Finset.range (r + 1), (r.choose (k + 1) : ℝ) * f (k + 1)
      = ∑ k ∈ Finset.range r, (r.choose (k + 1) : ℝ) * f (k + 1)
        + (r.choose (r + 1) : ℝ) * f (r + 1) :=
    Finset.sum_range_succ (fun k => (r.choose (k + 1) : ℝ) * f (k + 1)) r
  have h5 : (r.choose (r + 1) : ℝ) = 0 := by
    rw [Nat.choose_eq_zero_of_lt (by omega)]
    norm_num
  have h6 : ((r + 1).choose 0 : ℝ) = 1 := by simp
  have h7 : (r.choose 0 : ℝ) = 1 := by simp
  rw [h5, zero_mul, add_zero] at h4
  rw [h6, one_mul] at h1
  rw [h7, one_mul] at h3
  linarith [h1, h2, h3, h4]

/-- The Pascal splitting identity `sum_range_choose_succ_eq_add` specialized to `f = killedHeat`. -/
private theorem sum_range_choose_killedHeat_succ_eq_add (B : Finset (Site d)) (r : ℕ) (x y : Site d)
    :
    ∑ k ∈ Finset.range (r + 1 + 1),
        ((r + 1).choose k : ℝ) * Graph.killedHeat (lattice d) (B : Set (Site d)) k x y
      = ∑ k ∈ Finset.range (r + 1),
          (r.choose k : ℝ) * Graph.killedHeat (lattice d) (B : Set (Site d)) k x y
        + ∑ k ∈ Finset.range (r + 1),
          (r.choose k : ℝ) * Graph.killedHeat (lattice d) (B : Set (Site d)) (k + 1) x y := by
  simpa using sum_range_choose_succ_eq_add
    (fun k => Graph.killedHeat (lattice d) (B : Set (Site d)) k x y) r

/-- For `x ∈ B`, `walkOp` of the binomial mixture `∑_k C(r,k) killedHeat k · y` at `x` equals the
shifted mixture `∑_k C(r,k) killedHeat (k+1) x y`. -/
private theorem walkOp_sum_choose_killedHeat_eq (B : Finset (Site d)) (r : ℕ) (x y : Site d)
    (hxB : x ∈ B) :
    LatticeProb.walkOp (fun z => ∑ k ∈ Finset.range (r + 1), (r.choose k : ℝ) *
        Graph.killedHeat (lattice d) (B : Set (Site d)) k z y) x
      = ∑ k ∈ Finset.range (r + 1), (r.choose k : ℝ) *
        Graph.killedHeat (lattice d) (B : Set (Site d)) (k + 1) x y := by
  have hterm : ∀ k ∈ Finset.range (r + 1), (r.choose k : ℝ) *
        Graph.killedHeat (lattice d) (B : Set (Site d)) (k + 1) x y
      = (∑ a : Dir d, (r.choose k : ℝ) *
          Graph.killedHeat (lattice d) (B : Set (Site d)) k (x + dirVec a) y)
        / (2 * (d : ℝ)) := by
    intro k _
    rw [Graph.Zd.killedHeat_succ_walkOp (B : Set (Site d)) k x y, Finset.mem_coe, if_pos hxB]
    simp only [walkOp_eq_sum_dir]
    rw [← Finset.mul_sum, mul_div_assoc]
  have hswap : ∑ a : Dir d, ∑ k ∈ Finset.range (r + 1), (r.choose k : ℝ) *
        Graph.killedHeat (lattice d) (B : Set (Site d)) k (x + dirVec a) y
      = ∑ k ∈ Finset.range (r + 1), ∑ a : Dir d, (r.choose k : ℝ) *
        Graph.killedHeat (lattice d) (B : Set (Site d)) k (x + dirVec a) y :=
    Finset.sum_comm
  rw [Finset.sum_congr rfl hterm, ← Finset.sum_div]
  simp only [walkOp_eq_sum_dir]
  rw [hswap]

/-- Restates `lazyKilled B 0 x y` as the `if x ∈ B then (if x = y then 1 else 0) else 0`
indicator, by `rfl`. -/
private theorem lazyKilled_zero_eq_ite (B : Finset (Site d)) (x y : Site d) :
    lazyKilled B 0 x y = if x ∈ B then (if x = y then 1 else 0) else 0 := rfl

/-- Restates `lazyKilled B (r+1) x y` as its defining `if`-expression, by `rfl`. -/
private theorem lazyKilled_succ_eq_ite (B : Finset (Site d)) (r : ℕ) (x y : Site d) :
    lazyKilled B (r + 1) x y = if x ∈ B then
      lazyKilled B r x y / 2 + (∑ a : Dir d, lazyKilled B r (x + dirVec a) y) / (4 * (d : ℝ))
      else 0 := rfl

/-- `lazyKilled B (r+1) x y` equals `Q (lazyKilled B r · y) x` when `x ∈ B`, and `0` otherwise,
i.e. one step of the lazy operator `Q`. -/
private theorem lazyKilled_succ_eq_Q (B : Finset (Site d)) (r : ℕ) (x y : Site d) :
    lazyKilled B (r + 1) x y = if x ∈ B then Q (fun z => lazyKilled B r z y) x else 0 := by
  rw [lazyKilled_succ_eq_ite]
  by_cases hxB : x ∈ B
  · rw [if_pos hxB, if_pos hxB, Q_eq_walkOp, walkOp_eq_sum_dir]
    rw [add_div, div_div, show (2 * (d : ℝ)) * 2 = 4 * (d : ℝ) by ring]
  · rw [if_neg hxB, if_neg hxB]

/-- The binomial-mixture identity: `lazyKilled B r x y = 2^{-r} ∑_{k ≤ r} C(r,k) killedHeat k x
y`. -/
private theorem lazyKilled_eq_sum_choose_killedHeat (_unused_hd : 1 ≤ d) (B : Finset (Site d))
    (r : ℕ) (x y : Site d) :
    lazyKilled B r x y = (2 : ℝ)⁻¹ ^ r *
      ∑ k ∈ Finset.range (r + 1), (r.choose k : ℝ) * Graph.killedHeat (lattice d) (B : Set (Site d))
          k x y := by
  induction r generalizing x with
  | zero =>
    rw [lazyKilled_zero_eq_ite, Finset.sum_range_one, Network.killedHeat_zero, pow_zero,
      Nat.choose_zero_right, Nat.cast_one, one_mul]
    by_cases h : x ∈ B <;> simp [h]
  | succ r ih =>
    rw [lazyKilled_succ_eq_Q]
    by_cases hxB : x ∈ B
    · rw [if_pos hxB]
      have hfun : (fun z : Site d => lazyKilled B r z y) = fun z => (2 : ℝ)⁻¹ ^ r *
          (∑ k ∈ Finset.range (r + 1), (r.choose k : ℝ) *
            Graph.killedHeat (lattice d) (B : Set (Site d)) k z y) := funext ih
      rw [hfun]
      simp only [Q_eq_walkOp, walkOp_const_mul_eq]
      rw
          [walkOp_sum_choose_killedHeat_eq B r x y hxB, sum_range_choose_killedHeat_succ_eq_add B r
              x y, pow_succ]
      ring
    · rw [if_neg hxB, Finset.sum_eq_zero (fun k _ => by
        rw [Network.killedHeat_of_source_not_mem (C := (B : Set (Site d)))
          (by simpa using hxB) k y, mul_zero]), mul_zero]


-- lazyKilled_eq_sum_choose_killedHeat written with binomWeight (binomWeight_of_le /
-- binomWeight_of_lt, extend every
-- inner sum to range (R+1), R := T.sup id); Finset.sum_comm; for each k,
-- ∑_{r ∈ T} binomWeight k r ≤ 2 (sum_le_hasSum with hasSum_binomWeight k, binomWeight_nonneg);
-- then ∑_{k ≤ R} killedHeat k ≤ tsum (Summable.sum_le_tsum, Network.summable_killedHeat with
-- q ∉ B, Graph.Zd.latticeConnected).  SPLIT?
/-- Implementation lemma for `sum_lazyKilled_le_two_mul_tsum_killedHeat`. -/
private theorem sum_lazyKilled_le_two_mul_tsum_killedHeat' (hd : 1 ≤ d) (B : Finset (Site d))
    (x y : Site d) (T : Finset ℕ) :
    ∑ r ∈ T, lazyKilled B r x y
      ≤ 2 * ∑' k : ℕ, Graph.killedHeat (lattice d) (B : Set (Site d)) k x y := by
  haveI : NeZero d := NeZero.of_pos (by omega)
  let R : ℕ := T.sup (id : ℕ → ℕ)
  have hsub : T ⊆ Finset.range (R + 1) := by
    intro r hr
    rw [Finset.mem_range]
    have h1 : r ≤ R := le_sup (f := id) hr
    omega
  have hlazy : ∀ r ∈ T, lazyKilled B r x y
      = ∑ k ∈ Finset.range (R + 1), binomWeight k r
          * Graph.killedHeat (lattice d) (B : Set (Site d)) k x y := by
    intro r hr
    have hmem : r ∈ Finset.range (R + 1) := hsub hr
    have hrle : r + 1 ≤ R + 1 := by
      rw [Finset.mem_range] at hmem
      omega
    have step1 : (∑ k ∈ Finset.range (r + 1), 2⁻¹ ^ r * ((r.choose k : ℝ)
          * Graph.killedHeat (lattice d) (B : Set (Site d)) k x y))
        = ∑ k ∈ Finset.range (r + 1), binomWeight k r
          * Graph.killedHeat (lattice d) (B : Set (Site d)) k x y := by
      apply Finset.sum_congr rfl
      intro k hk
      have hk' : k ≤ r := by
        rw [Finset.mem_range] at hk
        omega
      rw [binomWeight_of_le hk']
      ring
    have step2 : (∑ k ∈ Finset.range (r + 1), binomWeight k r
          * Graph.killedHeat (lattice d) (B : Set (Site d)) k x y)
        = ∑ k ∈ Finset.range (R + 1), binomWeight k r
          * Graph.killedHeat (lattice d) (B : Set (Site d)) k x y := by
      apply Finset.sum_subset (Finset.range_subset_range.mpr hrle)
      intro k hk hkr
      rw [Finset.mem_range] at hkr
      rw [binomWeight_of_lt (show r < k by omega)]
      ring
    rw [lazyKilled_eq_sum_choose_killedHeat hd B r x y, Finset.mul_sum, step1, step2]
  have hbw : ∀ k ∈ Finset.range (R + 1), (∑ r ∈ T, binomWeight k r) ≤ 2 := by
    intro k _
    exact sum_le_hasSum T (fun r _ => binomWeight_nonneg k r) (hasSum_binomWeight k)
  have hfin : (∑ r ∈ T, ∑ k ∈ Finset.range (R + 1), binomWeight k r
        * Graph.killedHeat (lattice d) (B : Set (Site d)) k x y)
      ≤ ∑ k ∈ Finset.range (R + 1), 2
        * Graph.killedHeat (lattice d) (B : Set (Site d)) k x y := by
    rw [Finset.sum_comm]
    apply Finset.sum_le_sum
    intro k hk
    rw [← Finset.sum_mul]
    exact mul_le_mul_of_nonneg_right (hbw k hk)
      (Network.killedHeat_nonneg (B : Set (Site d)) k x y)
  have htsum : (∑ k ∈ Finset.range (R + 1), 2
        * Graph.killedHeat (lattice d) (B : Set (Site d)) k x y)
      ≤ 2 * ∑' k : ℕ, Graph.killedHeat (lattice d) (B : Set (Site d)) k x y := by
    obtain ⟨q, hq⟩ := Infinite.exists_notMem_finset B
    have hsum : Summable (fun k : ℕ => (2 : ℝ)
        * Graph.killedHeat (lattice d) (B : Set (Site d)) k x y) :=
      (Network.summable_killedHeat (Graph.Zd.latticeConnected d) B hq x y).mul_left 2
    have h := Summable.sum_le_tsum (Finset.range (R + 1))
      (fun i _ => mul_nonneg (by norm_num)
        (Network.killedHeat_nonneg (B : Set (Site d)) i x y)) hsum
    rwa [tsum_mul_left] at h
  calc ∑ r ∈ T, lazyKilled B r x y
      ≤ ∑ r ∈ T, ∑ k ∈ Finset.range (R + 1), binomWeight k r
          * Graph.killedHeat (lattice d) (B : Set (Site d)) k x y :=
        Finset.sum_le_sum (fun r hr => le_of_eq (hlazy r hr))
    _ ≤ ∑ k ∈ Finset.range (R + 1), 2
          * Graph.killedHeat (lattice d) (B : Set (Site d)) k x y := hfin
    _ ≤ 2 * ∑' k : ℕ, Graph.killedHeat (lattice d) (B : Set (Site d)) k x y := htsum

/-- For any finite set `T` of times, `∑_{r ∈ T} lazyKilled B r x y ≤ 2 ∑' k, killedHeat k x y`,
since the binomial weights of `lazyKilled` sum to at most `2` at each time `k`. -/
private theorem sum_lazyKilled_le_two_mul_tsum_killedHeat (hd : 1 ≤ d) (B : Finset (Site d))
    (x y : Site d) (T : Finset ℕ) :
    ∑ r ∈ T, lazyKilled B r x y
      ≤ 2 * ∑' k : ℕ, Graph.killedHeat (lattice d) (B : Set (Site d)) k x y := by
  exact sum_lazyKilled_le_two_mul_tsum_killedHeat' hd B x y T


/-! ### E. The free lazy kernel -/

-- iterate_delta0_eq_binom j w; every srwHeat d k w ≤ C / r^d (srwHeat_le_div_pow_of_le_graphNorm);
-- the weights sum to 1
-- (Nat.sum_range_choose: ∑ choose = 2^j, (2⁻¹)^j * 2^j = 1); Finset.sum_le_sum, ← Finset.mul_sum.
/-- The free lazy kernel inherits the off-diagonal Gaussian bound: `Q^[j] delta0 w ≤ C / r ^ d`
whenever `1 ≤ r ≤ graphNorm w`, as a binomial mixture of the corresponding `srwHeat` bound. -/
private theorem iterate_Q_delta0_le_div_pow_of_le_graphNorm (hd : 1 ≤ d) :
    ∃ C : ℝ, 0 < C ∧ ∀ (j : ℕ) (w : Site d) (r : ℕ), 1 ≤ r → r ≤ graphNorm w →
      Q^[j] (delta0 : Site d → ℝ) w ≤ C / (r : ℝ) ^ d := by
  obtain ⟨C, hCpos, hC⟩ := srwHeat_le_div_pow_of_le_graphNorm hd
  refine ⟨C, hCpos, ?_⟩
  intro j w r hr hrw
  rw [iterate_delta0_eq_binom]
  have hchoose : (∑ k ∈ Finset.range (j + 1), (j.choose k : ℝ)) = (2 : ℝ) ^ j :=
    (by rw [← Nat.cast_sum, Nat.sum_range_choose]; push_cast; ring)
  have hstep : ∑ k ∈ Finset.range (j + 1), (j.choose k : ℝ) * srwHeat d k w
      ≤ (2 : ℝ) ^ j * (C / (r : ℝ) ^ d) := (by
    rw [← hchoose, Finset.sum_mul]
    exact Finset.sum_le_sum
        (fun k _ => mul_le_mul_of_nonneg_left (hC k w r hr hrw) (Nat.cast_nonneg _)))
  have hmul : (2 : ℝ)⁻¹ ^ j * ((2 : ℝ) ^ j * (C / (r : ℝ) ^ d)) = C / (r : ℝ) ^ d :=
    (by rw [← mul_assoc, ← mul_pow, inv_mul_cancel₀ (by norm_num), one_pow, one_mul])
  exact le_trans (mul_le_mul_of_nonneg_left hstep (pow_nonneg (by norm_num) _)) (le_of_eq hmul)


-- 1D lazy local CLT lower bound.  P1 m k = srwHeat 1 (2m) ![2k] (srwHeat_one_two_mul, reversed);
-- exists_srwHeat_one_sub_gauss_le_int with ε := exp(-A²)/2: √(πm) P1 m k ≥ exp(-k²/m) - ε
-- ≥ exp(-A²)/2 (k² ≤ A² m, Real.exp_le_exp); c := exp(-A²)/(2√π); Real.sqrt_mul.
/-- The 1D lazy local CLT lower bound: for every `A > 0` there are `c > 0` and `m₀` such that `c
/ √m ≤ P1 m k` whenever `m ≥ m₀` and `|k| ≤ A√m`. -/
private theorem exists_const_le_P1_of_le_sqrt_mul (A : ℝ) (hA : 0 < A) :
    ∃ c : ℝ, 0 < c ∧ ∃ m₀ : ℕ, 1 ≤ m₀ ∧ ∀ m : ℕ, m₀ ≤ m → ∀ k : ℤ,
      |(k : ℝ)| ≤ A * Real.sqrt (m : ℝ) → c / Real.sqrt (m : ℝ) ≤ P1 m k := by
  have hε : 0 < Real.exp (-(A ^ 2)) / 2 := div_pos (Real.exp_pos _) two_pos
  obtain ⟨m₀, hm₀, H⟩ := exists_srwHeat_one_sub_gauss_le_int hA hε
  refine ⟨Real.exp (-(A ^ 2)) / (2 * Real.sqrt Real.pi),
    div_pos (Real.exp_pos _) (mul_pos two_pos (Real.sqrt_pos.mpr Real.pi_pos)), m₀, hm₀, ?_⟩
  intro m hm k hk
  have hm1 : 1 ≤ m := le_trans hm₀ hm
  have hmpos : 0 < (m : ℝ) := (by exact_mod_cast hm1)
  have hk2 : (k : ℝ) ^ 2 ≤ (A * Real.sqrt (m : ℝ)) ^ 2 :=
    sq_le_sq.mpr (by rw [abs_of_nonneg (mul_nonneg hA.le (Real.sqrt_nonneg _))]; exact hk)
  have hsq : (k : ℝ) ^ 2 ≤ A ^ 2 * (m : ℝ) := (by
    rwa [mul_pow, Real.sq_sqrt (Nat.cast_nonneg m)] at hk2)
  have hdiv : (k : ℝ) ^ 2 / (m : ℝ) ≤ A ^ 2 := (by
    rw [div_le_iff₀ hmpos]
    linarith)
  have hexp : Real.exp (-(A ^ 2)) ≤ Real.exp (-((k : ℝ) ^ 2 / (m : ℝ))) := (by
    rw [Real.exp_le_exp]
    exact neg_le_neg hdiv)
  have hkey : |Real.sqrt (Real.pi * (m : ℝ)) * P1 m k - Real.exp (-((k : ℝ) ^ 2 / (m : ℝ)))|
      ≤ Real.exp (-(A ^ 2)) / 2 := (by
    have h := H m hm k hk
    rwa [srwHeat_one_two_mul] at h)
  have h2 : Real.exp (-(A ^ 2)) / 2 ≤ Real.sqrt (Real.pi * (m : ℝ)) * P1 m k := (by
    have h4 := (abs_le.mp hkey).1
    linarith only [h4, hexp])
  have hsqrt : 0 < Real.sqrt (Real.pi * (m : ℝ)) :=
    Real.sqrt_pos.mpr (mul_pos Real.pi_pos hmpos)
  have h3 : Real.exp (-(A ^ 2)) / 2 / Real.sqrt (Real.pi * (m : ℝ)) ≤ P1 m k := (by
    rw [div_le_iff₀ hsqrt]
    calc Real.exp (-(A ^ 2)) / 2 ≤ Real.sqrt (Real.pi * (m : ℝ)) * P1 m k := h2
      _ = P1 m k * Real.sqrt (Real.pi * (m : ℝ)) := mul_comm _ _)
  have heq : Real.exp (-(A ^ 2)) / (2 * Real.sqrt Real.pi) / Real.sqrt (m : ℝ)
      = Real.exp (-(A ^ 2)) / 2 / Real.sqrt (Real.pi * (m : ℝ)) := (by
    rw [Real.sqrt_mul Real.pi_nonneg, div_div, div_div]
    ring)
  rw [heq]
  exact h3


-- Counting: {c : Fin r → Fin d | c t = i} has d^r / d elements.  Sum over c of the indicator
-- via Fintype.sum_pow / Finset.prod_univ_sum style factorisation, or by the equivalence
-- Equiv.piSplitAt t; Fintype.card_pi, Fintype.card_fin.
/-- The fibre `{c : Fin r → Fin d // c t = i}` of a fixed coordinate has exactly `d^{r-1}`
elements. -/
private theorem card_fiber_eq_pow_sub_one {d r : ℕ} (t : Fin r) (i : Fin d) :
    Fintype.card {c : Fin r → Fin d // c t = i} = d ^ (r - 1) := by
  have hr : 1 ≤ r := Nat.succ_le_of_lt (Nat.lt_of_le_of_lt (Nat.zero_le (t : ℕ)) t.isLt)
  have e : {c : Fin r → Fin d // c t = i} ≃ ({j : Fin r // j ≠ t} → Fin d) :=
    { toFun := fun c j => c.1 j.1
      invFun := fun g => ⟨fun j => if h : j = t then i else g ⟨j, h⟩, by simp⟩
      left_inv := by
        intro c
        apply Subtype.ext
        funext j
        by_cases h : j = t
        · simp [h, c.2]
        · simp [h]
      right_inv := by
        intro g
        funext j
        simp [j.2] }
  rw [Fintype.card_congr e, Fintype.card_fun, Fintype.card_fin]
  have h1 : Fintype.card {j : Fin r // j ≠ t} = r - 1 := by
    rw [Fintype.card_subtype_compl (fun j : Fin r => j = t),
      Fintype.card_subtype_eq t, Fintype.card_fin]
  rw [h1]

/-- The indicator sum `∑_c (if c t = i then 1 else 0)` equals the cardinality of the fibre `{c //
c t = i}`. -/
private theorem sum_ite_eq_fiber_eq_card {d r : ℕ} (t : Fin r) (i : Fin d) :
    (∑ c : Fin r → Fin d, (if c t = i then (1 : ℝ) else 0))
      = ((Fintype.card {c : Fin r → Fin d // c t = i} : ℕ) : ℝ) := by
  rw [Fintype.card_subtype]
  exact Finset.sum_boole (fun c : Fin r → Fin d => c t = i) Finset.univ

/-- For `r ≥ 1` and `d > 0`, `(d^{r-1} : ℝ) = d^r / d`. -/
private theorem cast_pow_sub_one_eq_pow_div {d r : ℕ} (hr : 1 ≤ r) (hd0 : (0 : ℝ) < (d : ℝ)) :
    ((d ^ (r - 1) : ℕ) : ℝ) = (d : ℝ) ^ r / (d : ℝ) := by
  rw [Nat.cast_pow, eq_div_iff (ne_of_gt hd0), ← pow_succ, Nat.sub_add_cancel hr]

/-- The one-coordinate fibre count as a real number: `∑_c (if c t = i then 1 else 0) = d^r / d`. -/
private theorem sum_ite_eq_eq_pow_div (hd : 1 ≤ d) (r : ℕ) (t : Fin r) (i : Fin d) :
    ∑ c : Fin r → Fin d, (if c t = i then (1 : ℝ) else 0) = (d : ℝ) ^ r / d := by
  have hr : 1 ≤ r := Nat.succ_le_of_lt (Nat.lt_of_le_of_lt (Nat.zero_le (t : ℕ)) t.isLt)
  have hd0 : (0 : ℝ) < (d : ℝ) := Nat.cast_pos.mpr (Nat.lt_of_lt_of_le Nat.zero_lt_one hd)
  rw
      [sum_ite_eq_fiber_eq_card t i, card_fiber_eq_pow_sub_one t i, cast_pow_sub_one_eq_pow_div hr
          hd0]


-- Same with two distinct coordinates t ≠ t' fixed: d^r / d^2.
/-- Implementation lemma for `sum_ite_eq_eq_pow_div_sq`. -/
private theorem sum_ite_eq_eq_pow_div_sq' (hd : 1 ≤ d) (r : ℕ) {t t' : Fin r} (htt : t ≠ t')
    (i : Fin d) :
    (∑ c : Fin r → Fin d, (if c t = i ∧ c t' = i then (1 : ℝ) else 0)) = (d : ℝ) ^ r / d ^ 2 := by
  have hr2 : 2 ≤ r := by
    by_contra hcon
    push Not at hcon
    have h1 := t.isLt
    have h2 := t'.isLt
    exact htt (Fin.ext (by omega))
  have hne : (d : ℝ) ≠ 0 := by
    have hd0 : 0 < d := by omega
    exact_mod_cast (ne_of_gt hd0)
  have hidx : Fintype.card {x : Fin r // x ≠ t ∧ x ≠ t'} = r - 2 := by
    rw [Fintype.card_subtype]
    have h1 : (Finset.univ.filter (fun x : Fin r => x ≠ t ∧ x ≠ t'))
        = Finset.univ \ ({t, t'} : Finset (Fin r)) := by
      ext x
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_sdiff,
        Finset.mem_insert, Finset.mem_singleton, not_or]
    have hpair : ({t, t'} : Finset (Fin r)).card = 2 := by
      rw [Finset.card_insert_of_notMem (by simpa using htt), Finset.card_singleton]
    rw [h1, Finset.card_sdiff, Finset.inter_univ, Finset.card_univ, Fintype.card_fin, hpair]
  have hcard : Fintype.card {c : Fin r → Fin d // c t = i ∧ c t' = i} = d ^ (r - 2) := by
    let e : {c : Fin r → Fin d // c t = i ∧ c t' = i} ≃
        ({x : Fin r // x ≠ t ∧ x ≠ t'} → Fin d) :=
      { toFun := fun c x => c.1 x.1
        invFun := fun f => ⟨fun x => if h : x ≠ t ∧ x ≠ t' then f ⟨x, h⟩ else i,
          ⟨by change (if h : t ≠ t ∧ t ≠ t' then f ⟨t, h⟩ else i) = i
              rw [dif_neg (fun h => h.1 rfl)],
           by change (if h : t' ≠ t ∧ t' ≠ t' then f ⟨t', h⟩ else i) = i
              rw [dif_neg (fun h => h.2 rfl)]⟩⟩
        left_inv := fun c => by
          apply Subtype.ext
          funext x
          change (if h : x ≠ t ∧ x ≠ t' then c.1 x else i) = c.1 x
          by_cases h : x ≠ t ∧ x ≠ t'
          · rw [dif_pos h]
          · rw [dif_neg h]
            rcases not_and_or.mp h with h1 | h1
            · rw [not_not.mp h1]
              exact c.2.1.symm
            · rw [not_not.mp h1]
              exact c.2.2.symm
        right_inv := fun f => by
          funext y
          change (if h : (y : Fin r) ≠ t ∧ (y : Fin r) ≠ t' then f ⟨(y : Fin r), h⟩ else i) = f y
          rw [dif_pos y.2] }
    rw [Fintype.card_congr e, Fintype.card_fun, Fintype.card_fin, hidx]
  rw [Finset.sum_boole]
  rw [← Fintype.card_subtype (fun c : Fin r → Fin d => c t = i ∧ c t' = i), hcard,
    Nat.cast_pow, pow_sub₀ (d : ℝ) hne hr2, div_eq_mul_inv]

/-- The two-coordinate fibre count: for distinct `t ≠ t'`, `∑_c (if c t = i ∧ c t' = i then 1
else 0) = d^r / d^2`. -/
private theorem sum_ite_eq_eq_pow_div_sq (hd : 1 ≤ d) (r : ℕ) {t t' : Fin r} (htt : t ≠ t')
    (i : Fin d) :
    ∑ c : Fin r → Fin d, (if c t = i ∧ c t' = i then (1 : ℝ) else 0) = (d : ℝ) ^ r / d ^ 2 := by
  exact sum_ite_eq_eq_pow_div_sq' hd r htt i


-- Chebyshev input: expand (cnt - r/d)^2 with cnt = ∑_t 1{c t = i} (unfold cnt, Nat.cast_sum),
-- Finset.sum_comm, sum_ite_eq_eq_pow_div, sum_ite_eq_eq_pow_div_sq (diagonal t = t' separately:
-- ite_and, Finset.sum_ite_eq);
-- result d^r (r/d)(1 - 1/d) ≤ d^r r/d.  SPLIT?
/-- A Chebyshev-type second-moment bound: `∑_c (cnt c i - r/d)^2 ≤ d^r * r / d`, from the one-
and two-coordinate fibre counts. -/
private theorem sum_sq_cnt_sub_div_le (hd : 1 ≤ d) (r : ℕ) (i : Fin d) :
    ∑ c : Fin r → Fin d, ((cnt c i : ℝ) - r / d) ^ 2 ≤ (d : ℝ) ^ r * r / d := by
  have hdR : (0 : ℝ) < (d : ℝ) := (by
    exact_mod_cast (Nat.lt_of_lt_of_le Nat.zero_lt_one hd))
  have hdne : (d : ℝ) ≠ 0 := ne_of_gt hdR
  have hcard : (Fintype.card (Fin r → Fin d) : ℝ) = (d : ℝ) ^ r := (by
    rw [Fintype.card_fun, Fintype.card_fin, Fintype.card_fin]
    push_cast
    ring)
  set X : (Fin r → Fin d) → Fin r → ℝ := (fun c t => if c t = i then (1 : ℝ) else 0) with hX
  have hcnt : ∀ c : Fin r → Fin d, (cnt c i : ℝ) = ∑ t : Fin r, X c t := (by
    intro c
    unfold cnt
    rw [Nat.cast_sum]
    refine Finset.sum_congr rfl (fun t _ => ?_)
    by_cases h : c t = i <;> simp [hX, h])
  have hterm : ∀ c : Fin r → Fin d, ((cnt c i : ℝ) - r / d) = ∑ t : Fin r, (X c t - 1 / d) := (by
    intro c
    rw [hcnt c, Finset.sum_sub_distrib]
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    ring)
  have hS1 : ∀ t : Fin r, ∑ c : Fin r → Fin d, X c t = (d : ℝ) ^ r / d := (by
    intro t
    simp only [hX]
    exact sum_ite_eq_eq_pow_div hd r t i)
  have hXX : ∀ (t t' : Fin r) (c : Fin r → Fin d),
      X c t * X c t' = (if c t = i ∧ c t' = i then (1 : ℝ) else 0) := (by
    intro t t' c
    by_cases h1 : c t = i <;> by_cases h2 : c t' = i <;> simp [hX, h1, h2])
  have hZ2off : ∀ t t' : Fin r, t' ≠ t →
      ∑ c : Fin r → Fin d, (X c t - 1 / d) * (X c t' - 1 / d) = 0 := (by
    intro t t' hne
    have hexp : ∀ c : Fin r → Fin d,
        (X c t - 1 / d) * (X c t' - 1 / d)
          = X c t * X c t' - (1 / d) * X c t - (1 / d) * X c t' + (1 / d) ^ 2 := (by
      intro c
      ring)
    have hsum1 : ∑ c : Fin r → Fin d, (X c t - 1 / d) * (X c t' - 1 / d)
        = ∑ c : Fin r → Fin d,
            (X c t * X c t' - (1 / d) * X c t - (1 / d) * X c t' + (1 / d) ^ 2) :=
      Finset.sum_congr rfl (fun c _ => hexp c)
    rw [hsum1, Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_sub_distrib]
    rw [← Finset.mul_sum, ← Finset.mul_sum]
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, hcard]
    have hsum2 : ∑ c : Fin r → Fin d, X c t * X c t'
        = ∑ c : Fin r → Fin d, (if c t = i ∧ c t' = i then (1 : ℝ) else 0) :=
      Finset.sum_congr rfl (fun c _ => hXX t t' c)
    rw
        [hsum2, sum_ite_eq_eq_pow_div_sq (t := t) (t' := t') hd r (fun h => hne h.symm) i, hS1 t,
            hS1 t']
    field_simp
    ring)
  have hZd : ∀ t : Fin r, ∑ c : Fin r → Fin d, (X c t - 1 / d) * (X c t - 1 / d)
      = (d : ℝ) ^ r * ((d : ℝ) - 1) / d ^ 2 := (by
    intro t
    have hpt : ∀ c : Fin r → Fin d,
        (X c t - 1 / d) * (X c t - 1 / d) = (1 - 2 / d) * X c t + (1 / d) ^ 2 := (by
      intro c
      by_cases h : c t = i <;> simp [hX, h] <;> ring)
    have hsum1 : ∑ c : Fin r → Fin d, (X c t - 1 / d) * (X c t - 1 / d)
        = ∑ c : Fin r → Fin d, ((1 - 2 / d) * X c t + (1 / d) ^ 2) :=
      Finset.sum_congr rfl (fun c _ => hpt c)
    rw [hsum1, Finset.sum_add_distrib, ← Finset.mul_sum]
    rw [hS1 t, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, hcard]
    field_simp
    ring)
  have hfinal : (r : ℝ) * ((d : ℝ) ^ r * ((d : ℝ) - 1) / d ^ 2) ≤ (d : ℝ) ^ r * r / d := (by
    have h1 : ((d : ℝ) - 1) / d ^ 2 ≤ 1 / d := (by
      field_simp
      nlinarith [hdR, pow_pos hdR 2])
    calc (r : ℝ) * ((d : ℝ) ^ r * ((d : ℝ) - 1) / d ^ 2)
        = ((r : ℝ) * (d : ℝ) ^ r) * (((d : ℝ) - 1) / d ^ 2) := (by ring)
      _ ≤ ((r : ℝ) * (d : ℝ) ^ r) * (1 / d) :=
          mul_le_mul_of_nonneg_left h1 (mul_nonneg (Nat.cast_nonneg r) (le_of_lt (pow_pos hdR r)))
      _ = (d : ℝ) ^ r * r / d := (by ring))
  have e1 : ∑ c : Fin r → Fin d, ((cnt c i : ℝ) - r / d) ^ 2
      = ∑ c : Fin r → Fin d, (∑ t : Fin r, (X c t - 1 / d)) ^ 2 := (by
    refine Finset.sum_congr rfl (fun c _ => ?_)
    rw [hterm c])
  have e2 : ∑ c : Fin r → Fin d, (∑ t : Fin r, (X c t - 1 / d)) ^ 2
      = ∑ c : Fin r → Fin d, ∑ t : Fin r, ∑ t' : Fin r,
          (X c t - 1 / d) * (X c t' - 1 / d) := (by
    refine Finset.sum_congr rfl (fun c _ => ?_)
    rw [pow_two]
    exact Finset.sum_mul_sum Finset.univ Finset.univ
      (fun t => (X c t - 1 / d)) (fun t' => (X c t' - 1 / d)))
  have e3 : ∑ c : Fin r → Fin d, ∑ t : Fin r, ∑ t' : Fin r,
          (X c t - 1 / d) * (X c t' - 1 / d)
      = ∑ t : Fin r, ∑ t' : Fin r, ∑ c : Fin r → Fin d,
          (X c t - 1 / d) * (X c t' - 1 / d) := (by
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl (fun t _ => Finset.sum_comm))
  have e4 : ∑ t : Fin r, ∑ t' : Fin r, ∑ c : Fin r → Fin d,
          (X c t - 1 / d) * (X c t' - 1 / d)
      = ∑ t : Fin r, (d : ℝ) ^ r * ((d : ℝ) - 1) / d ^ 2 := (by
    refine Finset.sum_congr rfl (fun t _ => ?_)
    have hkey : ∀ t' : Fin r, (∑ c : Fin r → Fin d,
          (X c t - 1 / d) * (X c t' - 1 / d))
        = if t' = t then (d : ℝ) ^ r * ((d : ℝ) - 1) / d ^ 2 else 0 := (by
      intro t'
      by_cases h : t' = t
      · rw [h, if_pos rfl]; exact hZd t
      · rw [if_neg h]; exact hZ2off t t' h)
    have hsum : ∑ t' : Fin r, ∑ c : Fin r → Fin d,
          (X c t - 1 / d) * (X c t' - 1 / d)
        = ∑ t' : Fin r, (if t' = t then (d : ℝ) ^ r * ((d : ℝ) - 1) / d ^ 2 else 0) :=
      Finset.sum_congr rfl (fun t' _ => hkey t')
    rw [hsum, Finset.sum_ite_eq']
    simp)
  have e5 : ∑ t : Fin r, (d : ℝ) ^ r * ((d : ℝ) - 1) / d ^ 2
      = (r : ℝ) * ((d : ℝ) ^ r * ((d : ℝ) - 1) / d ^ 2) := (by
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul])
  rw [e1, e2, e3, e4, e5]
  exact hfinal


-- Balanced schedules carry at least half the mass for r ≥ 8 d^2:
-- 1{∃ i, cnt c i < r/(2d)} ≤ ∑_i (cnt c i - r/d)^2 / (r/(2d))^2 (for such i, r/d - cnt ≥ r/(2d));
-- sum over c with sum_sq_cnt_sub_div_le: ≤ d · d^r (r/d) (2d/r)^2 = 4 d^2 d^r / r ≤ d^r/2.  SPLIT?
/-- For `r ≥ 8d^2`, at most half the schedules `c : Fin r → Fin d` have some coordinate count
`cnt c i` below `r/(2d)`, by Chebyshev's inequality applied to `sum_sq_cnt_sub_div_le`. -/
private theorem sum_ite_exists_cnt_lt_le_half_pow (hd : 1 ≤ d) (r : ℕ) (hr : 8 * d ^ 2 ≤ r) :
    ∑ c : Fin r → Fin d, (if ∃ i, (cnt c i : ℝ) < r / (2 * d) then (1 : ℝ) else 0)
      ≤ (d : ℝ) ^ r / 2 := by
  have hd0 : 0 < d := (Nat.lt_of_lt_of_le Nat.zero_lt_one hd)
  have hdR : (0 : ℝ) < (d : ℝ) := (Nat.cast_pos.mpr hd0)
  have hr0 : 0 < r := (lt_of_lt_of_le (Nat.mul_pos (by norm_num) (pow_pos hd0 2)) hr)
  have hrR : (0 : ℝ) < (r : ℝ) := (Nat.cast_pos.mpr hr0)
  have h2d : (0 : ℝ) < 2 * (d : ℝ) := (by linarith)
  have hden : (0 : ℝ) < r / (2 * d) := (div_pos hrR h2d)
  have hden2 : (0 : ℝ) < (r / (2 * d)) ^ 2 := (pow_pos hden 2)
  have h8 : 8 * (d : ℝ) ^ 2 ≤ (r : ℝ) := (by
    have hcast : ((8 * d ^ 2 : ℕ) : ℝ) ≤ ((r : ℕ) : ℝ) := (Nat.cast_le.mpr hr)
    have hpush : ((8 * d ^ 2 : ℕ) : ℝ) = 8 * (d : ℝ) ^ 2 := (by push_cast; ring)
    rw [hpush] at hcast
    exact hcast)
  have hs2 : ∑ i : Fin d, ∑ c : Fin r → Fin d, ((cnt c i : ℝ) - r / d) ^ 2 / (r / (2 * d)) ^ 2
      ≤ (d : ℝ) * (((d : ℝ) ^ r * (r : ℝ) / (d : ℝ)) / (r / (2 * d)) ^ 2) := (by
    have hY : ∀ i : Fin d,
        ∑ c : Fin r → Fin d, ((cnt c i : ℝ) - r / d) ^ 2 / (r / (2 * d)) ^ 2
          ≤ ((d : ℝ) ^ r * (r : ℝ) / (d : ℝ)) / (r / (2 * d)) ^ 2 := (by
      intro i
      rw [← Finset.sum_div]
      exact div_le_div_of_nonneg_right (sum_sq_cnt_sub_div_le hd r i) (le_of_lt hden2))
    calc ∑ i : Fin d, ∑ c : Fin r → Fin d, ((cnt c i : ℝ) - r / d) ^ 2 / (r / (2 * d)) ^ 2
        ≤ ∑ _i : Fin d, ((d : ℝ) ^ r * (r : ℝ) / (d : ℝ)) / (r / (2 * d)) ^ 2 :=
          Finset.sum_le_sum (fun i _ => hY i)
      _ = (d : ℝ) * (((d : ℝ) ^ r * (r : ℝ) / (d : ℝ)) / (r / (2 * d)) ^ 2) :=
          (by rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]))
  have hs3 : (d : ℝ) * (((d : ℝ) ^ r * (r : ℝ) / (d : ℝ)) / (r / (2 * d)) ^ 2)
      ≤ (d : ℝ) ^ r / 2 := (by
    have hnum : (d : ℝ) * (((d : ℝ) ^ r * (r : ℝ) / (d : ℝ)) / (r / (2 * d)) ^ 2)
        = 4 * (d : ℝ) ^ 2 * (d : ℝ) ^ r / (r : ℝ) := (by field_simp; ring)
    rw [hnum, div_le_iff₀ hrR]
    have h4 : 4 * (d : ℝ) ^ 2 ≤ (r : ℝ) / 2 := (by
      calc 4 * (d : ℝ) ^ 2 = (8 * (d : ℝ) ^ 2) / 2 := (by ring)
        _ ≤ (r : ℝ) / 2 := div_le_div_of_nonneg_right h8 (by norm_num))
    have h5 : 4 * (d : ℝ) ^ 2 * (d : ℝ) ^ r ≤ ((r : ℝ) / 2) * (d : ℝ) ^ r :=
      mul_le_mul_of_nonneg_right h4 (pow_nonneg (le_of_lt hdR) r)
    have h6 : ((r : ℝ) / 2) * (d : ℝ) ^ r = (d : ℝ) ^ r / 2 * (r : ℝ) := (by ring)
    rw [← h6]
    exact h5)
  calc ∑ c : Fin r → Fin d, (if ∃ i, (cnt c i : ℝ) < r / (2 * d) then (1 : ℝ) else 0)
      ≤ ∑ c : Fin r → Fin d, ∑ i : Fin d, ((cnt c i : ℝ) - r / d) ^ 2 / (r / (2 * d)) ^ 2 := (by
        apply Finset.sum_le_sum
        intro c _
        by_cases h : ∃ i, (cnt c i : ℝ) < r / (2 * d)
        · obtain ⟨i₀, hi₀⟩ := h
          rw [if_pos ⟨i₀, hi₀⟩]
          have hsingle := Finset.single_le_sum (s := Finset.univ)
            (f := fun i : Fin d => ((cnt c i : ℝ) - r / d) ^ 2 / (r / (2 * d)) ^ 2)
            (fun i _ => div_nonneg (sq_nonneg _) (le_of_lt hden2)) (Finset.mem_univ i₀)
          have h1 : (1 : ℝ) ≤ ((cnt c i₀ : ℝ) - r / d) ^ 2 / (r / (2 * d)) ^ 2 := (by
            rw [le_div_iff₀ hden2, one_mul]
            have hsum : r / (2 * d) + (cnt c i₀ : ℝ) ≤ r / d := (by
              calc r / (2 * d) + (cnt c i₀ : ℝ) ≤ r / (2 * d) + r / (2 * d) :=
                    add_le_add_right (le_of_lt hi₀) _
                _ = 2 * (r / (2 * d)) := (two_mul _).symm
                _ = r / d := (by field_simp))
            have hb : r / (2 * d) ≤ r / d - (cnt c i₀ : ℝ) := ((le_sub_iff_add_le).mpr hsum)
            have h2 : (r / (2 * d)) ^ 2 ≤ (r / d - (cnt c i₀ : ℝ)) ^ 2 :=
              pow_le_pow_left₀ (le_of_lt hden) hb 2
            rw [show ((cnt c i₀ : ℝ) - r / d) ^ 2 = (r / d - (cnt c i₀ : ℝ)) ^ 2 by ring]
            exact h2)
          exact le_trans h1 hsingle
        · rw [if_neg h]
          exact Finset.sum_nonneg (fun i _ => div_nonneg (sq_nonneg _) (le_of_lt hden2)))
    _ = ∑ i : Fin d, ∑ c : Fin r → Fin d, ((cnt c i : ℝ) - r / d) ^ 2 / (r / (2 * d)) ^ 2 :=
        (by rw [Finset.sum_comm])
    _ ≤ (d : ℝ) * (((d : ℝ) ^ r * (r : ℝ) / (d : ℝ)) / (r / (2 * d)) ^ 2) := hs2
    _ ≤ (d : ℝ) ^ r / 2 := hs3


-- Per-schedule bound: K (cnt c) w = ∏_i P1 (cnt c i) (w i) (unfold K); each factor
-- ≥ c/√(cnt c i) ≥ c/(√2 s) by the 1D bound (hP1) since cnt c i ≥ m₀,
-- |w i| ≤ graphNorm w ≤ s ≤ A √(cnt c i) (A = √(2d), cnt ≥ n/(2d) ≥ s²/(2d)), cnt ≤ n ≤ 2 s²;
-- Finset.prod_le_prod, Finset.prod_const, card_univ.  SPLIT?
/-- For a schedule `c` whose every coordinate count is balanced (at least `n/(2d)` and at least
`m₀`), the product kernel `K (cnt c) w` is at least `(c₁/(√2 s))^d`, from the 1D bound
applied to each coordinate. -/
private theorem const_div_pow_le_prod_P1 (hd : 1 ≤ d) (c₁ : ℝ) (hc₁ : 0 < c₁) (m₀ : ℕ)
    (hP1 : ∀ m : ℕ, m₀ ≤ m → ∀ k : ℤ, |(k : ℝ)| ≤ Real.sqrt (2 * d) * Real.sqrt (m : ℝ) →
      c₁ / Real.sqrt (m : ℝ) ≤ P1 m k)
    (s n : ℕ) (hs : 1 ≤ s) (hn1 : s ^ 2 ≤ n) (hn2 : n ≤ 2 * s ^ 2) (w : Site d)
    (hw : graphNorm w ≤ s) (c : Fin n → Fin d)
    (hc : ∀ i, (n : ℝ) / (2 * d) ≤ cnt c i) (hm₀ : ∀ i, m₀ ≤ cnt c i) :
    (c₁ / (Real.sqrt 2 * s)) ^ d ≤ K (cnt c) w := by
  have hdR : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd
  have hsR : (0 : ℝ) < (s : ℝ) := by exact_mod_cast hs
  have h2d : (0 : ℝ) < 2 * (d : ℝ) := by positivity
  have hn1R : (1 : ℝ) ≤ (n : ℝ) := by
    have hs1 : (1 : ℝ) ≤ (s : ℝ) := by exact_mod_cast hs
    have hs21 : (1 : ℝ) ≤ (s : ℝ) ^ 2 := by
      have h1 : (0 : ℝ) ≤ (s : ℝ) - 1 := by linarith
      have h2 : (0 : ℝ) ≤ (s : ℝ) + 1 := by linarith
      nlinarith [mul_nonneg h1 h2]
    have hs2n : (s : ℝ) ^ 2 ≤ (n : ℝ) := by exact_mod_cast hn1
    linarith
  have hbase : (0 : ℝ) < (n : ℝ) / (2 * (d : ℝ)) := by
    have h1 : (1 : ℝ) / (2 * (d : ℝ)) ≤ (n : ℝ) / (2 * (d : ℝ)) :=
      div_le_div_of_nonneg_right hn1R h2d.le
    have hpos : (0 : ℝ) < 1 / (2 * (d : ℝ)) := by positivity
    linarith
  have hprod : ∀ i : Fin d, c₁ / (Real.sqrt 2 * (s : ℝ)) ≤ P1 (cnt c i) (w i) := by
    intro i
    have hcnt_ub : (cnt c i : ℝ) ≤ 2 * (s : ℝ) ^ 2 := by
      have h1 : (cnt c i : ℝ) ≤ (n : ℝ) := by exact_mod_cast cnt_le c i
      have h2 : (n : ℝ) ≤ 2 * (s : ℝ) ^ 2 := by exact_mod_cast hn2
      linarith
    have hsqrt_ub : Real.sqrt (cnt c i : ℝ) ≤ Real.sqrt 2 * (s : ℝ) := by
      have h := Real.sqrt_le_sqrt hcnt_ub
      rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2) ((s : ℝ) ^ 2), Real.sqrt_sq hsR.le] at h
      exact h
    have hcnt_pos : 0 < (cnt c i : ℝ) := lt_of_lt_of_le hbase (hc i)
    have hsqr : 0 < Real.sqrt (cnt c i : ℝ) := by
      rw [Real.sqrt_pos]; exact hcnt_pos
    have hnle : (n : ℝ) ≤ 2 * (d : ℝ) * (cnt c i : ℝ) :=
      calc (n : ℝ) ≤ (cnt c i : ℝ) * (2 * (d : ℝ)) := (div_le_iff₀ h2d).mp (hc i)
        _ = 2 * (d : ℝ) * (cnt c i : ℝ) := by ring
    have h2dcnt : (s : ℝ) ^ 2 ≤ 2 * (d : ℝ) * (cnt c i : ℝ) := by
      have hs2n : (s : ℝ) ^ 2 ≤ (n : ℝ) := by exact_mod_cast hn1
      linarith
    have hs_le : (s : ℝ) ≤ Real.sqrt (2 * d) * Real.sqrt (cnt c i : ℝ) := by
      have h := Real.sqrt_le_sqrt h2dcnt
      rw [Real.sqrt_sq hsR.le,
        Real.sqrt_mul (by positivity : (0 : ℝ) ≤ 2 * (d : ℝ)) (cnt c i : ℝ)] at h
      exact h
    have hwi : |((w i : ℤ) : ℝ)| ≤ Real.sqrt (2 * d) * Real.sqrt (cnt c i : ℝ) := by
      have hsingle_nat : (w i).natAbs ≤ graphNorm w := by
        rw [graphNorm]
        exact Finset.single_le_sum (f := fun j : Fin d => (w j).natAbs) (fun j _ => Nat.zero_le _)
          (Finset.mem_univ i)
      have hwabs : ((w i).natAbs : ℝ) ≤ (s : ℝ) := by
        exact_mod_cast le_trans hsingle_nat hw
      have hAbs : ((w i).natAbs : ℝ) = |((w i : ℤ) : ℝ)| := by
        rw [Nat.cast_natAbs, Int.cast_abs]
      calc |((w i : ℤ) : ℝ)| = ((w i).natAbs : ℝ) := hAbs.symm
        _ ≤ (s : ℝ) := hwabs
        _ ≤ Real.sqrt (2 * d) * Real.sqrt (cnt c i : ℝ) := hs_le
    have h1 : c₁ / (Real.sqrt 2 * (s : ℝ)) ≤ c₁ / Real.sqrt (cnt c i : ℝ) :=
      div_le_div_of_nonneg_left hc₁.le hsqr hsqrt_ub
    exact le_trans h1 (hP1 (cnt c i) (hm₀ i) (w i) hwi)
  have hconst : (∏ _i : Fin d, (c₁ / (Real.sqrt 2 * (s : ℝ))))
      = (c₁ / (Real.sqrt 2 * (s : ℝ))) ^ d := by
    rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  unfold K
  rw [← hconst]
  refine Finset.prod_le_prod (fun i _ => ?_) (fun i _ => hprod i)
  exact div_nonneg hc₁.le (le_of_lt (mul_pos (Real.sqrt_pos.mpr (by norm_num)) hsR))


-- Pointwise: by_cases on the `∃ i, ...` (if_pos: sub_self, mul_zero, hF0 c; if_neg: sub_zero,
-- mul_one, push_neg gives ∀ i, n/(2d) ≤ cnt c i, then hβ c).
/-- Pointwise comparison used to restrict a nonnegative-weighted sum to balanced schedules: `β *
(1 - indicator of unbalanced) ≤ F c`. -/
private theorem le_of_forall_cnt_ge_of_nonneg (n : ℕ) (F : (Fin n → Fin d) → ℝ) (hF0 : ∀ c, 0 ≤ F c)
    (β : ℝ)
    (hβ : ∀ c : Fin n → Fin d, (∀ i, (n : ℝ) / (2 * d) ≤ cnt c i) → β ≤ F c)
    (c : Fin n → Fin d) :
    β * (1 - if ∃ i, (cnt c i : ℝ) < n / (2 * d) then (1 : ℝ) else 0) ≤ F c := by
  by_cases h : ∃ i, (cnt c i : ℝ) < n / (2 * d)
  · rw [if_pos h, sub_self, mul_zero]
    exact hF0 c
  · rw [if_neg h, sub_zero, mul_one]
    exact hβ c (fun i => le_of_not_gt (fun hi => h ⟨i, hi⟩))

-- Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fun, Fintype.card_fin,
-- nsmul_eq_mul, Nat.cast_pow (∑ 1 = d^n); sum_ite_exists_cnt_lt_le_half_pow hd n hn; linarith.
/-- At least half the mass `d^n/2` is carried by balanced schedules, for `n ≥ 8d^2`. -/
private theorem pow_div_two_le_sum_one_sub_ite (hd : 1 ≤ d) (n : ℕ) (hn : 8 * d ^ 2 ≤ n) :
    (d : ℝ) ^ n / 2 ≤ ∑ c : Fin n → Fin d,
      (1 - if ∃ i, (cnt c i : ℝ) < n / (2 * d) then (1 : ℝ) else 0) := by
  have hsum : ∑ c : Fin n → Fin d,
      (1 - (if ∃ i, (cnt c i : ℝ) < n / (2 * d) then (1 : ℝ) else 0))
      = (d : ℝ) ^ n - ∑ c : Fin n → Fin d,
          (if ∃ i, (cnt c i : ℝ) < n / (2 * d) then (1 : ℝ) else 0) := by
    rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fun,
      Fintype.card_fin]
    simp [nsmul_eq_mul]
  rw [hsum]
  linarith [sum_ite_exists_cnt_lt_le_half_pow hd n hn]

-- mul_le_mul_of_nonneg_left (pow_div_two_le_sum_one_sub_ite) hβ0, Finset.mul_sum,
-- Finset.sum_le_sum with le_of_forall_cnt_ge_of_nonneg.
/-- Combines `pow_div_two_le_sum_one_sub_ite` with the pointwise bound
`le_of_forall_cnt_ge_of_nonneg` to lower-bound `∑_c F c` by `β * (d^n/2)`. -/
private theorem mul_pow_div_two_le_sum (hd : 1 ≤ d) (n : ℕ) (hn : 8 * d ^ 2 ≤ n)
    (F : (Fin n → Fin d) → ℝ) (hF0 : ∀ c, 0 ≤ F c) (β : ℝ) (hβ0 : 0 ≤ β)
    (hβ : ∀ c : Fin n → Fin d, (∀ i, (n : ℝ) / (2 * d) ≤ cnt c i) → β ≤ F c) :
    β * ((d : ℝ) ^ n / 2) ≤ ∑ c : Fin n → Fin d, F c := by
  have h2 := mul_le_mul_of_nonneg_left (pow_div_two_le_sum_one_sub_ite hd n hn) hβ0
  rw [Finset.mul_sum] at h2
  exact le_trans h2 (Finset.sum_le_sum (fun c _ => le_of_forall_cnt_ge_of_nonneg n F hF0 β hβ c))

-- iterate_delta0_eq (0 < d), le_div_iff₀ (pow_pos), mul_pow_div_two_le_sum with
-- F := fun c => K (cnt c) w (K_nonneg); linarith / ring.
/-- Applies `mul_pow_div_two_le_sum` to `F c = K (cnt c) w` to lower-bound `Q^[n] delta0 w` by
`β/2`. -/
private theorem div_two_le_iterate_Q_delta0 (hd : 1 ≤ d) (n : ℕ) (hn : 8 * d ^ 2 ≤ n) (w : Site d)
    (β : ℝ)
    (hβ0 : 0 ≤ β)
    (hβ : ∀ c : Fin n → Fin d, (∀ i, (n : ℝ) / (2 * d) ≤ cnt c i) → β ≤ K (cnt c) w) :
    β / 2 ≤ Q^[n] (delta0 : Site d → ℝ) w := by
  rw [iterate_delta0_eq (by omega : 0 < d) n w]
  rw [le_div_iff₀ (by positivity : (0 : ℝ) < (d : ℝ) ^ n)]
  have h := mul_pow_div_two_le_sum hd n hn (fun c => K (cnt c) w)
    (fun c => K_nonneg (cnt c) w) β hβ0 hβ
  nlinarith

-- s ≤ s ^ 2 (Nat.le_self_pow two_ne_zero s); omega / le_trans.
/-- If `s ≥ 2dm₀ + 8d^2 + 1` and `s^2 ≤ n`, then `8d^2 ≤ n`. -/
private theorem le_of_sq_le_sq_add (m₀ s n : ℕ) (hs : 2 * d * m₀ + 8 * d ^ 2 + 1 ≤ s)
    (hn : s ^ 2 ≤ n) :
    8 * d ^ 2 ≤ n := by
  have h1 : 8 * d ^ 2 ≤ s := by omega
  have h2 : s ≤ s ^ 2 := by
    cases s with
    | zero => simp
    | succ k => nlinarith
  omega

-- 2 d m₀ ≤ s ≤ s ^ 2 ≤ n (Nat.le_self_pow), cast (Nat.cast_le, push_cast):
-- m₀ ≤ n/(2d) (le_div_iff₀) ≤ k; Nat.cast_le.mp.
/-- Under the scale hypotheses `s^2 ≤ n` and `s` large, a coordinate count `k` with `n/(2d) ≤ k`
satisfies `m₀ ≤ k`. -/
private theorem le_cnt_of_sq_le (hd : 1 ≤ d) (m₀ s n k : ℕ) (hs : 2 * d * m₀ + 8 * d ^ 2 + 1 ≤ s)
    (hn : s ^ 2 ≤ n) (hk : (n : ℝ) / (2 * d) ≤ (k : ℝ)) : m₀ ≤ k := by
  have hdR : (0 : ℝ) < (d : ℝ) := by exact_mod_cast (Nat.lt_of_lt_of_le Nat.zero_lt_one hd)
  have h2d : (0 : ℝ) < 2 * (d : ℝ) := by linarith
  have hs1 : 2 * d * m₀ ≤ s := by omega
  have hs2 : s ≤ s ^ 2 := by nlinarith [Nat.zero_le s]
  have hmn : (2 * d * m₀ : ℝ) ≤ (n : ℝ) := by
    exact_mod_cast (le_trans hs1 (le_trans hs2 hn))
  have hm : (m₀ : ℝ) ≤ (n : ℝ) / (2 * d) := by
    rw [le_div_iff₀ h2d]
    linarith
  exact_mod_cast le_trans hm hk

-- div_mul_eq_div_div, div_pow; ring.
/-- Algebraic identity rewriting `(c₁/(√2 s))^d / 2` as `(c₁/√2)^d / 2 / s^d`. -/
private theorem div_sq_mul_pow_eq_div_pow (c₁ s : ℝ) :
    (c₁ / (Real.sqrt 2 * s)) ^ d / 2 = (c₁ / Real.sqrt 2) ^ d / 2 / s ^ d := by
  rw [div_pow, div_pow, mul_pow]
  rw [div_div, div_div]
  ring_nf

-- Free lazy near-diagonal lower bound.  iterate_delta0_eq; restrict the sum to balanced c
-- (Finset.sum_le_sum_of_subset_of_nonneg, K_nonneg), const_div_pow_le_prod_P1 on each, count ≥
-- d^n/2 by
-- sum_ite_exists_cnt_lt_le_half_pow (complement), s₀ large so that n ≥ 8d² and s²/(2d) ≥ m₀
-- (exists_const_le_P1_of_le_sqrt_mul, A = √(2d)).
-- c₀ := (c₁/√2)^d / 2.  SPLIT?
/-- The free lazy near-diagonal lower bound: there are `c₀ > 0` and `s₀` such that `c₀ / s^d ≤
Q^[n] delta0 w` whenever `s ≥ s₀`, `s^2 ≤ n ≤ 2s^2`, and `graphNorm w ≤ s`. -/
private theorem exists_const_le_iterate_Q_delta0_div_pow (hd : 1 ≤ d) :
    ∃ c₀ : ℝ, 0 < c₀ ∧ ∃ s₀ : ℕ, 1 ≤ s₀ ∧ ∀ s : ℕ, s₀ ≤ s → ∀ n : ℕ, s ^ 2 ≤ n → n ≤ 2 * s ^ 2 →
      ∀ w : Site d, graphNorm w ≤ s → c₀ / (s : ℝ) ^ d ≤ Q^[n] (delta0 : Site d → ℝ) w := by
  have hd0 : 0 < d := hd
  have hdR : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd0
  have hA : 0 < Real.sqrt (2 * (d : ℝ)) := Real.sqrt_pos.mpr (by linarith)
  obtain ⟨c₁, hc₁, m₀, _, hP1⟩ := exists_const_le_P1_of_le_sqrt_mul (Real.sqrt (2 * (d : ℝ))) hA
  have hsq2 : 0 < Real.sqrt 2 := Real.sqrt_pos.mpr two_pos
  refine ⟨(c₁ / Real.sqrt 2) ^ d / 2, div_pos (pow_pos (div_pos hc₁ hsq2) d) two_pos,
    2 * d * m₀ + 8 * d ^ 2 + 1, Nat.le_add_left 1 _, ?_⟩
  intro s hs n hn1 hn2 w hw
  have hs1 : 1 ≤ s := le_trans (Nat.le_add_left 1 _) hs
  have hn8 : 8 * d ^ 2 ≤ n := le_of_sq_le_sq_add m₀ s n hs hn1
  have hβ : ∀ c : Fin n → Fin d, (∀ i, (n : ℝ) / (2 * d) ≤ cnt c i) →
      (c₁ / (Real.sqrt 2 * s)) ^ d ≤ K (cnt c) w := fun c hc =>
    const_div_pow_le_prod_P1 hd c₁ hc₁ m₀ hP1 s n hs1 hn1 hn2 w hw c hc
      (fun i => le_cnt_of_sq_le hd m₀ s n (cnt c i) hs hn1 (hc i))
  have hβ0 : 0 ≤ (c₁ / (Real.sqrt 2 * (s : ℝ))) ^ d :=
    pow_nonneg (div_nonneg hc₁.le (mul_nonneg hsq2.le (Nat.cast_nonneg s))) d
  have h4 := div_two_le_iterate_Q_delta0 hd n hn8 w _ hβ0 hβ
  rw [div_sq_mul_pow_eq_div_pow] at h4
  exact h4

/-! ### F. Killed near-diagonal bound and chaining -/

-- Choice of M: M : ℕ with (M : ℝ)^d ≥ 2 C / c₀ (M := ⌈2C/c₀⌉₊ + 1, M^d ≥ M).
/-- There is `M ≥ 1` with `C / M^d ≤ c₀/2`, the arithmetic input for absorbing the off-diagonal
correction into the near-diagonal lower bound. -/
private theorem exists_nat_div_pow_le_half (hd : 1 ≤ d) (C c₀ : ℝ) (_unused_hC : 0 < C)
    (hc₀ : 0 < c₀) :
    ∃ M : ℕ, 1 ≤ M ∧ C / (M : ℝ) ^ d ≤ c₀ / 2 := by
  obtain ⟨M, hM⟩ := exists_nat_ge (max 1 (2 * C / c₀))
  have h1 : (1 : ℝ) ≤ (M : ℝ) := le_trans (le_max_left _ _) hM
  have h2 : 2 * C / c₀ ≤ (M : ℝ) := le_trans (le_max_right _ _) hM
  have h3 : 2 * C ≤ c₀ * (M : ℝ) := (mul_div_cancel₀ (2 * C) (ne_of_gt hc₀)).symm.trans_le
      (mul_le_mul_of_nonneg_left h2 (le_of_lt hc₀))
  have h4 : (M : ℝ) ≤ (M : ℝ) ^ d := le_self_pow₀ h1 (lt_of_lt_of_le Nat.zero_lt_one hd).ne'
  refine ⟨M, by exact_mod_cast h1, ?_⟩
  rw [div_le_iff₀ (pow_pos (lt_of_lt_of_le one_pos h1) d)]
  nlinarith [h3, h4, hc₀]


-- le_lazyKilled_of_forall_le with S := C/(M s)^d: for z ∉ B, graphNorm (z - b) > M s
-- (contrapositive of hB),
-- so iterate_Q_delta0_le_div_pow_of_le_graphNorm with r := M s gives Q^[j] δ₀(z - b) ≤ C/(Ms)^d;
-- exists_const_le_iterate_Q_delta0_div_pow at w := a - b;
-- exists_nat_div_pow_le_half: c₀/s^d - C/(M s)^d ≥ (c₀/2)/s^d (mul_pow, div_div).  c₁ := c₀/2, s₁
-- := s₀.
/-- Given `C/M^d ≤ c₀/2`, the off-diagonal correction at scale `Ms` satisfies `C/(Ms)^d ≤
(c₀/2)/s^d`. -/
private theorem div_mul_pow_le_half_div_pow (C M s c0 : ℝ) (d : ℕ) (hM : C / M ^ d ≤ c0 / 2)
    (hs : 0 < s) : C / (M * s) ^ d ≤ (c0 / 2) / s ^ d := by
  have hl : C / (M * s) ^ d = (C / M ^ d) * (1 / s ^ d) := by
    rw [div_eq_mul_inv, mul_pow, mul_inv]; ring
  have hr : (c0 / 2) / s ^ d = (c0 / 2) * (1 / s ^ d) := by
    rw [div_eq_mul_inv]; ring
  rw [hl, hr]
  exact mul_le_mul_of_nonneg_right hM (by positivity)

/-- Algebraic identity: `c₀/s^d - (c₀/2)/s^d = (c₀/2)/s^d`. -/
private theorem sub_div_pow_eq_half_div_pow (c0 s : ℝ) (d : ℕ) : c0 / s ^ d - (c0 / 2) / s ^ d =
    (c0 / 2) / s ^ d := by
  rw [div_sub_div_same]; ring

/-- The killed near-diagonal lower bound: there are `c₁ > 0`, `M`, `s₁` such that `c₁/s^d ≤
lazyKilled B n a b` once `graphNorm (a-b) ≤ s` and `B` contains everything within `Ms` of
`b`, from the free bound minus the off-diagonal correction. -/
private theorem exists_const_le_lazyKilled_div_pow (hd : 1 ≤ d) :
    ∃ c₁ : ℝ, 0 < c₁ ∧ ∃ M s₁ : ℕ, 1 ≤ M ∧ 1 ≤ s₁ ∧ ∀ s : ℕ, s₁ ≤ s → ∀ n : ℕ,
      s ^ 2 ≤ n → n ≤ 2 * s ^ 2 → ∀ (B : Finset (Site d)) (a b : Site d),
        graphNorm (a - b) ≤ s → (∀ z : Site d, graphNorm (z - b) ≤ M * s → z ∈ B) →
          c₁ / (s : ℝ) ^ d ≤ lazyKilled B n a b := by
  obtain ⟨C, hCpos, hC32⟩ := iterate_Q_delta0_le_div_pow_of_le_graphNorm hd
  obtain ⟨c0, hc0pos, s0, hs01, hc039⟩ := exists_const_le_iterate_Q_delta0_div_pow hd
  obtain ⟨M, hM1, hM⟩ := exists_nat_div_pow_le_half hd C c0 hCpos hc0pos
  refine ⟨c0 / 2, by linarith, M, max s0 1, hM1, le_max_right s0 1, ?_⟩
  intro s hs n hn1 hn2 B a b hab hB
  have hs1 : 1 ≤ s := le_trans (le_max_right s0 1) hs
  have hs0 : s0 ≤ s := le_trans (le_max_left s0 1) hs
  have hspos : (0 : ℝ) < (s : ℝ) := Nat.cast_pos.mpr (lt_of_lt_of_le Nat.zero_lt_one hs1)
  have hMs1 : 1 ≤ M * s := Nat.one_le_iff_ne_zero.mpr
    (Nat.mul_ne_zero (Nat.one_le_iff_ne_zero.mp hM1) (Nat.one_le_iff_ne_zero.mp hs1))
  have hcast : ((M * s : ℕ) : ℝ) = (M : ℝ) * (s : ℝ) := Nat.cast_mul M s
  have hSnonneg : (0 : ℝ) ≤ C / ((M : ℝ) * (s : ℝ)) ^ d :=
    div_nonneg (le_of_lt hCpos)
      (pow_nonneg (mul_nonneg (Nat.cast_nonneg M) (Nat.cast_nonneg s)) d)
  have hstep : ∀ j : ℕ, ∀ z : Site d, z ∉ B →
      Q^[j] (delta0 : Site d → ℝ) (z - b) ≤ C / ((M : ℝ) * (s : ℝ)) ^ d := fun j z hz => by
    have hnatgt : M * s < graphNorm (z - b) := Nat.lt_of_not_le (fun h => hz (hB z h))
    have hb := hC32 j (z - b) (M * s) hMs1 (le_of_lt hnatgt)
    rw [hcast] at hb
    exact hb
  have hS : ∀ j ≤ n, ∀ z : Site d, z ∉ B →
      Q^[j] (delta0 : Site d → ℝ) (z - b) ≤ C / ((M : ℝ) * (s : ℝ)) ^ d := fun j _ => hstep j
  have h29 := le_lazyKilled_of_forall_le hd B b (C / ((M : ℝ) * (s : ℝ)) ^ d) hSnonneg n hS a
  have h39 := hc039 s hs0 n hn1 hn2 (a - b) hab
  have hSle : C / ((M : ℝ) * (s : ℝ)) ^ d ≤ (c0 / 2) / (s : ℝ) ^ d :=
    div_mul_pow_le_half_div_pow C M (s : ℝ) c0 d hM hspos
  have hid := sub_div_pow_eq_half_div_pow c0 (s : ℝ) d
  linarith


-- One chaining step: f (k n + n) a b ≥ ∑_{z ∈ S} f (k n) a z * f n z b (hck) ≥ card S · β · α
-- (Finset.sum_le_sum, mul_le_mul, Finset.sum_const, nsmul_eq_mul).
/-- One chaining step: if `f` satisfies the Chapman-Kolmogorov super-additivity `hck` and is at
least `β`, `α` on `S` at times `p`, `n` respectively, then `|S| * β * α ≤ f (p+n) a b`. -/
private theorem card_mul_le_sum_add_of_forall_le (f : ℕ → Site d → Site d → ℝ)
    (hck : ∀ m n x y (S : Finset (Site d)), ∑ z ∈ S, f m x z * f n z y ≤ f (m + n) x y)
    (S : Finset (Site d)) (p n : ℕ) (a b : Site d) (α β : ℝ) (hα : 0 ≤ α) (hβ : 0 ≤ β)
    (h1 : ∀ z ∈ S, β ≤ f p a z) (h2 : ∀ z ∈ S, α ≤ f n z b) :
    (S.card : ℝ) * β * α ≤ f (p + n) a b := by
  have hterm : ∀ z : Site d, z ∈ S → β * α ≤ f p a z * f n z b := fun z hz => mul_le_mul (h1 z hz)
      (h2 z hz) hα (le_trans hβ (h1 z hz))
  have hsum : (∑ z ∈ S, β * α) = (S.card : ℝ) * β * α := (Finset.sum_const (β * α)).trans
      ((nsmul_eq_mul (S.card) (β * α)).trans (mul_assoc _ _ _).symm)
  rw [← hsum]
  exact le_trans (Finset.sum_le_sum hterm) (hck p n a b S)


-- Chaining.  Induction on k from 1 (Nat.le_induction): k = 1 is hlink 0; step k → k+1 uses
-- card_mul_le_sum_add_of_forall_le with S := S k, p := k n (so (k+1) n = k n + n, Nat.succ_mul), β
-- := α^k σ^(k-1),
-- card ≥ σ (hcard k, 0 < k < N); pow_succ.
/-- Implementation lemma for `pow_mul_pow_sub_one_le_chain`. -/
private theorem pow_mul_pow_sub_one_le_chain' {d : ℕ} (f : ℕ → Site d → Site d → ℝ)
    (hck : ∀ m n x y (S : Finset (Site d)), ∑ z ∈ S, f m x z * f n z y ≤ f (m + n) x y)
    (S : ℕ → Finset (Site d)) (n N : ℕ) (α σ : ℝ) (hα : 0 ≤ α) (hσ : 0 ≤ σ)
    (hcard : ∀ i, 0 < i → i < N → σ ≤ ((S i).card : ℝ))
    (hlink : ∀ i < N, ∀ a ∈ S i, ∀ b ∈ S (i + 1), α ≤ f n a b) :
    ∀ k, 1 ≤ k → k ≤ N → ∀ a ∈ S 0, ∀ b ∈ S k, α ^ k * σ ^ (k - 1) ≤ f (k * n) a b := by
  intro k hk1
  induction k, hk1 using Nat.le_induction with
  | base =>
      intro hkN a ha b hb
      simpa using hlink 0 (by omega) a ha b hb
  | succ j hj ih =>
      intro hkN a ha b hb
      have hlt : j < N := by omega
      have hcardge : σ ≤ ((S j).card : ℝ) := hcard j (by omega) hlt
      have hBnn : 0 ≤ α ^ j * σ ^ (j - 1) :=
        mul_nonneg (pow_nonneg hα j) (pow_nonneg hσ (j - 1))
      have hstep42 := card_mul_le_sum_add_of_forall_le f hck (S j) (j * n) n a b α
          (α ^ j * σ ^ (j - 1)) hα hBnn
        (fun z hz => ih (by omega) a ha z hz)
        (fun z hz => hlink j hlt z hz b hb)
      have hstep42' : ((S j).card : ℝ) * (α ^ j * σ ^ (j - 1)) * α ≤ f ((j + 1) * n) a b := by
        simpa [Nat.succ_mul] using hstep42
      have hle1 : α ^ (j + 1) * σ ^ j
          ≤ ((S j).card : ℝ) * (α ^ j * σ ^ (j - 1)) * α := by
        have hσpow : σ ^ j = σ ^ (j - 1) * σ := by
          rw [← pow_succ, show j - 1 + 1 = j from by omega]
        rw [pow_succ, hσpow]
        calc α ^ j * α * (σ ^ (j - 1) * σ)
            = σ * (α ^ j * σ ^ (j - 1)) * α := by ring
          _ ≤ ((S j).card : ℝ) * (α ^ j * σ ^ (j - 1)) * α :=
              mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hcardge hBnn) hα
      rw [Nat.add_sub_cancel j 1]
      exact le_trans hle1 hstep42'

/-- Chaining `card_mul_le_sum_add_of_forall_le` along `k` links: `α^k σ^{k-1} ≤ f (kn) a b` for
`a ∈ S 0`, `b ∈ S k`, given a uniform link bound `α` and cardinality bound `σ` on the
intermediate sets. -/
private theorem pow_mul_pow_sub_one_le_chain (f : ℕ → Site d → Site d → ℝ)
    (hck : ∀ m n x y (S : Finset (Site d)), ∑ z ∈ S, f m x z * f n z y ≤ f (m + n) x y)
    (S : ℕ → Finset (Site d)) (n N : ℕ) (α σ : ℝ) (hα : 0 ≤ α) (hσ : 0 ≤ σ)
    (hcard : ∀ i, 0 < i → i < N → σ ≤ ((S i).card : ℝ))
    (hlink : ∀ i < N, ∀ a ∈ S i, ∀ b ∈ S (i + 1), α ≤ f n a b) :
    ∀ k, 1 ≤ k → k ≤ N → ∀ a ∈ S 0, ∀ b ∈ S k, α ^ k * σ ^ (k - 1) ≤ f (k * n) a b := by
  exact pow_mul_pow_sub_one_le_chain' f hck S n N α σ hα hσ hcard hlink


-- Floor quotients of close numerators: Int.ediv_le_ediv (monotone, gives 0 ≤),
-- Int.mul_ediv_self_le (N (a/N) ≤ a), Int.lt_mul_ediv_self_add (b < N (b/N) + N), so
-- N (a/N - b/N) < N (T + 2); lt_of_mul_lt_mul_left, Int.lt_add_one_iff.
/-- For integers with `a - b ≤ N(T+1)`, the floor quotients satisfy `0 ≤ a/N - b/N ≤ T+1`. -/
private theorem sub_ediv_le_add_one_of_sub_le (N a b T : ℤ) (hN : 0 < N) (hba : b ≤ a)
    (hab : a - b ≤ N * (T + 1)) :
    0 ≤ a / N - b / N ∧ a / N - b / N ≤ T + 1 := by
  constructor
  · exact sub_nonneg.mpr (Int.ediv_le_ediv hN hba)
  · have h1 : a ≤ b + N * (T + 1) := by linarith
    have h2 : a / N ≤ (b + N * (T + 1)) / N := Int.ediv_le_ediv hN h1
    rw [Int.add_mul_ediv_left b (T + 1) hN.ne'] at h2
    linarith

-- le_total D 0; sub_ediv_le_add_one_of_sub_le with (a, b) := ((t+1) D, t D) if 0 ≤ D, else
-- (t D, (t+1) D) (abs_of_nonneg / abs_of_nonpos on D); abs_le, linarith.
/-- For `|D| ≤ N(T+1)`, consecutive floor quotients of `t*D` differ by at most `T+1`: `|(t+1)D/N
- tD/N| ≤ T+1`. -/
private theorem abs_sub_ediv_le_add_one (N D T t : ℤ) (hN : 0 < N) (hD : |D| ≤ N * (T + 1)) :
    |(t + 1) * D / N - t * D / N| ≤ T + 1 := by
  rcases le_total 0 D with hD0 | hD0
  · have h := sub_ediv_le_add_one_of_sub_le N ((t + 1) * D) (t * D) T hN (by nlinarith) (by
      have := abs_of_nonneg hD0
      rw [this] at hD
      nlinarith)
    rw [abs_of_nonneg h.1]
    exact h.2
  · have h := sub_ediv_le_add_one_of_sub_le N (t * D) ((t + 1) * D) T hN (by nlinarith) (by
      have := abs_of_nonpos hD0
      rw [this] at hD
      nlinarith)
    rw [abs_of_nonpos (by linarith [h.1])]
    linarith [h.2]

-- Int.ediv_nonneg (mul_nonneg), Int.ediv_le_of_le_mul (t D ≤ D N: mul_le_mul_of_nonneg_right,
-- mul_comm).
/-- For `0 ≤ t ≤ N` and `D ≥ 0`, `0 ≤ tD/N ≤ D`. -/
private theorem ediv_mem_Icc_of_nonneg (N t D : ℤ) (hN : 0 < N) (ht0 : 0 ≤ t) (htN : t ≤ N)
    (hD : 0 ≤ D) :
    0 ≤ t * D / N ∧ t * D / N ≤ D := by
  constructor
  · exact Int.ediv_nonneg (mul_nonneg ht0 hD) hN.le
  · exact Int.ediv_le_of_le_mul hN (by nlinarith)

-- Int.ediv_nonpos_of_nonpos_of_neg (mul_nonpos_of_nonneg_of_nonpos),
-- Int.le_ediv_of_mul_le (D N ≤ t D: nlinarith).
/-- For `0 ≤ t ≤ N` and `D ≤ 0`, `D ≤ tD/N ≤ 0`. -/
private theorem ediv_mem_Icc_of_nonpos (N t D : ℤ) (hN : 0 < N) (ht0 : 0 ≤ t) (htN : t ≤ N)
    (hD : D ≤ 0) :
    D ≤ t * D / N ∧ t * D / N ≤ 0 := by
  constructor
  · exact Int.le_ediv_of_mul_le hN (by nlinarith)
  · exact Int.ediv_nonpos_of_nonpos_of_neg (mul_nonpos_of_nonneg_of_nonpos ht0 hD) hN

-- abs_le at ha hb and goal; le_total 0 (b - a) with ediv_mem_Icc_of_nonneg / ediv_mem_Icc_of_nonpos
-- (D := b - a); linarith.
/-- Interpolating between `a` and `b` by floor division stays within the bound: `|a + t(b-a)/N| ≤
m` when `|a|, |b| ≤ m`. -/
private theorem abs_add_mul_ediv_le (N t a b m : ℤ) (hN : 0 < N) (ht0 : 0 ≤ t) (htN : t ≤ N)
    (ha : |a| ≤ m) (hb : |b| ≤ m) : |a + t * (b - a) / N| ≤ m := by
  rw [abs_le] at ha hb ⊢
  rcases le_total 0 (b - a) with hD | hD
  · have h1 : 0 ≤ t * (b - a) / N := Int.ediv_nonneg (mul_nonneg ht0 hD) hN.le
    have h2 : t * (b - a) / N ≤ b - a := Int.ediv_le_of_le_mul hN (by nlinarith)
    constructor <;> linarith
  · have h1 : b - a ≤ t * (b - a) / N := Int.le_ediv_of_mul_le hN (by nlinarith)
    have h2 : t * (b - a) / N ≤ 0 :=
      Int.ediv_nonpos_of_nonpos_of_neg (mul_nonpos_of_nonneg_of_nonpos ht0 hD) hN
    constructor <;> linarith

-- Nat.lt_div_mul_add (0 < 4 d): s < s/(4d) * (4d) + 4d; then
-- 2 K' s ≤ 2 K' (4d (s/(4d)+1)) ≤ 8 d (K'+1) (s/(4d)+1) (Nat.mul_le_mul, nlinarith).
/-- An arithmetic bound `2K's ≤ 8d(K'+1)(s/(4d)+1)` from rounding `s` up to a multiple of `4d`. -/
private theorem two_mul_le_mul_div_add_one (hd : 1 ≤ d) (K' s : ℕ) :
    2 * K' * s ≤ 8 * d * (K' + 1) * (s / (4 * d) + 1) := by
  have hd0 : 0 < 4 * d := Nat.mul_pos (by norm_num) (Nat.lt_of_lt_of_le Nat.zero_lt_one hd)
  have h5 : s < s / (4 * d) * (4 * d) + 4 * d := Nat.lt_div_mul_add hd0
  have h6 : s ≤ 4 * d * (s / (4 * d) + 1) := by
    have h7 : s / (4 * d) * (4 * d) = 4 * d * (s / (4 * d)) := Nat.mul_comm _ _
    rw [h7] at h5
    have h8 : 4 * d * (s / (4 * d) + 1) = 4 * d * (s / (4 * d)) + 4 * d := by ring
    rw [h8]
    omega
  calc 2 * K' * s ≤ 2 * K' * (4 * d * (s / (4 * d) + 1)) := Nat.mul_le_mul_left _ h6
    _ = 8 * d * K' * (s / (4 * d) + 1) := by ring
    _ ≤ 8 * d * (K' + 1) * (s / (4 * d) + 1) := by
        have h9 : 8 * d * K' ≤ 8 * d * (K' + 1) := Nat.mul_le_mul_left _ (by omega)
        exact Nat.mul_le_mul_right _ h9

-- natAbs_sub_le_two_mul_of_abs_le m b a hb ha ((b - a).natAbs ≤ 2 m), Int.natCast_natAbs, 2 m ≤ 2
-- K' s
-- (Nat.mul_le_mul_left), two_mul_le_mul_div_add_one; exact_mod_cast / push_cast.
/-- For `m ≤ K's` and `|a|, |b| ≤ m`, `|b-a| ≤ 8d(K'+1)(s/(4d)+1)`. -/
private theorem abs_sub_le_mul_div_add_one (hd : 1 ≤ d) (K' s m : ℕ) (hm : m ≤ K' * s) (a b : ℤ)
    (ha : |a| ≤ (m : ℤ)) (hb : |b| ≤ (m : ℤ)) :
    |b - a| ≤ ((8 * d * (K' + 1) : ℕ) : ℤ) * (((s / (4 * d) : ℕ) : ℤ) + 1) := by
  have h1 : |b - a| ≤ 2 * (m : ℤ) := by
    rw [abs_le] at ha hb ⊢
    constructor <;> linarith
  have h4 : 2 * (K' * s) ≤ 8 * d * (K' + 1) * (s / (4 * d) + 1) := by
    have h := two_mul_le_mul_div_add_one hd K' s
    calc 2 * (K' * s) = 2 * K' * s := by ring
      _ ≤ 8 * d * (K' + 1) * (s / (4 * d) + 1) := h
  have h2 : (2 * m : ℤ) ≤ ((8 * d * (K' + 1) * (s / (4 * d) + 1) : ℕ) : ℤ) := by
    have h3 : 2 * m ≤ 8 * d * (K' + 1) * (s / (4 * d) + 1) := by
      have h10 : 2 * m ≤ 2 * (K' * s) := by omega
      omega
    exact_mod_cast h3
  have hgoal : ((8 * d * (K' + 1) : ℕ) : ℤ) * (((s / (4 * d) : ℕ) : ℤ) + 1)
      = ((8 * d * (K' + 1) * (s / (4 * d) + 1) : ℕ) : ℤ) := by push_cast; ring
  rw [hgoal]
  linarith

-- Anchor points: w i j := x j + (min i N * (y j - x j)) / N  (Int division), N := 8 d (K'+1).
-- w i between x and y coordinatewise, so in box m; consecutive difference ≤ |y j - x j|/N + 1
-- and |y j - x j| ≤ 2m ≤ 2K's, 2K's/(8d(K'+1)) ≤ s/(4d) (Int.ediv_le_ediv, Int.le_ediv_iff_mul_le,
-- omega/nlinarith).  SPLIT?
/-- There is a chain of anchor points `w : ℕ → Site d` from `x` to `y` inside `box d m`, taking
`8d(K'+1)` steps, each moving every coordinate by at most `s/(4d)+1`. -/
private theorem exists_path_le_div_add_one (K' s m : ℕ) (hd : 1 ≤ d) (_unused_hs : 4 * d ≤ s)
    (hm : m ≤ K' * s)
    (x y : Site d) (hx : x ∈ box d m) (hy : y ∈ box d m) :
    ∃ w : ℕ → Site d, w 0 = x ∧ w (8 * d * (K' + 1)) = y ∧ (∀ i, w i ∈ box d m) ∧
      ∀ i (j : Fin d), |w (i + 1) j - w i j| ≤ ((s / (4 * d) + 1 : ℕ) : ℤ) := by
  have hNpos : (0 : ℤ) < ((8 * d * (K' + 1) : ℕ) : ℤ) := by
    have h : 0 < 8 * d * (K' + 1) := Nat.mul_pos (Nat.mul_pos (by norm_num) hd) (Nat.succ_pos K')
    exact_mod_cast h
  refine ⟨fun i j => x j + ((min i (8 * d * (K' + 1)) : ℕ) : ℤ) * (y j - x j)
      / ((8 * d * (K' + 1) : ℕ) : ℤ), ?_, ?_, ?_, ?_⟩
  · funext j
    simp
  · funext j
    simp only [min_self]
    rw [Int.mul_ediv_cancel_left _ hNpos.ne']
    ring
  · intro i j
    exact abs_add_mul_ediv_le _ _ (x j) (y j) m hNpos (Nat.cast_nonneg _)
      (by exact_mod_cast min_le_right _ _) (hx j) (hy j)
  · intro i j
    have hcast : (((s / (4 * d) + 1 : ℕ) : ℤ)) = ((s / (4 * d) : ℕ) : ℤ) + 1 := by push_cast; ring
    rw [hcast]
    by_cases hi : i < 8 * d * (K' + 1)
    · have h1 : min (i + 1) (8 * d * (K' + 1)) = i + 1 := min_eq_left hi
      have h2 : min i (8 * d * (K' + 1)) = i := min_eq_left hi.le
      simp only [h1, h2, Nat.cast_succ, add_sub_add_left_eq_sub]
      exact abs_sub_ediv_le_add_one _ _ _ _ hNpos
        (abs_sub_le_mul_div_add_one hd K' s m hm (x j) (y j) (hx j) (hy j))
    · have h1 : min (i + 1) (8 * d * (K' + 1)) = 8 * d * (K' + 1) := min_eq_right (by omega)
      have h2 : min i (8 * d * (K' + 1)) = 8 * d * (K' + 1) := min_eq_right (by omega)
      simp only [h1, h2, sub_self, abs_zero]
      positivity

-- Link geometry: a = w + u, b = w' + v with u, v ∈ originBox t, t = s/(4d):
-- graphNorm (a - b) = ∑_j |..| ≤ d (s/(4d) + 1 + 2 t) ≤ s (4 d (s/(4d)) ≤ s, s/(4d) ≥ 1);
-- Int.natAbs_add_le, Finset.sum_le_card_nsmul; b ∈ box (m + t) ⊆ box (m + s).
/-- Two points built by adding small offsets `u, v` (from `originBox d (s/(4d))`) to nearby
anchors `w, w'` are within `graphNorm` distance `s` of each other. -/
private theorem graphNorm_add_sub_add_le (hd : 1 ≤ d) (s : ℕ) (hs : 4 * d ≤ s) (w w' : Site d)
    (hstep : ∀ j : Fin d, |w' j - w j| ≤ ((s / (4 * d) + 1 : ℕ) : ℤ))
    (u v : Site d) (hu : u ∈ originBox d (s / (4 * d))) (hv : v ∈ originBox d (s / (4 * d))) :
    graphNorm ((w + u) - (w' + v)) ≤ s := by
  have h4d : 0 < 4 * d := by omega
  have ht1 : 1 ≤ s / (4 * d) := (Nat.one_le_div_iff h4d).mpr hs
  have hu_le : ∀ i : Fin d, |u i| ≤ ((s / (4 * d) : ℕ) : ℤ) := by
    intro i
    rw [originBox_eq] at hu
    exact abs_le.mpr (Finset.mem_Icc.mp (Fintype.mem_piFinset.mp hu i))
  have hv_le : ∀ i : Fin d, |v i| ≤ ((s / (4 * d) : ℕ) : ℤ) := by
    intro i
    rw [originBox_eq] at hv
    exact abs_le.mpr (Finset.mem_Icc.mp (Fintype.mem_piFinset.mp hv i))
  have hfinal : d * (3 * (s / (4 * d)) + 1) ≤ s := by
    have h2 : d ≤ d * (s / (4 * d)) := by simpa using Nat.mul_le_mul_left d ht1
    calc d * (3 * (s / (4 * d)) + 1) = 3 * (d * (s / (4 * d))) + d := by ring
      _ ≤ 3 * (d * (s / (4 * d))) + d * (s / (4 * d)) := Nat.add_le_add_left h2 _
      _ = (s / (4 * d)) * (4 * d) := by ring
      _ ≤ s := Nat.div_mul_le_self s (4 * d)
  have hcoord : ∀ i : Fin d, ((w + u - (w' + v)) i).natAbs ≤ 3 * (s / (4 * d)) + 1 := by
    intro i
    have heq : (w + u - (w' + v)) i = (w i - w' i) + (u i - v i) := by
      simp only [Pi.sub_apply, Pi.add_apply]; ring
    have h1 : |w i - w' i| ≤ ((s / (4 * d) + 1 : ℕ) : ℤ) := by
      simpa [abs_sub_comm] using hstep i
    have h2 : |u i - v i| ≤ 2 * ((s / (4 * d) : ℕ) : ℤ) := by
      rw [abs_sub_le_iff]
      constructor <;>
        linarith [neg_abs_le (u i), le_abs_self (u i), neg_abs_le (v i), le_abs_self (v i),
          hu_le i, hv_le i]
    have h3 : |(w + u - (w' + v)) i| ≤ ((3 * (s / (4 * d)) + 1 : ℕ) : ℤ) := by
      rw [heq]
      calc |(w i - w' i) + (u i - v i)| ≤ |w i - w' i| + |u i - v i| := abs_add_le _ _
        _ ≤ ((s / (4 * d) + 1 : ℕ) : ℤ) + 2 * ((s / (4 * d) : ℕ) : ℤ) := add_le_add h1 h2
        _ = ((3 * (s / (4 * d)) + 1 : ℕ) : ℤ) := by push_cast; ring
    refine Int.ofNat_le.mp ?_
    rw [Int.natCast_natAbs]
    exact h3
  calc ∑ i, ((w + u - (w' + v)) i).natAbs
      ≤ ∑ _i : Fin d, (3 * (s / (4 * d)) + 1) := Finset.sum_le_sum fun i _ => hcoord i
    _ = d * (3 * (s / (4 * d)) + 1) := by simp
    _ ≤ s := hfinal

/-- An offset point `w' + v` with `w' ∈ box d m` and `v ∈ originBox d (s/(4d))` lies in `box d
(m+s)`. -/
private theorem add_mem_box_add (_unused_hd : 1 ≤ d) (s m : ℕ) (_unused_hs : 4 * d ≤ s)
    (w' v : Site d)
    (hw' : w' ∈ box d m) (hv : v ∈ originBox d (s / (4 * d))) :
    w' + v ∈ box d (m + s) := by
  intro i
  have hv_le : ∀ i : Fin d, |v i| ≤ ((s / (4 * d) : ℕ) : ℤ) := by
    intro i
    rw [originBox_eq] at hv
    exact abs_le.mpr (Finset.mem_Icc.mp (Fintype.mem_piFinset.mp hv i))
  have hts : ((s / (4 * d) : ℕ) : ℤ) ≤ (s : ℤ) := by
    exact_mod_cast Nat.div_le_self s (4 * d)
  calc |(w' + v) i| = |w' i + v i| := by simp
    _ ≤ |w' i| + |v i| := abs_add_le _ _
    _ ≤ (m : ℤ) + (s : ℤ) := add_le_add (hw' i) (le_trans (hv_le i) hts)
    _ = ((m + s : ℕ) : ℤ) := by push_cast; ring

/-- Combines `graphNorm_add_sub_add_le` and `add_mem_box_add`: points in the offset images of
adjacent anchors are within `s` of each other and the second lies in `box d (m+s)`. -/
private theorem graphNorm_sub_le_and_mem_box (hd : 1 ≤ d) (s m : ℕ) (hs : 4 * d ≤ s) (w w' : Site d)
    (hw' : w' ∈ box d m)
    (hstep : ∀ j : Fin d, |w' j - w j| ≤ ((s / (4 * d) + 1 : ℕ) : ℤ))
    (a b : Site d) (ha : a ∈ (originBox d (s / (4 * d))).image (w + ·))
    (hb : b ∈ (originBox d (s / (4 * d))).image (w' + ·)) :
    graphNorm (a - b) ≤ s ∧ b ∈ box d (m + s) := by
  obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp ha
  obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hb
  exact ⟨graphNorm_add_sub_add_le hd s hs w w' hstep u v hu hv,
    add_mem_box_add hd s m hs w' v hw' hv⟩


-- If b ∈ box (m + s) and graphNorm (z - b) ≤ M s then z ∈ box (m + (M + 1) s)
-- (|z j| ≤ |b j| + |z j - b j| ≤ m + s + M s; single coordinate ≤ graphNorm: Finset.single_le_sum).
/-- If `b ∈ box d (m+s)` and `graphNorm (z-b) ≤ Ms`, then `z ∈ box d (m + (M+1)s)`. -/
private theorem mem_box_of_graphNorm_sub_le (s m M : ℕ) (b z : Site d) (hb : b ∈ box d (m + s))
    (hz : graphNorm (z - b) ≤ M * s) : z ∈ box d (m + (M + 1) * s) := by
  intro i
  have hb' : (b i).natAbs ≤ m + s := (by
    have h := hb i
    rw [← Int.natCast_natAbs] at h
    exact_mod_cast h)
  have hsub : ((z - b) i).natAbs ≤ M * s := (by
    have hs : ((z - b) i).natAbs ≤ graphNorm (z - b) :=
      Finset.single_le_sum (s := Finset.univ) (f := fun j : Fin d => ((z - b) j).natAbs)
        (fun j _ => Nat.zero_le _) (Finset.mem_univ i)
    omega)
  have hkey : (z i).natAbs ≤ ((z - b) i).natAbs + (b i).natAbs := (by
    have h : z i = (z - b) i + b i := (by
      simp only [Pi.sub_apply]
      ring)
    rw [h]
    exact Int.natAbs_add_le _ _)
  have hfin : (z i).natAbs ≤ m + (M + 1) * s := (by
    have hMs : (M + 1) * s = M * s + s := Nat.succ_mul M s
    omega)
  rw [← Int.natCast_natAbs]
  exact_mod_cast hfin


-- Translate of a box: Finset.card_image_of_injective (add_right_injective w), card_originBox'.
/-- Translating `originBox d t` by `w` preserves its cardinality `(2t+1)^d`. -/
private theorem card_image_add_originBox_eq (w : Site d) (t : ℕ) :
    ((originBox d t).image (w + ·)).card = (2 * t + 1) ^ d := by
  rw [Finset.card_image_of_injective _ (add_right_injective w), card_originBox']


-- split_ifs at ha (Finset.mem_singleton; subst with hw0 / hwN); Finset.mem_image.mpr ⟨0, _,
-- add_zero _⟩,
-- 0 ∈ originBox d t (originBox, Fintype.mem_piFinset, Finset.mem_Icc; simp).
/-- Membership in the piecewise target set (endpoints or a translated `originBox`) implies
membership in the translated `originBox` at interior indices. -/
private theorem mem_image_add_originBox_of_mem_ite (w : ℕ → Site d) (x y : Site d) (N t : ℕ)
    (hw0 : w 0 = x)
    (hwN : w N = y) (i : ℕ) (a : Site d)
    (ha : a ∈ (if i = 0 then {x} else if i = N then {y}
      else (originBox d t).image (w i + ·) : Finset (Site d))) :
    a ∈ (originBox d t).image (w i + ·) := by
  split_ifs at ha with h0 hN
  · rw [Finset.mem_singleton] at ha
    rw [ha, h0, ← hw0]
    exact Finset.mem_image.mpr ⟨0, by simp [originBox, Finset.mem_Icc], by simp⟩
  · rw [Finset.mem_singleton] at ha
    rw [ha, hN, ← hwN]
    exact Finset.mem_image.mpr ⟨0, by simp [originBox, Finset.mem_Icc], by simp⟩
  · exact ha

-- if_neg (i ≠ 0), if_neg (i ≠ N) (omega), card_image_add_originBox_eq; le_of_eq.
/-- At an interior index `i`, the piecewise target set has cardinality at least `(2t+1)^d`, by
`card_image_add_originBox_eq`. -/
private theorem two_mul_add_one_pow_le_card_ite (w : ℕ → Site d) (x y : Site d) (N t i : ℕ)
    (hi0 : 0 < i)
    (hiN : i < N) :
    (((2 * t + 1) ^ d : ℕ) : ℝ) ≤ ((if i = 0 then {x} else if i = N then {y}
      else (originBox d t).image (w i + ·) : Finset (Site d)).card : ℝ) := by
  rw [if_neg (by omega : ¬ i = 0), if_neg (by omega : ¬ i = N)]
  rw [card_image_add_originBox_eq (w i) t]

-- Nat.lt_div_mul_add (0 < 4 d): s < s/(4d) * (4d) + 4d; cast (exact_mod_cast), div_le_iff₀;
-- s/(4d) + 1 ≤ 2 (s/(4d)) + 1; push_cast, nlinarith.
/-- Rounding bound: `s/(4d) ≤ 2(s/(4d))+1` as real numbers. -/
private theorem div_le_two_mul_div_add_one (hd : 1 ≤ d) (s : ℕ) :
    (s : ℝ) / (4 * d) ≤ ((2 * (s / (4 * d)) + 1 : ℕ) : ℝ) := by
  have hd0 : 0 < 4 * d := Nat.mul_pos (by norm_num) (Nat.lt_of_lt_of_le Nat.zero_lt_one hd)
  have h1 : s < s / (4 * d) * (4 * d) + 4 * d := Nat.lt_div_mul_add hd0
  have h2 : (s : ℝ) < ((s / (4 * d) : ℕ) : ℝ) * (4 * (d : ℝ)) + 4 * (d : ℝ) := by
    exact_mod_cast h1
  have h3 : (0 : ℝ) < 4 * (d : ℝ) := by positivity
  have hq : (0 : ℝ) ≤ ((s / (4 * d) : ℕ) : ℝ) := Nat.cast_nonneg _
  rw [div_le_iff₀ h3]
  push_cast
  nlinarith [h2, h3, hq]

-- ← div_pow, Nat.cast_pow; pow_le_pow_left₀ (div_nonneg) (div_le_two_mul_div_add_one hd s) d.
/-- Raising `div_le_two_mul_div_add_one` to the `d`-th power: `s^d/(4d)^d ≤ (2(s/(4d))+1)^d`. -/
private theorem pow_div_pow_le_two_mul_div_add_one_pow (hd : 1 ≤ d) (s : ℕ) :
    (s : ℝ) ^ d / (4 * (d : ℝ)) ^ d ≤ (((2 * (s / (4 * d)) + 1) ^ d : ℕ) : ℝ) := by
  have h3 := div_le_two_mul_div_add_one hd s
  have h4 : (0 : ℝ) ≤ (s : ℝ) / (4 * d) := by positivity
  have h5 : ((s : ℝ) / (4 * d)) ^ d ≤ (((2 * (s / (4 * d)) + 1 : ℕ) : ℝ)) ^ d :=
    pow_le_pow_left₀ h4 h3 d
  have h6 : (s : ℝ) ^ d / (4 * (d : ℝ)) ^ d = ((s : ℝ) / (4 * d)) ^ d := by rw [div_pow]
  have h7 : (((2 * (s / (4 * d)) + 1 : ℕ) : ℝ)) ^ d
      = (((2 * (s / (4 * d)) + 1) ^ d : ℕ) : ℝ) := by push_cast; ring
  rw [h6]
  rw [← h7]
  exact h5

-- div_pow, pow_succ, pow_mul / ← pow_mul; field_simp; ring.
/-- Algebraic identity: `(c/S^d)^{k+1} * (S^d/A^d)^k = c^{k+1}/(A^d)^k/S^d`. -/
private theorem pow_mul_pow_eq_pow_div (c A S : ℝ) (hA : A ≠ 0) (hS : S ≠ 0) (k : ℕ) :
    (c / S ^ d) ^ (k + 1) * (S ^ d / A ^ d) ^ k = c ^ (k + 1) / (A ^ d) ^ k / S ^ d := by
  rw [div_pow, div_pow, pow_succ]
  field_simp
  ring

-- N = k + 1 (Nat.exists_eq_add_of_le'), Nat.add_sub_cancel; ← pow_mul_pow_eq_pow_div;
-- mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) hσ k) (pow_nonneg (div_nonneg ..)).
/-- Given `S^d/A^d ≤ σ`, `c^N/(A^d)^{N-1}/S^d ≤ (c/S^d)^N σ^{N-1}`. -/
private theorem pow_div_pow_div_le_pow_mul_pow (c A S σ : ℝ) (hc : 0 ≤ c) (hA : 0 < A) (hS : 0 < S)
    (hσ : S ^ d / A ^ d ≤ σ) (N : ℕ) (hN : 1 ≤ N) :
    c ^ N / (A ^ d) ^ (N - 1) / S ^ d ≤ (c / S ^ d) ^ N * σ ^ (N - 1) := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hN
  have hsub : 1 + k - 1 = k := by omega
  rw [hsub]
  have hk : 1 + k = k + 1 := by omega
  rw [hk]
  rw [← pow_mul_pow_eq_pow_div c A S (ne_of_gt hA) (ne_of_gt hS) k]
  exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) hσ k) (by positivity)

-- Single-time lower bound at scale s.  M := M₁ + 1 (M₁ from exists_const_le_lazyKilled_div_pow); N
-- := 8 d (K'+1);
-- S i := {x} if i = 0, {y} if i = N, else (originBox d t).image (w i + ·)
-- (exists_path_le_div_add_one);
-- each S i ⊆ image of w i (x = w 0, y = w N, 0 ∈ originBox); pow_mul_pow_sub_one_le_chain with f :=
-- lazyKilled B
-- (hck = sum_lazyKilled_mul_le_lazyKilled_add), α := c₁/s^d (exists_const_le_lazyKilled_div_pow via
-- graphNorm_sub_le_and_mem_box, mem_box_of_graphNorm_sub_le),
-- σ := (2t+1)^d ≥ (s/(8d))^d (card_image_add_originBox_eq).  α^N σ^(N-1) ≥ c₂/s^d with
-- c₂ := c₁^N (8d)^{-d(N-1)}; s₂ := max s₁ (8 d).  SPLIT?
/-- The single-time chained lower bound: for every `K'` there are `c₂ > 0`, `s₂`, `N` such that
`c₂/s^d ≤ lazyKilled B (Nn) x y` for `x, y ∈ box d m` with `m ≤ K's`, provided `B` covers
`box d (m+Ms)`, by chaining `pow_mul_pow_sub_one_le_chain` over the anchor path of
`exists_path_le_div_add_one`. -/
private theorem exists_const_le_lazyKilled_mul_div_pow (hd : 1 ≤ d) :
    ∃ M : ℕ, 1 ≤ M ∧ ∀ K' : ℕ, ∃ c₂ : ℝ, 0 < c₂ ∧ ∃ s₂ N : ℕ, 1 ≤ N ∧ 1 ≤ s₂ ∧
      ∀ s : ℕ, s₂ ≤ s → ∀ m : ℕ, m ≤ K' * s → ∀ B : Finset (Site d),
        (∀ z ∈ box d (m + M * s), z ∈ B) → ∀ n : ℕ, s ^ 2 ≤ n → n ≤ 2 * s ^ 2 →
          ∀ x ∈ box d m, ∀ y ∈ box d m, c₂ / (s : ℝ) ^ d ≤ lazyKilled B (N * n) x y := by
  obtain ⟨c₁, hc₁, M₁, s₁, _, hs₁, h41⟩ := exists_const_le_lazyKilled_div_pow hd
  refine ⟨M₁ + 1, by omega, fun K' => ?_⟩
  have hN1 : 1 ≤ 8 * d * (K' + 1) :=
    Nat.mul_pos (Nat.mul_pos (by norm_num) hd) (Nat.succ_pos K')
  have hdR : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd
  have h4d : (0 : ℝ) < 4 * (d : ℝ) := by linarith
  refine ⟨c₁ ^ (8 * d * (K' + 1)) / ((4 * (d : ℝ)) ^ d) ^ (8 * d * (K' + 1) - 1),
    div_pos (pow_pos hc₁ _) (pow_pos (pow_pos h4d _) _),
    max s₁ (4 * d), 8 * d * (K' + 1), hN1, le_trans hs₁ (le_max_left _ _), ?_⟩
  intro s hs m hm B hB n hn1 hn2 x hx y hy
  have hs1 : s₁ ≤ s := le_trans (le_max_left _ _) hs
  have hs4 : 4 * d ≤ s := le_trans (le_max_right _ _) hs
  have hspos : (0 : ℝ) < (s : ℝ) := by
    have h : 0 < s := lt_of_lt_of_le (Nat.mul_pos (by norm_num) hd) hs4
    exact_mod_cast h
  obtain ⟨w, hw0, hwN, hwbox, hwstep⟩ := exists_path_le_div_add_one K' s m hd hs4 hm x y hx hy
  let S : ℕ → Finset (Site d) := fun i =>
    if i = 0 then {x} else if i = 8 * d * (K' + 1) then {y}
      else (originBox d (s / (4 * d))).image (w i + ·)
  have hlink : ∀ i < 8 * d * (K' + 1), ∀ a ∈ S i, ∀ b ∈ S (i + 1),
      c₁ / (s : ℝ) ^ d ≤ lazyKilled B n a b := by
    intro i _ a ha b hb
    have ha' := mem_image_add_originBox_of_mem_ite w x y _ (s / (4 * d)) hw0 hwN i a ha
    have hb' := mem_image_add_originBox_of_mem_ite w x y _ (s / (4 * d)) hw0 hwN (i + 1) b hb
    obtain ⟨h1, h2⟩ := graphNorm_sub_le_and_mem_box hd s m hs4 (w i) (w (i + 1)) (hwbox (i + 1))
        (hwstep i)
      a b ha' hb'
    exact h41 s hs1 n hn1 hn2 B a b h1
        (fun z hz => hB z (mem_box_of_graphNorm_sub_le s m M₁ b z h2 hz))
  have hcard : ∀ i, 0 < i → i < 8 * d * (K' + 1) →
      (((2 * (s / (4 * d)) + 1) ^ d : ℕ) : ℝ) ≤ ((S i).card : ℝ) :=
    fun i h0 hiN => two_mul_add_one_pow_le_card_ite w x y _ (s / (4 * d)) i h0 hiN
  have hx0 : x ∈ S 0 := by
    show x ∈ (if (0 : ℕ) = 0 then {x} else _ : Finset (Site d))
    rw [if_pos rfl]
    exact Finset.mem_singleton_self x
  have hyN : y ∈ S (8 * d * (K' + 1)) := by
    show y ∈ (if 8 * d * (K' + 1) = 0 then {x} else if 8 * d * (K' + 1) = 8 * d * (K' + 1)
      then {y} else _ : Finset (Site d))
    rw [if_neg (by omega), if_pos rfl]
    exact Finset.mem_singleton_self y
  have h43 := pow_mul_pow_sub_one_le_chain (lazyKilled B) (sum_lazyKilled_mul_le_lazyKilled_add B) S
      n (8 * d * (K' + 1))
    (c₁ / (s : ℝ) ^ d) ((((2 * (s / (4 * d)) + 1) ^ d : ℕ) : ℝ))
    (div_nonneg hc₁.le (pow_nonneg hspos.le d)) (Nat.cast_nonneg _) hcard hlink
    (8 * d * (K' + 1)) hN1 le_rfl x hx0 y hyN
  exact le_trans (pow_div_pow_div_le_pow_mul_pow c₁ (4 * (d : ℝ)) (s : ℝ) _ hc₁.le h4d hspos
    (pow_div_pow_le_two_mul_div_add_one_pow hd s) _ hN1) h43

-- Summing over n ∈ Icc (s²) (2 s²): T := (Icc (s^2) (2 s^2)).image (N * ·) (injective, N ≥ 1:
-- Finset.sum_image, mul_left_cancel₀); card = s² + 1 ≥ s²;
-- sum_lazyKilled_le_two_mul_tsum_killedHeat, killedGreenReal_eq_tsum_killedHeat_div:
-- g ≥ (1/(4d)) ∑_{r∈T} lazyKilled ≥ (s²/(4d)) c₂/s^d = (c₂/(4d)) s^{2-d} (zpow_sub₀, zpow_natCast).
/-- Summing `exists_const_le_lazyKilled_mul_div_pow` over `n ∈ [s^2, 2s^2]` gives the
Green-function lower bound `c₃ s^{2-d} ≤ killedGreenReal B x y`. -/
private theorem exists_const_mul_rpow_le_killedGreenReal (hd : 1 ≤ d) :
    ∃ M : ℕ, 1 ≤ M ∧ ∀ K' : ℕ, ∃ c₃ : ℝ, 0 < c₃ ∧ ∃ s₂ : ℕ, 1 ≤ s₂ ∧
      ∀ s : ℕ, s₂ ≤ s → ∀ m : ℕ, m ≤ K' * s → ∀ B : Finset (Site d),
        (∀ z ∈ box d (m + M * s), z ∈ B) → ∀ x ∈ box d m, ∀ y ∈ box d m,
          c₃ * (s : ℝ) ^ ((2 : ℤ) - d) ≤ Graph.killedGreenReal (lattice d) (B : Set (Site d)) x y :=
              by
  obtain ⟨M, hM1, h48⟩ := exists_const_le_lazyKilled_mul_div_pow hd
  refine ⟨M, hM1, fun K' => ?_⟩
  obtain ⟨c₂, hc₂, s₂, N, hN, hs₂, h48'⟩ := h48 K'
  have hdpos : (0:ℝ) < (d:ℝ) := (by
    have h : 0 < d := (by omega)
    exact_mod_cast h)
  have h4d : (0:ℝ) < 4 * (d:ℝ) := (by linarith)
  have h2d : (0:ℝ) < 2 * (d:ℝ) := (by linarith)
  refine ⟨c₂ / (4 * (d:ℝ)), div_pos hc₂ h4d, max s₂ 1, le_max_right s₂ 1, ?_⟩
  intro s hs m hm B hB x hx y hy
  have hs1 : 1 ≤ s := le_trans (le_max_right s₂ 1) hs
  have hs2 : s₂ ≤ s := le_trans (le_max_left s₂ 1) hs
  have hsd : (0:ℝ) < (s:ℝ) := (by exact_mod_cast hs1)
  have hsd0 : (s:ℝ) ≠ 0 := ne_of_gt hsd
  have hspow_nonneg : (0:ℝ) ≤ (s:ℝ)^d := pow_nonneg (le_of_lt hsd) d
  have hXnonneg : (0:ℝ) ≤ c₂ / (s:ℝ)^d := div_nonneg (le_of_lt hc₂) hspow_nonneg
  have hNinj : Function.Injective (fun a : ℕ => N * a) :=
    fun a b hab => Nat.eq_of_mul_eq_mul_left hN hab
  have hTcard : s^2 ≤ ((Finset.Icc (s^2) (2 * s^2)).image (N * ·)).card := (by
    rw [Finset.card_image_of_injective _ hNinj, Nat.card_Icc]
    omega)
  have hcast : ((s^2 : ℕ) : ℝ) ≤ (((Finset.Icc (s^2) (2 * s^2)).image (N * ·)).card : ℝ) := (by
    exact_mod_cast hTcard)
  have hle : ∀ r ∈ (Finset.Icc (s^2) (2 * s^2)).image (N * ·),
      c₂ / (s:ℝ)^d ≤ lazyKilled B r x y := (by
    intro r hr
    obtain ⟨n, hn, rfl⟩ := Finset.mem_image.mp hr
    exact h48' s hs2 m hm B hB n (Finset.mem_Icc.mp hn).1 (Finset.mem_Icc.mp hn).2 x hx y hy)
  have hcardle : (((Finset.Icc (s^2) (2 * s^2)).image (N * ·)).card : ℝ) * (c₂ / (s:ℝ)^d)
      ≤ ∑ r ∈ (Finset.Icc (s^2) (2 * s^2)).image (N * ·), lazyKilled B r x y := (by
    have h := Finset.card_nsmul_le_sum ((Finset.Icc (s^2) (2 * s^2)).image (N * ·))
      (fun r => lazyKilled B r x y) (c₂ / (s:ℝ)^d) hle
    simpa [nsmul_eq_mul] using h)
  have hsum2 : (s:ℝ)^2 * (c₂ / (s:ℝ)^d)
      ≤ ∑ r ∈ (Finset.Icc (s^2) (2 * s^2)).image (N * ·), lazyKilled B r x y := (by
    have h1 : (s:ℝ)^2 = ((s^2 : ℕ) : ℝ) := (by rw [Nat.cast_pow])
    rw [h1]
    exact le_trans (mul_le_mul_of_nonneg_right hcast hXnonneg) hcardle)
  have hsum_le : (s:ℝ)^2 * (c₂ / (s:ℝ)^d)
      ≤ 2 * (∑' k : ℕ, Graph.killedHeat (lattice d) (B : Set (Site d)) k x y) :=
    le_trans hsum2
        (sum_lazyKilled_le_two_mul_tsum_killedHeat hd B x y ((Finset.Icc (s^2) (2 * s^2)).image (N *
            ·)))
  have hP : c₂ * ((s:ℝ)^2 / (s:ℝ)^d) = (s:ℝ)^2 * (c₂ / (s:ℝ)^d) := (by ring)
  rw [killedGreenReal_eq_tsum_killedHeat_div hd B x y]
  simp only [zpow_sub₀ hsd0, zpow_natCast]
  calc c₂ / (4 * (d:ℝ)) * ((s:ℝ)^2 / (s:ℝ)^d)
      = (c₂ * ((s:ℝ)^2 / (s:ℝ)^d)) / (4 * (d:ℝ)) := (by ring)
    _ = ((s:ℝ)^2 * (c₂ / (s:ℝ)^d)) / (4 * (d:ℝ)) := (by rw [hP])
    _ ≤ (2 * (∑' k : ℕ, Graph.killedHeat (lattice d) (B : Set (Site d)) k x y)) / (4 * (d:ℝ)) :=
          div_le_div_of_nonneg_right hsum_le (le_of_lt h4d)
    _ = (∑' k : ℕ, Graph.killedHeat (lattice d) (B : Set (Site d)) k x y) / (2 * (d:ℝ)) := (by ring)


/-! ### G. Small scales and the lower bound -/

-- One step: x ∈ B, x' = x ± unit i: killedHeat (n+1) x y ≥ killedHeat n x' y / (2d).
-- Graph.Zd.killedHeat_succ_walkOp, if_pos, LatticeProb.walkOp = nbrSum/(2d), the single term
-- ≤ nbrSum (Finset.single_le_sum, Network.killedHeat_nonneg, le_add_of_nonneg_right/left).
/-- A single step of the killed walk from a neighbour `x' = x ± unit i` of `x ∈ C` contributes at
least `killedHeat n x' y / (2d)` to `killedHeat (n+1) x y`. -/
private theorem killedHeat_div_two_mul_le_killedHeat_succ (hd : 1 ≤ d) (C : Set (Site d)) (n : ℕ)
    {x x' : Site d} (hx : x ∈ C)
    (i : Fin d) (hx' : x' = x + unit i ∨ x' = x - unit i) (y : Site d) :
    Graph.killedHeat (lattice d) C n x' y / (2 * (d : ℝ))
      ≤ Graph.killedHeat (lattice d) C (n + 1) x y := by
  have hnn : ∀ z : Site d, 0 ≤ Graph.killedHeat (lattice d) C n z y :=
    fun z => Network.killedHeat_nonneg (G := lattice d) C n z y
  rw [Graph.Zd.killedHeat_succ_walkOp, if_pos hx, LatticeProb.walkOp, LatticeProb.nbrSum]
  refine div_le_div_of_nonneg_right ?_ (by positivity)
  rcases hx' with h | h
  · rw [h]
    exact le_trans (le_add_of_nonneg_right (hnn (x - unit i)))
      (Finset.single_le_sum (fun j _ => add_nonneg (hnn (x + unit j)) (hnn (x - unit j)))
        (Finset.mem_univ i))
  · rw [h]
    exact le_trans (le_add_of_nonneg_left (hnn (x + unit i)))
      (Finset.single_le_sum (fun j _ => add_nonneg (hnn (x + unit j)) (hnn (x - unit j)))
        (Finset.mem_univ i))


-- Finset.add_sum_erase at i on both sides; the erased sums agree termwise (Finset.sum_congr,
-- Finset.ne_of_mem_erase, hoff); omega.
/-- If `x'` agrees with `x` off coordinate `i` and its `i`-th distance to `y` is one less, then
`∑_j |x'_j - y_j| + 1 = ∑_j |x_j - y_j|`. -/
private theorem sum_natAbs_add_one_eq_of_ne {x' x y : Site d} (i : Fin d)
    (hoff : ∀ j, j ≠ i → x' j = x j)
    (hi : (x' i - y i).natAbs + 1 = (x i - y i).natAbs) :
    (∑ j, (x' j - y j).natAbs) + 1 = ∑ j, (x j - y j).natAbs := by
  rw [← Finset.add_sum_erase _ (fun j => (x' j - y j).natAbs) (Finset.mem_univ i),
      ← Finset.add_sum_erase _ (fun j => (x j - y j).natAbs) (Finset.mem_univ i)]
  rw [add_right_comm, hi]
  congr 1
  exact Finset.sum_congr rfl (fun j hj => by rw [hoff j (Finset.ne_of_mem_erase hj)])

-- intro j; j = i: Pi.add_apply, unit, Pi.single_eq_same, abs_le (hx i, hy i), omega;
-- j ≠ i: Pi.single_eq_of_ne, add_zero, hx j.
/-- Stepping coordinate `i` of `x` up by one toward `y` keeps the result in `box d m`, when `x_i
< y_i`. -/
private theorem add_unit_mem_box_of_lt {m : ℕ} {x y : Site d} (hx : x ∈ box d m) (hy : y ∈ box d m)
    {i : Fin d} (h : x i < y i) : x + unit i ∈ box d m := by
  intro j
  by_cases hji : j = i
  · subst hji
    rw [Pi.add_apply, unit, Pi.single_eq_same]
    have h1 := hx j
    have h2 := hy j
    have h3 : x j < y j := h
    rw [abs_le] at h1 h2 ⊢
    omega
  · rw [Pi.add_apply, unit, Pi.single_eq_of_ne hji, add_zero]
    exact hx j

-- As add_unit_mem_box_of_lt with Pi.sub_apply, sub_zero.
/-- Stepping coordinate `i` of `x` down by one toward `y` keeps the result in `box d m`, when
`y_i < x_i`. -/
private theorem sub_unit_mem_box_of_lt {m : ℕ} {x y : Site d} (hx : x ∈ box d m) (hy : y ∈ box d m)
    {i : Fin d} (h : y i < x i) : x - unit i ∈ box d m := by
  intro j
  by_cases hji : j = i
  · subst hji
    rw [Pi.sub_apply, unit, Pi.single_eq_same]
    have h1 := hx j
    have h2 := hy j
    have h3 : y j < x j := h
    rw [abs_le] at h1 h2 ⊢
    omega
  · rw [Pi.sub_apply, unit, Pi.single_eq_of_ne hji, sub_zero]
    exact hx j

-- unfold graphNorm, Pi.sub_apply; sum_natAbs_add_one_eq_of_ne i (off-diagonal: unit,
-- Pi.single_eq_of_ne,
-- add_zero; diagonal: Pi.single_eq_same, omega using h).
/-- Stepping toward `y` in coordinate `i` (with `x_i < y_i`) decreases the `graphNorm` distance
to `y` by exactly one. -/
private theorem graphNorm_add_unit_sub_add_one_eq {x y : Site d} {i : Fin d} (h : x i < y i) :
    graphNorm (x + unit i - y) + 1 = graphNorm (x - y) := by
  unfold graphNorm
  rw [← Finset.add_sum_erase _ (fun j => ((x + unit i - y) j).natAbs) (Finset.mem_univ i),
      ← Finset.add_sum_erase _ (fun j => ((x - y) j).natAbs) (Finset.mem_univ i)]
  rw [add_right_comm]
  congr 1
  · simp only [Pi.add_apply, Pi.sub_apply, unit, Pi.single_eq_same]
    have h1 : (((x i + 1 - y i).natAbs : ℤ)) = y i - x i - 1 := by
      rw [show x i + 1 - y i = -((y i - x i) - 1) by ring, Int.natAbs_neg,
        Int.natAbs_of_nonneg (by omega)]
    have h2 : (((x i - y i).natAbs : ℤ)) = y i - x i := by
      rw [show x i - y i = -(y i - x i) by ring, Int.natAbs_neg,
        Int.natAbs_of_nonneg (by omega)]
    omega
  · exact Finset.sum_congr rfl (fun j hj => by
      have hji : j ≠ i := Finset.ne_of_mem_erase hj
      have hxj : (x + unit i - y) j = (x - y) j := by
        simp only [Pi.add_apply, Pi.sub_apply, unit, Pi.single_eq_of_ne hji, add_zero]
      rw [hxj])

-- As graphNorm_add_unit_sub_add_one_eq with x - unit i (Pi.sub_apply, sub_zero).
/-- The symmetric statement of `graphNorm_add_unit_sub_add_one_eq` for `y_i < x_i`. -/
private theorem graphNorm_sub_unit_sub_add_one_eq {x y : Site d} {i : Fin d} (h : y i < x i) :
    graphNorm (x - unit i - y) + 1 = graphNorm (x - y) := by
  unfold graphNorm
  rw [← Finset.add_sum_erase _ (fun j => ((x - unit i - y) j).natAbs) (Finset.mem_univ i),
      ← Finset.add_sum_erase _ (fun j => ((x - y) j).natAbs) (Finset.mem_univ i)]
  rw [add_right_comm]
  congr 1
  · simp only [Pi.sub_apply, unit, Pi.single_eq_same]
    have h1 : (((x i - 1 - y i).natAbs : ℤ)) = x i - y i - 1 := by
      rw [show x i - 1 - y i = (x i - y i) - 1 by ring,
        Int.natAbs_of_nonneg (by omega)]
    have h2 : (((x i - y i).natAbs : ℤ)) = x i - y i :=
      Int.natAbs_of_nonneg (by omega)
    omega
  · exact Finset.sum_congr rfl (fun j hj => by
      have hji : j ≠ i := Finset.ne_of_mem_erase hj
      have hxj : (x - unit i - y) j = (x - y) j := by
        simp only [Pi.sub_apply, unit, Pi.single_eq_of_ne hji, sub_zero]
      rw [hxj])

-- ∃ i, x i ≠ y i (by_contra, funext, push_neg); lt_or_gt_of_ne: x + unit i with
-- add_unit_mem_box_of_lt, graphNorm_add_unit_sub_add_one_eq (Or.inl rfl), or x - unit i with
-- sub_unit_mem_box_of_lt,
-- graphNorm_sub_unit_sub_add_one_eq (Or.inr rfl).
/-- For `x ≠ y` in `box d m`, there is a neighbour `x'` of `x` in `box d m`, obtained by a single
lattice step toward `y`, whose `graphNorm` distance to `y` is one less than that of `x`. -/
private theorem exists_step_graphNorm_add_one_eq {m : ℕ} {x y : Site d} (hx : x ∈ box d m)
    (hy : y ∈ box d m)
    (hxy : x ≠ y) :
    ∃ x' ∈ box d m, ∃ i : Fin d, (x' = x + unit i ∨ x' = x - unit i) ∧
      graphNorm (x' - y) + 1 = graphNorm (x - y) := by
  have hex : ∃ i : Fin d, x i ≠ y i := by
    by_contra h
    exact hxy (funext fun i => by simpa using not_not.mp (not_exists.mp h i))
  obtain ⟨i, hi⟩ := hex
  rcases lt_or_gt_of_ne hi with hlt | hgt
  · exact ⟨x + unit i, add_unit_mem_box_of_lt hx hy hlt, i, Or.inl rfl,
      graphNorm_add_unit_sub_add_one_eq hlt⟩
  · exact ⟨x - unit i, sub_unit_mem_box_of_lt hx hy hgt, i, Or.inr rfl,
      graphNorm_sub_unit_sub_add_one_eq hgt⟩

-- pow_zero; graphNorm_eq_zero_iff, sub_eq_zero give x = y (subst); Network.killedHeat_zero,
-- if_pos hx, if_pos rfl.
/-- The base case `(2d)⁻¹^0 ≤ killedHeat C 0 x y` when `x ∈ C` and `graphNorm (x-y) = 0`. -/
private theorem inv_two_mul_pow_zero_le_killedHeat_zero (C : Set (Site d)) {x y : Site d}
    (hx : x ∈ C)
    (h : graphNorm (x - y) = 0) :
    (2 * (d : ℝ))⁻¹ ^ 0 ≤ Graph.killedHeat (lattice d) C 0 x y := by
  rw [pow_zero, Network.killedHeat_zero, if_pos hx]
  have hxy : x = y := by
    have h1 : x - y = 0 := graphNorm_eq_zero_iff.mp h
    simpa using sub_eq_zero.mp h1
  rw [if_pos hxy]

-- Monotone lattice path.  Induction on n generalizing x.  n = 0: x = y (graphNorm_eq_zero_iff),
-- killedHeat 0 = 1 (Network.killedHeat_zero, hB).  n+1: x ≠ y; step toward y (as
-- exists_step_sum_natAbs_add_one_eq:
-- x' := x ∓ unit i ∈ box m with graphNorm (x' - y) = n); killedHeat_div_two_mul_le_killedHeat_succ;
-- pow_succ.  SPLIT?
/-- The monotone-lattice-path lower bound: `(2d)⁻¹^n ≤ killedHeat C n x y` whenever `box d m ⊆
C`, `x, y ∈ box d m`, and `graphNorm (x-y) = n`. -/
private theorem inv_two_mul_pow_le_killedHeat_of_graphNorm_eq (hd : 1 ≤ d) (m : ℕ)
    (C : Set (Site d)) (hB : ∀ z ∈ box d m, z ∈ C) :
    ∀ (n : ℕ) (x y : Site d), x ∈ box d m → y ∈ box d m → graphNorm (x - y) = n →
      (2 * (d : ℝ))⁻¹ ^ n ≤ Graph.killedHeat (lattice d) C n x y := by
  have hdR : (0 : ℝ) < 2 * (d : ℝ) := by
    have h : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd
    linarith
  intro n
  induction n with
  | zero =>
    intro x y hx _ h
    exact inv_two_mul_pow_zero_le_killedHeat_zero C (hB x hx) h
  | succ n ih =>
    intro x y hx hy h
    have hxy : x ≠ y := by
      rintro rfl
      rw [sub_self, graphNorm_zero] at h
      omega
    obtain ⟨x', hx', i, hrel, hnorm⟩ := exists_step_graphNorm_add_one_eq hx hy hxy
    have h' : graphNorm (x' - y) = n := by omega
    have h50 := killedHeat_div_two_mul_le_killedHeat_succ hd C n (hB x hx) i hrel y
    have hih := ih x' y hx' hy h'
    calc (2 * (d : ℝ))⁻¹ ^ (n + 1) = (2 * (d : ℝ))⁻¹ ^ n / (2 * (d : ℝ)) := by
          rw [pow_succ, div_eq_mul_inv]
      _ ≤ Graph.killedHeat (lattice d) C n x' y / (2 * (d : ℝ)) :=
          div_le_div_of_nonneg_right hih hdR.le
      _ ≤ Graph.killedHeat (lattice d) C (n + 1) x y := h50

-- killedGreenReal_eq_tsum_killedHeat_div and Summable.le_tsum / le_tsum
-- (Network.summable_killedHeat, q ∉ B,
-- Network.killedHeat_nonneg); div_le_div_of_nonneg_right.
/-- `killedHeat B k x y / (2d) ≤ killedGreenReal B x y`, since the Green function is the full
series and each term is nonnegative. -/
private theorem killedHeat_div_two_mul_le_killedGreenReal (hd : 1 ≤ d) (B : Finset (Site d)) (k : ℕ)
    (x y : Site d) :
    Graph.killedHeat (lattice d) (B : Set (Site d)) k x y / (2 * (d : ℝ))
      ≤ Graph.killedGreenReal (lattice d) (B : Set (Site d)) x y := by
  haveI : NeZero d := ⟨by omega⟩
  obtain ⟨q, hq⟩ := Infinite.exists_notMem_finset B
  have hsum : Summable (fun k => Graph.killedHeat (lattice d) (B : Set (Site d)) k x y) :=
    Network.summable_killedHeat (Graph.Zd.latticeConnected d) B hq x y
  have hk : Graph.killedHeat (lattice d) (B : Set (Site d)) k x y
      ≤ ∑' j, Graph.killedHeat (lattice d) (B : Set (Site d)) j x y :=
    Summable.le_tsum hsum k (fun j _ => Network.killedHeat_nonneg _ j x y)
  rw [killedGreenReal_eq_tsum_killedHeat_div hd B x y]
  exact div_le_div_of_nonneg_right hk (by positivity)


-- ρ ↦ s conversion: s ≤ ρ ≤ 2 M s ⇒ ρ^{2-d} ≤ 2M s^{2-d}.  d = 1: zpow_one; d ≥ 2:
-- zpow_le_zpow_left₀-type antitonicity for nonpositive exponents (s ≤ ρ), and 1 ≤ 2M.
/-- For `s ≤ ρ ≤ 2Ms`, `ρ^{2-d} ≤ 2M s^{2-d}`. -/
private theorem rpow_two_sub_le_two_mul_rpow_two_sub (M s ρ : ℕ) (hM : 1 ≤ M) (hs : 1 ≤ s)
    (hsρ : s ≤ ρ) (hρ : ρ ≤ 2 * M * s)
    (hd : 1 ≤ d) :
    (ρ : ℝ) ^ ((2 : ℤ) - d) ≤ 2 * M * (s : ℝ) ^ ((2 : ℤ) - d) := by
  have hs1 : (1 : ℝ) ≤ (s : ℝ) := Nat.one_le_cast.mpr hs
  have hsρ' : (s : ℝ) ≤ (ρ : ℝ) := Nat.cast_le.mpr hsρ
  have hs0 : (0 : ℝ) < (s : ℝ) := Nat.cast_pos.mpr (lt_of_lt_of_le Nat.zero_lt_one hs)
  have hρ0 : (0 : ℝ) < (ρ : ℝ) := lt_of_lt_of_le hs0 hsρ'
  have hM1 : (1 : ℝ) ≤ (M : ℝ) := Nat.one_le_cast.mpr hM
  by_cases hd2 : 2 ≤ d
  · have hcast : ((d - 2 : ℕ) : ℤ) = (d : ℤ) - 2 := (by rw [Nat.cast_sub (R := ℤ) hd2]; ring)
    have he : ((2 : ℤ) - (d : ℤ)) = -(((d - 2 : ℕ) : ℤ)) := (by rw [hcast]; ring)
    have hpow : (s : ℝ) ^ (d - 2) ≤ (ρ : ℝ) ^ (d - 2) :=
      pow_le_pow_left₀ (le_of_lt hs0) hsρ' _
    have hA : ((ρ : ℝ) ^ (d - 2))⁻¹ ≤ ((s : ℝ) ^ (d - 2))⁻¹ :=
      (inv_le_inv₀ (pow_pos hρ0 _) (pow_pos hs0 _)).mpr hpow
    have hnn : (0 : ℝ) ≤ ((s : ℝ) ^ (d - 2))⁻¹ := inv_nonneg.mpr (pow_nonneg (le_of_lt hs0) _)
    have hM2 : (1 : ℝ) ≤ 2 * (M : ℝ) := (by linarith)
    have hB : ((s : ℝ) ^ (d - 2))⁻¹ ≤ 2 * (M : ℝ) * ((s : ℝ) ^ (d - 2))⁻¹ :=
      le_trans (le_of_eq (one_mul _).symm) (mul_le_mul_of_nonneg_right hM2 hnn)
    calc (ρ : ℝ) ^ ((2 : ℤ) - (d : ℤ))
        = ((ρ : ℝ) ^ (d - 2))⁻¹ := (by rw [he, zpow_neg, zpow_natCast])
      _ ≤ ((s : ℝ) ^ (d - 2))⁻¹ := hA
      _ ≤ 2 * (M : ℝ) * ((s : ℝ) ^ (d - 2))⁻¹ := hB
      _ = 2 * (M : ℝ) * (s : ℝ) ^ ((2 : ℤ) - (d : ℤ)) := (by rw [he, zpow_neg, zpow_natCast])
  · have hd1 : d = 1 := (by omega)
    subst hd1
    have h1e : ((2 : ℤ) - ((1 : ℕ) : ℤ)) = 1 := (by norm_num)
    rw [h1e, zpow_one, zpow_one]
    have hcast : ((2 * M * s : ℕ) : ℝ) = 2 * (M : ℝ) * (s : ℝ) := (by push_cast; ring)
    exact le_trans (Nat.cast_le.mpr hρ) (le_of_eq hcast)


-- For 1 ≤ ρ: ρ^{2-d} ≤ ρ (zpow_le_zpow_right₀ with 2 - d ≤ 1, one_le_cast), zpow_one.
/-- For `ρ ≥ 1`, `ρ^{2-d} ≤ ρ`. -/
private theorem rpow_two_sub_le_self (ρ : ℕ) (hρ : 1 ≤ ρ) (hd : 1 ≤ d) :
    (ρ : ℝ) ^ ((2 : ℤ) - d) ≤ ρ := by
  calc (ρ : ℝ) ^ ((2 : ℤ) - (d : ℤ)) ≤ (ρ : ℝ) ^ (1 : ℤ) :=
        zpow_le_zpow_right₀ (by exact_mod_cast hρ) (by omega)
    _ = ρ := zpow_one _


-- graphNorm (x - y) ≤ 2 d m for x, y ∈ box m (as sum_natAbs_le_two_mul_mul: each |x j - y j| ≤ 2m).
/-- For integers `a, b` with `|a|, |b| ≤ m`, `|a-b| ≤ 2m`. -/
private theorem natAbs_sub_le_two_mul_of_abs_le (m : ℕ) (a b : ℤ) (ha : |a| ≤ (m : ℤ))
    (hb : |b| ≤ (m : ℤ)) :
    (a - b).natAbs ≤ 2 * m := by
  have h1 : |a - b| ≤ (2 * m : ℤ) := by
    calc |a - b| ≤ |a| + |b| := abs_sub a b
      _ ≤ (m : ℤ) + m := add_le_add ha hb
      _ = 2 * m := by ring
  have h2 : ((a - b).natAbs : ℤ) ≤ 2 * m := by
    rw [Int.natCast_natAbs]; exact h1
  exact_mod_cast h2

/-- Implementation lemma for `graphNorm_sub_le_two_mul_mul_of_mem_box`. -/
private theorem graphNorm_sub_le_two_mul_mul_of_mem_box' (m : ℕ) {x y : Site d} (hx : x ∈ box d m)
    (hy : y ∈ box d m) :
    graphNorm (x - y) ≤ 2 * d * m := by
  rw [graphNorm]
  have hsum : ∑ i : Fin d, ((x - y) i).natAbs ≤ ∑ _i : Fin d, (2 * m) :=
    Finset.sum_le_sum (fun i _ => natAbs_sub_le_two_mul_of_abs_le m (x i) (y i) (hx i) (hy i))
  have hconst : (∑ _i : Fin d, (2 * m)) = 2 * d * m := by
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    push_cast
    ring
  rw [hconst] at hsum
  exact hsum

/-- For `x, y ∈ box d m`, `graphNorm (x-y) ≤ 2dm`. -/
private theorem graphNorm_sub_le_two_mul_mul_of_mem_box (m : ℕ) {x y : Site d} (hx : x ∈ box d m)
    (hy : y ∈ box d m) :
    graphNorm (x - y) ≤ 2 * d * m := by
  exact graphNorm_sub_le_two_mul_mul_of_mem_box' m hx hy


-- Box monotonicity: intro i; le_trans (hx i) (Nat.cast_le.mpr hab) (exact_mod_cast).
/-- Box monotonicity: `x ∈ box d a` and `a ≤ b` give `x ∈ box d b`. -/
private theorem mem_box_of_mem_box_of_le {a b : ℕ} (hab : a ≤ b) {x : Site d} (hx : x ∈ box d a) :
    x ∈ box d b := by
  intro i
  exact le_trans (hx i) (by exact_mod_cast hab)

-- Nat.le_div_iff_mul_le (0 < M): (s₂ + 1) * M ≤ ρ (mul_comm).
/-- If `M(s₂+1) ≤ ρ`, then `s₂+1 ≤ ρ/M`. -/
private theorem add_one_le_ediv_of_mul_le (M s₂ ρ : ℕ) (hM : 1 ≤ M) (hρ : M * (s₂ + 1) ≤ ρ) :
    s₂ + 1 ≤ ρ / M := by
  exact (Nat.le_div_iff_mul_le (by omega : 0 < M)).mpr (by rw [Nat.mul_comm]; exact hρ)

-- Nat.lt_div_mul_add (0 < M): ρ < ρ/M * M + M ≤ 2 M (ρ/M) (hs; nlinarith).
/-- If `ρ/M ≥ 1`, then `ρ ≤ 2M(ρ/M)`. -/
private theorem le_two_mul_mul_ediv_of_one_le_ediv (M ρ : ℕ) (hM : 1 ≤ M) (hs : 1 ≤ ρ / M) :
    ρ ≤ 2 * M * (ρ / M) := by
  have hMpos : 0 < M := by omega
  have h1 : ρ < ρ / M * M + M := Nat.lt_div_mul_add hMpos
  have h3 : M ≤ M * (ρ / M) := by
    have := Nat.mul_le_mul_left M hs
    simpa using this
  have h4 : ρ / M * M + M ≤ ρ / M * M + M * (ρ / M) := Nat.add_le_add_left h3 _
  have h5 : ρ / M * M + M * (ρ / M) = 2 * M * (ρ / M) := by ring
  exact le_of_lt (h1.trans_le (h4.trans_eq h5))

-- m ≤ K ρ ≤ K (2 M s) (Nat.mul_le_mul_left); ring_nf / Nat.mul_assoc, Nat.mul_left_comm.
/-- If `m ≤ Kρ` and `ρ ≤ 2Ms`, then `m ≤ 2KMs`. -/
private theorem le_two_mul_mul_mul_of_le_mul (K M s ρ m : ℕ) (hm : m ≤ K * ρ) (hρ : ρ ≤ 2 * M * s) :
    m ≤ 2 * K * M * s := by
  calc m ≤ K * ρ := hm
    _ ≤ K * (2 * M * s) := Nat.mul_le_mul_left K hρ
    _ = 2 * K * M * s := by ring

-- 2 d m ≤ 2 d (K ρ) ≤ 2 d (K ρ₀) (Nat.mul_le_mul_left twice); Nat.mul_assoc.
/-- If `m ≤ Kρ` and `ρ ≤ ρ₀`, then `2dm ≤ 2dKρ₀`. -/
private theorem two_mul_mul_le_two_mul_mul_mul_of_le (K m ρ ρ₀ : ℕ) (hm : m ≤ K * ρ) (hρ : ρ ≤ ρ₀) :
    2 * d * m ≤ 2 * d * K * ρ₀ := by
  calc 2 * d * m ≤ 2 * d * (K * ρ) := Nat.mul_le_mul_left (2 * d) hm
    _ ≤ 2 * d * (K * ρ₀) := Nat.mul_le_mul_left (2 * d) (Nat.mul_le_mul_left K hρ)
    _ = 2 * d * K * ρ₀ := by ring

-- pow_le_pow_of_le_one (inv_nonneg, inv_le_one_of_one_le₀ with 1 ≤ 2 d) (by omega).
/-- Monotonicity of the base case bound in the box radius: `(2d)⁻¹^{L+1} ≤ (2d)⁻¹^{ℓ+1}` when `ℓ
≤ L`. -/
private theorem inv_two_mul_pow_add_one_le_of_le (hd : 1 ≤ d) (ℓ L : ℕ) (h : ℓ ≤ L) :
    (2 * (d : ℝ))⁻¹ ^ (L + 1) ≤ (2 * (d : ℝ))⁻¹ ^ (ℓ + 1) := by
  have hdR : (1 : ℝ) ≤ 2 * (d : ℝ) := by
    have h1 : (1 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
    linarith
  have h0 : (0 : ℝ) ≤ (2 * (d : ℝ))⁻¹ := inv_nonneg.mpr (by linarith)
  have h1 : (2 * (d : ℝ))⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hdR
  exact pow_le_pow_of_le_one h0 h1 (by omega : ℓ + 1 ≤ L + 1)

-- inv_two_mul_pow_le_killedHeat_of_graphNorm_eq hd m (B : Set) (Finset.mem_coe.mpr ∘ hB) (graphNorm
-- (x - y)) x y hx hy rfl,
-- killedHeat_div_two_mul_le_killedGreenReal hd B, pow_succ, div_eq_mul_inv,
-- div_le_div_of_nonneg_right,
-- inv_two_mul_pow_add_one_le_of_le hd _ L hL.
/-- The small-radius Green-function lower bound `(2d)⁻¹^{L+1} ≤ killedGreenReal B x y`, from the
monotone-lattice-path bound and `killedHeat_div_two_mul_le_killedGreenReal`. -/
private theorem inv_two_mul_pow_add_one_le_killedGreenReal (hd : 1 ≤ d) (B : Finset (Site d))
    (m L : ℕ)
    (hB : ∀ z ∈ box d m, z ∈ B) {x y : Site d} (hx : x ∈ box d m) (hy : y ∈ box d m)
    (hL : graphNorm (x - y) ≤ L) :
    (2 * (d : ℝ))⁻¹ ^ (L + 1) ≤ Graph.killedGreenReal (lattice d) (B : Set (Site d)) x y := by
  have hdR : (0 : ℝ) < 2 * (d : ℝ) := by
    have h : (0 : ℝ) < (d : ℝ) := by exact_mod_cast (Nat.lt_of_lt_of_le Nat.zero_lt_one hd)
    linarith
  have h1 : (2 * (d : ℝ))⁻¹ ^ (L + 1) ≤ (2 * (d : ℝ))⁻¹ ^ (graphNorm (x - y) + 1) := by
    have h0 : (0 : ℝ) ≤ (2 * (d : ℝ))⁻¹ := inv_nonneg.mpr hdR.le
    have h1' : (2 * (d : ℝ))⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (by
      have h : (1 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
      linarith)
    exact pow_le_pow_of_le_one h0 h1' (by omega : graphNorm (x - y) + 1 ≤ L + 1)
  have h2 := inv_two_mul_pow_le_killedHeat_of_graphNorm_eq hd m (B : Set (Site d))
      (fun z hz => Finset.mem_coe.mpr (hB z hz))
    (graphNorm (x - y)) x y hx hy rfl
  have h3 := killedHeat_div_two_mul_le_killedGreenReal hd B (graphNorm (x - y)) x y
  calc (2 * (d : ℝ))⁻¹ ^ (L + 1) ≤ (2 * (d : ℝ))⁻¹ ^ (graphNorm (x - y) + 1) := h1
    _ = (2 * (d : ℝ))⁻¹ ^ (graphNorm (x - y)) / (2 * (d : ℝ)) := by rw [pow_succ, div_eq_mul_inv]
    _ ≤ Graph.killedHeat (lattice d) (B : Set (Site d)) (graphNorm (x - y)) x y / (2 * (d : ℝ)) :=
        div_le_div_of_nonneg_right h2 hdR.le
    _ ≤ Graph.killedGreenReal (lattice d) (B : Set (Site d)) x y := h3

-- c R ≤ (c₃/(2M)) R ≤ (c₃/(2M)) (2 M S) = c₃ S ≤ g: mul_le_mul_of_nonneg_right,
-- mul_le_mul_of_nonneg_left
-- (div_nonneg), field_simp / div_mul_cancel₀.
/-- Interpolation step: `c ≤ c₃/(2M)`, `R ≤ 2MS` and `c₃S ≤ g` together give `cR ≤ g`. -/
private theorem mul_le_of_le_div_two_mul_of_le (c c₃ M R S g : ℝ) (hM : 0 < M)
    (hc : c ≤ c₃ / (2 * M)) (hc₃ : 0 ≤ c₃) (hR0 : 0 ≤ R) (hR : R ≤ 2 * M * S)
    (hg : c₃ * S ≤ g) : c * R ≤ g := by
  have h1 : c * R ≤ (c₃ / (2 * M)) * (2 * M * S) :=
    mul_le_mul hc hR hR0 (by positivity)
  have h2 : (c₃ / (2 * M)) * (2 * M * S) = c₃ * S := by
    field_simp
  linarith

-- c R ≤ c ρ₀ ≤ (a/ρ₀) ρ₀ = a ≤ g: mul_le_mul_of_nonneg_left, mul_le_mul_of_nonneg_right,
-- div_mul_cancel₀.
/-- Interpolation step: `c ≤ a/ρ₀`, `R ≤ ρ₀` and `a ≤ g` together give `cR ≤ g`. -/
private theorem mul_le_of_le_div_of_le (c a R ρ₀ g : ℝ) (hc0 : 0 ≤ c) (hρ₀ : 0 < ρ₀)
    (hc : c ≤ a / ρ₀) (hR : R ≤ ρ₀) (hg : a ≤ g) : c * R ≤ g := by
  have h1 : c * R ≤ c * ρ₀ := mul_le_mul_of_nonneg_left hR hc0
  have h2 : c * ρ₀ ≤ a := by
    have h3 : c * ρ₀ ≤ (a / ρ₀) * ρ₀ := mul_le_mul_of_nonneg_right hc (le_of_lt hρ₀)
    rwa [div_mul_cancel₀ a (ne_of_gt hρ₀)] at h3
  linarith

-- Fix M, (for K' := 2 K M) c₃, s₂ from exists_const_mul_rpow_le_killedGreenReal.  ρ₀ := M (s₂ + 1).
-- ρ ≥ ρ₀: s := ρ / M (Nat.div), s ≥ s₂, s ≤ ρ, ρ ≤ 2 M s, m ≤ Kρ ≤ K'·s,
--   box (m + M s) ⊆ box (m + ρ) (box monotonicity, cf. Harnack.lean),
--   exists_const_mul_rpow_le_killedGreenReal, rpow_two_sub_le_two_mul_rpow_two_sub.
-- ρ < ρ₀: ℓ := graphNorm (x - y) ≤ 2dKρ₀ (graphNorm_sub_le_two_mul_mul_of_mem_box);
-- inv_two_mul_pow_le_killedHeat_of_graphNorm_eq (box m ⊆ B),
-- killedHeat_div_two_mul_le_killedGreenReal:
--   g ≥ (2d)⁻¹^(2dKρ₀+1), and ρ^{2-d} ≤ ρ₀ (rpow_two_sub_le_self).
-- c := min (c₃/(2M)) ((2d)⁻¹^(2dKρ₀+1)/ρ₀).  SPLIT?
/-- For `B` containing `box d (m+ρ)` and `x, y ∈ box d m` with `m ≤ Kρ`, the killed Green
function satisfies `g_B(x,y) ≥ c(K) ρ^{2-d}`, uniformly in `d ≥ 1`. -/
theorem killedGreenReal_ge_box (hd : 1 ≤ d) (K : ℕ) :
    ∃ c : ℝ, 0 < c ∧ ∀ (m ρ : ℕ), 1 ≤ ρ → m ≤ K * ρ → ∀ B : Finset (Site d),
      (∀ z ∈ box d (m + ρ), z ∈ B) → ∀ x ∈ box d m, ∀ y ∈ box d m,
        c * (ρ : ℝ) ^ ((2 : ℤ) - d) ≤ Graph.killedGreenReal (lattice d) (B : Set (Site d)) x y := by
  obtain ⟨M, hM1, h49⟩ := exists_const_mul_rpow_le_killedGreenReal hd
  obtain ⟨c₃, hc₃, s₂, _, H⟩ := h49 (2 * K * M)
  have hdR : (0 : ℝ) < 2 * (d : ℝ) := by
    have h : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd
    linarith
  have hMR : (0 : ℝ) < (M : ℝ) := by exact_mod_cast hM1
  have hρ₀N : 0 < M * (s₂ + 1) := Nat.mul_pos hM1 (Nat.succ_pos s₂)
  have hρ₀R : (0 : ℝ) < ((M * (s₂ + 1) : ℕ) : ℝ) := by exact_mod_cast hρ₀N
  have ha : (0 : ℝ) < (2 * (d : ℝ))⁻¹ ^ (2 * d * K * (M * (s₂ + 1)) + 1) :=
    pow_pos (inv_pos.mpr hdR) _
  have hcpos : (0 : ℝ) < min (c₃ / (2 * (M : ℝ)))
      ((2 * (d : ℝ))⁻¹ ^ (2 * d * K * (M * (s₂ + 1)) + 1) / ((M * (s₂ + 1) : ℕ) : ℝ)) :=
    lt_min (div_pos hc₃ (by linarith)) (div_pos ha hρ₀R)
  refine ⟨_, hcpos, ?_⟩
  intro m ρ hρ hm B hB x hx y hy
  have hR0 : (0 : ℝ) ≤ (ρ : ℝ) ^ ((2 : ℤ) - d) := zpow_nonneg (Nat.cast_nonneg _) _
  by_cases hbig : M * (s₂ + 1) ≤ ρ
  · have hs2 : s₂ + 1 ≤ ρ / M := add_one_le_ediv_of_mul_le M s₂ ρ hM1 hbig
    have hsρ : ρ / M ≤ ρ := Nat.div_le_self ρ M
    have hρs : ρ ≤ 2 * M * (ρ / M) := le_two_mul_mul_ediv_of_one_le_ediv M ρ hM1 (by omega)
    have hMs : M * (ρ / M) ≤ ρ := Nat.mul_div_le ρ M
    have hm' : m ≤ 2 * K * M * (ρ / M) := le_two_mul_mul_mul_of_le_mul K M (ρ / M) ρ m hm hρs
    have hB' : ∀ z ∈ box d (m + M * (ρ / M)), z ∈ B :=
      fun z hz => hB z (mem_box_of_mem_box_of_le (by omega) hz)
    have hg := H (ρ / M) (by omega) m hm' B hB' x hx y hy
    have h53 := rpow_two_sub_le_two_mul_rpow_two_sub M (ρ / M) ρ hM1 (by omega) hsρ hρs hd
    exact mul_le_of_le_div_two_mul_of_le _ c₃ (M : ℝ) _ _ _ hMR (min_le_left _ _) hc₃.le hR0 h53 hg
  · have hρle : ρ ≤ M * (s₂ + 1) := by omega
    have hnorm : graphNorm (x - y) ≤ 2 * d * K * (M * (s₂ + 1)) :=
      le_trans (graphNorm_sub_le_two_mul_mul_of_mem_box m hx hy)
          (two_mul_mul_le_two_mul_mul_mul_of_le K m ρ _ hm hρle)
    have hB' : ∀ z ∈ box d m, z ∈ B :=
      fun z hz => hB z (mem_box_of_mem_box_of_le (by omega) hz)
    have hg := inv_two_mul_pow_add_one_le_killedGreenReal hd B m _ hB' hx hy hnorm
    have hRρ₀ : (ρ : ℝ) ^ ((2 : ℤ) - d) ≤ ((M * (s₂ + 1) : ℕ) : ℝ) :=
      le_trans (rpow_two_sub_le_self ρ hρ hd) (by exact_mod_cast hρle)
    exact mul_le_of_le_div_of_le _ _ _ _ _ hcpos.le hρ₀R (min_le_right _ _) hRρ₀ hg

end GreenTwoSided

end LatticeProb
