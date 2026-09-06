/-
The truncated Green function of the lazy random walk, and the growth the papers
quote for it: `G_n(0,0)` is of order `√n` in `d = 1`, of order `log n` in
`d = 2`, and bounded in `d ≥ 3`.

`lazyGreen n y x = ∑_{k < n} Q^k(y, x)` is the expected number of visits to `x`
before time `n` of the lazy walk started at `y`.  It is a function of `x - y`
alone, so every estimate is an estimate at the origin.

The upper bounds come from the sup bound `Q^r(0,x) = O(r^{-d/2})` of
`LatticeProb.iterate_delta0_sup_bound` together with the three series bounds of
`LatticeProb.Walk.Series`, and are the ones the papers cite.  The lower bounds
come from the opposite estimate `Q^r(0,0) ≥ (4r+1)^{-d/2}`, which needs no local
limit theorem: the coordinate decomposition writes `Q^r(0,0)` as an average over
schedules of a product of one-dimensional central weights, each schedule spends
at most `r` steps in each coordinate, and the one-dimensional central weight
`p_m(0)` is at least `(4m+1)^{-1/2}` because `p_m(0)^2 (4m+1)` is
nondecreasing in `m`.
-/
import Mathlib
import LatticeProb.Walk.GreenBounds

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace LatticeProb

open Finset

variable {d : ℕ}

/-! ### The kernel and the truncated Green function -/

/-- The point mass at `y`. -/
noncomputable def delta (y : Site d) : Site d → ℝ := fun x => if x = y then 1 else 0

theorem delta_eq (y x : Site d) : delta y x = (delta0 : Site d → ℝ) (x - y) := by
  unfold delta delta0
  simp [sub_eq_zero]

/-- Translating the argument commutes with one step of the lazy walk. -/
theorem Q_translate (f : Site d → ℝ) (y : Site d) :
    Q (fun x => f (x - y)) = fun x => Q f (x - y) := by
  funext x
  unfold Q
  congr 2
  refine Finset.sum_congr rfl fun a _ => ?_
  show f (x + dirVec a - y) = f (x - y + dirVec a)
  congr 1
  abel

theorem Q_iterate_translate (f : Site d → ℝ) (y : Site d) (k : ℕ) (x : Site d) :
    Q^[k] (fun z => f (z - y)) x = Q^[k] f (x - y) := by
  induction k generalizing x with
  | zero => rfl
  | succ k ih =>
      simp only [Function.iterate_succ_apply']
      rw [show Q^[k] (fun z => f (z - y)) = fun z => Q^[k] f (z - y) from funext ih,
        Q_translate]

/-- The `k`-step transition kernel of the lazy walk, `Q^k(y, x)`. -/
noncomputable def lazyKernel (k : ℕ) (y x : Site d) : ℝ := Q^[k] (delta y) x

/-- The truncated Green function of the lazy walk,
`G_n(y, x) = ∑_{k < n} Q^k(y, x)`: the expected number of visits to `x` strictly
before time `n`, starting from `y`. -/
noncomputable def lazyGreen (n : ℕ) (y x : Site d) : ℝ :=
  ∑ k ∈ Finset.range n, lazyKernel k y x

theorem lazyKernel_eq (k : ℕ) (y x : Site d) :
    lazyKernel k y x = Q^[k] (delta0 : Site d → ℝ) (x - y) := by
  unfold lazyKernel
  rw [show (delta y : Site d → ℝ) = fun z => (delta0 : Site d → ℝ) (z - y) from
    funext fun z => delta_eq y z]
  exact Q_iterate_translate _ y k x

/-- The truncated Green function depends only on the displacement, and at the
origin it is the `g_R` of `LatticeProb.Walk.Lazy`. -/
theorem lazyGreen_eq (n : ℕ) (y x : Site d) : lazyGreen n y x = gR n (x - y) := by
  unfold lazyGreen gR
  exact Finset.sum_congr rfl fun k _ => lazyKernel_eq k y x

theorem lazyGreen_zero (n : ℕ) : lazyGreen n (0 : Site d) 0 = gR n (0 : Site d) := by
  rw [lazyGreen_eq]; norm_num

theorem lazyGreen_nonneg (n : ℕ) (y x : Site d) : 0 ≤ lazyGreen n y x := by
  rw [lazyGreen_eq]; exact gR_nonneg n _

/-! ### The lower bound on the one-dimensional central weight -/

/-- `p_m(0)^2 (4m+1)` is at least `1`, by induction on `m` from
`p_{m+1}(0)/p_m(0) = (2m+1)/(2m+2)`: the inequality
`(2m+1)^2 (4m+5) ≥ (2m+2)^2 (4m+1)` is what makes the induction close. -/
theorem one_le_sq_P1_zero_mul (m : ℕ) : 1 ≤ P1 m 0 ^ 2 * (4 * (m : ℝ) + 1) := by
  induction m with
  | zero =>
    have h0 : P1 0 0 = 1 := by rw [P1_zero_eq]; norm_num [Nat.centralBinom]
    rw [h0]; norm_num
  | succ m ih =>
    have hpos := P1_zero_pos m
    have hrec := P1_zero_succ m
    have hm : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
    have hden : (0 : ℝ) < 2 * (m : ℝ) + 2 := by linarith
    have hsq : (0 : ℝ) < P1 m 0 ^ 2 := by positivity
    have hkey : ((2 * (m : ℝ) + 1) / (2 * (m : ℝ) + 2)) ^ 2 * (4 * ((m : ℝ) + 1) + 1)
        ≥ 4 * (m : ℝ) + 1 := by
      rw [div_pow, div_mul_eq_mul_div, ge_iff_le, le_div_iff₀ (by positivity)]
      nlinarith [sq_nonneg ((m : ℝ))]
    have hcast : ((m + 1 : ℕ) : ℝ) = (m : ℝ) + 1 := by push_cast; ring
    rw [hcast, hrec, mul_pow]
    nlinarith [hkey, ih, hsq]

/-- `p_m(0) ≥ (4m+1)^{-1/2}`. -/
theorem inv_sqrt_le_P1_zero (m : ℕ) :
    (Real.sqrt (4 * (m : ℝ) + 1))⁻¹ ≤ P1 m 0 := by
  have hm : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
  have hpos : (0 : ℝ) < 4 * (m : ℝ) + 1 := by linarith
  have hs : (0 : ℝ) < Real.sqrt (4 * (m : ℝ) + 1) := Real.sqrt_pos.mpr hpos
  have hsq : Real.sqrt (4 * (m : ℝ) + 1) ^ 2 = 4 * (m : ℝ) + 1 := Real.sq_sqrt hpos.le
  have h := one_le_sq_P1_zero_mul m
  have hp := P1_zero_pos m
  have ht : (P1 m 0 * Real.sqrt (4 * (m : ℝ) + 1)) ^ 2 = P1 m 0 ^ 2 * (4 * (m : ℝ) + 1) := by
    rw [mul_pow, hsq]
  have h1 : 1 ≤ (P1 m 0 * Real.sqrt (4 * (m : ℝ) + 1)) ^ 2 := by rw [ht]; exact h
  rw [inv_le_iff_one_le_mul₀ hs]
  nlinarith [h1, mul_pos hp hs]

/-! ### The lower bound on the kernel at the origin -/

/-- `Q^r(0,0) ≥ (4r+1)^{-d/2}`.  Each of the `d^r` coordinate schedules spends
at most `r` steps in each coordinate, so the product of one-dimensional central
weights it contributes is at least `(4r+1)^{-d/2}`. -/
theorem iterate_delta0_zero_ge (hd : 0 < d) (r : ℕ) :
    ((Real.sqrt (4 * (r : ℝ) + 1))⁻¹) ^ d ≤ Q^[r] (delta0 : Site d → ℝ) (0 : Site d) := by
  have hr : (0 : ℝ) ≤ (r : ℝ) := Nat.cast_nonneg r
  have hdr : (0 : ℝ) < (d : ℝ) ^ r := by
    have : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd
    positivity
  have hterm : ∀ c : Fin r → Fin d,
      ((Real.sqrt (4 * (r : ℝ) + 1))⁻¹) ^ d ≤ K (cnt c) (0 : Site d) := by
    intro c
    unfold K
    rw [show ((Real.sqrt (4 * (r : ℝ) + 1))⁻¹) ^ d
        = ∏ _i : Fin d, (Real.sqrt (4 * (r : ℝ) + 1))⁻¹ by
      rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]]
    refine Finset.prod_le_prod (fun i _ => by positivity) fun i _ => ?_
    have hle : (cnt c i : ℝ) ≤ (r : ℝ) := by exact_mod_cast cnt_le c i
    refine le_trans ?_ (inv_sqrt_le_P1_zero (cnt c i))
    have h3 : (0 : ℝ) < Real.sqrt (4 * (cnt c i : ℝ) + 1) := Real.sqrt_pos.mpr (by positivity)
    have h2 : Real.sqrt (4 * (cnt c i : ℝ) + 1) ≤ Real.sqrt (4 * (r : ℝ) + 1) :=
      Real.sqrt_le_sqrt (by linarith)
    exact inv_anti₀ h3 h2
  rw [iterate_delta0_eq hd r 0, le_div_iff₀ hdr]
  calc ((Real.sqrt (4 * (r : ℝ) + 1))⁻¹) ^ d * (d : ℝ) ^ r
      = ∑ _c : Fin r → Fin d, ((Real.sqrt (4 * (r : ℝ) + 1))⁻¹) ^ d := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fun, Fintype.card_fin,
          Fintype.card_fin, nsmul_eq_mul]
        push_cast
        ring
    _ ≤ ∑ c : Fin r → Fin d, K (cnt c) (0 : Site d) :=
        Finset.sum_le_sum fun c _ => hterm c

/-- `g_R(0) ≥ ∑_{r < R} (4r+1)^{-d/2}`. -/
theorem sum_le_gR_zero (hd : 0 < d) (R : ℕ) :
    ∑ r ∈ Finset.range R, ((Real.sqrt (4 * (r : ℝ) + 1))⁻¹) ^ d ≤ gR R (0 : Site d) :=
  Finset.sum_le_sum fun r _ => iterate_delta0_zero_ge hd r


/-! ### Telescoping sums -/

/-- `∑_{r < n} (4r+1)^{-1/2} ≥ (√(4n+1) - 1)/2`: each term dominates half of a
telescoping difference of square roots. -/
theorem sqrt_sub_one_le_sum_inv_sqrt (n : ℕ) :
    (Real.sqrt (4 * (n : ℝ) + 1) - 1) / 2
      ≤ ∑ r ∈ Finset.range n, (Real.sqrt (4 * (r : ℝ) + 1))⁻¹ := by
  induction n with
  | zero => norm_num
  | succ n ih =>
      have hn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
      have hp : (0 : ℝ) < 4 * (n : ℝ) + 1 := by linarith
      have hs : (0 : ℝ) < Real.sqrt (4 * (n : ℝ) + 1) := Real.sqrt_pos.mpr hp
      have hsq : Real.sqrt (4 * (n : ℝ) + 1) ^ 2 = 4 * (n : ℝ) + 1 := Real.sq_sqrt hp.le
      have hp' : (0 : ℝ) < 4 * ((n : ℝ) + 1) + 1 := by linarith
      have hs' : (0 : ℝ) < Real.sqrt (4 * ((n : ℝ) + 1) + 1) := Real.sqrt_pos.mpr hp'
      have hsq' : Real.sqrt (4 * ((n : ℝ) + 1) + 1) ^ 2 = 4 * ((n : ℝ) + 1) + 1 :=
        Real.sq_sqrt hp'.le
      have hstep : (Real.sqrt (4 * ((n : ℝ) + 1) + 1) - Real.sqrt (4 * (n : ℝ) + 1)) / 2
          ≤ (Real.sqrt (4 * (n : ℝ) + 1))⁻¹ := by
        rw [div_le_iff₀ (by norm_num), inv_eq_one_div, div_mul_eq_mul_div,
          le_div_iff₀ hs]
        nlinarith [hs, hs', hsq, hsq', sq_nonneg (Real.sqrt (4 * ((n : ℝ) + 1) + 1)
          - Real.sqrt (4 * (n : ℝ) + 1))]
      rw [Finset.sum_range_succ]
      have hcast : ((n + 1 : ℕ) : ℝ) = (n : ℝ) + 1 := by push_cast; ring
      rw [hcast]
      linarith [ih, hstep]

/-- `∑_{r < n} (r+1)^{-1} ≥ log (n+1)`, by telescoping `log((r+2)/(r+1)) ≤ 1/(r+1)`. -/
theorem log_le_sum_inv_succ (n : ℕ) :
    Real.log ((n : ℝ) + 1) ≤ ∑ r ∈ Finset.range n, ((r : ℝ) + 1)⁻¹ := by
  induction n with
  | zero => norm_num
  | succ n ih =>
      have hn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
      have h1 : (0 : ℝ) < (n : ℝ) + 1 := by linarith
      have h2 : (0 : ℝ) < (n : ℝ) + 2 := by linarith
      have hstep : Real.log ((n : ℝ) + 2) - Real.log ((n : ℝ) + 1) ≤ ((n : ℝ) + 1)⁻¹ := by
        have hlog : Real.log (((n : ℝ) + 2) / ((n : ℝ) + 1))
            ≤ ((n : ℝ) + 2) / ((n : ℝ) + 1) - 1 :=
          Real.log_le_sub_one_of_pos (by positivity)
        rw [Real.log_div (by linarith) (by linarith)] at hlog
        have hid : ((n : ℝ) + 2) / ((n : ℝ) + 1) - 1 = ((n : ℝ) + 1)⁻¹ := by
          field_simp; ring
        linarith [hlog, hid]
      rw [Finset.sum_range_succ]
      have hcast : ((n + 1 : ℕ) : ℝ) + 1 = (n : ℝ) + 2 := by push_cast; ring
      rw [hcast]
      have hcast2 : ((n : ℕ) : ℝ) + 1 = (n : ℝ) + 1 := rfl
      linarith [ih, hstep]

/-! ### `d = 1`: the truncated Green function is of order `√n` -/

/-- `g_n(0) ≥ √n - 1/2` in one dimension. -/
theorem sqrt_le_gR_one_dim (n : ℕ) :
    Real.sqrt (n : ℝ) - 1 / 2 ≤ gR n (0 : Site 1) := by
  refine le_trans ?_ (sum_le_gR_zero (d := 1) one_pos n)
  have hpow : ∀ r : ℕ, ((Real.sqrt (4 * (r : ℝ) + 1))⁻¹) ^ 1
      = (Real.sqrt (4 * (r : ℝ) + 1))⁻¹ := fun r => pow_one _
  rw [Finset.sum_congr rfl fun r _ => hpow r]
  refine le_trans ?_ (sqrt_sub_one_le_sum_inv_sqrt n)
  have hn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
  have h2 : 2 * Real.sqrt (n : ℝ) ≤ Real.sqrt (4 * (n : ℝ) + 1) := by
    have hb : (2 * Real.sqrt (n : ℝ)) ^ 2 ≤ 4 * (n : ℝ) + 1 := by
      rw [mul_pow, Real.sq_sqrt hn]; norm_num
    nlinarith [Real.sq_sqrt (show (0:ℝ) ≤ 4 * (n : ℝ) + 1 by linarith),
      Real.sqrt_nonneg (4 * (n : ℝ) + 1), Real.sqrt_nonneg (n : ℝ), hb]
  linarith

/-- `g_n(0) ≤ 1 + 2 C √n` in one dimension, with `C = greenConst 1`. -/
theorem gR_one_dim_le (n : ℕ) (hn : 1 ≤ n) :
    gR n (0 : Site 1) ≤ 1 + 2 * greenConst 1 * Real.sqrt (n : ℝ) := by
  have hmain := gR_le (d := 1) one_pos hn (0 : Site 1)
  have hterm : ∀ r ∈ Finset.Ico 1 n,
      greenConst 1 * ((r : ℝ) ^ (-((1 : ℕ) : ℝ) / 2)) = greenConst 1 * (Real.sqrt (r : ℝ))⁻¹ := by
    intro r hr
    have hr1 : 1 ≤ r := (Finset.mem_Ico.mp hr).1
    have hrpos : (0 : ℝ) < (r : ℝ) := by exact_mod_cast hr1
    congr 1
    rw [show -((1 : ℕ) : ℝ) / 2 = -(1 / 2) by norm_num, Real.rpow_neg hrpos.le,
      ← Real.sqrt_eq_rpow]
  rw [Finset.sum_congr rfl hterm, ← Finset.mul_sum] at hmain
  have hreindex : ∑ r ∈ Finset.Ico 1 n, (Real.sqrt (r : ℝ))⁻¹
      = ∑ k ∈ Finset.range (n - 1), (1 : ℝ) / Real.sqrt ((k : ℝ) + 1) := by
    rw [Finset.sum_Ico_eq_sum_range]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [one_div]
    congr 2
    push_cast
    ring
  have hsum : ∑ r ∈ Finset.Ico 1 n, (Real.sqrt (r : ℝ))⁻¹ ≤ 2 * Real.sqrt (n : ℝ) := by
    rw [hreindex]
    refine (sum_inv_sqrt_le (n - 1)).trans ?_
    have : Real.sqrt ((n - 1 : ℕ) : ℝ) ≤ Real.sqrt (n : ℝ) :=
      Real.sqrt_le_sqrt (by exact_mod_cast Nat.sub_le n 1)
    linarith
  have hg : 0 ≤ greenConst 1 := greenConst_nonneg 1
  nlinarith [hmain, hsum, hg]

/-! ### `d = 2`: the truncated Green function is of order `log n` -/

/-- `g_n(0) ≥ (log (n+1)) / 4` in two dimensions. -/
theorem log_le_gR_two_dim (n : ℕ) :
    Real.log ((n : ℝ) + 1) / 4 ≤ gR n (0 : Site 2) := by
  refine le_trans ?_ (sum_le_gR_zero (d := 2) (by norm_num) n)
  have hterm : ∀ r ∈ Finset.range n, ((r : ℝ) + 1)⁻¹ / 4
      ≤ ((Real.sqrt (4 * (r : ℝ) + 1))⁻¹) ^ 2 := by
    intro r _
    have hr : (0 : ℝ) ≤ (r : ℝ) := Nat.cast_nonneg r
    have hp : (0 : ℝ) < 4 * (r : ℝ) + 1 := by linarith
    have hsq : Real.sqrt (4 * (r : ℝ) + 1) ^ 2 = 4 * (r : ℝ) + 1 := Real.sq_sqrt hp.le
    rw [inv_pow, hsq, div_le_iff₀ (by norm_num), inv_mul_eq_div, le_div_iff₀ hp,
      inv_mul_eq_div, div_le_iff₀ (by linarith)]
    linarith
  have := Finset.sum_le_sum hterm
  rw [← Finset.sum_div] at this
  linarith [log_le_sum_inv_succ n, this]

/-- `g_n(0) ≤ 1 + C (1 + log n)` in two dimensions, with `C = greenConst 2`. -/
theorem gR_two_dim_le (n : ℕ) (hn : 1 ≤ n) :
    gR n (0 : Site 2) ≤ 1 + greenConst 2 * (1 + Real.log (n : ℝ)) := by
  have hmain := gR_le (d := 2) (by norm_num) hn (0 : Site 2)
  have hterm : ∀ r ∈ Finset.Ico 1 n,
      greenConst 2 * ((r : ℝ) ^ (-((2 : ℕ) : ℝ) / 2)) = greenConst 2 * ((r : ℝ))⁻¹ := by
    intro r hr
    have hr1 : 1 ≤ r := (Finset.mem_Ico.mp hr).1
    have hrpos : (0 : ℝ) < (r : ℝ) := by exact_mod_cast hr1
    congr 1
    rw [show -((2 : ℕ) : ℝ) / 2 = -1 from by norm_num, Real.rpow_neg_one]
  rw [Finset.sum_congr rfl hterm, ← Finset.mul_sum] at hmain
  have hg : 0 ≤ greenConst 2 := greenConst_nonneg 2
  nlinarith [hmain, sum_inv_le_one_add_log n, hg]

/-! ### `d ≥ 3`: the truncated Green function is bounded -/

/-- `g_n(0) ≤ 1 + 3 C` for every `n`, in dimension `d ≥ 3`: the walk is
transient and the expected number of visits to the origin is bounded uniformly
in the horizon. -/
theorem gR_high_dim_le (hd : 3 ≤ d) (n : ℕ) (hn : 1 ≤ n) (x : Site d) :
    gR n x ≤ 1 + 3 * greenConst d := by
  have hd0 : 0 < d := by omega
  have hg : 0 ≤ greenConst d := greenConst_nonneg d
  have hmain := gR_le hd0 hn x
  have hterm : ∀ r ∈ Finset.Ico 1 n,
      greenConst d * ((r : ℝ) ^ (-(d : ℝ) / 2)) ≤ greenConst d * ((r : ℝ) ^ (-(3 : ℝ) / 2)) := by
    intro r hr
    have hr1 : 1 ≤ r := (Finset.mem_Ico.mp hr).1
    have hr1' : (1 : ℝ) ≤ (r : ℝ) := by exact_mod_cast hr1
    refine mul_le_mul_of_nonneg_left ?_ hg
    refine Real.rpow_le_rpow_of_exponent_le hr1' ?_
    have : (3 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
    linarith
  have hsum : ∑ r ∈ Finset.Ico 1 n, greenConst d * ((r : ℝ) ^ (-(d : ℝ) / 2))
      ≤ greenConst d * 3 :=
    (Finset.sum_le_sum hterm).trans (by
      rw [← Finset.mul_sum]
      exact mul_le_mul_of_nonneg_left (sum_rpow_three_halves_le n) hg)
  linarith [hmain, hsum]

/-- In dimension `d ≥ 3` the truncated Green function at the origin is between
`1` and a constant, for every horizon. -/
theorem one_le_gR_high_dim (_hd : 3 ≤ d) {n : ℕ} (hn : 1 ≤ n) :
    1 ≤ gR n (0 : Site d) := one_le_gR_zero hn

end LatticeProb
