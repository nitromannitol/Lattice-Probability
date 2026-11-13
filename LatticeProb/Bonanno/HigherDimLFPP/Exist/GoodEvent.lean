/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module HigherDimLFPP.Exist.GoodEvent at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.HigherDimLFPP.Exist.Sites
import LatticeProb.Bonanno.HigherDimLFPP.Exist.Lemma35
import LatticeProb.Bonanno.HigherDimLFPP.Field.Exists

/-!
# The good event of DGZ Lemma 3.3 (packet P-X8)

Source: DGZ arXiv:2310.03996, proof of Lemma 3.3 (the events `E₁`, `E₂`, `E₃`, (3.12)); planning
audit HA5, Details D9 ("Events", "Percolation events", "Probability"), D6 (Peierls, diameter and
enclosure bounds), D4 (Lemma O, Lemma 3.4′).

This file collects the ingredients of the probability estimate `P[E] > 1/2` of HA5 D9 that do not
depend on the assembly:

* numerics for DGZ's intermediate scale `k = ⌊(log m)²⌋` (`L33.kpar`): `k ≤ 36 n^{1/3}`,
  `√(k(m+k)) ≤ 37 n^{2/3}`, `√(k n) ≤ 6 n^{2/3}` for `1 ≤ m ≤ n` (`L33.kpar_le`,
  `L33.sqrt_kpar_mul_add_le`, `L33.sqrt_kpar_mul_le`);
* the oscillation part of `E₁` (`L33.oscBad`): its complement gives the hypothesis `hosc` of
  `DGZ.lfppDistance_le_of_good_sites_exp` with threshold `n^{2/3}`; by Lemma O (`Osc.box_osc_tail`)
  and a union bound over the `(2·2^{m+1}+1)^d` coarse sites its probability is at most `1/10` once
  `n` is large (`L33.measure_oscBad_le`, `L33.exists_osc_threshold`);
* the diameter event `E₃ₐ` (HA5 D6(iii) with `N = 2^{m+k+1}`, `D = 2^{k-2}`): its probability
  bound `(2N+1)^d 2^{-⌊D/2⌋}` is at most `1/10` once `m` is large (`L33.exists_diam_threshold`);
  the proof uses `2^{k+1} > e^{(log m)² log 2} ≥ m³` for `log m ≥ 3 / log 2`;
* the percolation parameters (`L33.exists_level`): `θ = (2·3^d)^{-1}`, a level `p = 1 - η` with
  `2d(1-p) ≤ θ^{(r+1)^d}` (`r` the range of the product bound) and enclosure probability
  `11^d·2d(1-p) + 2^{-5} ≤ 1/20` (HA5 D6(iv) with `N₀ = 5`);
* generic tools: `L33.half_le_measure_diff` (outer-measure bookkeeping
  `P(E \ B) ≥ P(E) - P(B)`), `L33.lowerQuantile_le_of_le_on` (a lower quantile is at most `X` if
  `D ≤ X` on a set of probability `≥ p`), and `IsBandVersion.add3` (three adjacent bands add up to a
  version of their union).

No probability estimate in this file needs measurability of the events (outer measures).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped ENNReal
open HigherDimLFPP.Perc (Zd LAdj WithinInf ProductBound IsClosedCluster Encloses)

namespace HigherDimLFPP

namespace L33

/-! ### Numerics -/

/-- DGZ's intermediate scale `k = ⌊(log m)²⌋` (Lemma 3.3; HA5 D9). -/
def kpar (m : ℕ) : ℕ := ⌊Real.log m ^ 2⌋₊

theorem rpow_third_pow_three {x : ℝ} (hx : 0 ≤ x) : (x ^ (1 / 3 : ℝ)) ^ 3 = x := by
  rw [← Real.rpow_mul_natCast hx]
  norm_num

theorem rpow_third_sq {x : ℝ} (hx : 0 ≤ x) : (x ^ (1 / 3 : ℝ)) ^ 2 = x ^ (2 / 3 : ℝ) := by
  rw [← Real.rpow_mul_natCast hx]
  congr 1
  norm_num

/-- `(x^{2/3})² = x^{1/3} x`. -/
theorem rpow_two_thirds_sq {x : ℝ} (hx : 0 ≤ x) : (x ^ (2 / 3 : ℝ)) ^ 2 = x ^ (1 / 3 : ℝ) * x := by
  rw [← Real.rpow_mul_natCast hx, ← Real.rpow_add_one' hx (by norm_num)]
  congr 1
  norm_num

theorem sqrt_le_rpow_two_thirds {x : ℝ} (hx : 1 ≤ x) : √x ≤ x ^ (2 / 3 : ℝ) := by
  rw [Real.sqrt_eq_rpow]
  exact Real.rpow_le_rpow_of_exponent_le hx (by norm_num)

theorem rpow_third_le_rpow_two_thirds {x : ℝ} (hx : 1 ≤ x) : x ^ (1 / 3 : ℝ) ≤ x ^ (2 / 3 : ℝ) :=
  Real.rpow_le_rpow_of_exponent_le hx (by norm_num)

theorem rpow_third_le_self {x : ℝ} (hx : 1 ≤ x) : x ^ (1 / 3 : ℝ) ≤ x := by
  calc x ^ (1 / 3 : ℝ) ≤ x ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hx (by norm_num)
    _ = x := Real.rpow_one x

theorem one_le_rpow_two_thirds {x : ℝ} (hx : 1 ≤ x) : 1 ≤ x ^ (2 / 3 : ℝ) :=
  Real.one_le_rpow hx (by norm_num)

/-- `(log x)² ≤ 36 x^{1/3}` for `x ≥ 1` (from `log y ≤ y` at `y = x^{1/6}`). -/
theorem log_sq_le_rpow_third {x : ℝ} (hx : 1 ≤ x) : Real.log x ^ 2 ≤ 36 * x ^ (1 / 3 : ℝ) := by
  have hx0 : 0 < x := by linarith
  set y : ℝ := x ^ (1 / 6 : ℝ) with hy
  have hy0 : 0 < y := Real.rpow_pos_of_pos hx0 _
  have hlog : Real.log y = Real.log x / 6 := by
    rw [hy, Real.log_rpow hx0]
    ring
  have h1 : Real.log y ≤ y := (Real.log_le_sub_one_of_pos hy0).trans (by linarith)
  have hl0 : 0 ≤ Real.log x := Real.log_nonneg hx
  have h2 : Real.log x ≤ 6 * y := by linarith
  have hy2 : y ^ 2 = x ^ (1 / 3 : ℝ) := by
    rw [hy, ← Real.rpow_mul_natCast hx0.le]
    congr 1
    norm_num
  calc Real.log x ^ 2 ≤ (6 * y) ^ 2 := pow_le_pow_left₀ hl0 h2 2
    _ = 36 * x ^ (1 / 3 : ℝ) := by rw [mul_pow, hy2]; norm_num

/-- `k ≤ 36 m^{1/3}`. -/
theorem kpar_le_rpow {m : ℕ} (hm : 1 ≤ m) : (kpar m : ℝ) ≤ 36 * (m : ℝ) ^ (1 / 3 : ℝ) := by
  have hm' : (1 : ℝ) ≤ m := by exact_mod_cast hm
  exact (Nat.floor_le (sq_nonneg _)).trans (log_sq_le_rpow_third hm')

/-- `k ≤ 36 n^{1/3}` for `1 ≤ m ≤ n`. -/
theorem kpar_le {m n : ℕ} (hm : 1 ≤ m) (hmn : m ≤ n) :
    (kpar m : ℝ) ≤ 36 * (n : ℝ) ^ (1 / 3 : ℝ) := by
  refine (kpar_le_rpow hm).trans ?_
  have : (m : ℝ) ^ (1 / 3 : ℝ) ≤ (n : ℝ) ^ (1 / 3 : ℝ) :=
    Real.rpow_le_rpow (Nat.cast_nonneg m) (by exact_mod_cast hmn) (by norm_num)
  linarith

/-- `k ≤ 36 n^{2/3}` for `1 ≤ m ≤ n`. -/
theorem kpar_le_two_thirds {m n : ℕ} (hm : 1 ≤ m) (hmn : m ≤ n) :
    (kpar m : ℝ) ≤ 36 * (n : ℝ) ^ (2 / 3 : ℝ) := by
  have hn : (1 : ℝ) ≤ n := by exact_mod_cast hm.trans hmn
  have := rpow_third_le_rpow_two_thirds hn
  linarith [kpar_le hm hmn]

/-- `√(k(m+k)) ≤ 37 n^{2/3}` (`k = kpar m`, `1 ≤ m ≤ n`): the exponent of the middle band. -/
theorem sqrt_kpar_mul_add_le {m n : ℕ} (hm : 1 ≤ m) (hmn : m ≤ n) :
    √((kpar m : ℝ) * ((m : ℝ) + kpar m)) ≤ 37 * (n : ℝ) ^ (2 / 3 : ℝ) := by
  have hm' : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hmn' : (m : ℝ) ≤ n := by exact_mod_cast hmn
  have hk := kpar_le_rpow hm
  have h3 : (m : ℝ) ^ (1 / 3 : ℝ) ≤ m := rpow_third_le_self hm'
  have h3n : (m : ℝ) ^ (1 / 3 : ℝ) ≤ (n : ℝ) ^ (1 / 3 : ℝ) :=
    Real.rpow_le_rpow (by linarith) hmn' (by norm_num)
  have hpos : 0 ≤ (m : ℝ) ^ (1 / 3 : ℝ) := Real.rpow_nonneg (by linarith) _
  have hk0 : (0 : ℝ) ≤ kpar m := Nat.cast_nonneg _
  have h1 : (m : ℝ) + kpar m ≤ 37 * m := by linarith
  have hprod : (kpar m : ℝ) * ((m : ℝ) + kpar m) ≤ 1332 * ((n : ℝ) ^ (1 / 3 : ℝ) * n) := by
    calc (kpar m : ℝ) * ((m : ℝ) + kpar m) ≤ (36 * (m : ℝ) ^ (1 / 3 : ℝ)) * (37 * m) :=
          mul_le_mul hk h1 (by positivity) (by positivity)
      _ = 1332 * ((m : ℝ) ^ (1 / 3 : ℝ) * m) := by ring
      _ ≤ 1332 * ((n : ℝ) ^ (1 / 3 : ℝ) * n) := by
          have := mul_le_mul h3n hmn' (by linarith) (Real.rpow_nonneg (by linarith) _)
          linarith
  rw [← rpow_two_thirds_sq (by linarith : (0 : ℝ) ≤ n)] at hprod
  have hn23 : 0 ≤ (n : ℝ) ^ (2 / 3 : ℝ) := Real.rpow_nonneg (by linarith) _
  calc √((kpar m : ℝ) * ((m : ℝ) + kpar m)) ≤ √((37 * (n : ℝ) ^ (2 / 3 : ℝ)) ^ 2) := by
        refine Real.sqrt_le_sqrt (hprod.trans ?_)
        rw [mul_pow]
        nlinarith [sq_nonneg ((n : ℝ) ^ (2 / 3 : ℝ))]
    _ = 37 * (n : ℝ) ^ (2 / 3 : ℝ) := Real.sqrt_sq (by positivity)

/-- `√(k n) ≤ 6 n^{2/3}` (`k = kpar m`, `1 ≤ m ≤ n`): the exponent of Lemma 3.5 at scale `k`. -/
theorem sqrt_kpar_mul_le {m n : ℕ} (hm : 1 ≤ m) (hmn : m ≤ n) :
    √((kpar m : ℝ) * n) ≤ 6 * (n : ℝ) ^ (2 / 3 : ℝ) := by
  have hk := kpar_le hm hmn
  have hprod : (kpar m : ℝ) * n ≤ 36 * ((n : ℝ) ^ (1 / 3 : ℝ) * n) := by
    calc (kpar m : ℝ) * n ≤ (36 * (n : ℝ) ^ (1 / 3 : ℝ)) * n :=
          mul_le_mul_of_nonneg_right hk (Nat.cast_nonneg n)
      _ = 36 * ((n : ℝ) ^ (1 / 3 : ℝ) * n) := by ring
  rw [← rpow_two_thirds_sq (Nat.cast_nonneg n)] at hprod
  have hn23 : 0 ≤ (n : ℝ) ^ (2 / 3 : ℝ) := Real.rpow_nonneg (Nat.cast_nonneg n) _
  calc √((kpar m : ℝ) * n) ≤ √((6 * (n : ℝ) ^ (2 / 3 : ℝ)) ^ 2) := by
        refine Real.sqrt_le_sqrt (hprod.trans ?_)
        rw [mul_pow]
        norm_num
    _ = 6 * (n : ℝ) ^ (2 / 3 : ℝ) := Real.sqrt_sq (by positivity)

/-- `2^j ≤ e^j`. -/
theorem two_pow_le_exp (j : ℕ) : (2 : ℝ) ^ j ≤ Real.exp j := by
  have h2 : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
  calc (2 : ℝ) ^ j ≤ Real.exp 1 ^ j := pow_le_pow_left₀ (by norm_num) h2 j
    _ = Real.exp j := by rw [← Real.exp_nat_mul, mul_one]

/-- `2 e^{-6} ≤ 1/10`. -/
theorem two_mul_exp_neg_six_le : 2 * Real.exp (-6) ≤ 1 / 10 := by
  have h := Real.quadratic_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 6)
  have h6 : (20 : ℝ) ≤ Real.exp 6 := by norm_num at h; linarith
  rw [Real.exp_neg]
  have hpos : 0 < Real.exp 6 := Real.exp_pos 6
  rw [← div_eq_mul_inv, div_le_div_iff₀ hpos (by norm_num)]
  linarith

/-- **Threshold for the oscillation event** (HA5 D9, `E₁`): for `B ≥ 0` and `c > 0` there is `n₁`
such that for `n ≥ n₁` and `m ≤ n`, `u = n^{2/3}/2 - B ≥ 0` and
`(2·2^{m+1}+1)^d · 2 e^{-u²/c} ≤ 1/10`. -/
theorem exists_osc_threshold (d : ℕ) {B c : ℝ} (hB : 0 ≤ B) (hc : 0 < c) :
    ∃ n₁ : ℕ, ∀ n m : ℕ, n₁ ≤ n → m ≤ n →
      0 ≤ (n : ℝ) ^ (2 / 3 : ℝ) / 2 - B ∧
        (((2 * 2 ^ (m + 1) + 1 : ℕ) : ℝ)) ^ d *
            (2 * Real.exp (-((n : ℝ) ^ (2 / 3 : ℝ) / 2 - B) ^ 2 / c)) ≤ 1 / 10 := by
  set Q : ℝ := 1 + 16 * c * (4 * d + 6) + 4 * B with hQ
  have hd0 : (0 : ℝ) ≤ d := Nat.cast_nonneg d
  have hcd : 0 ≤ 16 * c * (4 * d + 6) := by positivity
  have hQ1 : 1 ≤ Q := by linarith
  refine ⟨⌈Q ^ 3⌉₊, fun n m hn hmn => ?_⟩
  have hnQ : Q ^ 3 ≤ (n : ℝ) := (Nat.le_ceil _).trans (by exact_mod_cast hn)
  set q : ℝ := (n : ℝ) ^ (1 / 3 : ℝ) with hq
  have hq3 : q ^ 3 = n := rpow_third_pow_three (Nat.cast_nonneg n)
  have hq2 : q ^ 2 = (n : ℝ) ^ (2 / 3 : ℝ) := rpow_third_sq (Nat.cast_nonneg n)
  have hq0 : 0 ≤ q := Real.rpow_nonneg (Nat.cast_nonneg n) _
  have hqQ : Q ≤ q := by
    by_contra h
    push Not at h
    have : q ^ 3 < Q ^ 3 := pow_lt_pow_left₀ h hq0 (by norm_num)
    linarith
  have hq1 : 1 ≤ q := hQ1.trans hqQ
  have hqB : 4 * B ≤ q := by linarith
  have hqc : 16 * c * (4 * d + 6) ≤ q := by linarith
  have hqq : q ≤ q ^ 2 := by nlinarith
  rw [← hq2]
  set u : ℝ := q ^ 2 / 2 - B with hu
  have hu4 : q ^ 2 / 4 ≤ u := by rw [hu]; linarith
  have hu0 : 0 ≤ u := le_trans (by positivity) hu4
  refine ⟨hu0, ?_⟩
  -- the number of coarse sites
  have hcount : (((2 * 2 ^ (m + 1) + 1 : ℕ) : ℝ)) ^ d ≤ Real.exp ((n + 3) * d) := by
    have h1 : (2 * 2 ^ (m + 1) + 1 : ℕ) ≤ 2 ^ (n + 3) := by
      have hp : 1 ≤ 2 ^ (m + 1) := Nat.one_le_two_pow
      have : 2 ^ (m + 1) ≤ 2 ^ (n + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
      calc 2 * 2 ^ (m + 1) + 1 ≤ 4 * 2 ^ (m + 1) := by omega
        _ ≤ 4 * 2 ^ (n + 1) := by omega
        _ = 2 ^ (n + 3) := by ring
    have h2 : (((2 * 2 ^ (m + 1) + 1 : ℕ) : ℝ)) ≤ Real.exp (n + 3) := by
      calc (((2 * 2 ^ (m + 1) + 1 : ℕ) : ℝ)) ≤ ((2 ^ (n + 3) : ℕ) : ℝ) := by exact_mod_cast h1
        _ = (2 : ℝ) ^ (n + 3) := by push_cast; ring
        _ ≤ Real.exp ((n + 3 : ℕ) : ℝ) := two_pow_le_exp (n + 3)
        _ = Real.exp (n + 3) := by push_cast; ring_nf
    calc (((2 * 2 ^ (m + 1) + 1 : ℕ) : ℝ)) ^ d ≤ Real.exp (n + 3) ^ d :=
          pow_le_pow_left₀ (Nat.cast_nonneg _) h2 d
      _ = Real.exp ((n + 3) * d) := by
          rw [← Real.exp_nat_mul]
          ring_nf
  -- the exponent
  have hq4 : (16 * c) * (((n : ℝ) + 3) * d + 6) ≤ q ^ 4 := by
    rw [← hq3]
    have hq31 : 1 ≤ q ^ 3 := one_le_pow₀ hq1
    have hA : ((q ^ 3 + 3) * d + 6) ≤ q ^ 3 * (4 * d + 6) := by nlinarith
    calc (16 * c) * ((q ^ 3 + 3) * d + 6) ≤ (16 * c) * (q ^ 3 * (4 * d + 6)) :=
          mul_le_mul_of_nonneg_left hA (by positivity)
      _ = q ^ 3 * (16 * c * (4 * d + 6)) := by ring
      _ ≤ q ^ 3 * q := mul_le_mul_of_nonneg_left hqc (by positivity)
      _ = q ^ 4 := by ring
  have hexp : ((n : ℝ) + 3) * d + (-u ^ 2 / c) ≤ -6 := by
    have hu2 : q ^ 4 / 16 ≤ u ^ 2 := by
      have : (q ^ 2 / 4) ^ 2 ≤ u ^ 2 := pow_le_pow_left₀ (by positivity) hu4 2
      nlinarith
    have : ((n : ℝ) + 3) * d + 6 ≤ u ^ 2 / c := by
      rw [le_div_iff₀ hc]
      nlinarith
    have e : -u ^ 2 / c = -(u ^ 2 / c) := neg_div c (u ^ 2)
    linarith
  calc (((2 * 2 ^ (m + 1) + 1 : ℕ) : ℝ)) ^ d * (2 * Real.exp (-u ^ 2 / c))
      ≤ Real.exp ((n + 3) * d) * (2 * Real.exp (-u ^ 2 / c)) :=
        mul_le_mul_of_nonneg_right hcount (by positivity)
    _ = 2 * Real.exp (((n : ℝ) + 3) * d + (-u ^ 2 / c)) := by rw [Real.exp_add]; ring
    _ ≤ 2 * Real.exp (-6) := by gcongr
    _ ≤ 1 / 10 := two_mul_exp_neg_six_le

/-- The `ENNReal` form of the diameter bound `(2N+1)^d 2^{-j}` is the `ofReal` of its real value. -/
theorem box_mul_pow_eq_ofReal (N d j : ℕ) :
    (2 * (N : ℝ≥0∞) + 1) ^ d * 2⁻¹ ^ j = ENNReal.ofReal ((2 * (N : ℝ) + 1) ^ d * (2⁻¹ : ℝ) ^ j) := by
  rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_pow (by positivity),
    ENNReal.ofReal_pow (by positivity), ENNReal.ofReal_inv_of_pos two_pos, ENNReal.ofReal_ofNat,
    ENNReal.ofReal_add (by positivity) zero_le_one, ENNReal.ofReal_one,
    ENNReal.ofReal_mul zero_le_two, ENNReal.ofReal_ofNat, ENNReal.ofReal_natCast]

/-- **Threshold for the diameter event** `E₃ₐ` (HA5 D9, D6(iii) with `N = 2^{m+k+1}`,
`D = 2^{k-2}`, `k = ⌊(log m)²⌋`): for `m` large, `k ≥ 4` and
`(2N+1)^d 2^{-⌊D/2⌋} ≤ 1/10`. The proof: `log m ≥ 3/log 2` gives `2^{k+1} > m³`, hence
`2^{k-3} > m³/16 ≥ (13d+4) m ≥ (m+k+3)d + 4` (`k ≤ (log m)² ≤ 9m`), and
`(2N+1)^d 2^{-2^{k-3}} ≤ 2^{(m+k+3)d - 2^{k-3}} ≤ 2^{-4}`. -/
theorem exists_diam_threshold (d : ℕ) :
    ∃ m₃ : ℕ, 8 ≤ m₃ ∧ ∀ m : ℕ, m₃ ≤ m → 4 ≤ kpar m ∧
      (2 * ((2 ^ (m + kpar m + 1) : ℕ) : ℝ≥0∞) + 1) ^ d * 2⁻¹ ^ (2 ^ (kpar m - 2) / 2) ≤
        ENNReal.ofReal (1 / 10) := by
  refine ⟨max 8 (max ⌈Real.exp (3 / Real.log 2)⌉₊ (16 * (13 * d + 4))), le_max_left _ _,
    fun m hm => ?_⟩
  have hm8 : 8 ≤ m := (le_max_left _ _).trans hm
  have hmexp : Real.exp (3 / Real.log 2) ≤ m :=
    (Nat.le_ceil _).trans (by exact_mod_cast (le_max_left _ _).trans ((le_max_right _ _).trans hm))
  have hm16 : 16 * (13 * d + 4) ≤ m := (le_max_right _ _).trans ((le_max_right _ _).trans hm)
  have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast (by omega : 1 ≤ m)
  have hm0 : (0 : ℝ) < m := by linarith
  have hlog2 : 0 < Real.log 2 := Real.log_pos one_lt_two
  have hlog21 : Real.log 2 ≤ 1 := Crude.log_two_le_one
  set ℓ : ℝ := Real.log m with hℓdef
  have hℓ : 3 / Real.log 2 ≤ ℓ := (Real.le_log_iff_exp_le hm0).2 hmexp
  have h3 : 3 ≤ 3 / Real.log 2 := by
    rw [le_div_iff₀ hlog2]
    linarith
  have hℓ3 : 3 ≤ ℓ := h3.trans hℓ
  set k : ℕ := kpar m with hkdef
  have hk_le : (k : ℝ) ≤ ℓ ^ 2 := Nat.floor_le (sq_nonneg _)
  have hk_lt : ℓ ^ 2 < k + 1 := Nat.lt_floor_add_one _
  have hk9 : 9 ≤ k := by
    have : (9 : ℝ) ≤ ℓ ^ 2 := by nlinarith
    exact Nat.le_floor (by exact_mod_cast this)
  refine ⟨by omega, ?_⟩
  -- `2^{k+1} > m³`
  have hpow : (m : ℝ) ^ 3 < (2 : ℝ) ^ (k + 1) := by
    have h1 : 3 * ℓ ≤ Real.log 2 * ℓ ^ 2 := by
      have : 3 ≤ Real.log 2 * ℓ := by
        rw [div_le_iff₀ hlog2] at hℓ
        linarith
      nlinarith
    have h2 : Real.log 2 * ℓ ^ 2 < Real.log 2 * (k + 1) := mul_lt_mul_of_pos_left hk_lt hlog2
    calc (m : ℝ) ^ 3 = Real.exp (((3 : ℕ) : ℝ) * ℓ) := by
          rw [Real.exp_nat_mul, hℓdef, Real.exp_log hm0]
      _ < Real.exp (Real.log 2 * (k + 1)) := Real.exp_lt_exp.2 (by push_cast; linarith)
      _ = (2 : ℝ) ^ (k + 1) := by
          rw [← Real.exp_log (pow_pos two_pos (k + 1) : (0 : ℝ) < 2 ^ (k + 1)), Real.log_pow]
          congr 1
          push_cast
          ring
  -- `k ≤ 9 m`
  have hk9m : (k : ℝ) ≤ 9 * m := by
    have h1 := DGZ.log_sq_le_nine_mul_rpow hm1 le_rfl
    have h2 : (m : ℝ) ^ (2 / 3 : ℝ) ≤ m := by
      calc (m : ℝ) ^ (2 / 3 : ℝ) ≤ (m : ℝ) ^ (1 : ℝ) :=
            Real.rpow_le_rpow_of_exponent_le hm1 (by norm_num)
        _ = m := Real.rpow_one _
    linarith
  -- `2^{k-2}/2 = 2^{k-3}`
  have hF : 2 ^ (k - 2) / 2 = 2 ^ (k - 3) := by
    have : k - 2 = (k - 3) + 1 := by omega
    rw [this, pow_succ, Nat.mul_div_cancel _ two_pos]
  set E : ℕ := (m + k + 3) * d with hE
  have hEF : E + 4 ≤ 2 ^ (k - 3) := by
    have h16 : ((2 ^ (k - 3) : ℕ) : ℝ) * 16 = (2 : ℝ) ^ (k + 1) := by
      have : k + 1 = (k - 3) + 4 := by omega
      rw [this, pow_add]
      push_cast
      norm_num
    have hd0 : (0 : ℝ) ≤ d := Nat.cast_nonneg d
    have hE' : ((E + 4 : ℕ) : ℝ) ≤ (13 * d + 4) * m := by
      rw [hE]
      push_cast
      nlinarith
    have hm2 : 16 * (13 * (d : ℝ) + 4) ≤ (m : ℝ) ^ 2 := by
      have : (16 * (13 * d + 4) : ℝ) ≤ m := by exact_mod_cast hm16
      nlinarith
    have hm3 : (13 * (d : ℝ) + 4) * m * 16 ≤ (m : ℝ) ^ 3 := by nlinarith
    have : ((E + 4 : ℕ) : ℝ) ≤ ((2 ^ (k - 3) : ℕ) : ℝ) := by nlinarith
    exact_mod_cast this
  rw [hF, box_mul_pow_eq_ofReal]
  refine ENNReal.ofReal_le_ofReal ?_
  -- real inequality
  have hN : 2 * ((2 ^ (m + k + 1) : ℕ) : ℝ) + 1 ≤ (2 : ℝ) ^ (m + k + 3) := by
    have : (1 : ℝ) ≤ 2 ^ (m + k + 1) := one_le_pow₀ (by norm_num)
    push_cast
    have e : (2 : ℝ) ^ (m + k + 3) = 4 * 2 ^ (m + k + 1) := by ring
    linarith
  have h1 : (2 * ((2 ^ (m + k + 1) : ℕ) : ℝ) + 1) ^ d ≤ (2 : ℝ) ^ E := by
    rw [hE, pow_mul]
    exact pow_le_pow_left₀ (by positivity) hN d
  have hsplit : 2 ^ (k - 3) = (2 ^ (k - 3) - E) + E := by omega
  have h2 : (2 : ℝ) ^ E * (2⁻¹ : ℝ) ^ (2 ^ (k - 3)) = (2⁻¹ : ℝ) ^ (2 ^ (k - 3) - E) := by
    conv_lhs => rw [hsplit, pow_add]
    rw [mul_comm, mul_assoc, ← mul_pow, inv_mul_cancel₀ two_ne_zero, one_pow, mul_one]
  have h3 : (2⁻¹ : ℝ) ^ (2 ^ (k - 3) - E) ≤ (2⁻¹ : ℝ) ^ 4 :=
    pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)
  calc (2 * ((2 ^ (m + k + 1) : ℕ) : ℝ) + 1) ^ d * (2⁻¹ : ℝ) ^ (2 ^ (k - 3))
      ≤ (2 : ℝ) ^ E * (2⁻¹ : ℝ) ^ (2 ^ (k - 3)) := mul_le_mul_of_nonneg_right h1 (by positivity)
    _ = (2⁻¹ : ℝ) ^ (2 ^ (k - 3) - E) := h2
    _ ≤ (2⁻¹ : ℝ) ^ 4 := h3
    _ ≤ 1 / 10 := by norm_num

/-! ### Percolation parameters -/

/-- `θ = (2·3^d)^{-1}` satisfies `θ ≤ 1`. -/
theorem theta_le_one (d : ℕ) : ENNReal.ofReal (2 * 3 ^ d : ℝ)⁻¹ ≤ 1 := by
  rw [← ENNReal.ofReal_one]
  refine ENNReal.ofReal_le_ofReal (inv_le_one_of_one_le₀ ?_)
  have : (1 : ℝ) ≤ 3 ^ d := one_le_pow₀ (by norm_num)
  linarith

/-- `3^d θ ≤ 1/2` for `θ = (2·3^d)^{-1}`. -/
theorem three_pow_mul_theta_le (d : ℕ) :
    (3 : ℝ≥0∞) ^ d * ENNReal.ofReal (2 * 3 ^ d : ℝ)⁻¹ ≤ 2⁻¹ := by
  have h3 : (3 : ℝ≥0∞) ^ d = ENNReal.ofReal ((3 : ℝ) ^ d) := by
    rw [ENNReal.ofReal_pow (by norm_num), ENNReal.ofReal_ofNat]
  rw [h3, ← ENNReal.ofReal_mul (by positivity)]
  have e : (3 : ℝ) ^ d * (2 * 3 ^ d)⁻¹ = 2⁻¹ := by
    have : (3 : ℝ) ^ d ≠ 0 := pow_ne_zero d (by norm_num)
    field_simp
  rw [e, ENNReal.ofReal_inv_of_pos two_pos, ENNReal.ofReal_ofNat]

/-- `1 - (1 - η) = η` in `ℝ≥0∞`. -/
theorem one_sub_ofReal_one_sub {η : ℝ} (hη1 : η ≤ 1) :
    1 - ENNReal.ofReal (1 - η) = ENNReal.ofReal η := by
  rw [← ENNReal.ofReal_one, ← ENNReal.ofReal_sub _ (by linarith)]
  congr 1
  ring

/-- **The percolation parameters** of DGZ Lemma 3.3 (HA5 D9, "Percolation events"): for the range
`r` of the product bound there is `η ∈ (0, 1/10]` such that, with `θ = (2·3^d)^{-1}` and closed-site
probability `ε = 2d η`, the Peierls hypothesis `ε ≤ θ^{(r+1)^d}` holds and the enclosure bound with
`N₀ = 5` is small: `(2·5+1)^d ε + 2^{-5} ≤ 1/20`. -/
theorem exists_level (d r : ℕ) (hd : 0 < d) :
    ∃ η : ℝ, 0 < η ∧ η ≤ 1 / 10 ∧
      2 * (d : ℝ≥0∞) * ENNReal.ofReal η ≤ ENNReal.ofReal (2 * 3 ^ d : ℝ)⁻¹ ^ ((r + 1) ^ d) ∧
      (2 * ((5 : ℕ) : ℝ≥0∞) + 1) ^ d * (2 * (d : ℝ≥0∞) * ENNReal.ofReal η) + 2⁻¹ ^ (5 : ℕ) ≤
        ENNReal.ofReal (1 / 20) := by
  set θr : ℝ := (2 * 3 ^ d : ℝ)⁻¹ with hθr
  set K : ℕ := (r + 1) ^ d with hK
  have hθ0 : 0 < θr := by positivity
  have hθ1 : θr ≤ 1 := by
    refine inv_le_one_of_one_le₀ ?_
    have : (1 : ℝ) ≤ 3 ^ d := one_le_pow₀ (by norm_num)
    linarith
  have hθK0 : 0 < θr ^ K := pow_pos hθ0 K
  have hθK1 : θr ^ K ≤ 1 := pow_le_one₀ hθ0.le hθ1
  have hd' : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have h11 : (1 : ℝ) ≤ 11 ^ d := one_le_pow₀ (by norm_num)
  set η : ℝ := θr ^ K / (2 * d * 11 ^ d * 100) with hη
  have hden : 0 < 2 * (d : ℝ) * 11 ^ d * 100 := by positivity
  have hη0 : 0 < η := div_pos hθK0 hden
  have h2dη : 2 * (d : ℝ) * η = θr ^ K / (11 ^ d * 100) := by
    rw [hη]
    field_simp
  have e1 : 2 * (d : ℝ≥0∞) * ENNReal.ofReal η = ENNReal.ofReal (2 * d * η) := by
    rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul (by positivity),
      ENNReal.ofReal_ofNat, ENNReal.ofReal_natCast]
  refine ⟨η, hη0, ?_, ?_, ?_⟩
  · rw [hη, div_le_iff₀ hden]
    nlinarith
  · rw [e1, ← ENNReal.ofReal_pow hθ0.le]
    refine ENNReal.ofReal_le_ofReal ?_
    rw [h2dη, div_le_iff₀ (by positivity)]
    nlinarith
  · rw [e1]
    have h5 : (2 * ((5 : ℕ) : ℝ≥0∞) + 1) ^ d = ENNReal.ofReal ((11 : ℝ) ^ d) := by
      rw [ENNReal.ofReal_pow (by norm_num)]
      norm_num
    have h32 : (2⁻¹ : ℝ≥0∞) ^ (5 : ℕ) = ENNReal.ofReal (1 / 32) := by
      rw [← ENNReal.ofReal_ofNat 2, ← ENNReal.ofReal_inv_of_pos two_pos, ← ENNReal.ofReal_pow
        (by norm_num)]
      norm_num
    rw [h5, h32, ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_add (by positivity)
      (by norm_num)]
    refine ENNReal.ofReal_le_ofReal ?_
    have : (11 : ℝ) ^ d * (2 * d * η) ≤ 1 / 100 := by
      rw [h2dη]
      have : (11 : ℝ) ^ d * (θr ^ K / (11 ^ d * 100)) = θr ^ K / 100 := by
        field_simp
      rw [this]
      linarith
    linarith

/-! ### The oscillation event of `E₁` -/

/-- `U ⊆ [-2,2]^d`. -/
theorem cube_subset_box (d : ℕ) : cube d ⊆ Osc.box (0 : Rd d) 2 := fun z hz i => by
  have h := hz i
  simp only [PiLp.zero_apply, sub_zero]
  exact h.le

/-- **The oscillation bad event** of `E₁` (HA5 D9): for some coarse site `x` of the lattice box
`[-2^{m+1}, 2^{m+1}]^d`, two points of the box `2^{-m} x + [-3·2^{-m}, 3·2^{-m}]^d` have field values
differing by more than `T`. -/
def oscBad {d : ℕ} {Ω : Type*} (H : Rd d → Ω → ℝ) (m : ℕ) (T : ℝ) : Set Ω :=
  ⋃ x ∈ Perc.boxF (0 : Zd d) (2 ^ (m + 1)),
    {ω | ∃ z ∈ Osc.box (DGZ.latPt ((2 : ℝ)⁻¹ ^ m) x) (3 * ((2 : ℝ) ^ m)⁻¹),
      ∃ w ∈ Osc.box (DGZ.latPt ((2 : ℝ)⁻¹ ^ m) x) (3 * ((2 : ℝ) ^ m)⁻¹), T < |H z ω - H w ω|}

/-- Outside the oscillation bad event, the coarse field satisfies the oscillation hypothesis of
`DGZ.lfppDistance_le_of_good_sites` with threshold `T` at every coarse site of `U`. -/
theorem osc_le_of_not_mem_oscBad {d : ℕ} {Ω : Type*} {H : Rd d → Ω → ℝ} {m : ℕ} {T : ℝ} {ω : Ω}
    (hω : ω ∉ oscBad H m T) (x : Zd d) (hx : DGZ.latPt ((2 : ℝ)⁻¹ ^ m) x ∈ cube d) :
    ∀ z ∈ DGZ.cbox (DGZ.latPt ((2 : ℝ)⁻¹ ^ m) x) (3 * (2 : ℝ)⁻¹ ^ m),
      |H z ω - H (DGZ.latPt ((2 : ℝ)⁻¹ ^ m) x) ω| ≤ T := by
  intro z hz
  have hs : (0 : ℝ) < (2 : ℝ)⁻¹ ^ m := by positivity
  have hxbox : x ∈ Perc.boxF (0 : Zd d) (2 ^ (m + 1)) := by
    rw [Perc.mem_boxF]
    intro i
    have hi := hx i
    rw [DGZ.latPt_apply, abs_mul, abs_of_pos hs] at hi
    have hreal : |((x i : ℤ) : ℝ)| < (2 : ℝ) ^ (m + 1) := by
      have e : (2 : ℝ)⁻¹ ^ m * (2 : ℝ) ^ (m + 1) = 2 := by
        rw [pow_succ, ← mul_assoc, ← mul_pow, inv_mul_cancel₀ two_ne_zero, one_pow, one_mul]
      by_contra hge
      push Not at hge
      have := mul_le_mul_of_nonneg_left hge hs.le
      linarith
    have hint : |x i| < (2 : ℤ) ^ (m + 1) := by exact_mod_cast hreal
    simp only [Pi.zero_apply, sub_zero]
    push_cast
    exact hint.le
  by_contra hlt
  push Not at hlt
  refine hω (mem_iUnion₂.2 ⟨x, hxbox, z, ?_, DGZ.latPt ((2 : ℝ)⁻¹ ^ m) x, ?_, hlt⟩)
  · intro i
    have := hz i
    rwa [show (3 : ℝ) * (2 : ℝ)⁻¹ ^ m = 3 * ((2 : ℝ) ^ m)⁻¹ by rw [inv_pow]] at this
  · intro i
    rw [sub_self, abs_zero]
    positivity

/-- **Probability of the oscillation bad event** (Lemma O, `Osc.box_osc_tail`, and a union bound
over the `(2·2^{m+1}+1)^d` coarse sites; HA5 D4, D9): for a continuous version `H` of
`H_{2^{-m},b}` with the increment constant `L`, and `u ≥ 0`,
`P(oscBad H m (2(blockConst + u))) ≤ (2·2^{m+1}+1)^d · 2 exp(-u²/(2(3√d)² L))`. -/
theorem measure_oscBad_le {d : ℕ} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {W : WN d → Ω → ℝ} {κ : Rd d → ℝ} (hW : IsWhiteNoise P W) {m : ℕ} {b : ℝ}
    {H : Rd d → Ω → ℝ} (hH : IsBandVersion P W κ ((2 : ℝ) ^ m)⁻¹ b H) {L : ℝ} (hL0 : 0 ≤ L)
    (hL : ∀ z w : Rd d, ‖bandVec κ ((2 : ℝ) ^ m)⁻¹ b z - bandVec κ ((2 : ℝ) ^ m)⁻¹ b w‖ ^ 2 ≤
      L * ‖z - w‖ ^ 2 / (((2 : ℝ) ^ m)⁻¹) ^ 2) {u : ℝ} (hu : 0 ≤ u) :
    P (oscBad H m (2 * (Osc.blockConst d L (√(d : ℝ) * 3) + u))) ≤
      ENNReal.ofReal ((((2 * 2 ^ (m + 1) + 1 : ℕ) : ℝ)) ^ d *
        (2 * Real.exp (-u ^ 2 / (2 * ((√(d : ℝ) * 3) ^ 2 * L))))) := by
  set g : ℝ := 2 * Real.exp (-u ^ 2 / (2 * ((√(d : ℝ) * 3) ^ 2 * L))) with hg
  calc P (oscBad H m (2 * (Osc.blockConst d L (√(d : ℝ) * 3) + u)))
      ≤ ∑ x ∈ Perc.boxF (0 : Zd d) (2 ^ (m + 1)),
          P {ω | ∃ z ∈ Osc.box (DGZ.latPt ((2 : ℝ)⁻¹ ^ m) x) (3 * ((2 : ℝ) ^ m)⁻¹),
            ∃ w ∈ Osc.box (DGZ.latPt ((2 : ℝ)⁻¹ ^ m) x) (3 * ((2 : ℝ) ^ m)⁻¹),
              2 * (Osc.blockConst d L (√(d : ℝ) * 3) + u) < |H z ω - H w ω|} :=
        measure_biUnion_finset_le _ _
    _ ≤ ∑ _x ∈ Perc.boxF (0 : Zd d) (2 ^ (m + 1)), ENNReal.ofReal g :=
        Finset.sum_le_sum fun x _ =>
          Osc.box_osc_tail hW (dyadic_pos m) hH hL0 hL _ (by norm_num) hu
    _ = ENNReal.ofReal ((((2 * 2 ^ (m + 1) + 1 : ℕ) : ℝ)) ^ d * g) := by
        rw [Finset.sum_const, nsmul_eq_mul, Perc.card_boxF,
          ENNReal.ofReal_mul (p := (((2 * 2 ^ (m + 1) + 1 : ℕ) : ℝ)) ^ d) (q := g) (by positivity),
          ← Nat.cast_pow, ENNReal.ofReal_natCast]

/-! ### Generic tools -/

/-- **Outer-measure bookkeeping**: if `P(E) ≥ 1 - η`, `P(B) ≤ β` and `1/2 + β ≤ 1 - η`, then
`P(E \ B) ≥ 1/2` (no measurability needed). -/
theorem half_le_measure_diff {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {E B : Set Ω}
    {η β : ℝ} (hE : ENNReal.ofReal (1 - η) ≤ P E) (hB : P B ≤ ENNReal.ofReal β) (hβ : 0 ≤ β)
    (h : 1 / 2 + β ≤ 1 - η) : 2⁻¹ ≤ P (E \ B) := by
  have h1 : P E ≤ P (E \ B) + P B := by
    calc P E ≤ P ((E \ B) ∪ B) := measure_mono fun ω hω => by
          by_cases hb : ω ∈ B
          · exact Or.inr hb
          · exact Or.inl ⟨hω, hb⟩
      _ ≤ P (E \ B) + P B := measure_union_le _ _
  have h2 : ENNReal.ofReal (1 / 2) + ENNReal.ofReal β ≤ P (E \ B) + ENNReal.ofReal β := by
    rw [← ENNReal.ofReal_add (by norm_num) hβ]
    calc ENNReal.ofReal (1 / 2 + β) ≤ ENNReal.ofReal (1 - η) := ENNReal.ofReal_le_ofReal h
      _ ≤ P E := hE
      _ ≤ P (E \ B) + P B := h1
      _ ≤ P (E \ B) + ENNReal.ofReal β := add_le_add le_rfl hB
  have h3 := ENNReal.le_of_add_le_add_right ENNReal.ofReal_ne_top h2
  rwa [one_div, ENNReal.ofReal_inv_of_pos two_pos, ENNReal.ofReal_ofNat] at h3

/-- A lower quantile is at most `X` if `D ≤ X` on a set of (outer) probability at least `p`. -/
theorem lowerQuantile_le_of_le_on {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {D : Ω → ℝ} (hD : Measurable D) {p : ℝ≥0∞} (hp0 : 0 < p)
    (hp1 : p < 1) {X : ℝ} {G : Set Ω} (hG : ∀ ω ∈ G, D ω ≤ X) (hPG : p ≤ P G) :
    LQGMetric.lowerQuantile (P.map D) p ≤ X := by
  refine (LQGMetric.le_measure_Iic_iff_lowerQuantile_le (μ := P.map D) hp0 hp1).1 ?_
  rw [Measure.map_apply hD measurableSet_Iic]
  exact hPG.trans (measure_mono fun ω hω => hG ω hω)

end L33

/-- **Three adjacent bands** (`a ≤ b ≤ c ≤ e`): the sum of versions of `H_{c,e}`, `H_{b,c}` and
`H_{a,b}` is a version of `H_{a,e}` (band additivity, HA2 D1.4). -/
theorem IsBandVersion.add3 {d : ℕ} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {W : WN d → Ω → ℝ} {κ : Rd d → ℝ} (hκ : IsLFPPKernel κ) (hW : IsWhiteNoise P W) {a b c e : ℝ}
    (ha : 0 < a) (hab : a ≤ b) (hbc : b ≤ c) (hce : c ≤ e) {H₀ H₁ H₂ : Rd d → Ω → ℝ}
    (h₀ : IsBandVersion P W κ c e H₀) (h₁ : IsBandVersion P W κ b c H₁)
    (h₂ : IsBandVersion P W κ a b H₂) :
    IsBandVersion P W κ a e (fun z ω => H₀ z ω + H₁ z ω + H₂ z ω) where
  continuous ω := ((h₀.continuous ω).add (h₁.continuous ω)).add (h₂.continuous ω)
  measurable z := ((h₀.measurable z).add (h₁.measurable z)).add (h₂.measurable z)
  ae_eq z := by
    have hb : 0 < b := lt_of_lt_of_le ha hab
    filter_upwards [h₀.ae_eq z, h₁.ae_eq z, h₂.ae_eq z,
      hW.bandVec_add_ae hκ ha hab (hbc.trans hce) z, hW.bandVec_add_ae hκ hb hbc hce z]
      with ω e0 e1 e2 e3 e4
    show H₀ z ω + H₁ z ω + H₂ z ω = _
    rw [e0, e1, e2, e3, e4]
    ring

end HigherDimLFPP
