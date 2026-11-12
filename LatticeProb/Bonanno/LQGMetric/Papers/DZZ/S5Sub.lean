/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DZZ.S5Sub at commit fdb5cad; only the module paths of local imports are changed. -/
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Order.LiminfLimsup
import Mathlib.Topology.Algebra.Order.LiminfLimsup

/-!
# The near-subadditive step of DZZ Lemma 5.3 (P2-DZZ56)

Ding–Zeitouni–Zhang, arXiv:1807.00422, `LBM_LGDarXiv.tex`, proof of Lemma 5.3, l. 2414–2423:
with `χ_δ = E log D̃_{γ,δ,η}(u,v) / log δ⁻¹`,
`χ_{δδ̃} ≤ (log δ⁻¹ χ_δ + log δ̃⁻¹ χ_δ̃) / (log δ⁻¹ + log δ̃⁻¹) + (log δ⁻¹)^{−0.01}` for `δ < δ̃`;
"applying [Hammersley 1962] (see also [DZ10, Lemma 6.4.10]) this yields that `χ_δ` converges to
some constant `χ` as `δ → 0` over a sequence `δ_k = 2^{−k}`, and then by continuity the
convergence extends to arbitrary `δ → 0`."

* **`tendsto_div_of_near_subadd`**: Hammersley's generalized subadditive lemma in the form used
  (error `C (k+l) k^{−θ}` for `l ≤ k`, `k ≥ k₀`, `0 < θ ≤ 1`, and `0 ≤ a n ≤ M n`, the crude
  bound DZZ (eq-very-crude)): `a n / n` converges. Own proof of the standard argument (binary
  doubling `a(2^j m)/(2^j m) ≤ a m/m + C' m^{−θ}`, then the greedy dyadic decomposition of `n`,
  error `O(n^{1−θ} log n)`); Hammersley's paper is not in `literature/`.
* **`dzz_chi_dyadic_tendsto`**: DZZ's inequality in their normalized form along `δ_k = 2^{−k}`
  ⇒ `χ_{2^{−k}} → χ`.
* **`tendsto_of_dyadic_antitone`**: "by continuity" (l. 2422): for `f` antitone in `δ`
  (`D_δ` decreases in `δ`, `lgdDZZ_antitone`), `f(2^{−k})/(k log 2) → χ` gives
  `f(δ)/log δ⁻¹ → χ` as `δ → 0⁺`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Filter Topology Set

namespace LQGMetric
namespace DZZ

section Hammersley

variable {a : ℕ → ℝ} {C θ M : ℝ} {k₀ : ℕ}

private lemma two_pow_rpow_neg (j : ℕ) (θ : ℝ) :
    ((2 : ℝ) ^ j) ^ (-θ) = ((2 : ℝ) ^ (-θ)) ^ j := by
  rw [← Real.rpow_natCast, ← Real.rpow_natCast, ← Real.rpow_mul (by norm_num),
    ← Real.rpow_mul (by norm_num), mul_comm]

/-- Binary doubling: `a(2^j m)/(2^j m) ≤ a m/m + C m^{−θ} T (1 − ρ^j)`, `ρ = 2^{−θ}`,
`T = 1/(1−ρ)`. -/
lemma doubling_bound (hθ : 0 < θ) (hC : 0 ≤ C)
    (hsub : ∀ k l : ℕ, k₀ ≤ k → 1 ≤ l → l ≤ k →
      a (k + l) ≤ a k + a l + C * ((k : ℝ) + l) * (k : ℝ) ^ (-θ))
    {m : ℕ} (hm : 1 ≤ m) (hm₀ : k₀ ≤ m) (j : ℕ) :
    a (2 ^ j * m) / ((2 ^ j * m : ℕ) : ℝ) ≤ a m / m + C * (m : ℝ) ^ (-θ) *
      (1 / (1 - (2 : ℝ) ^ (-θ))) * (1 - ((2 : ℝ) ^ (-θ)) ^ j) := by
  set ρ : ℝ := (2 : ℝ) ^ (-θ)
  have hρ1 : ρ < 1 := Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)
  have hρ0 : 0 < ρ := by positivity
  have hm0 : (0 : ℝ) < m := by exact_mod_cast hm
  induction j with
  | zero => simp
  | succ j ih =>
    set k := 2 ^ j * m
    have hk1 : 1 ≤ k := Nat.one_le_iff_ne_zero.mpr (by positivity)
    have hk0 : k₀ ≤ k := hm₀.trans (Nat.le_mul_of_pos_left m (by positivity))
    have hk : (0 : ℝ) < k := by exact_mod_cast hk1
    have h2 : 2 ^ (j + 1) * m = k + k := by rw [pow_succ]; ring
    have hs := hsub k k hk0 hk1 le_rfl
    rw [h2]
    have hkr : (k : ℝ) ^ (-θ) = ρ ^ j * (m : ℝ) ^ (-θ) := by
      simp only [k, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat]
      rw [Real.mul_rpow (by positivity) hm0.le, two_pow_rpow_neg]
    have step : a (k + k) / ((k + k : ℕ) : ℝ) ≤ a k / k + C * ρ ^ j * (m : ℝ) ^ (-θ) := by
      rw [div_le_iff₀ (by push_cast; linarith)]
      push_cast
      rw [hkr] at hs
      have : a k / k * (k + k) = 2 * a k := by field_simp; ring
      nlinarith
    refine step.trans ?_
    have hT : (1 / (1 - ρ)) * (1 - ρ) = 1 := by field_simp [(sub_pos.mpr hρ1).ne']
    have key : C * (m : ℝ) ^ (-θ) * (1 / (1 - ρ)) * (1 - ρ ^ j) + C * ρ ^ j * (m : ℝ) ^ (-θ) =
        C * (m : ℝ) ^ (-θ) * (1 / (1 - ρ)) * (1 - ρ ^ (j + 1)) := by
      have e : (1 - ρ ^ (j + 1)) = (1 - ρ ^ j) + ρ ^ j * (1 - ρ) := by ring
      have h' : C * (m : ℝ) ^ (-θ) * (1 / (1 - ρ)) * (ρ ^ j * (1 - ρ)) =
          C * ρ ^ j * (m : ℝ) ^ (-θ) * ((1 / (1 - ρ)) * (1 - ρ)) := by ring
      rw [e, mul_add, h', hT, mul_one]
    linarith [ih]

/-- Greedy dyadic decomposition: with `S = a m/m + C m^{−θ}/(1−2^{−θ})`,
`a n ≤ n S + M m + 2^θ C ⌊log₂ n⌋ n^{1−θ}` for all `n`. -/
lemma greedy_bound (hθ : 0 < θ) (hθ1 : θ ≤ 1) (hC : 0 ≤ C) (hnn : ∀ n, 0 ≤ a n)
    (hM : ∀ n, a n ≤ M * n)
    (hsub : ∀ k l : ℕ, k₀ ≤ k → 1 ≤ l → l ≤ k →
      a (k + l) ≤ a k + a l + C * ((k : ℝ) + l) * (k : ℝ) ^ (-θ))
    {m : ℕ} (hm : 1 ≤ m) (hm₀ : k₀ ≤ m) (n : ℕ) :
    a n ≤ n * (a m / m + C * (m : ℝ) ^ (-θ) * (1 / (1 - (2 : ℝ) ^ (-θ)))) + M * m +
      2 ^ θ * C * (Nat.log 2 n) * (n : ℝ) ^ (1 - θ) := by
  set ρ : ℝ := (2 : ℝ) ^ (-θ)
  have hρ1 : ρ < 1 := Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)
  have hρ0 : 0 < ρ := by positivity
  have hm0 : (0 : ℝ) < m := by exact_mod_cast hm
  have hM0 : 0 ≤ M := by have := hM 1; have := hnn 1; simp at *; linarith
  set S := a m / m + C * (m : ℝ) ^ (-θ) * (1 / (1 - ρ))
  have hS : 0 ≤ S := by
    have : 0 < 1 - ρ := sub_pos.mpr hρ1
    have := hnn m; positivity
  have hdbl : ∀ j, a (2 ^ j * m) ≤ ((2 ^ j * m : ℕ) : ℝ) * S := fun j => by
    have h := doubling_bound hθ hC hsub hm hm₀ j
    have hpos : (0 : ℝ) < ((2 ^ j * m : ℕ) : ℝ) := by
      exact_mod_cast Nat.mul_pos (by positivity) hm
    rw [div_le_iff₀ hpos] at h
    refine h.trans ?_
    rw [mul_comm]
    refine mul_le_mul_of_nonneg_left ?_ hpos.le
    have : 0 ≤ C * (m : ℝ) ^ (-θ) * (1 / (1 - ρ)) := by
      have : 0 < 1 - ρ := sub_pos.mpr hρ1; positivity
    have : 0 ≤ ρ ^ j := by positivity
    nlinarith
  have herr : ∀ n : ℕ, 0 ≤ 2 ^ θ * C * (Nat.log 2 n) * (n : ℝ) ^ (1 - θ) := fun n => by positivity
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    by_cases hnm : n < m
    · have h1 : a n ≤ M * m := (hM n).trans (mul_le_mul_of_nonneg_left
        (by exact_mod_cast hnm.le) hM0)
      have : 0 ≤ (n : ℝ) * S := by positivity
      linarith [herr n]
    push_neg at hnm
    have hq : n / m ≠ 0 := (Nat.div_pos hnm hm).ne'
    set j := Nat.log 2 (n / m)
    have hjle : 2 ^ j * m ≤ n :=
      (Nat.mul_le_mul_right m (Nat.pow_log_le_self 2 hq)).trans (Nat.div_mul_le_self n m)
    have hjlt : n < 2 ^ (j + 1) * m :=
      (Nat.div_lt_iff_lt_mul hm).mp (Nat.lt_pow_succ_log_self (by norm_num) _)
    set k := 2 ^ j * m
    set r := n - k
    have hnkr : n = k + r := (Nat.add_sub_cancel' hjle).symm
    have hrk : r < k := by
      have : 2 ^ (j + 1) * m = k + k := by simp only [k]; rw [pow_succ]; ring
      omega
    rcases Nat.eq_zero_or_pos r with hr0 | hr1
    · have : n = k := by omega
      rw [this]
      have h := hdbl j
      change a k ≤ (k : ℝ) * S at h
      have : 0 ≤ M * m := by positivity
      linarith [herr k]
    -- the split `n = k + r`, `1 ≤ r < k`
    have hk1 : 1 ≤ k := Nat.one_le_iff_ne_zero.mpr (by positivity)
    have hk0 : k₀ ≤ k := hm₀.trans (Nat.le_mul_of_pos_left m (by positivity))
    have hs := hsub k r hk0 hr1 hrk.le
    have ihr := ih r (by omega)
    have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
    have hk : (0 : ℝ) < k := by exact_mod_cast hk1
    have hkn : (n : ℝ) / 2 ≤ k := by
      have : (n : ℝ) < 2 * k := by
        have : n < 2 * k := by omega
        exact_mod_cast this
      linarith
    -- error of the split
    have hsplit : C * ((k : ℝ) + r) * (k : ℝ) ^ (-θ) ≤ 2 ^ θ * C * (n : ℝ) ^ (1 - θ) := by
      have e1 : ((k : ℝ) + r) = n := by rw [hnkr]; push_cast; ring
      rw [e1]
      have h1 : (k : ℝ) ^ (-θ) ≤ ((n : ℝ) / 2) ^ (-θ) :=
        Real.rpow_le_rpow_of_nonpos (by positivity) hkn (by linarith)
      have h2 : (n : ℝ) * ((n : ℝ) / 2) ^ (-θ) = 2 ^ θ * (n : ℝ) ^ (1 - θ) := by
        rw [Real.div_rpow hn0.le (by norm_num), Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2),
          div_inv_eq_mul, sub_eq_add_neg, Real.rpow_add hn0, Real.rpow_one]
        ring
      calc C * (n : ℝ) * (k : ℝ) ^ (-θ) ≤ C * (n : ℝ) * ((n : ℝ) / 2) ^ (-θ) :=
            mul_le_mul_of_nonneg_left h1 (by positivity)
        _ = 2 ^ θ * C * (n : ℝ) ^ (1 - θ) := by rw [mul_assoc, h2]; ring
    -- the logarithm drops by one
    have hlog : Nat.log 2 r + 1 ≤ Nat.log 2 n := by
      rw [← Nat.log_mul_base (by norm_num) (by omega)]
      exact Nat.log_mono_right (by omega)
    have hpow : (r : ℝ) ^ (1 - θ) ≤ (n : ℝ) ^ (1 - θ) :=
      Real.rpow_le_rpow (by positivity) (by exact_mod_cast (show r ≤ n by omega)) (by linarith)
    have hlogR : ((Nat.log 2 r : ℕ) : ℝ) + 1 ≤ (Nat.log 2 n : ℕ) := by exact_mod_cast hlog
    have hr_err : 2 ^ θ * C * (Nat.log 2 r) * (r : ℝ) ^ (1 - θ) + 2 ^ θ * C * (n : ℝ) ^ (1 - θ)
        ≤ 2 ^ θ * C * (Nat.log 2 n) * (n : ℝ) ^ (1 - θ) := by
      have h0 : 0 ≤ 2 ^ θ * C := by positivity
      have h3 : 2 ^ θ * C * (Nat.log 2 r) * (r : ℝ) ^ (1 - θ) ≤
          2 ^ θ * C * (Nat.log 2 r) * (n : ℝ) ^ (1 - θ) :=
        mul_le_mul_of_nonneg_left hpow (by positivity)
      have h4 : 0 ≤ (n : ℝ) ^ (1 - θ) := by positivity
      have h5 : 2 ^ θ * C * (((Nat.log 2 r : ℕ) : ℝ) + 1) * (n : ℝ) ^ (1 - θ) ≤
          2 ^ θ * C * (Nat.log 2 n : ℕ) * (n : ℝ) ^ (1 - θ) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hlogR h0) h4
      have e : 2 ^ θ * C * (((Nat.log 2 r : ℕ) : ℝ) + 1) * (n : ℝ) ^ (1 - θ) =
          2 ^ θ * C * (Nat.log 2 r : ℕ) * (n : ℝ) ^ (1 - θ) + 2 ^ θ * C * (n : ℝ) ^ (1 - θ) := by
        ring
      linarith
    have hnr : (n : ℝ) = k + r := by rw [hnkr]; push_cast; ring
    calc a n = a (k + r) := by rw [← hnkr]
      _ ≤ a k + a r + C * ((k : ℝ) + r) * (k : ℝ) ^ (-θ) := hs
      _ ≤ k * S + (r * S + M * m + 2 ^ θ * C * (Nat.log 2 r) * (r : ℝ) ^ (1 - θ)) +
          2 ^ θ * C * (n : ℝ) ^ (1 - θ) := by
        have h := hdbl j
        change a k ≤ (k : ℝ) * S at h
        linarith
      _ ≤ n * S + M * m + 2 ^ θ * C * (Nat.log 2 n) * (n : ℝ) ^ (1 - θ) := by
        have : (n : ℝ) * S = k * S + r * S := by rw [hnr]; ring
        linarith

/-- **Hammersley's near-subadditive lemma** (DZZ l. 2421, [Hammersley 1962], [DZ10, Lemma
6.4.10]) in the form used by DZZ: if `a (k+l) ≤ a k + a l + C (k+l) k^{−θ}` for `1 ≤ l ≤ k`,
`k ≥ k₀` (`0 < θ ≤ 1`) and `0 ≤ a n ≤ M n`, then `a n / n` converges. -/
theorem tendsto_div_of_near_subadd (hθ : 0 < θ) (hθ1 : θ ≤ 1) (hC : 0 ≤ C)
    (hnn : ∀ n, 0 ≤ a n) (hM : ∀ n, a n ≤ M * n)
    (hsub : ∀ k l : ℕ, k₀ ≤ k → 1 ≤ l → l ≤ k →
      a (k + l) ≤ a k + a l + C * ((k : ℝ) + l) * (k : ℝ) ^ (-θ)) :
    ∃ χ, Tendsto (fun n : ℕ => a n / n) atTop (𝓝 χ) := by
  set x : ℕ → ℝ := fun n => a n / n
  have hM0 : 0 ≤ M := by have := hM 1; have := hnn 1; simp at *; linarith
  have hx0 : ∀ n, 0 ≤ x n := fun n => div_nonneg (hnn n) (Nat.cast_nonneg n)
  have hxM : ∀ n, x n ≤ M := fun n => by
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp [x, hM0]
    · have : (0 : ℝ) < n := by exact_mod_cast hn
      exact (div_le_iff₀ this).mpr (hM n)
  set T : ℝ := 1 / (1 - (2 : ℝ) ^ (-θ))
  have hlogt : Tendsto (fun n : ℕ => (Nat.log 2 n : ℝ) * (n : ℝ) ^ (-θ)) atTop (𝓝 0) := by
    have h1 : Tendsto (fun y : ℝ => Real.log y / y ^ θ) atTop (𝓝 0) :=
      (isLittleO_log_rpow_atTop hθ).tendsto_div_nhds_zero
    have h2 := (h1.comp tendsto_natCast_atTop_atTop).const_mul (1 / Real.log 2)
    rw [mul_zero] at h2
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds h2
      (Eventually.of_forall fun n => by positivity) ?_
    filter_upwards [eventually_ge_atTop 1] with n hn
    have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
    have hl := Real.natLog_le_logb n 2
    simp only [Nat.cast_ofNat] at hl
    rw [Real.logb] at hl
    calc (Nat.log 2 n : ℝ) * (n : ℝ) ^ (-θ) ≤ (Real.log n / Real.log 2) * (n : ℝ) ^ (-θ) :=
          mul_le_mul_of_nonneg_right hl (by positivity)
      _ = 1 / Real.log 2 * (Real.log n / (n : ℝ) ^ θ) := by
          rw [Real.rpow_neg hn0.le]; ring
  have hkey : ∀ m : ℕ, 1 ≤ m → k₀ ≤ m → ∀ ε > 0,
      ∀ᶠ n in atTop, x n < x m + C * (m : ℝ) ^ (-θ) * T + ε := by
    intro m hm hm₀ ε hε
    have hA : Tendsto (fun n : ℕ => M * m / (n : ℝ) +
        2 ^ θ * C * ((Nat.log 2 n : ℝ) * (n : ℝ) ^ (-θ))) atTop (𝓝 0) := by
      have := (tendsto_const_div_atTop_nhds_zero_nat (M * m)).add (hlogt.const_mul (2 ^ θ * C))
      simpa using this
    filter_upwards [hA (Iio_mem_nhds hε), eventually_ge_atTop 1] with n hn hn1
    have hn0 : (0 : ℝ) < n := by exact_mod_cast hn1
    have hg := greedy_bound hθ hθ1 hC hnn hM hsub hm hm₀ n
    have e : (n : ℝ) ^ (1 - θ) = n * (n : ℝ) ^ (-θ) := by
      rw [sub_eq_add_neg, Real.rpow_add hn0, Real.rpow_one]
    rw [e] at hg
    have hb : x n ≤ x m + C * (m : ℝ) ^ (-θ) * T +
        (M * m / n + 2 ^ θ * C * ((Nat.log 2 n : ℝ) * (n : ℝ) ^ (-θ))) := by
      simp only [x, T]
      rw [div_le_iff₀ hn0]
      calc a n ≤ _ := hg
        _ = _ := by field_simp; ring
    linarith [show _ < ε from hn]
  set L := liminf x atTop
  have hb : IsBoundedUnder (· ≥ ·) atTop x := isBoundedUnder_of ⟨0, hx0⟩
  have hcb : IsCoboundedUnder (· ≥ ·) atTop x := isCoboundedUnder_ge_of_le atTop hxM
  refine ⟨L, tendsto_order.2 ⟨fun b hbL => eventually_lt_of_lt_liminf hbL hb, fun b hbL => ?_⟩⟩
  set ε := (b - L) / 3
  have hε : 0 < ε := by simp only [ε]; linarith
  have hfreq : ∃ᶠ m in atTop, x m < L + ε := frequently_lt_of_liminf_lt hcb (by linarith)
  have hev : ∀ᶠ m : ℕ in atTop, 1 ≤ m ∧ k₀ ≤ m ∧ C * (m : ℝ) ^ (-θ) * T < ε := by
    have ht : Tendsto (fun m : ℕ => C * (m : ℝ) ^ (-θ) * T) atTop (𝓝 0) := by
      have := (((tendsto_rpow_neg_atTop hθ).comp tendsto_natCast_atTop_atTop).const_mul
        C).mul_const T
      simpa using this
    filter_upwards [eventually_ge_atTop 1, eventually_ge_atTop k₀, ht (Iio_mem_nhds hε)] with
      m h1 h2 h3
    exact ⟨h1, h2, h3⟩
  obtain ⟨m, hm1, hm, hm₀, hmT⟩ := (hfreq.and_eventually hev).exists
  have hεd : 3 * ε = b - L := by simp only [ε]; ring
  filter_upwards [hkey m hm hm₀ ε hε] with n hn
  linarith

end Hammersley

/-- **DZZ l. 2418–2421 along `δ_k = 2^{−k}`**: with `χ k = χ_{2^{−k}}` (so `log δ⁻¹ = k log 2`),
`χ_{δδ̃} ≤ (log δ⁻¹ χ_δ + log δ̃⁻¹ χ_δ̃)/(log δ⁻¹ + log δ̃⁻¹) + (log δ⁻¹)^{−θ}` for `δ ≤ δ̃`
(`l ≤ k`), `δ` small (`k ≥ k₀`), and `0 ≤ χ ≤ M` (DZZ (eq-very-crude)) give convergence of
`χ_{2^{−k}}`. -/
theorem dzz_chi_dyadic_tendsto {χ : ℕ → ℝ} {k₀ : ℕ} {θ M : ℝ} (hθ : 0 < θ) (hθ1 : θ ≤ 1)
    (h0 : ∀ k, 0 ≤ χ k) (hM : ∀ k, χ k ≤ M)
    (hsub : ∀ k l : ℕ, k₀ ≤ k → 1 ≤ l → l ≤ k →
      χ (k + l) ≤ (k : ℝ) / (k + l) * χ k + (l : ℝ) / (k + l) * χ l +
        ((k : ℝ) * Real.log 2) ^ (-θ)) :
    ∃ c, Tendsto χ atTop (𝓝 c) := by
  set a : ℕ → ℝ := fun n => n * χ n
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have haM : ∀ n, a n ≤ M * n := fun n => by
    simp only [a]; rw [mul_comm]; exact mul_le_mul_of_nonneg_right (hM n) (Nat.cast_nonneg n)
  obtain ⟨c, hc⟩ := tendsto_div_of_near_subadd (a := a) (C := Real.log 2 ^ (-θ)) (M := M)
    (k₀ := k₀) hθ hθ1 (by positivity) (fun n => mul_nonneg (Nat.cast_nonneg n) (h0 n)) haM
    (fun k l hk hl hlk => by
      have h := hsub k l hk hl hlk
      have hkl : (0 : ℝ) < k + l := by
        have : (1 : ℝ) ≤ l := by exact_mod_cast hl
        positivity
      simp only [a]
      push_cast
      rw [Real.mul_rpow (Nat.cast_nonneg k) hl2.le] at h
      have := mul_le_mul_of_nonneg_left h hkl.le
      have e : ((k : ℝ) + l) * ((k : ℝ) / (k + l) * χ k + (l : ℝ) / (k + l) * χ l +
          (k : ℝ) ^ (-θ) * Real.log 2 ^ (-θ)) = k * χ k + l * χ l +
          Real.log 2 ^ (-θ) * ((k : ℝ) + l) * (k : ℝ) ^ (-θ) := by
        field_simp
      linarith)
  refine ⟨c, hc.congr' ?_⟩
  filter_upwards [eventually_ge_atTop 1] with n hn
  have : (n : ℝ) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
  simp only [a]; field_simp

/-- **"By continuity the convergence extends to arbitrary `δ → 0`"** (DZZ l. 2422): `f(δ) =
E log D_δ` is nonnegative and antitone in `δ` (`one_le_lgdDZZ`, `lgdDZZ_antitone`), so
`f(2^{−k})/(k log 2) → χ` gives `f(δ)/log δ⁻¹ → χ` as `δ → 0⁺` (sandwich between the dyadic
scales `2^{−k−1} < δ ≤ 2^{−k}`). -/
theorem tendsto_of_dyadic_antitone {f : ℝ → ℝ} {χ : ℝ} (hf0 : ∀ δ, 0 < δ → 0 ≤ f δ)
    (hanti : ∀ δ δ', 0 < δ → δ ≤ δ' → f δ' ≤ f δ)
    (hdy : Tendsto (fun k : ℕ => f ((2 : ℝ)⁻¹ ^ k) / (k * Real.log 2)) atTop (𝓝 χ)) :
    Tendsto (fun δ => f δ / Real.log δ⁻¹) (𝓝[>] 0) (𝓝 χ) := by
  set y : ℕ → ℝ := fun k => f ((2 : ℝ)⁻¹ ^ k) / (k * Real.log 2)
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  set kf : ℝ → ℕ := fun δ => ⌊Real.logb 2 δ⁻¹⌋₊
  have hk : Tendsto kf (𝓝[>] 0) atTop :=
    tendsto_nat_floor_atTop.comp ((Real.tendsto_logb_atTop (by norm_num)).comp
      tendsto_inv_nhdsGT_zero)
  have hU : Tendsto (fun k : ℕ => y (k + 1) * (1 + 1 / (k : ℝ))) atTop (𝓝 χ) := by
    have := (hdy.comp (tendsto_add_atTop_nat 1)).mul
      ((tendsto_const_nhds : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (𝓝 1)).add
        tendsto_one_div_atTop_nhds_zero_nat)
    simpa using this
  have hL : Tendsto (fun k : ℕ => y k * (1 - 1 / ((k : ℝ) + 1))) atTop (𝓝 χ) := by
    have := hdy.mul ((tendsto_const_nhds : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (𝓝 1)).sub
      tendsto_one_div_add_atTop_nhds_zero_nat)
    simpa using this
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' (hL.comp hk) (hU.comp hk) ?_ ?_ <;>
  · filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < 1 / 2 by norm_num)] with δ hδ
    obtain ⟨hδ0, hδ2⟩ := hδ
    set X := Real.logb 2 δ⁻¹
    have hinv : 2 < δ⁻¹ := by
      rw [lt_inv_comm₀ (by norm_num) hδ0]; linarith
    have hlogX : Real.log δ⁻¹ = X * Real.log 2 := by
      simp only [X, Real.logb]; field_simp
    have hX1 : 1 < X := by
      rw [Real.lt_logb_iff_rpow_lt (by norm_num) (by positivity)]; simpa using hinv
    have hkX : (kf δ : ℝ) ≤ X := Nat.floor_le (by linarith)
    have hXk : X < kf δ + 1 := Nat.lt_floor_add_one X
    have hk1 : 1 ≤ kf δ := Nat.le_floor (by rw [Nat.cast_one]; exact hX1.le)
    set k := kf δ
    have hk0 : (0 : ℝ) < k := by exact_mod_cast hk1
    have hlogδ : Real.log δ = -(X * Real.log 2) := by rw [← hlogX, Real.log_inv, neg_neg]
    have hpow : ∀ j : ℕ, Real.log ((2 : ℝ)⁻¹ ^ j) = -(j * Real.log 2) := fun j => by
      rw [Real.log_pow, Real.log_inv]; ring
    have hup : δ ≤ (2 : ℝ)⁻¹ ^ k := by
      rw [← Real.log_le_log_iff hδ0 (by positivity), hlogδ, hpow]
      nlinarith
    have hlo : (2 : ℝ)⁻¹ ^ (k + 1) ≤ δ := by
      rw [← Real.log_le_log_iff (by positivity) hδ0, hlogδ, hpow]
      push_cast; nlinarith
    have f1 := hanti _ _ hδ0 hup
    have f2 := hanti _ _ (by positivity) hlo
    have hfδ := hf0 δ hδ0
    have hLpos : 0 < Real.log δ⁻¹ := by rw [hlogX]; nlinarith
    simp only [Function.comp, y]
    first
    | -- lower bound
      have e : f ((2 : ℝ)⁻¹ ^ k) / (k * Real.log 2) * (1 - 1 / ((k : ℝ) + 1)) =
          f ((2 : ℝ)⁻¹ ^ k) / ((k + 1) * Real.log 2) := by field_simp; ring
      rw [e, div_le_div_iff₀ (by positivity) hLpos]
      have h1 : Real.log δ⁻¹ ≤ (k + 1) * Real.log 2 := by rw [hlogX]; nlinarith
      have := hf0 _ (show (0 : ℝ) < (2 : ℝ)⁻¹ ^ k by positivity)
      nlinarith
    | -- upper bound
      have e : f ((2 : ℝ)⁻¹ ^ (k + 1)) / (((k + 1 : ℕ) : ℝ) * Real.log 2) * (1 + 1 / (k : ℝ)) =
          f ((2 : ℝ)⁻¹ ^ (k + 1)) / (k * Real.log 2) := by push_cast; field_simp
      rw [e, div_le_div_iff₀ hLpos (by positivity)]
      have h1 : k * Real.log 2 ≤ Real.log δ⁻¹ := by rw [hlogX]; nlinarith
      nlinarith

end DZZ
end LQGMetric
