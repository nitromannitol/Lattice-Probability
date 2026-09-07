/-
The central binomial ratio, uniformly on the diffusive scale.

The one-dimensional local limit theorem rests on

  `C(2m, m+k) / C(2m, m) = ∏_{j < k} (m - j)/(m + j + 1)`,

whose logarithm is `-k²/m` up to an error `4k³/m²`.  On `|k| ≤ A√m` that error
is `4A³/√m`, so the ratio converges to `exp(-k²/m)` uniformly over the whole
diffusive window.  Nothing here needs Stirling's formula: Stirling enters the
local limit theorem only through the NORMALIZATION `C(2m,m) ~ 4^m/√(πm)`, and
the uniformity in `k`, which is the substantive half, is the estimate below.

The one analytic input is the second-order bound `|log(1+x) - x| ≤ 2x²` on
`|x| ≤ 1/2`, which is Mathlib's `Real.abs_log_sub_add_sum_range_le` at one term.
-/
import Mathlib

set_option autoImplicit false
set_option relaxedAutoImplicit false

open Finset Filter Topology

namespace LatticeProb

/-! ### Two elementary estimates -/


theorem abs_log_one_add_sub_le {x : ℝ} (hx : |x| ≤ 1/2) :
    |Real.log (1 + x) - x| ≤ 2 * x ^ 2 := by
  have hx1 : |(-x)| < 1 := by
    rw [abs_neg]
    linarith
  have h := Real.abs_log_sub_add_sum_range_le hx1 1
  rw [Finset.sum_range_one] at h
  simp only [pow_one, Nat.cast_zero, zero_add, div_one] at h
  have hsub : (1 : ℝ) - -x = 1 + x := by ring
  rw [hsub] at h
  have hden : (1 : ℝ) - |(-x)| ≥ 1/2 := by
    rw [abs_neg]; linarith
  have hnum : |(-x)| ^ (1 + 1) = x ^ 2 := by
    rw [show (1:ℕ) + 1 = 2 from rfl, sq_abs, neg_sq]
  rw [hnum] at h
  have hpos : (0:ℝ) < 1 - |(-x)| := by linarith
  have hle : x ^ 2 / (1 - |(-x)|) ≤ 2 * x ^ 2 := by
    rw [div_le_iff₀ hpos]
    nlinarith [sq_nonneg x]
  rw [show Real.log (1 + x) - x = -x + Real.log (1 + x) from by ring]
  linarith

theorem abs_exp_sub_exp_le_of_nonpos {a b : ℝ} (ha : a ≤ 0) (hb : b ≤ 0) :
    |Real.exp a - Real.exp b| ≤ |a - b| := by
  rcases le_total a b with h | h
  · rw [abs_of_nonpos (by simp [Real.exp_le_exp.mpr h]), abs_of_nonpos (by linarith)]
    have h1 : Real.exp b - Real.exp a = Real.exp b * (1 - Real.exp (a - b)) := by
      rw [mul_sub, mul_one, ← Real.exp_add, show b + (a - b) = a from by ring]
    have h2 : (1 : ℝ) - Real.exp (a - b) ≤ b - a := by
      have := Real.add_one_le_exp (a - b)
      linarith
    have h3 : Real.exp b ≤ 1 := Real.exp_le_one_iff.mpr hb
    have h4 : (0:ℝ) ≤ b - a := by linarith
    nlinarith [Real.exp_pos b, Real.exp_pos (a-b)]
  · rw [abs_of_nonneg (by simp [Real.exp_le_exp.mpr h]), abs_of_nonneg (by linarith)]
    have h1 : Real.exp a - Real.exp b = Real.exp a * (1 - Real.exp (b - a)) := by
      rw [mul_sub, mul_one, ← Real.exp_add, show a + (b - a) = b from by ring]
    have h2 : (1 : ℝ) - Real.exp (b - a) ≤ a - b := by
      have := Real.add_one_le_exp (b - a)
      linarith
    have h3 : Real.exp a ≤ 1 := Real.exp_le_one_iff.mpr ha
    have h4 : (0:ℝ) ≤ a - b := by linarith
    nlinarith [Real.exp_pos a, Real.exp_pos (b-a)]


/-! ### The ratio of central binomial coefficients -/


theorem choose_two_mul_prod (m : ℕ) : ∀ k : ℕ, k ≤ m →
    (Nat.choose (2 * m) (m + k) : ℝ) * ∏ j ∈ Finset.range k, ((m : ℝ) + j + 1)
      = (Nat.choose (2 * m) m : ℝ) * ∏ j ∈ Finset.range k, ((m : ℝ) - j) := by
  intro k
  induction k with
  | zero => intro _; simp
  | succ k ih =>
      intro hk
      have hkm : k ≤ m := by omega
      have hnat : Nat.choose (2 * m) (m + k + 1) * (m + k + 1)
          = Nat.choose (2 * m) (m + k) * (2 * m - (m + k)) :=
        Nat.choose_succ_right_eq (2 * m) (m + k)
      have hsub : 2 * m - (m + k) = m - k := by omega
      rw [hsub] at hnat
      have hcast : (Nat.choose (2 * m) (m + k + 1) : ℝ) * ((m : ℝ) + k + 1)
          = (Nat.choose (2 * m) (m + k) : ℝ) * ((m : ℝ) - k) := by
        have := congrArg (fun n : ℕ => (n : ℝ)) hnat
        push_cast [Nat.cast_sub hkm] at this
        linarith
      rw [Finset.prod_range_succ, Finset.prod_range_succ]
      have hstep : (Nat.choose (2 * m) (m + (k + 1)) : ℝ)
          * ((∏ j ∈ Finset.range k, ((m : ℝ) + j + 1)) * ((m : ℝ) + k + 1))
          = ((Nat.choose (2 * m) (m + k + 1) : ℝ) * ((m : ℝ) + k + 1))
            * ∏ j ∈ Finset.range k, ((m : ℝ) + j + 1) := by
        rw [show m + (k + 1) = m + k + 1 from by omega]
        ring
      rw [hstep, hcast]
      have hih := ih hkm
      calc (Nat.choose (2 * m) (m + k) : ℝ) * ((m : ℝ) - k)
            * ∏ j ∈ Finset.range k, ((m : ℝ) + j + 1)
          = ((Nat.choose (2 * m) (m + k) : ℝ)
              * ∏ j ∈ Finset.range k, ((m : ℝ) + j + 1)) * ((m : ℝ) - k) := by ring
        _ = ((Nat.choose (2 * m) m : ℝ) * ∏ j ∈ Finset.range k, ((m : ℝ) - j)) * ((m : ℝ) - k) := by
            rw [hih]
        _ = (Nat.choose (2 * m) m : ℝ) * ((∏ j ∈ Finset.range k, ((m : ℝ) - j)) * ((m : ℝ) - k)) := by
            ring


/-! ### The logarithm of the ratio -/


theorem abs_log_term_add_le (m j : ℕ) (hj : 2 * j + 2 ≤ m) :
    |Real.log (((m : ℝ) - j) / ((m : ℝ) + j + 1)) + (2 * (j : ℝ) + 1) / (m : ℝ)|
      ≤ 4 * ((j : ℝ) + 1) ^ 2 / (m : ℝ) ^ 2 := by
  have hm : (1 : ℝ) ≤ (m : ℝ) := by
    have : 1 ≤ m := by omega
    exact_mod_cast this
  have hmpos : (0 : ℝ) < (m : ℝ) := by linarith
  have hjm : 2 * (j : ℝ) + 2 ≤ (m : ℝ) := by exact_mod_cast hj
  set x : ℝ := -(j : ℝ) / (m : ℝ) with hxdef
  set y : ℝ := ((j : ℝ) + 1) / (m : ℝ) with hydef
  have hxabs : |x| ≤ 1/2 := by
    rw [hxdef, abs_div, abs_neg, Nat.abs_cast, abs_of_pos hmpos, div_le_iff₀ hmpos]
    linarith
  have hyabs : |y| ≤ 1/2 := by
    rw [hydef, abs_div, abs_of_pos hmpos, abs_of_nonneg (by positivity : (0:ℝ) ≤ (j:ℝ) + 1),
      div_le_iff₀ hmpos]
    linarith
  have h1 : (m : ℝ) - j = (m : ℝ) * (1 + x) := by
    rw [hxdef]; field_simp; ring
  have h2 : (m : ℝ) + j + 1 = (m : ℝ) * (1 + y) := by
    rw [hydef]; field_simp; ring
  have hx1 : (0 : ℝ) < 1 + x := by
    have := abs_le.mp hxabs
    linarith [this.1]
  have hy1 : (0 : ℝ) < 1 + y := by
    have := abs_le.mp hyabs
    linarith [this.1]
  have hlog : Real.log (((m : ℝ) - j) / ((m : ℝ) + j + 1))
      = Real.log (1 + x) - Real.log (1 + y) := by
    rw [h1, h2, Real.log_div (by positivity) (by positivity),
      Real.log_mul (ne_of_gt hmpos) (ne_of_gt hx1), Real.log_mul (ne_of_gt hmpos) (ne_of_gt hy1)]
    ring
  have hxy : x - y = -((2 * (j : ℝ) + 1) / (m : ℝ)) := by
    rw [hxdef, hydef]; field_simp; ring
  have hrw : Real.log (((m : ℝ) - j) / ((m : ℝ) + j + 1)) + (2 * (j : ℝ) + 1) / (m : ℝ)
      = (Real.log (1 + x) - x) - (Real.log (1 + y) - y) := by
    rw [hlog]
    have : (2 * (j : ℝ) + 1) / (m : ℝ) = -(x - y) := by rw [hxy]; ring
    rw [this]; ring
  rw [hrw]
  have hA := abs_log_one_add_sub_le hxabs
  have hB := abs_log_one_add_sub_le hyabs
  have htri : |(Real.log (1 + x) - x) - (Real.log (1 + y) - y)|
      ≤ |Real.log (1 + x) - x| + |Real.log (1 + y) - y| := abs_sub _ _
  have hxsq : x ^ 2 ≤ ((j : ℝ) + 1) ^ 2 / (m : ℝ) ^ 2 := by
    rw [hxdef, div_pow, neg_sq]
    refine div_le_div_of_nonneg_right ?_ (by positivity)
    nlinarith [Nat.cast_nonneg (α := ℝ) j]
  have hysq : y ^ 2 ≤ ((j : ℝ) + 1) ^ 2 / (m : ℝ) ^ 2 := by
    rw [hydef, div_pow]
  rw [show 4 * ((j : ℝ) + 1) ^ 2 / (m : ℝ) ^ 2 = 4 * (((j : ℝ) + 1) ^ 2 / (m : ℝ) ^ 2) from by
    ring]
  linarith


/-! ### The ratio as a product, and its logarithm -/

theorem choose_two_mul_pos (m : ℕ) : 0 < Nat.choose (2 * m) m :=
  Nat.choose_pos (by omega)

theorem binomRatio_eq_prod (m k : ℕ) (hk : k ≤ m) :
    (Nat.choose (2 * m) (m + k) : ℝ) / (Nat.choose (2 * m) m : ℝ)
      = ∏ j ∈ Finset.range k, (((m : ℝ) - j) / ((m : ℝ) + j + 1)) := by
  have hB : (0 : ℝ) < (Nat.choose (2 * m) m : ℝ) := by
    exact_mod_cast choose_two_mul_pos m
  have hP1 : (0 : ℝ) < ∏ j ∈ Finset.range k, ((m : ℝ) + j + 1) := by
    refine Finset.prod_pos fun j _ => ?_
    positivity
  have h := choose_two_mul_prod m k hk
  rw [Finset.prod_div_distrib]
  field_simp
  linarith [h]

theorem binomRatio_pos (m k : ℕ) (hk : k ≤ m) :
    0 < (Nat.choose (2 * m) (m + k) : ℝ) / (Nat.choose (2 * m) m : ℝ) := by
  have hB : (0 : ℝ) < (Nat.choose (2 * m) m : ℝ) := by
    exact_mod_cast choose_two_mul_pos m
  have hA : (0 : ℝ) < (Nat.choose (2 * m) (m + k) : ℝ) := by
    have : 0 < Nat.choose (2 * m) (m + k) := Nat.choose_pos (by omega)
    exact_mod_cast this
  positivity

theorem binomRatio_le_one (m k : ℕ) :
    (Nat.choose (2 * m) (m + k) : ℝ) / (Nat.choose (2 * m) m : ℝ) ≤ 1 := by
  have hB : (0 : ℝ) < (Nat.choose (2 * m) m : ℝ) := by
    exact_mod_cast choose_two_mul_pos m
  rw [div_le_one hB]
  have hmid : Nat.choose (2 * m) (m + k) ≤ Nat.choose (2 * m) (2 * m / 2) :=
    Nat.choose_le_middle (m + k) (2 * m)
  rw [show 2 * m / 2 = m from by omega] at hmid
  exact_mod_cast hmid

theorem log_binomRatio (m k : ℕ) (hk : 2 * k ≤ m) :
    Real.log ((Nat.choose (2 * m) (m + k) : ℝ) / (Nat.choose (2 * m) m : ℝ))
      = ∑ j ∈ Finset.range k, Real.log (((m : ℝ) - j) / ((m : ℝ) + j + 1)) := by
  rw [binomRatio_eq_prod m k (by omega)]
  refine Real.log_prod fun j hj => ?_
  rw [Finset.mem_range] at hj
  have hjm : (j : ℝ) < (m : ℝ) := by
    have : j < m := by omega
    exact_mod_cast this
  have h1 : (m : ℝ) - j ≠ 0 := by linarith
  have h2 : (m : ℝ) + j + 1 ≠ 0 := by positivity
  exact div_ne_zero h1 h2

/-! ### The logarithm of the ratio is `-k²/m` up to `4k³/m²` -/

theorem sum_two_mul_add_one (k : ℕ) :
    ∑ j ∈ Finset.range k, (2 * (j : ℝ) + 1) = (k : ℝ) ^ 2 := by
  induction k with
  | zero => simp
  | succ k ih =>
      rw [Finset.sum_range_succ, ih]
      push_cast
      ring

/-- **The logarithm of the central binomial ratio.**  It is `-k²/m` with an
error `4k³/m²`, uniformly over `2k ≤ m`. -/
theorem abs_log_binomRatio_add_le (m k : ℕ) (hk : 2 * k ≤ m) :
    |Real.log ((Nat.choose (2 * m) (m + k) : ℝ) / (Nat.choose (2 * m) m : ℝ))
        + (k : ℝ) ^ 2 / (m : ℝ)|
      ≤ 4 * (k : ℝ) ^ 3 / (m : ℝ) ^ 2 := by
  rcases Nat.eq_zero_or_pos k with hk0 | hkpos
  · subst hk0
    simp
  have hm : 1 ≤ m := by omega
  have hmR : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
  have hmpos : (0 : ℝ) < (m : ℝ) := by linarith
  have hkR : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hkpos
  have hsum : ∑ j ∈ Finset.range k, ((2 * (j : ℝ) + 1) / (m : ℝ)) = (k : ℝ) ^ 2 / (m : ℝ) := by
    rw [← Finset.sum_div, sum_two_mul_add_one]
  rw [log_binomRatio m k hk, ← hsum, ← Finset.sum_add_distrib]
  refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
  have hterm : ∀ j ∈ Finset.range k,
      |Real.log (((m : ℝ) - j) / ((m : ℝ) + j + 1)) + (2 * (j : ℝ) + 1) / (m : ℝ)|
        ≤ 4 * (k : ℝ) ^ 2 / (m : ℝ) ^ 2 := by
    intro j hj
    rw [Finset.mem_range] at hj
    have hjm : 2 * j + 2 ≤ m := by omega
    refine le_trans (abs_log_term_add_le m j hjm) ?_
    have hjk : (j : ℝ) + 1 ≤ (k : ℝ) := by
      have : j + 1 ≤ k := by omega
      exact_mod_cast this
    have hnn : (0 : ℝ) ≤ (j : ℝ) + 1 := by positivity
    have hsq : ((j : ℝ) + 1) ^ 2 ≤ (k : ℝ) ^ 2 := by nlinarith
    have hmsq : (0 : ℝ) < (m : ℝ) ^ 2 := by positivity
    rw [div_le_div_iff_of_pos_right hmsq]
    linarith
  refine le_trans (Finset.sum_le_sum hterm) ?_
  rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  have hmsq : (0 : ℝ) < (m : ℝ) ^ 2 := by positivity
  have heq : (k : ℝ) * (4 * (k : ℝ) ^ 2 / (m : ℝ) ^ 2) = 4 * (k : ℝ) ^ 3 / (m : ℝ) ^ 2 := by
    field_simp
  rw [heq]

/-! ### The ratio converges to the Gaussian factor, uniformly on the diffusive scale -/

/-- **The central binomial ratio on the diffusive scale.**  For every `A` and
every accuracy `ε` there is a horizon past which

  `|C(2m, m+k)/C(2m, m) - exp(-k²/m)| ≤ ε`

for every `k` with `k ≤ A√m`.  This is the uniformity in `k` that the
one-dimensional local limit theorem needs, and it uses no Stirling formula. -/
theorem exists_binomRatio_sub_exp_le {A ε : ℝ} (hA : 0 < A) (hε : 0 < ε) :
    ∃ m₀ : ℕ, 1 ≤ m₀ ∧ ∀ m : ℕ, m₀ ≤ m → ∀ k : ℕ, (k : ℝ) ≤ A * Real.sqrt (m : ℝ) →
      |(Nat.choose (2 * m) (m + k) : ℝ) / (Nat.choose (2 * m) m : ℝ)
          - Real.exp (-((k : ℝ) ^ 2 / (m : ℝ)))| ≤ ε := by
  set M : ℝ := max ((2 * A + 2) ^ 2) ((4 * A ^ 3 / ε) ^ 2) with hM
  refine ⟨⌈M⌉₊ + 1, by omega, fun m hm k hk => ?_⟩
  have hmR : M ≤ (m : ℝ) := by
    have h1 : M ≤ (⌈M⌉₊ : ℝ) := Nat.le_ceil M
    have h2 : ((⌈M⌉₊ : ℕ) : ℝ) ≤ (m : ℝ) := by
      have : ⌈M⌉₊ ≤ m := by omega
      exact_mod_cast this
    linarith
  have hm1 : 1 ≤ m := by omega
  have hm1R : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm1
  have hmpos : (0 : ℝ) < (m : ℝ) := by linarith
  have hsq : Real.sqrt (m : ℝ) * Real.sqrt (m : ℝ) = (m : ℝ) :=
    Real.mul_self_sqrt (le_of_lt hmpos)
  have hs1 : (1 : ℝ) ≤ Real.sqrt (m : ℝ) := by
    rw [show (1 : ℝ) = Real.sqrt 1 from (Real.sqrt_one).symm]
    exact Real.sqrt_le_sqrt hm1R
  have hspos : (0 : ℝ) < Real.sqrt (m : ℝ) := by linarith
  -- the first threshold: `2k ≤ m`
  have hbig1 : (2 * A + 2) ≤ Real.sqrt (m : ℝ) := by
    have h1 : (2 * A + 2) ^ 2 ≤ (m : ℝ) := le_trans (le_max_left _ _) hmR
    have h2 : Real.sqrt ((2 * A + 2) ^ 2) ≤ Real.sqrt (m : ℝ) := Real.sqrt_le_sqrt h1
    rwa [Real.sqrt_sq (by linarith)] at h2
  have hknn : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
  have h2k : 2 * (k : ℝ) ≤ (m : ℝ) := by
    have hka : 2 * (k : ℝ) ≤ 2 * A * Real.sqrt (m : ℝ) := by linarith
    nlinarith [hspos, hs1]
  have hkm : 2 * k ≤ m := by exact_mod_cast h2k
  -- the second threshold: the error is below `ε`
  have hbig2 : 4 * A ^ 3 / ε ≤ Real.sqrt (m : ℝ) := by
    have h1 : (4 * A ^ 3 / ε) ^ 2 ≤ (m : ℝ) := le_trans (le_max_right _ _) hmR
    have h2 : Real.sqrt ((4 * A ^ 3 / ε) ^ 2) ≤ Real.sqrt (m : ℝ) := Real.sqrt_le_sqrt h1
    rwa [Real.sqrt_sq (by positivity)] at h2
  have herr : 4 * (k : ℝ) ^ 3 / (m : ℝ) ^ 2 ≤ ε := by
    have hk3 : (k : ℝ) ^ 3 ≤ A ^ 3 * ((m : ℝ) * Real.sqrt (m : ℝ)) := by
      have hpow : (k : ℝ) ^ 3 ≤ (A * Real.sqrt (m : ℝ)) ^ 3 := by
        refine pow_le_pow_left₀ hknn hk 3
      calc (k : ℝ) ^ 3 ≤ (A * Real.sqrt (m : ℝ)) ^ 3 := hpow
        _ = A ^ 3 * (Real.sqrt (m : ℝ) * Real.sqrt (m : ℝ) * Real.sqrt (m : ℝ)) := by ring
        _ = A ^ 3 * ((m : ℝ) * Real.sqrt (m : ℝ)) := by rw [hsq]
    have hmsq : (0 : ℝ) < (m : ℝ) ^ 2 := by positivity
    rw [div_le_iff₀ hmsq]
    have hAe : 4 * A ^ 3 ≤ ε * Real.sqrt (m : ℝ) := by
      rw [div_le_iff₀ hε] at hbig2
      linarith
    calc 4 * (k : ℝ) ^ 3 ≤ 4 * (A ^ 3 * ((m : ℝ) * Real.sqrt (m : ℝ))) := by linarith
      _ = (4 * A ^ 3) * ((m : ℝ) * Real.sqrt (m : ℝ)) := by ring
      _ ≤ (ε * Real.sqrt (m : ℝ)) * ((m : ℝ) * Real.sqrt (m : ℝ)) :=
          mul_le_mul_of_nonneg_right hAe (by positivity)
      _ = ε * (m : ℝ) * (Real.sqrt (m : ℝ) * Real.sqrt (m : ℝ)) := by ring
      _ = ε * (m : ℝ) * (m : ℝ) := by rw [hsq]
      _ = ε * (m : ℝ) ^ 2 := by ring
  -- the comparison of the two exponentials
  have hratpos : 0 < (Nat.choose (2 * m) (m + k) : ℝ) / (Nat.choose (2 * m) m : ℝ) :=
    binomRatio_pos m k (by omega)
  have hlognp : Real.log ((Nat.choose (2 * m) (m + k) : ℝ) / (Nat.choose (2 * m) m : ℝ)) ≤ 0 :=
    Real.log_nonpos (le_of_lt hratpos) (binomRatio_le_one m k)
  have hgnp : -((k : ℝ) ^ 2 / (m : ℝ)) ≤ 0 := neg_nonpos.mpr (by positivity)
  have hexp : Real.exp (Real.log ((Nat.choose (2 * m) (m + k) : ℝ)
      / (Nat.choose (2 * m) m : ℝ)))
      = (Nat.choose (2 * m) (m + k) : ℝ) / (Nat.choose (2 * m) m : ℝ) :=
    Real.exp_log hratpos
  calc |(Nat.choose (2 * m) (m + k) : ℝ) / (Nat.choose (2 * m) m : ℝ)
          - Real.exp (-((k : ℝ) ^ 2 / (m : ℝ)))|
      = |Real.exp (Real.log ((Nat.choose (2 * m) (m + k) : ℝ) / (Nat.choose (2 * m) m : ℝ)))
          - Real.exp (-((k : ℝ) ^ 2 / (m : ℝ)))| := by rw [hexp]
    _ ≤ |Real.log ((Nat.choose (2 * m) (m + k) : ℝ) / (Nat.choose (2 * m) m : ℝ))
          - -((k : ℝ) ^ 2 / (m : ℝ))| := abs_exp_sub_exp_le_of_nonpos hlognp hgnp
    _ = |Real.log ((Nat.choose (2 * m) (m + k) : ℝ) / (Nat.choose (2 * m) m : ℝ))
          + (k : ℝ) ^ 2 / (m : ℝ)| := by congr 1; ring
    _ ≤ 4 * (k : ℝ) ^ 3 / (m : ℝ) ^ 2 := abs_log_binomRatio_add_le m k hkm
    _ ≤ ε := herr

end LatticeProb
