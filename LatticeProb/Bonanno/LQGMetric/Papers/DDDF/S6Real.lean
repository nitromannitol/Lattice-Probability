/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DDDF.S6Real at commit fdb5cad; only the module paths of local imports are changed. -/
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Sqrt

/-!
# DDDF §6.2: the real analysis behind (6.99) and (1.3) (task P2-DDDF6)

DDDF = Ding–Dubédat–Dunlap–Falconet, arXiv:1904.08021, `literature/src/1904.08021/tightness.tex`.
In log scale `a(t) = log λ_{2^{-t}}`:

* `mulCont_log` — DDDF l. 1622–1638: from (6.98) `|a(n+r) − a(n)| ≤ C₁` (`r ∈ [0,1]`) and (5.76)
  `|a(n+k) − a(n) − a(k)| ≤ C₂√k` (`n, k ≥ 1`) we get
  `|a(t+t') − a(t) − a(t')| ≤ B + C₂ √(t ∧ t')`. DDDF's (6.101) (`eq:S1`, `r + r' ∈ [0,2]`) is
  obtained from two uses of (6.98); DDDF's (6.100) (`eq:S2`) needs `n ∧ n' ≥ 1`, the case
  `n ∧ n' = 0` costs the constant `|a(0)|`.
* `expo_log` — (1.3) from (5.77) and (6.98) (DDDF l. 162–166 with l. 1608–1612).
* `le_of_asymp` — the identification of the exponent `ρ` in the proof of Prop 26
  (DDDF l. 1276–1281: "Combining (5.78) and (5.54) we get `ρ = 2^{-(1−ξQ)}`").
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace LQGMetric
namespace DDDF
namespace S6

/-- `t = ⌊t⌋ + r` with `r ∈ [0,1)` -/
lemma floor_decomp {t : ℝ} (ht : 0 ≤ t) :
    0 ≤ t - (⌊t⌋₊ : ℝ) ∧ t - (⌊t⌋₊ : ℝ) ≤ 1 ∧ (⌊t⌋₊ : ℝ) ≤ t := by
  have h1 := Nat.floor_le ht
  have h2 := Nat.lt_floor_add_one t
  refine ⟨by linarith, by linarith, h1⟩

/-- **DDDF (6.99) in log scale** (l. 1622–1638). -/
theorem mulCont_log {a : ℝ → ℝ} {C₁ C₂ : ℝ} (hC₂ : 0 ≤ C₂)
    (h98 : ∀ (n : ℕ) (r : ℝ), 0 ≤ r → r ≤ 1 → |a ((n : ℝ) + r) - a n| ≤ C₁)
    (h76 : ∀ n k : ℕ, 1 ≤ n → 1 ≤ k → |a ((n : ℝ) + k) - a n - a k| ≤ C₂ * √(k : ℝ))
    (t t' : ℝ) (ht : 0 ≤ t) (ht' : 0 ≤ t') :
    |a (t + t') - a t - a t'| ≤ 4 * C₁ + |a 0| + C₂ * √(min t t') := by
  have hC₁ : 0 ≤ C₁ := (abs_nonneg _).trans (h98 0 0 le_rfl zero_le_one)
  -- the dyadic step (6.100)
  have hdy : ∀ n n' : ℕ, |a ((n : ℝ) + n') - a n - a n'| ≤ |a 0| + C₂ * √(min (n : ℝ) n') := by
    intro n n'
    have hs : 0 ≤ C₂ * √(min (n : ℝ) n') := mul_nonneg hC₂ (Real.sqrt_nonneg _)
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp only [Nat.cast_zero, zero_add] at hs ⊢
      have e : a ↑n' - a 0 - a ↑n' = -a 0 := by ring
      rw [e, abs_neg]; linarith
    rcases Nat.eq_zero_or_pos n' with rfl | hn'
    · simp only [Nat.cast_zero, add_zero] at hs ⊢
      have e : a ↑n - a ↑n - a 0 = -a 0 := by ring
      rw [e, abs_neg]; linarith
    rcases le_total n' n with h | h
    · have hm : min (n : ℝ) n' = n' := min_eq_right (by exact_mod_cast h)
      rw [hm]; linarith [h76 n n' hn hn', abs_nonneg (a 0)]
    · have hm : min (n : ℝ) n' = n := min_eq_left (by exact_mod_cast h)
      have := h76 n' n hn' hn
      rw [hm, show (n : ℝ) + n' = n' + n by ring]
      have e : a ((n' : ℝ) + n) - a n - a n' = a ((n' : ℝ) + n) - a n' - a n := by ring
      rw [e]; linarith [abs_nonneg (a 0)]
  obtain ⟨hr0, hr1, hnt⟩ := floor_decomp ht
  obtain ⟨hr0', hr1', hnt'⟩ := floor_decomp ht'
  set n := ⌊t⌋₊
  set n' := ⌊t'⌋₊
  set r := t - n
  set r' := t' - n'
  have ht_eq : t = (n : ℝ) + r := by simp [r]
  have ht_eq' : t' = (n' : ℝ) + r' := by simp [r']
  have e1 : |a t - a n| ≤ C₁ := by rw [ht_eq]; exact h98 n r hr0 hr1
  have e2 : |a t' - a n'| ≤ C₁ := by rw [ht_eq']; exact h98 n' r' hr0' hr1'
  -- (6.101): `|a(t + t') − a(n + n')| ≤ 2 C₁`
  have e3 : |a (t + t') - a ((n : ℝ) + n')| ≤ 2 * C₁ := by
    rcases le_total (r + r') 1 with h | h
    · have hsum : t + t' = (n : ℝ) + n' + (r + r') := by rw [ht_eq, ht_eq']; ring
      rw [hsum]
      have := h98 (n + n') (r + r') (by linarith) h
      push_cast at this; linarith
    · have hsum' : t + t' = (n : ℝ) + n' + 1 + (r + r' - 1) := by rw [ht_eq, ht_eq']; ring
      have h1 := h98 (n + n' + 1) (r + r' - 1) (by linarith) (by linarith)
      have h2 := h98 (n + n') 1 zero_le_one le_rfl
      rw [hsum']
      push_cast at h1 h2
      obtain ⟨l1, u1⟩ := abs_le.1 h1
      obtain ⟨l2, u2⟩ := abs_le.1 h2
      rw [abs_le]; constructor <;> linarith
  have e4 := hdy n n'
  have hmin : √(min (n : ℝ) n') ≤ √(min t t') :=
    Real.sqrt_le_sqrt (min_le_min hnt hnt')
  have e5 : C₂ * √(min (n : ℝ) n') ≤ C₂ * √(min t t') := mul_le_mul_of_nonneg_left hmin hC₂
  have key : a (t + t') - a t - a t' = (a (t + t') - a ((n : ℝ) + n')) +
      (a ((n : ℝ) + n') - a n - a n') - (a t - a n) - (a t' - a n') := by ring
  rw [key]
  obtain ⟨l1, u1⟩ := abs_le.1 e1
  obtain ⟨l2, u2⟩ := abs_le.1 e2
  obtain ⟨l3, u3⟩ := abs_le.1 e3
  obtain ⟨l4, u4⟩ := abs_le.1 e4
  rw [abs_le]; constructor <;> linarith

/-- **DDDF (1.3) in log scale**: from (5.77) `|a(n) + nκ| ≤ C√n` (`n ≥ 1`) and (6.98) we get
`|a(t) + tκ| ≤ (C₁ + |κ| + |C|) √t` for `t ≥ 1`. -/
theorem expo_log {a : ℝ → ℝ} {C₁ C κ : ℝ}
    (h98 : ∀ (n : ℕ) (r : ℝ), 0 ≤ r → r ≤ 1 → |a ((n : ℝ) + r) - a n| ≤ C₁)
    (h77 : ∀ n : ℕ, 1 ≤ n → |a n + n * κ| ≤ C * √(n : ℝ)) (t : ℝ) (ht : 1 ≤ t) :
    |a t + t * κ| ≤ (C₁ + |κ| + |C|) * √t := by
  have hC₁ : 0 ≤ C₁ := (abs_nonneg _).trans (h98 0 0 le_rfl zero_le_one)
  obtain ⟨hr0, hr1, hnt⟩ := floor_decomp (zero_le_one.trans ht)
  set n := ⌊t⌋₊
  have hn1 : 1 ≤ n := Nat.le_floor (by exact_mod_cast ht)
  set r := t - n
  have ht_eq : t = (n : ℝ) + r := by simp [r]
  have e1 : |a t - a n| ≤ C₁ := by rw [ht_eq]; exact h98 n r hr0 hr1
  have e2 := h77 n hn1
  have hs1 : 1 ≤ √t := Real.one_le_sqrt.2 ht
  have hsn : √(n : ℝ) ≤ √t := Real.sqrt_le_sqrt hnt
  have e3 : C * √(n : ℝ) ≤ |C| * √t :=
    (mul_le_mul_of_nonneg_right (le_abs_self C) (Real.sqrt_nonneg _)).trans
      (mul_le_mul_of_nonneg_left hsn (abs_nonneg C))
  have e4 : |r * κ| ≤ |κ| := by
    rw [abs_mul, abs_of_nonneg hr0]
    exact mul_le_of_le_one_left (abs_nonneg κ) hr1
  have key : a t + t * κ = (a t - a n) + (a n + n * κ) + r * κ := by rw [ht_eq]; ring
  rw [key]
  obtain ⟨l1, u1⟩ := abs_le.1 e1
  obtain ⟨l2, u2⟩ := abs_le.1 e2
  obtain ⟨l4, u4⟩ := abs_le.1 e4
  have h5 : C₁ + |κ| ≤ (C₁ + |κ|) * √t := le_mul_of_one_le_right (by positivity) hs1
  have h6 : (C₁ + |κ| + |C|) * √t = (C₁ + |κ|) * √t + |C| * √t := by ring
  rw [abs_le]; constructor <;> linarith

/-- the exponent identification (DDDF l. 1276–1281): if for every `ζ > 0`, for `K` large,
`K(u − ζ) ≤ K v + C √K`, then `u ≤ v`. -/
theorem le_of_asymp {u v C : ℝ}
    (h : ∀ ζ : ℝ, 0 < ζ → ∃ K₀ : ℕ, ∀ K : ℕ, K₀ ≤ K →
      (K : ℝ) * (u - ζ) ≤ K * v + C * √(K : ℝ)) : u ≤ v := by
  by_contra huv
  push Not at huv
  set ζ := (u - v) / 2 with hζ
  have hζ0 : 0 < ζ := by rw [hζ]; linarith
  obtain ⟨K₀, hK₀⟩ := h ζ hζ0
  set K : ℕ := max K₀ (⌈(|C| / ζ) ^ 2⌉₊ + 1)
  have hK := hK₀ K (le_max_left _ _)
  have hK1 : (⌈(|C| / ζ) ^ 2⌉₊ + 1 : ℝ) ≤ K := by exact_mod_cast le_max_right _ _
  have hKbig : (|C| / ζ) ^ 2 < K := by
    have := Nat.le_ceil ((|C| / ζ) ^ 2); linarith
  have hsq : |C| / ζ < √(K : ℝ) := (Real.lt_sqrt (by positivity)).2 hKbig
  have hKpos : (0 : ℝ) < K := lt_of_le_of_lt (by positivity) hKbig
  have hs0 : 0 < √(K : ℝ) := Real.sqrt_pos.2 hKpos
  have hss : √(K : ℝ) * √(K : ℝ) = K := Real.mul_self_sqrt hKpos.le
  -- `K ζ = √K √K ζ > √K |C| ≥ C √K`
  have h1 : |C| < √(K : ℝ) * ζ := by rwa [div_lt_iff₀ hζ0] at hsq
  have h2 : C * √(K : ℝ) < K * ζ := by
    calc C * √(K : ℝ) ≤ |C| * √(K : ℝ) := mul_le_mul_of_nonneg_right (le_abs_self C) hs0.le
      _ < (√(K : ℝ) * ζ) * √(K : ℝ) := mul_lt_mul_of_pos_right h1 hs0
      _ = (√(K : ℝ) * √(K : ℝ)) * ζ := by ring
      _ = K * ζ := by rw [hss]
  have h3 : (K : ℝ) * (u - ζ) = K * v + K * ζ := by rw [hζ]; ring
  linarith

end S6
end DDDF
end LQGMetric
