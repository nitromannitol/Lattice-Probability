/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module HigherDimLFPP.Exist.Prop31 at commit fdb5cad; only the module paths of local imports are changed.
   Declarations, examples and checks that the copied results do not use are omitted. -/
import LatticeProb.Bonanno.HigherDimLFPP.Exist.Lemma33
import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.S5Sub

/-!
# DGZ Proposition 3.1: existence of `lim (log λ_n)/n` (packet P-X8, target T2)

Source: DGZ arXiv:2310.03996, Proposition 3.1 and the crude part of Lemma 3.7(1); planning audit
HA5, Details D10 and finding G7 (the crude bounds are proved first, so the limit is finite).

**Statement** (`prop31`). For `d ≥ 2`, an admissible kernel `κ` and `ξ > 0` there is `χ ∈ ℝ` such
that for every white noise and continuous versions `H n` of `h_n = H_{2^{-n},1}` (`n ≥ 1`), the
lower medians `λ_n` of `D_n = D^ξ(h_n)` satisfy `(log λ_n)/n → χ`. `χ` does not depend on the
realization. `dgzProp11` restates it in DGZ's normalization: `λ_n = 2^{-(1-ξQ)n + o(n)}`.

**Proof** (HA5 D10). On a canonical realization (`field_exists_impl`), the crude bounds
(`exists_crude_bounds`) give `e^{-ξAn} ≤ λ_n ≤ e^{ξAn}` for `n ≥ 1`. Put `a_0 = 0` and
`a_n = log λ_n + ξAn ∈ [0, 2ξAn]`. DGZ Lemma 3.3 in median form (`lemma33_median`) gives, for
`k ≥ l ≥ 1`, `a_{k+l} ≤ a_k + a_l + C (k+l)^{2/3} ≤ a_k + a_l + C (k+l) k^{-1/3}`, so Hammersley's
near-subadditive lemma (`LQGMetric.DZZ.tendsto_div_of_near_subadd`, `θ = 1/3`) gives
`a_n/n → χ'`; then `χ = χ' - ξA`. For any other realization the medians are the same numbers
(`IsBandVersion.lowerQuantile_lfppDistance_eq`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped ENNReal

namespace HigherDimLFPP

universe u

namespace L33

/-- `(k+l)^{2/3} ≤ (k+l) k^{-1/3}` for `k > 0`, `l ≥ 0`. -/
theorem rpow_two_thirds_le_mul_rpow_neg {k l : ℝ} (hk : 0 < k) (hl : 0 ≤ l) :
    (k + l) ^ (2 / 3 : ℝ) ≤ (k + l) * k ^ (-(1 / 3 : ℝ)) := by
  have hkl : 0 < k + l := by linarith
  have e : (k + l) ^ (2 / 3 : ℝ) = (k + l) * (k + l) ^ (-(1 / 3 : ℝ)) := by
    rw [show (2 / 3 : ℝ) = 1 + -(1 / 3 : ℝ) by norm_num, Real.rpow_add hkl, Real.rpow_one]
  rw [e]
  exact mul_le_mul_of_nonneg_left
    (Real.rpow_le_rpow_of_nonpos hk (by linarith) (by norm_num)) hkl.le

end L33

open L33

/-- **DGZ Proposition 3.1** (HA5 D10; target T2 of packet P-X8). For `d ≥ 2`, an admissible
kernel `κ` and `ξ > 0` there is `χ ∈ ℝ` such that for every white noise `W` (on any probability
space) and continuous versions `H n` of `h_n = H_{2^{-n},1}`, `n ≥ 1`, the lower medians
`λ_n` of `D^ξ(h_n)` satisfy `(log λ_n)/n → χ`. -/
theorem prop31 {d : ℕ} (hd : 2 ≤ d) {κ : Rd d → ℝ} (hκ : IsLFPPKernel κ) {ξ : ℝ} (hξ : 0 < ξ) :
    ∃ χ : ℝ, ∀ {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} {W : WN d → Ω → ℝ},
      IsWhiteNoise P W → ∀ {H : ℕ → Rd d → Ω → ℝ},
        (∀ n, 1 ≤ n → IsBandVersion P W κ ((2 : ℝ) ^ n)⁻¹ 1 (H n)) →
          Tendsto (fun n : ℕ => Real.log (LQGMetric.lowerQuantile
            (P.map fun ω => lfppDistance d ξ (fun z => H n z ω)) 2⁻¹) / n) atTop (𝓝 χ) := by
  have : NeZero d := ⟨by omega⟩
  have hd0 : 0 < d := by omega
  have h20 : (0 : ℝ≥0∞) < 2⁻¹ := ENNReal.inv_pos.2 ENNReal.ofNat_ne_top
  have h21 : (2⁻¹ : ℝ≥0∞) < 1 := ENNReal.inv_lt_one.2 (by norm_num)
  -- a canonical realization with versions of every `h_n`
  obtain ⟨Ω₀, _, P₀, W₀, -, -, hW₀, -⟩ := (field_exists_impl d (by omega)).2 κ hκ
  choose G hG using fun n : ℕ => exists_isBandVersion hκ hW₀ (dyadic_pos n) 1
  set lam : ℕ → ℝ := fun n =>
    LQGMetric.lowerQuantile (P₀.map fun ω => lfppDistance d ξ (fun z => G n z ω)) 2⁻¹ with hlam
  have hlam0 : ∀ n, 0 < lam n := fun n =>
    (hG n).lowerQuantile_lfppDistance_pos hd0 hW₀ ξ h20 h21
  -- crude bounds
  obtain ⟨A, hA0, hA⟩ := exists_crude_bounds hκ
  have hcrude : ∀ n, 1 ≤ n →
      -(ξ * A * n) ≤ Real.log (lam n) ∧ Real.log (lam n) ≤ ξ * A * n := by
    intro n hn
    obtain ⟨-, h⟩ := hA hW₀ hn (hG n)
    obtain ⟨h1, h2⟩ := h ξ hξ
    exact ⟨(Real.le_log_iff_exp_le (hlam0 n)).2 h1, (Real.log_le_iff_le_exp (hlam0 n)).2 h2⟩
  -- near-subadditivity (DGZ Lemma 3.3, median form)
  obtain ⟨C, hC0, hC⟩ := lemma33_median hd hκ hξ
  have hsub : ∀ k l : ℕ, 1 ≤ k → 1 ≤ l → l ≤ k →
      Real.log (lam (k + l)) ≤ Real.log (lam k) + Real.log (lam l) +
        C * ((k : ℝ) + l) * (k : ℝ) ^ (-(1 / 3 : ℝ)) := by
    intro k l hk hl _
    have hGk : IsBandVersion P₀ W₀ κ ((2 : ℝ) ^ (k + l - l))⁻¹ 1 (G k) :=
      (hG k).congr_band (by rw [Nat.add_sub_cancel]) rfl
    have h := hC hW₀ (n := k + l) (m := l) hl (by omega) (hG (k + l)) (hG l) hGk
    have hlog := Real.log_le_log (hlam0 _) h
    rw [Real.log_mul (mul_pos (Real.exp_pos _) (hlam0 l)).ne' (hlam0 k).ne',
      Real.log_mul (Real.exp_pos _).ne' (hlam0 l).ne', Real.log_exp] at hlog
    have hk' : (0 : ℝ) < k := by exact_mod_cast hk
    have hpow := rpow_two_thirds_le_mul_rpow_neg hk' (Nat.cast_nonneg l)
    have e : ((k + l : ℕ) : ℝ) = (k : ℝ) + l := by push_cast; ring
    rw [e] at hlog
    have := mul_le_mul_of_nonneg_left hpow hC0
    linarith
  -- the shifted sequence
  set a : ℕ → ℝ := fun n => if n = 0 then 0 else Real.log (lam n) + ξ * A * n with ha
  have ha_pos : ∀ n, 1 ≤ n → a n = Real.log (lam n) + ξ * A * n := fun n hn => by
    simp only [ha]
    split_ifs with h
    · omega
    · rfl
  have ha0 : ∀ n, 0 ≤ a n := by
    intro n
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp [ha]
    · rw [ha_pos n hn]
      linarith [(hcrude n hn).1]
  have haM : ∀ n, a n ≤ (2 * ξ * A) * n := by
    intro n
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp [ha]
    · rw [ha_pos n hn]
      linarith [(hcrude n hn).2]
  have hsub' : ∀ k l : ℕ, 1 ≤ k → 1 ≤ l → l ≤ k →
      a (k + l) ≤ a k + a l + C * ((k : ℝ) + l) * (k : ℝ) ^ (-(1 / 3 : ℝ)) := by
    intro k l hk hl hlk
    rw [ha_pos (k + l) (by omega), ha_pos k hk, ha_pos l hl]
    have := hsub k l hk hl hlk
    push_cast
    linarith
  obtain ⟨χ', hχ'⟩ := LQGMetric.DZZ.tendsto_div_of_near_subadd (a := a) (C := C)
    (θ := 1 / 3) (M := 2 * ξ * A) (k₀ := 1) (by norm_num) (by norm_num) hC0 ha0 haM hsub'
  refine ⟨χ' - ξ * A, ?_⟩
  intro Ω _ P W hW H hH
  refine (hχ'.sub_const (ξ * A)).congr' ?_
  filter_upwards [eventually_ge_atTop 1] with n hn
  have hq : LQGMetric.lowerQuantile (P.map fun ω => lfppDistance d ξ (fun z => H n z ω)) 2⁻¹ =
      lam n := (hH n hn).lowerQuantile_lfppDistance_eq (hG n) hW hW₀ ξ 2⁻¹
  have hn' : (n : ℝ) ≠ 0 := by
    have : (1 : ℝ) ≤ n := by exact_mod_cast hn
    linarith
  rw [hq, ha_pos n hn]
  field_simp
  ring

end HigherDimLFPP
