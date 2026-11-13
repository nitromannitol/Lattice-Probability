/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module HigherDimLFPP.Exist.Exponent at commit fdb5cad; only the module paths of local imports are changed.
   Declarations, examples and checks that the copied results do not use are omitted. -/
import LatticeProb.Bonanno.HigherDimLFPP.Exist.Prop31

/-!
# Existence of the fixed-parameter LFPP exponent (packet P-X8, target T3)

Source: `source/higher-dimensional-lfpp-limit.pdf`, (1.3) and Appendix A.1 ¶2–3; DGZ
arXiv:2310.03996, Proposition 1.1 (existence part); planning audit HA5, Details D11 (from medians to
(1.3) for all cutoffs), D2 (concentration), D3 (quantiles), D4 (band bound), and (c) `ExponentExists`.

**Statement** (`exponent_exists`). For every `d ≥ 2`, admissible kernel `κ` and `ζ > 0` there is
`lam ∈ ℝ` (namely `-χ/log 2` with `χ = lim (log λ_n)/n` of DGZ Proposition 3.1, `prop31`; it does
not depend on the realization) such that for every probability space, white noise `W` and
continuous versions `H ε` of `H_{ε,1}` (`ε ∈ (0,1)`), `IsLFPPExponent H P ζ lam`:
`log D^ζ(H ε)/log ε → lam` in probability as `ε ↓ 0` through all real `ε`.
`theorem11_exponent_exists` is the existence conjunct of the frozen `theorem11`
(`∃ ζ₀ > 0, ∀ ζ ∈ (0, ζ₀), ∃ lam, IsLFPPExponent H P ζ lam`, with `ζ₀ = 1`).

**Proof** (HA5 D11). Fix `δ > 0`. For `ε ∈ [2^{-(N+1)}, 2^{-N}]` (`N ≥ 1`) write `X = log D(H ε)`,
`Y = log D(H 2^{-N})`, `ℓ_N = log λ_N`. Then
`|X - ℓ_N| ≤ |X - Y| + |Y - E Y| + |E Y - ℓ_N|`, where
* `|X - Y| ≤ ζ (C √(N+1) + u)` outside an event of probability `≤ 2 e^{-u²/(2 log 2)}` (the band
  estimate of App. A.1, `exists_cutoff_diff_sup_tail`, and the weight comparison
  `abs_log_lfppDistance_sub_le`);
* `|Y - E Y| < t` outside an event of probability `≤ 2 e^{-t²/(2 ζ² N log 2)}` (DGZ Lemma 2.7,
  `IsBandVersion.measure_abs_log_lfppDistance_sub_ge_le`);
* `|E Y - ℓ_N| ≤ c ζ √(N log 2)` (HA5 D3, `IsBandVersion.abs_log_lowerQuantile_lfppDistance_sub_le`).
With `u = δ N log 2/(8ζ)`, `t = δ N log 2/8` the bad events have total probability
`≤ 4 e^{-c' N}` and, for `N` large, `|X - ℓ_N| < (δ/2) N log 2 ≤ (δ/2)|log ε|`. Deterministically
(`Expo.abs_div_log_sub_le`), `|ℓ_N/log ε + χ/log 2| ≤ (|ℓ_N/N - χ| + |χ|/N)/log 2 ≤ δ/2` for `N`
large, because `log ε ∈ [-(N+1) log 2, -N log 2]` and `ℓ_N/N → χ` (`prop31`). Hence
`P(|X/log ε - lam| ≥ δ) ≤ 4 e^{-c' N} → 0` as `ε ↓ 0`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped ENNReal

namespace HigherDimLFPP

universe u

namespace Expo

/-- **The deterministic squeeze** (HA5 D11): if `log ε = L ∈ [-(N+1) log 2, -N log 2]` (`N ≥ 1`),
then `|ℓ/L - (-χ/log 2)| ≤ (|ℓ/N - χ| + |χ|/N)/log 2`. -/
theorem abs_div_log_sub_le {ℓ χ L : ℝ} {N : ℕ} (hN : 1 ≤ N)
    (hL1 : -(((N : ℝ) + 1) * Real.log 2) ≤ L) (hL2 : L ≤ -((N : ℝ) * Real.log 2)) :
    |ℓ / L - -χ / Real.log 2| ≤ (|ℓ / N - χ| + |χ| / N) / Real.log 2 := by
  have hlog : 0 < Real.log 2 := Real.log_pos one_lt_two
  have hN' : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hN0 : (0 : ℝ) < N := by linarith
  have hL0 : L < 0 := by
    have : 0 < (N : ℝ) * Real.log 2 := by positivity
    linarith
  set e : ℝ := ℓ / N - χ with he
  have hℓ : ℓ = N * (χ + e) := by
    rw [he]
    field_simp
    ring
  have hLne : L ≠ 0 := hL0.ne
  have key : ℓ / L - -χ / Real.log 2 =
      (N * e * Real.log 2 + χ * (N * Real.log 2 + L)) / (L * Real.log 2) := by
    rw [hℓ]
    field_simp
    ring
  have h1 : |(N : ℝ) * Real.log 2 + L| ≤ Real.log 2 := by
    rw [abs_le]
    constructor <;> linarith
  have h2 : |(N : ℝ) * e * Real.log 2 + χ * (N * Real.log 2 + L)| ≤
      Real.log 2 * (N * |e| + |χ|) := by
    calc |(N : ℝ) * e * Real.log 2 + χ * (N * Real.log 2 + L)|
        ≤ |(N : ℝ) * e * Real.log 2| + |χ * (N * Real.log 2 + L)| := abs_add_le _ _
      _ = N * |e| * Real.log 2 + |χ| * |(N : ℝ) * Real.log 2 + L| := by
          rw [abs_mul, abs_mul, abs_mul, abs_of_pos hN0, abs_of_pos hlog]
      _ ≤ N * |e| * Real.log 2 + |χ| * Real.log 2 := by gcongr
      _ = Real.log 2 * (N * |e| + |χ|) := by ring
  have h3 : (N : ℝ) * Real.log 2 * Real.log 2 ≤ |L * Real.log 2| := by
    rw [abs_mul, abs_of_neg hL0, abs_of_pos hlog]
    exact mul_le_mul_of_nonneg_right (by linarith) hlog.le
  rw [key, abs_div]
  calc |(N : ℝ) * e * Real.log 2 + χ * (N * Real.log 2 + L)| / |L * Real.log 2|
      ≤ Real.log 2 * (N * |e| + |χ|) / (N * Real.log 2 * Real.log 2) :=
        div_le_div₀ (by positivity) h2 (by positivity) h3
    _ = (|e| + |χ| / N) / Real.log 2 := by
        field_simp

end Expo

open Expo

/-- **Existence of the fixed-parameter LFPP exponent** (1.3) (HA5 D11, `ExponentExists`; target T3
of packet P-X8): for every `d ≥ 2`, admissible kernel `κ` and `ζ > 0` there is `lam ∈ ℝ`, chosen
before the realization, such that for every probability space, white noise `W` and continuous
versions `H ε` of `H_{ε,1}` (`ε ∈ (0,1)`), `log D^ζ_{ε,d} / log ε → lam` in probability as
`ε ↓ 0` (`IsLFPPExponent`). -/
theorem exponent_exists : ∀ d : ℕ, 2 ≤ d → ∀ κ : Rd d → ℝ, IsLFPPKernel κ → ∀ ζ > 0,
    ∃ lam : ℝ, ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (W : WN d → Ω → ℝ),
      IsWhiteNoise P W → ∀ H : ℝ → Rd d → Ω → ℝ,
        (∀ ε ∈ Ioo (0 : ℝ) 1, IsBandVersion P W κ ε 1 (H ε)) → IsLFPPExponent H P ζ lam := by
  intro d hd κ hκ ζ hζ
  have : NeZero d := ⟨by omega⟩
  have hd0 : 0 < d := by omega
  obtain ⟨χ, hχ⟩ := prop31.{u} hd hκ hζ
  obtain ⟨Cd, hCd0, hCd⟩ := exists_cutoff_diff_sup_tail.{u} hκ
  refine ⟨-χ / Real.log 2, ?_⟩
  intro Ω _ P W hW H hH
  have := hW.isProbabilityMeasure
  have hlog : 0 < Real.log 2 := Real.log_pos one_lt_two
  have h20 : (0 : ℝ≥0∞) < 2⁻¹ := ENNReal.inv_pos.2 ENNReal.ofNat_ne_top
  have h21 : (2⁻¹ : ℝ≥0∞) < 1 := ENNReal.inv_lt_one.2 (by norm_num)
  have hdy1 : ∀ N : ℕ, 1 ≤ N → ((2 : ℝ) ^ N)⁻¹ < 1 := fun N hN =>
    inv_lt_one_of_one_lt₀ (one_lt_pow₀ (by norm_num) (by omega))
  have hHN : ∀ N : ℕ, 1 ≤ N → IsBandVersion P W κ ((2 : ℝ) ^ N)⁻¹ 1 (H ((2 : ℝ) ^ N)⁻¹) :=
    fun N hN => hH _ ⟨dyadic_pos N, hdy1 N hN⟩
  -- the medians `λ_N` along the dyadic cutoffs: `(log λ_N)/N → χ`
  set ℓ : ℕ → ℝ := fun N => Real.log (LQGMetric.lowerQuantile
    (P.map fun ω => lfppDistance d ζ (fun z => H ((2 : ℝ) ^ N)⁻¹ z ω)) 2⁻¹) with hℓ
  have hlim : Tendsto (fun N : ℕ => ℓ N / N) atTop (𝓝 χ) :=
    hχ hW (H := fun N => H ((2 : ℝ) ^ N)⁻¹) hHN
  have hdiff := (hCd hW).2 hH
  set c₁ : ℝ := Conc.quantileConst (2⁻¹ : ℝ≥0∞).toReal with hc₁
  have hc₁0 : 0 ≤ c₁ := Conc.quantileConst_nonneg _
  rw [IsLFPPExponent, tendstoInMeasure_iff_dist]
  intro δ hδ
  rw [ENNReal.tendsto_nhds_zero]
  intro η hη
  obtain ⟨η', hη'0, hη'⟩ : ∃ η' : ℝ, 0 < η' ∧ ENNReal.ofReal η' ≤ η := by
    obtain ⟨r, -, hr1, hr2⟩ := ENNReal.lt_iff_exists_real_btwn.1 hη
    exact ⟨r, ENNReal.ofReal_pos.1 hr1, hr2.le⟩
  set cc : ℝ := δ ^ 2 * Real.log 2 / (128 * ζ ^ 2) with hcc
  have hcc0 : 0 < cc := by positivity
  set K : ℝ := 2 * ζ * Cd + c₁ * ζ * √(Real.log 2) with hK
  have hK0 : 0 ≤ K := by positivity
  -- eventual conditions on the dyadic index
  have hev1 : ∀ᶠ N : ℕ in atTop, 4 * Real.exp (-(cc * N)) ≤ η' := by
    have h1 : Tendsto (fun N : ℕ => cc * (N : ℝ)) atTop atTop :=
      tendsto_natCast_atTop_atTop.const_mul_atTop hcc0
    have h2 := (Real.tendsto_exp_neg_atTop_nhds_zero.comp h1).const_mul 4
    rw [mul_zero] at h2
    exact (h2.eventually (Iic_mem_nhds hη'0)).mono fun N hN => hN
  have hev2 : ∀ᶠ N : ℕ in atTop, |ℓ N / N - χ| < δ * Real.log 2 / 4 :=
    (Metric.tendsto_nhds.1 hlim (δ * Real.log 2 / 4) (by positivity)).mono fun N hN => by
      rwa [Real.dist_eq] at hN
  have hev3 : ∀ᶠ N : ℕ in atTop, |χ| / N ≤ δ * Real.log 2 / 4 :=
    (tendsto_const_div_atTop_nhds_zero_nat |χ|).eventually (Iic_mem_nhds (by positivity))
  have hev4 : ∀ᶠ N : ℕ in atTop, 4 * K / (δ * Real.log 2) ≤ √(N : ℝ) :=
    (Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop).eventually_ge_atTop _
  obtain ⟨N₀, hN₀⟩ := eventually_atTop.1
    ((((eventually_ge_atTop 1).and hev1).and hev2).and (hev3.and hev4))
  -- small `ε`: `ε ∈ (0, 2^{-N₀})`
  filter_upwards [Ioo_mem_nhdsGT (dyadic_pos N₀)] with ε hε
  obtain ⟨hε0, hεN₀⟩ := hε
  have hε1 : ε < 1 := hεN₀.trans_le (inv_le_one_of_one_le₀ (one_le_pow₀ (by norm_num)))
  have hεinv : 1 ≤ ε⁻¹ := (one_le_inv₀ hε0).2 hε1.le
  -- its dyadic index `N`: `2^{-(N+1)} ≤ ε ≤ 2^{-N}`
  obtain ⟨N, hN1, hN2⟩ := exists_nat_pow_near hεinv (by norm_num : (1 : ℝ) < 2)
  have hNN₀ : N₀ ≤ N := by
    have h1 : (2 : ℝ) ^ N₀ < ε⁻¹ :=
      (lt_inv_comm₀ (a := (2 : ℝ) ^ N₀) (b := ε) (by positivity) hε0).2 hεN₀
    have h2 : (2 : ℝ) ^ N₀ < 2 ^ (N + 1) := h1.trans hN2
    have := (pow_lt_pow_iff_right₀ (by norm_num : (1 : ℝ) < 2)).1 h2
    omega
  obtain ⟨⟨⟨hN1', hexp⟩, hℓN⟩, hχN, hsqrtN⟩ := hN₀ N hNN₀
  have hεup : ε ≤ ((2 : ℝ) ^ N)⁻¹ := (le_inv_comm₀ hε0 (by positivity)).2 hN1
  have hεlow : ((2 : ℝ) ^ (N + 1))⁻¹ ≤ ε := (inv_le_comm₀ (by positivity) hε0).2 hN2.le
  have hN' : (1 : ℝ) ≤ N := by exact_mod_cast hN1'
  -- `log ε ∈ [-(N+1) log 2, -N log 2]`
  have hL2 : Real.log ε ≤ -((N : ℝ) * Real.log 2) := by
    have := Real.log_le_log hε0 hεup
    rwa [Real.log_inv, Real.log_pow] at this
  have hL1 : -(((N : ℝ) + 1) * Real.log 2) ≤ Real.log ε := by
    have := Real.log_le_log (by positivity) hεlow
    rwa [Real.log_inv, Real.log_pow, Nat.cast_succ] at this
  have hL0 : Real.log ε < 0 := by
    have : 0 < (N : ℝ) * Real.log 2 := by positivity
    linarith
  -- the deterministic part
  have hdet : |ℓ N / Real.log ε - -χ / Real.log 2| ≤ δ / 2 := by
    refine (abs_div_log_sub_le hN1' hL1 hL2).trans ?_
    rw [div_le_iff₀ hlog]
    linarith
  -- the two bad events
  set V : ℝ := Real.log (1 / ((2 : ℝ) ^ N)⁻¹) with hV
  have hVeq : V = N * Real.log 2 := by rw [hV, one_div, inv_inv, Real.log_pow]
  set u : ℝ := δ * (N * Real.log 2) / (8 * ζ) with hu
  set t : ℝ := δ * (N * Real.log 2) / 8 with ht
  have hu0 : 0 ≤ u := by positivity
  have ht0 : 0 ≤ t := by positivity
  have hEa := hdiff N hN1' hεlow hεup hu0
  have hEb := (hHN N hN1').measure_abs_log_lfppDistance_sub_ge_le hκ hW (dyadic_pos N)
    (hdy1 N hN1').le ζ ht0
  have hmℓ := (hHN N hN1').abs_log_lowerQuantile_lfppDistance_sub_le hd0 hκ hW (dyadic_pos N)
    (hdy1 N hN1') hζ h20 h21
  -- the deterministic size of the error terms
  have hsmall : ζ * Cd * √((N : ℝ) + 1) + c₁ * ζ * √V ≤ δ / 4 * (N * Real.log 2) := by
    have hsN : 0 ≤ √(N : ℝ) := Real.sqrt_nonneg _
    have h1 : √((N : ℝ) + 1) ≤ 2 * √(N : ℝ) := by
      rw [Real.sqrt_le_left (by positivity), mul_pow, Real.sq_sqrt (Nat.cast_nonneg _)]
      linarith
    have h2 : √V = √(N : ℝ) * √(Real.log 2) := by
      rw [hVeq, Real.sqrt_mul (Nat.cast_nonneg _)]
    have h3 : ζ * Cd * √((N : ℝ) + 1) + c₁ * ζ * √V ≤ K * √(N : ℝ) := by
      rw [h2]
      have := mul_le_mul_of_nonneg_left h1 (by positivity : 0 ≤ ζ * Cd)
      calc ζ * Cd * √((N : ℝ) + 1) + c₁ * ζ * (√(N : ℝ) * √(Real.log 2))
          ≤ ζ * Cd * (2 * √(N : ℝ)) + c₁ * ζ * (√(N : ℝ) * √(Real.log 2)) := by linarith
        _ = K * √(N : ℝ) := by rw [hK]; ring
    have h4 : K * √(N : ℝ) ≤ δ / 4 * (N * Real.log 2) := by
      have hsq : √(N : ℝ) * √(N : ℝ) = N := Real.mul_self_sqrt (Nat.cast_nonneg _)
      rw [div_le_iff₀ (by positivity)] at hsqrtN
      have h5 := mul_le_mul_of_nonneg_right hsqrtN hsN
      have e : √(N : ℝ) * (δ * Real.log 2) * √(N : ℝ) = δ * Real.log 2 * N := by
        linear_combination (δ * Real.log 2) * hsq
      rw [e] at h5
      linarith
    linarith
  have hsub : {ω | δ ≤ dist (Real.log (lfppDistance d ζ (fun z => H ε z ω)) / Real.log ε)
        (-χ / Real.log 2)} ⊆
      {ω | ∃ z ∈ closure (cube d),
          Cd * √((N : ℝ) + 1) + u < |H ε z ω - H ((2 : ℝ) ^ N)⁻¹ z ω|} ∪
        {ω | t ≤ |Real.log (lfppDistance d ζ (fun z => H ((2 : ℝ) ^ N)⁻¹ z ω)) -
          ∫ ω', Real.log (lfppDistance d ζ (fun z => H ((2 : ℝ) ^ N)⁻¹ z ω')) ∂P|} := by
    intro ω hω
    by_contra hnot
    rw [mem_union, not_or] at hnot
    obtain ⟨hna, hnb⟩ := hnot
    have hna' : ∀ z ∈ closure (cube d),
        |H ε z ω - H ((2 : ℝ) ^ N)⁻¹ z ω| ≤ Cd * √((N : ℝ) + 1) + u := fun z hz =>
      le_of_not_gt fun hlt => hna ⟨z, hz, hlt⟩
    have hnb' : |Real.log (lfppDistance d ζ (fun z => H ((2 : ℝ) ^ N)⁻¹ z ω)) -
        ∫ ω', Real.log (lfppDistance d ζ (fun z => H ((2 : ℝ) ^ N)⁻¹ z ω')) ∂P| < t :=
      lt_of_not_ge hnb
    set X : ℝ := Real.log (lfppDistance d ζ (fun z => H ε z ω)) with hX
    set Y : ℝ := Real.log (lfppDistance d ζ (fun z => H ((2 : ℝ) ^ N)⁻¹ z ω)) with hY
    set mY : ℝ := ∫ ω', Real.log (lfppDistance d ζ (fun z => H ((2 : ℝ) ^ N)⁻¹ z ω')) ∂P
      with hmY
    have hXY : |X - Y| ≤ ζ * (Cd * √((N : ℝ) + 1) + u) := by
      have h := abs_log_lfppDistance_sub_le (ζ := ζ) ((hH ε ⟨hε0, hε1⟩).continuous ω)
        ((hHN N hN1').continuous ω) (M := Cd * √((N : ℝ) + 1) + u)
        (fun z hz => hna' z (subset_closure hz))
      rwa [abs_of_pos hζ] at h
    have hmℓ' : |mY - ℓ N| ≤ c₁ * ζ * √V := by
      rw [abs_sub_comm]
      exact hmℓ
    have hζu : ζ * u = δ * (N * Real.log 2) / 8 := by
      rw [hu]
      field_simp
    have htri : |X - ℓ N| ≤ |X - Y| + |Y - mY| + |mY - ℓ N| := by
      calc |X - ℓ N| = |(X - Y) + (Y - mY) + (mY - ℓ N)| := by ring_nf
        _ ≤ |(X - Y) + (Y - mY)| + |mY - ℓ N| := abs_add_le _ _
        _ ≤ |X - Y| + |Y - mY| + |mY - ℓ N| := by gcongr; exact abs_add_le _ _
    have hXℓ : |X - ℓ N| < δ / 2 * (N * Real.log 2) := by
      have e1 : ζ * (Cd * √((N : ℝ) + 1) + u) = ζ * Cd * √((N : ℝ) + 1) + ζ * u := by ring
      rw [e1, hζu] at hXY
      rw [ht] at hnb'
      linarith
    have hLabs : (N : ℝ) * Real.log 2 ≤ |Real.log ε| := by
      rw [abs_of_neg hL0]
      linarith
    have hfirst : |X - ℓ N| / |Real.log ε| < δ / 2 := by
      rw [div_lt_iff₀ (abs_pos.2 hL0.ne)]
      have := mul_le_mul_of_nonneg_left hLabs (by positivity : 0 ≤ δ / 2)
      linarith
    have hsplit : X / Real.log ε - -χ / Real.log 2 =
        (X - ℓ N) / Real.log ε + (ℓ N / Real.log ε - -χ / Real.log 2) := by
      have : Real.log ε ≠ 0 := hL0.ne
      field_simp
      ring
    have hlt : dist (X / Real.log ε) (-χ / Real.log 2) < δ := by
      rw [Real.dist_eq, hsplit]
      calc |(X - ℓ N) / Real.log ε + (ℓ N / Real.log ε - -χ / Real.log 2)|
          ≤ |(X - ℓ N) / Real.log ε| + |ℓ N / Real.log ε - -χ / Real.log 2| := abs_add_le _ _
        _ = |X - ℓ N| / |Real.log ε| + |ℓ N / Real.log ε - -χ / Real.log 2| := by
            rw [abs_div]
        _ < δ / 2 + δ / 2 := add_lt_add_of_lt_of_le hfirst hdet
        _ = δ := by ring
    exact (not_le.2 hlt) hω
  calc P {ω | δ ≤ dist (Real.log (lfppDistance d ζ (fun z => H ε z ω)) / Real.log ε)
        (-χ / Real.log 2)}
      ≤ P ({ω | ∃ z ∈ closure (cube d),
          Cd * √((N : ℝ) + 1) + u < |H ε z ω - H ((2 : ℝ) ^ N)⁻¹ z ω|} ∪
        {ω | t ≤ |Real.log (lfppDistance d ζ (fun z => H ((2 : ℝ) ^ N)⁻¹ z ω)) -
          ∫ ω', Real.log (lfppDistance d ζ (fun z => H ((2 : ℝ) ^ N)⁻¹ z ω')) ∂P|}) :=
        measure_mono hsub
    _ ≤ ENNReal.ofReal (2 * Real.exp (-u ^ 2 / (2 * Real.log 2))) +
          ENNReal.ofReal (2 * Real.exp (-t ^ 2 / (2 * ζ ^ 2 * V))) :=
        (measure_union_le _ _).trans (add_le_add hEa hEb)
    _ = ENNReal.ofReal (2 * Real.exp (-u ^ 2 / (2 * Real.log 2)) +
          2 * Real.exp (-t ^ 2 / (2 * ζ ^ 2 * V))) :=
        (ENNReal.ofReal_add (by positivity) (by positivity)).symm
    _ ≤ ENNReal.ofReal η' := by
        refine ENNReal.ofReal_le_ofReal ?_
        have hN0 : (N : ℝ) ≠ 0 := by linarith
        have e1 : -u ^ 2 / (2 * Real.log 2) = -(cc * (N : ℝ) ^ 2) := by
          rw [hu, hcc]
          field_simp
          ring
        have e2 : -t ^ 2 / (2 * ζ ^ 2 * V) = -(cc * N) := by
          rw [ht, hcc, hVeq]
          field_simp
          ring
        rw [e1, e2]
        have hNN : (N : ℝ) ≤ (N : ℝ) ^ 2 := le_self_pow₀ hN' two_ne_zero
        have h3 : Real.exp (-(cc * (N : ℝ) ^ 2)) ≤ Real.exp (-(cc * N)) := by
          rw [Real.exp_le_exp, neg_le_neg_iff]
          exact mul_le_mul_of_nonneg_left hNN hcc0.le
        linarith
    _ ≤ η := hη'

end HigherDimLFPP
