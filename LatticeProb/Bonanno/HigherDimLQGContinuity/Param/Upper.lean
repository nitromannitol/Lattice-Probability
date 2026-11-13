/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module HigherDimLQGContinuity.Param.Upper at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.HigherDimLQGContinuity.Param.Lipschitz
import LatticeProb.Bonanno.HigherDimLFPP.Frozen.BandVecNormSq

/-!
# The Markov upper bound `ϕ(ξ) ≤ 1 + ξ²/2` (packet PAR)

Blueprint Part A §1, `a:lem-phi-upper` (BWA; replaces NA0 A1a for the finiteness of `ξ_c`). For `d ≥ 2`
and `ξ > 0`: `ϕ(ξ) = ξ Q(ξ) ≤ 1 + ξ²/2`.

Proof: the straight segment `σ(t) = t e₁` is admissible, so `L(ξ, H_ε) ≤ ∫₀¹ e^{ξ H_ε(t e₁)} dt`. By Tonelli
and the Gaussian law of `H_ε(z)` (variance `log ε⁻¹`, `bandVec_norm_sq`),
`E ∫₀¹ e^{ξ H_ε(t e₁)} dt = ε^{-ξ²/2}`. Markov then gives, for `A < -ξ²/2`,
`P{log L(ξ, H_ε) / log ε ≤ A} ≤ e^{(ξ²/2 + A) log ε⁻¹} → 0`, and the lower-tail form of the constant-limit
lemma gives `1 - ϕ(ξ) ≥ -ξ²/2`. All integrals are lower Lebesgue integrals of the measurable upper bound
(the LFPP distance itself is not claimed measurable).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal

namespace HigherDimLQGContinuity

open HigherDimLQGMetric
open HigherDimLFPP (Rd WN e₁ IsLFPPKernel IsWhiteNoise IsBandVersion IsLFPPExponent lfppDistance
  segPath)

/-- The exponential moment of the band field: for `ε ∈ (0, 1)`,
`E e^{ξ H_ε(z)} = e^{ξ² log ε⁻¹ / 2}` (as a lower integral). -/
theorem lintegral_exp_bandVersion {d : ℕ} (hd : 1 ≤ d) {κ : Rd d → ℝ} (hκ : IsLFPPKernel κ)
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} {W : WN d → Ω → ℝ} (hW : IsWhiteNoise P W)
    {ε : ℝ} (hε : ε ∈ Ioo (0 : ℝ) 1) {H : Rd d → Ω → ℝ} (hH : IsBandVersion P W κ ε 1 H)
    (ξ : ℝ) (z : Rd d) :
    ∫⁻ ω, ENNReal.ofReal (Real.exp (ξ * H z ω)) ∂P =
      ENNReal.ofReal (Real.exp (ξ ^ 2 * Real.log ε⁻¹ / 2)) := by
  have := hW.isProbabilityMeasure
  set f : WN d := HigherDimLFPP.bandVec κ ε 1 z with hfdef
  have hlaw := hW.hasLaw_single f
  have hnorm : ‖f‖ ^ 2 = Real.log ε⁻¹ := by
    rw [(HigherDimLFPP.bandVec_norm_sq d hd κ hκ ε 1 hε.1 hε.2 z).2, one_div]
  have hae : (fun ω => ENNReal.ofReal (Real.exp (ξ * H z ω))) =ᵐ[P]
      fun ω => ENNReal.ofReal (Real.exp (ξ * W f ω)) :=
    (hH.ae_eq z).mono fun ω hω => by simp only [hω, hfdef]
  rw [lintegral_congr_ae hae]
  have hint : Integrable (fun ω => Real.exp (ξ * W f ω)) P := by
    rw [← mgf_pos_iff, mgf_gaussianReal hlaw]
    exact Real.exp_pos _
  rw [← ofReal_integral_eq_lintegral_ofReal hint
    (Eventually.of_forall fun _ => (Real.exp_pos _).le)]
  have hm := mgf_gaussianReal hlaw ξ
  rw [mgf] at hm
  rw [hm, Real.coe_toNNReal _ (sq_nonneg _), hnorm]
  ring_nf

/-- **Segment bound**: `L(ξ, φ) ≤ ∫₀¹ e^{ξ φ(t e₁)} dt` (as a lower integral over `(0, 1]`). -/
theorem ofReal_lfppDistance_le_lintegral_segPath {d : ℕ} (hd : 0 < d) {φ : Rd d → ℝ}
    (hφ : Continuous φ) (ξ : ℝ) :
    ENNReal.ofReal (lfppDistance d ξ φ) ≤
      ∫⁻ u in Ioc (0 : ℝ) 1, ENNReal.ofReal (Real.exp (ξ * φ (segPath 0 (e₁ d) u))) := by
  have hseg := HigherDimLFPP.mapsTo_segPath (HigherDimLFPP.convex_cube d)
    (HigherDimLFPP.zero_mem_cube d) (HigherDimLFPP.e₁_mem_cube d)
  have hle : lfppDistance d ξ φ ≤ ∫ u in (0 : ℝ)..1, Real.exp (ξ * φ (segPath 0 (e₁ d) u)) := by
    rw [HigherDimLFPP.lfppDistance_eq_lfppDistOn]
    refine (HigherDimLFPP.lfppDistOn_le_lfppLength
      (HigherDimLFPP.isPcwC1Path_segPath 0 (e₁ d)) hseg).trans_eq ?_
    rw [HigherDimLFPP.lfppLength_segPath, sub_zero, HigherDimLFPP.norm_e₁ hd, mul_one]
  have hc : Continuous fun u => Real.exp (ξ * φ (segPath 0 (e₁ d) u)) :=
    Real.continuous_exp.comp (continuous_const.mul (hφ.comp (HigherDimLFPP.continuous_segPath _ _)))
  rw [intervalIntegral.integral_of_le zero_le_one] at hle
  refine (ENNReal.ofReal_le_ofReal hle).trans_eq ?_
  exact ofReal_integral_eq_lintegral_ofReal (hc.integrableOn_Icc.mono_set Ioc_subset_Icc_self)
    (Eventually.of_forall fun _ => (Real.exp_pos _).le)

/-- Joint measurability of `(u, ω) ↦ e^{ξ H(u e₁, ω)}` for a field continuous in space and measurable in
`ω`. -/
theorem measurable_exp_segPath {d : ℕ} {Ω : Type} [MeasurableSpace Ω] {H : Rd d → Ω → ℝ}
    (hc : ∀ ω, Continuous fun z => H z ω) (hm : ∀ z, Measurable (H z)) (ξ : ℝ) :
    Measurable fun p : ℝ × Ω => ENNReal.ofReal (Real.exp (ξ * H (segPath 0 (e₁ d) p.1) p.2)) := by
  have h : Measurable (Function.uncurry fun (u : ℝ) (ω : Ω) => H (segPath 0 (e₁ d) u) ω) :=
    measurable_uncurry_of_continuous_of_measurable
      (fun ω => (hc ω).comp (HigherDimLFPP.continuous_segPath _ _)) (fun u => hm _)
  exact ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp (measurable_const.mul h))

/-- **The Markov bound** (`a:lem-phi-upper`): `ϕ(ξ) ≤ 1 + ξ²/2` for `d ≥ 2` and `ξ > 0`. -/
theorem phiXi_le_one_add_sq {d : ℕ} (hd : 2 ≤ d) {ξ : ℝ} (hξ : 0 < ξ) :
    phiXi d ξ ≤ 1 + ξ ^ 2 / 2 := by
  obtain ⟨κ, hκ⟩ := HigherDimLFPP.exists_isLFPPKernel d
  obtain ⟨W, hW⟩ := HigherDimLFPP.exists_isWhiteNoise d
  have := hW.isProbabilityMeasure
  obtain ⟨H, hH⟩ := exists_bandVersion_family hκ hW
  have hX := isLFPPExponent_phiXi hd hκ hW hH hξ.le
  suffices key : -(ξ ^ 2 / 2) ≤ 1 - phiXi d ξ by linarith
  refine par_le_limit_of_lower_tails hX fun A hA => ?_
  have hk : 0 < -(ξ ^ 2 / 2 + A) := by linarith
  have hbound : Tendsto (fun ε : ℝ => ENNReal.ofReal
      (Real.exp (-(-(ξ ^ 2 / 2 + A) * Real.log ε⁻¹)))) (𝓝[>] 0) (𝓝 0) := by
    have hh := log_inv_tendsto_atTop.const_mul_atTop hk
    have he := Real.tendsto_exp_neg_atTop_nhds_zero.comp hh
    simpa only [Function.comp_def, ENNReal.ofReal_zero] using ENNReal.tendsto_ofReal he
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hbound
    (Eventually.of_forall fun _ => bot_le) ?_
  filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < 1 by norm_num)] with ε hε
  set ℓ : ℝ := Real.log ε⁻¹ with hℓdef
  have hℓ : 0 < ℓ := Real.log_pos (one_lt_inv_iff₀.2 hε)
  set F : ℝ × (ℕ → ℝ) → ℝ≥0∞ := fun p =>
    ENNReal.ofReal (Real.exp (ξ * H ε (segPath 0 (e₁ d) p.1) p.2)) with hFdef
  have hFm : Measurable F :=
    measurable_exp_segPath (hH ε hε).continuous (hH ε hε).measurable ξ
  set Y : (ℕ → ℝ) → ℝ≥0∞ := fun ω => ∫⁻ u in Ioc (0 : ℝ) 1, F (u, ω) with hYdef
  have hYm : Measurable Y := hFm.lintegral_prod_left'
  have hEY : ∫⁻ ω, Y ω ∂LQGDimension.ExistAsm.stdP =
      ENNReal.ofReal (Real.exp (ξ ^ 2 * ℓ / 2)) := by
    rw [hYdef]
    rw [lintegral_lintegral_swap (f := fun ω u => F (u, ω))
      (hFm.comp measurable_swap).aemeasurable]
    have hinner : ∀ u : ℝ, ∫⁻ ω, F (u, ω) ∂LQGDimension.ExistAsm.stdP =
        ENNReal.ofReal (Real.exp (ξ ^ 2 * ℓ / 2)) := fun u => by
      simpa only [hFdef, hℓdef] using
        lintegral_exp_bandVersion (d := d) (by omega) hκ hW hε (hH ε hε) ξ (segPath 0 (e₁ d) u)
    simp only [hinner, setLIntegral_const, Real.volume_Ioc, sub_zero, ENNReal.ofReal_one, mul_one]
  have hsub : {ω | Real.log (lfppDistance d ξ (fun z => H ε z ω)) / Real.log ε ≤ A} ⊆
      {ω | ENNReal.ofReal (Real.exp (-A * ℓ)) ≤ Y ω} := by
    intro ω hω
    simp only [mem_ofPred_eq] at hω ⊢
    have hL : 0 < lfppDistance d ξ (fun z => H ε z ω) :=
      HigherDimLFPP.lfppDistance_pos (by omega) ((hH ε hε).continuous ω)
    have hlogε : Real.log ε = -ℓ := by rw [hℓdef, Real.log_inv]; ring
    rw [hlogε, div_neg, neg_le] at hω
    have hlog : -A * ℓ ≤ Real.log (lfppDistance d ξ (fun z => H ε z ω)) := by
      have := (le_div_iff₀ hℓ).1 hω
      linarith
    have hexp : Real.exp (-A * ℓ) ≤ lfppDistance d ξ (fun z => H ε z ω) := by
      calc Real.exp (-A * ℓ) ≤ Real.exp (Real.log (lfppDistance d ξ (fun z => H ε z ω))) :=
            Real.exp_le_exp.2 hlog
        _ = lfppDistance d ξ (fun z => H ε z ω) := Real.exp_log hL
    exact (ENNReal.ofReal_le_ofReal hexp).trans
      (ofReal_lfppDistance_le_lintegral_segPath (by omega) ((hH ε hε).continuous ω) ξ)
  calc LQGDimension.ExistAsm.stdP
        {ω | Real.log (lfppDistance d ξ (fun z => H ε z ω)) / Real.log ε ≤ A}
      ≤ LQGDimension.ExistAsm.stdP {ω | ENNReal.ofReal (Real.exp (-A * ℓ)) ≤ Y ω} :=
        measure_mono hsub
    _ ≤ (∫⁻ ω, Y ω ∂LQGDimension.ExistAsm.stdP) / ENNReal.ofReal (Real.exp (-A * ℓ)) :=
        meas_ge_le_lintegral_div hYm.aemeasurable
          (ENNReal.ofReal_pos.2 (Real.exp_pos _)).ne' ENNReal.ofReal_ne_top
    _ = ENNReal.ofReal (Real.exp (ξ ^ 2 * ℓ / 2) / Real.exp (-A * ℓ)) := by
        rw [hEY, ENNReal.ofReal_div_of_pos (Real.exp_pos _)]
    _ = ENNReal.ofReal (Real.exp (-(-(ξ ^ 2 / 2 + A) * ℓ))) := by
        rw [← Real.exp_sub]
        congr 2
        ring

end HigherDimLQGContinuity
