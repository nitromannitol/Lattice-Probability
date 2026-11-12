/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Dimension.GMCIdent4Final at commit fdb5cad; only the module paths of local imports are changed.
   Changed for Lean v4.35: the measurability argument of tendsto_integral_of_L1' (dropped from its signature) removed. -/
import LatticeProb.Bonanno.LQGMetric.Dimension.GMCIdent4Ver
import LatticeProb.Bonanno.LQGMetric.Dimension.GMCIdentFinal

/-!
# Identification for the white-noise field, part 3: the main theorem (P2-GMCID4, D85)

**`ae_tendsto_wnGMC_wnField`**: for the white-noise field `wnField W` (the circles inside `𝕍` carry
`√π W(K_σ)`) and `f ∈ C_c(𝕍)`, `0 < γ < 2`, almost surely

  `∫ f(z) CR(z)^{γ²/2} e^{γ h̃_{2^{-n}}(z) − γ²/2 Var h̃_{2^{-n}}(z)} dz → ∫ f dM_γ`,

`M_γ = qAreaMeasureOn γ (wnField W ω) 𝕍`. This is `GMCIdent.ae_tendsto_wnGMC` without its
hypotheses `hX` (for the coupled field), `hC`, `hXm`: a zero-boundary GFF `X` on an arbitrary
probability space enters only through deterministic facts and the law of its circle family
(handoff/P2-GMCID3.md). Proof: DZZ l. 648–658 by Berestycki's argument (arXiv:1506.09113, §4,
l. 680–700), as in `GMCIdentFinal`; the Lévy step uses the `𝓖_∞`-measurable version
`wnFieldVer` (`GMCIdent4Ver`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology Metric QuantumZipper
open scoped ENNReal NNReal

namespace LQGMetric
namespace GMCIdent4

open KilledHeat WhiteNoise DZZ GMCIdent GMCIdent2 GMCIdent3

variable {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω'] {P : Measure Ω}
  {P' : Measure Ω'} {X : Ω → Measure ℂ → ℝ} {W : WNSpace → Ω' → ℝ}

/-- copy of `GMCIdent.integrable_wnDens` (`hX` on another space, only for the bound on `hS`) -/
lemma integrable_wnDens_wn (hX : IsZeroBoundaryGFFOn openSquare X P) (hW : IsWhiteNoise P' W)
    (γ : ℝ) (n : ℕ) {s : ℝ} (hs : 0 < s) :
    Integrable (fun p : Ω' × ℂ => wnWeight γ n p.2 * Real.exp (γ * tildeVer W n p.2 p.1))
      (P'.prod (volume.restrict (sqIn s))) := by
  have hP := hW.isProbabilityMeasure
  have hSf : volume (sqIn s) < ∞ := (isCompact_sqIn hs).measure_lt_top
  have : IsFiniteMeasure (volume.restrict (sqIn s)) := isFiniteMeasure_restrict.2 hSf.ne
  obtain ⟨c, hc⟩ := exists_hS_diag_le hX hs
  have hm : Measurable fun p : Ω' × ℂ => wnWeight γ n p.2 * Real.exp (γ * tildeVer W n p.2 p.1) :=
    ((measurable_wnWeight hW γ n).comp measurable_snd).mul (Real.measurable_exp.comp
      (((measurable_tildeVer' hW n).comp measurable_swap).const_mul γ))
  rw [integrable_prod_iff' hm.aestronglyMeasurable]
  refine ⟨Eventually.of_forall fun z => ?_, ?_⟩
  · refine ((integrable_exp_tildeHInf hW γ n z).const_mul (wnWeight γ n z)).congr ?_
    filter_upwards [tildeVer_ae_eq hW n z] with ω h
    rw [h]
  · refine Integrable.of_bound (C := Real.exp (γ ^ 2 / 2 * c))
      (hm.aestronglyMeasurable.norm.prod_swap.integral_prod_right') ?_
    filter_upwards [ae_restrict_mem (isClosed_sqIn s).measurableSet] with z hz
    have e : ∫ ω, ‖wnWeight γ n z * Real.exp (γ * tildeVer W n z ω)‖ ∂P' =
        Real.exp (γ ^ 2 / 2 * hS z z) := by
      rw [← wnWeight_mul_integral hW γ n z, ← integral_const_mul]
      refine integral_congr_ae (Eventually.of_forall fun ω => ?_)
      simp only [Real.norm_eq_abs]
      exact abs_of_nonneg (mul_nonneg (Real.exp_pos _).le (Real.exp_pos _).le)
    simp only [Real.norm_eq_abs] at e ⊢
    rw [e, abs_of_nonneg (Real.exp_pos _).le]
    exact Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left (hc z hz) (by positivity))

lemma integrable_fwnDens_wn (hX : IsZeroBoundaryGFFOn openSquare X P) (hW : IsWhiteNoise P' W)
    (γ : ℝ) (n : ℕ) {f : ℂ → ℝ} (hf : Measurable f) {M : ℝ} (hM : ∀ z, |f z| ≤ M) {s : ℝ}
    (hs : 0 < s) {μ : Measure Ω'} (hμ : μ ≤ P') :
    Integrable (fun p : Ω' × ℂ => f p.2 * (wnWeight γ n p.2 * Real.exp (γ * tildeVer W n p.2 p.1)))
      (μ.prod (volume.restrict (sqIn s))) := by
  have hG := (integrable_wnDens_wn hX hW γ n hs).mono_measure (Measure.prod_mono hμ le_rfl)
  refine Integrable.mono' (hG.norm.const_mul M) ?_ (Eventually.of_forall fun p => ?_)
  · exact ((hf.comp measurable_snd).aestronglyMeasurable).mul hG.aestronglyMeasurable
  · rw [norm_mul]
    exact mul_le_mul_of_nonneg_right (by rw [Real.norm_eq_abs]; exact hM _) (norm_nonneg _)

/-- copy of `GMCIdent.integrable_wnGMC` -/
lemma integrable_wnGMC_wn (hX : IsZeroBoundaryGFFOn openSquare X P) (hW : IsWhiteNoise P' W)
    (γ : ℝ) (n : ℕ) {f : ℂ → ℝ} (hf : Measurable f) {M : ℝ} (hM : ∀ z, |f z| ≤ M) {s : ℝ}
    (hs : 0 < s) (hfS : ∀ z ∉ sqIn s, f z = 0) : Integrable (wnGMC W γ n f) P' := by
  have hP := hW.isProbabilityMeasure
  have hSf : volume (sqIn s) < ∞ := (isCompact_sqIn hs).measure_lt_top
  have : IsFiniteMeasure (volume.restrict (sqIn s)) := isFiniteMeasure_restrict.2 hSf.ne
  rw [show wnGMC W γ n f = fun ω =>
      ∫ z in sqIn s, f z * (wnWeight γ n z * Real.exp (γ * tildeVer W n z ω)) from
    funext (wnGMC_eq_setIntegral γ n hfS)]
  exact (integrable_fwnDens_wn hX hW γ n hf hM hs le_rfl).integral_prod_left

/-- copy of `GMCIdent.setIntegral_wnGMC` -/
lemma setIntegral_wnGMC_wn (hX : IsZeroBoundaryGFFOn openSquare X P) (hW : IsWhiteNoise P' W)
    (γ : ℝ) (n : ℕ) {f : ℂ → ℝ} (hf : Measurable f) {M : ℝ} (hM : ∀ z, |f z| ≤ M) {s : ℝ}
    (hs : 0 < s) (hfS : ∀ z ∉ sqIn s, f z = 0) {B : Set Ω'} (hB : MeasurableSet B) :
    ∫ ω in B, wnGMC W γ n f ω ∂P' = ∫ z in sqIn s, f z * limDens W P' γ n B z := by
  have hP := hW.isProbabilityMeasure
  have hSf : volume (sqIn s) < ∞ := (isCompact_sqIn hs).measure_lt_top
  have : IsFiniteMeasure (volume.restrict (sqIn s)) := isFiniteMeasure_restrict.2 hSf.ne
  simp_rw [wnGMC_eq_setIntegral (W := W) γ n hfS]
  rw [integral_integral_swap (f := fun ω z =>
    f z * (wnWeight γ n z * Real.exp (γ * tildeVer W n z ω)))
    (integrable_fwnDens_wn hX hW γ n hf hM hs Measure.restrict_le_self)]
  refine integral_congr_ae (Eventually.of_forall fun z => ?_)
  simp only
  rw [integral_const_mul, integral_const_mul, limDens, wnWeight]
  congr 2
  refine setIntegral_congr_ae hB ?_
  filter_upwards [tildeVer_ae_eq hW n z] with ω hω _
  rw [hω]; rfl

/-- **Main theorem for the white-noise field (DZZ l. 648–658).** The circle-average LQG measure
of the white-noise field is the a.s. limit of DZZ's white-noise approximations. -/
theorem ae_tendsto_wnGMC_wnField [IsProbabilityMeasure P] (hX : IsZeroBoundaryGFFOn openSquare X P)
    (hW : IsWhiteNoise P' W) {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) {f : ℂ → ℝ} (hf : Continuous f)
    (hfc : HasCompactSupport f) (hfU : tsupport f ⊆ openSquare) :
    ∀ᵐ ω ∂P', Tendsto (fun n => GMCIdent.wnGMC W γ n f ω) atTop
      (𝓝 (∫ z, f z ∂(qAreaMeasureOn γ (wnField W ω) openSquare))) := by
  have hP := hW.isProbabilityMeasure
  obtain ⟨s, hs, hTs⟩ := exists_sqIn_of_isCompact hfc hfU
  obtain ⟨M, hM⟩ := hf.bounded_above_of_compact_support hfc
  have hM' : ∀ z, |f z| ≤ M := fun z => by simpa [Real.norm_eq_abs] using hM z
  have hfS : ∀ z ∉ sqIn s, f z = 0 := fun z hz =>
    image_eq_zero_of_notMem_tsupport fun h => hz (hTs h)
  obtain ⟨k₀, hint, hYl, hL1⟩ := tendsto_eLpNorm_areaApprox_sub_wn hX hW hγ hγ2 hf hfc hfU
  set Y : ℕ → Ω' → ℝ := fun k ω => ∫ z, f z ∂(areaApprox γ (wnField W ω) k)
  set Yl : Ω' → ℝ := fun ω => ∫ z, f z ∂(qAreaMeasureOn γ (wnField W ω) openSquare)
  set ℱ := wnFil hW
  -- `Z_n = E[Yl | 𝓖_n]`
  have hZ : ∀ n, wnGMC W γ n f =ᵐ[P'] P'[Yl | ℱ n] := by
    intro n
    refine ae_eq_condExp_of_forall_setIntegral_eq (wnSigma_le hW _) hYl
      (fun B _ _ => (integrable_wnGMC_wn hX hW γ n hf.measurable hM' hs hfS).integrableOn)
      (fun B hB _ => ?_) (stronglyMeasurable_wnGMC hW γ n hf.measurable).aestronglyMeasurable
    have hB' : MeasurableSet B := wnSigma_le hW _ B hB
    rw [setIntegral_wnGMC_wn hX hW γ n hf.measurable hM' hs hfS hB']
    have T1 := tendsto_setIntegral_areaApprox_wn hX hW γ n hf.measurable hM' hs hfS hB
    have hshift : Tendsto (fun k : ℕ => k₀ + k) atTop atTop :=
      tendsto_atTop_mono (fun k => Nat.le_add_left k k₀) tendsto_id
    have T2 : Tendsto (fun k => ∫ ω in B, Y (k₀ + k) ω ∂P') atTop (𝓝 (∫ ω in B, Yl ω ∂P')) := by
      refine tendsto_integral_of_L1' _
        (Eventually.of_forall fun k => (hint (k₀ + k) (by omega)).restrict) ?_
      exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hL1 (fun _ => zero_le)
        fun k => eLpNorm_mono_measure _ Measure.restrict_le_self
    exact (tendsto_nhds_unique T2 (T1.comp hshift)).symm
  -- `Yl` is `𝓖_∞`-measurable up to a null set, through the version `wnFieldVer`
  have hYm : ∀ k, StronglyMeasurable[⨆ n, ℱ n]
      fun ω => ∫ z, f z ∂(areaApprox γ (wnFieldVer hW ω) k) := fun k =>
    stronglyMeasurable_areaApprox_sup hW (measurable_wnFieldVer hW) γ k hf.measurable hs hfS
  set g : Ω' → ℝ := fun ω => limUnder atTop fun k =>
    ∫ z, f z ∂(areaApprox γ (wnFieldVer hW ω) k)
  have hg : StronglyMeasurable[⨆ n, ℱ n] g := by
    let _ : MeasurableSpace Ω' := ⨆ n, ℱ n
    exact StronglyMeasurable.limUnder hYm
  have hYg : Yl =ᵐ[P'] g := by
    filter_upwards [ae_isVagueLimitOn_wn hX hW hγ hγ2, ae_areaApprox_wnFieldVer hW] with ω h h'
    simp only [g, h']
    exact ((h.2.2 f hf hfc hfU).limUnder_eq).symm
  have hgi : Integrable g P' := hYl.congr hYg
  have hc : ∀ n, P'[Yl | ℱ n] =ᵐ[P'] P'[g | ℱ n] := fun n => condExp_congr_ae hYg
  filter_upwards [ae_all_iff.2 hZ, ae_all_iff.2 hc, hgi.tendsto_ae_condExp hg, hYg] with
    ω h1 h3 h2 h4
  show Tendsto (fun n => wnGMC W γ n f ω) atTop (𝓝 (Yl ω))
  rw [h4]
  exact h2.congr fun n => ((h1 n).trans (h3 n)).symm

end GMCIdent4
end LQGMetric
