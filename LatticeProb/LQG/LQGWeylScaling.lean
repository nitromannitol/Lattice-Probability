import Mathlib
import LatticeProb.Gauss.GFF
import LatticeProb.LQG.LQGMeasure
import LatticeProb.LQG.LQGMeasureDerived
import LatticeProb.LQG.MassFunctional

/-! # Weyl scaling of the γ-LQG measure: LP form

LP form of the Proposed statement `LQGMeasureWeylScaling` (`HarmonicBalls/Proposed/LQG.lean:107`, Fact 2.1 III of
arXiv:2208.11795, p. 9): almost surely, `e^{γ f} · μ_h = μ_{h+f}` for every continuous `f : ℂ → ℝ`, where `μ_{h+f}` is
the vague limit of `ε^{γ²/2} e^{γ (h+f)_ε(z)} dz` along `ε = 2^{-k}`. The statement is the same expression, stated for
the LP definitions `IsWholePlaneGFF`, `IsLQGMeasureOfField`, `IsLQGLimit`, `addCircleAverage`, `fieldCircleAverage`
and `lqgQ`.

Proof: the derivation `lqgMeasureWeylScaling` of `HarmonicBalls/Proofs/Sec6/LQGWeylScaling.lean`, copied in LP form
with its vague-convergence helpers (`HarmonicBalls/Proofs/Sec6/VagueUniformTests.lean`,
`HarmonicBalls/Proofs/Sec6/ContinuousWeylCircleAverage.lean`, `HarmonicBalls/Proofs/Sec8/VagueMassConvergence.lean`).
The argument is deterministic once the circle averages are continuous at the dyadic radii: the exponential weight
`e^{γ f_ε}` converges to `e^{γ f}` uniformly on compact sets (Duplantier-Sheffield 2011, Prop. 1.1; Berestycki-Powell),
and the vague convergence of the regularized measures passes to the weighted limit. No new mathematics and no new input;
the almost-sure continuity at each dyadic radius is `ae_continuous_fieldCircleAverage_of_isWholePlaneGFF`, from the
joint continuity `IsWholePlaneGFF.ae_continuousOn_circle`.
-/

open MeasureTheory Filter Set Metric Topology
open scoped ENNReal
open LatticeProb.Gauss LatticeProb.LQG
open LatticeProb.LQG.ProfileDerived (dyadicScale_pos isLocallyFiniteMeasure_lqgApprox continuous_circleAverage_log_norm)
open LatticeProb.Gauss.Section6 (continuous_circleAverage_radius_center)

namespace LatticeProb.LQG.LQGWeylScalingDerived

/-! ## Vague convergence with uniform test functions (copied from `VagueMassConvergence`, `ContinuousWeylCircleAverage`,
`VagueUniformTests`, LP names) -/

/-- Vague convergence of locally finite measures gives the upper
portmanteau bound on compact sets. -/
theorem limsup_measure_compact_le_of_tendsto_compactlySupported
    (ν : ℕ → Measure ℂ) (μ : Measure ℂ)
    [∀ n, IsLocallyFiniteMeasure (ν n)] [IsLocallyFiniteMeasure μ]
    (h : ∀ f : ℂ → ℝ, Continuous f → HasCompactSupport f →
      Tendsto (fun n => ∫ x, f x ∂(ν n)) atTop (𝓝 (∫ x, f x ∂μ)))
    {K : Set ℂ} (hK : IsCompact K) : limsup (fun n => ν n K) atTop ≤ μ K := by
  rw [hK.measure_eq_iInf_isOpen (μ := μ)]
  refine le_iInf fun V => le_iInf fun hKV => le_iInf fun hV => ?_
  obtain ⟨R, hKR⟩ := hK.isBounded.subset_ball (0 : ℂ)
  obtain ⟨f, hf1, hfc, hfV, hf01⟩ :=
    exists_continuousMap_one_of_isCompact_subset_isOpen hK (hV.inter isOpen_ball)
      (subset_inter hKV hKR)
  have hfcont : Continuous (f : ℂ → ℝ) := f.continuous
  have hnn : ∀ x, 0 ≤ f x := fun x => (hf01 x).1
  have hint (η : Measure ℂ) [IsLocallyFiniteMeasure η] : Integrable (f : ℂ → ℝ) η :=
    hfcont.integrable_of_hasCompactSupport hfc
  have hlow (n : ℕ) : ν n K ≤ ENNReal.ofReal (∫ x, f x ∂(ν n)) := by
    rw [ofReal_integral_eq_lintegral_ofReal (hint (ν n)) (Eventually.of_forall hnn)]
    calc
      ν n K = ∫⁻ x, K.indicator 1 x ∂(ν n) := (lintegral_indicator_one hK.measurableSet).symm
      _ ≤ ∫⁻ x, ENNReal.ofReal (f x) ∂(ν n) := by
        apply lintegral_mono
        intro x
        by_cases hx : x ∈ K
        · simp [hx, hf1 hx]
        · simp [hx]
  have hup : ENNReal.ofReal (∫ x, f x ∂μ) ≤ μ V := by
    rw [ofReal_integral_eq_lintegral_ofReal (hint μ) (Eventually.of_forall hnn)]
    calc
      _ ≤ ∫⁻ x, V.indicator 1 x ∂μ := by
        apply lintegral_mono
        intro x
        by_cases hx : x ∈ V
        · simp [hx, (hf01 x).2]
        · have hzero : f x = 0 := image_eq_zero_of_notMem_tsupport
            (fun hx' => hx (hfV hx').1)
          simp [hx, hzero]
      _ = μ V := lintegral_indicator_one hV.measurableSet
  have ht := ENNReal.tendsto_ofReal (h f hfcont hfc)
  calc
    limsup (fun n => ν n K) atTop ≤
        limsup (fun n => ENNReal.ofReal (∫ x, f x ∂(ν n))) atTop :=
      limsup_le_limsup (Eventually.of_forall hlow)
    _ = ENNReal.ofReal (∫ x, f x ∂μ) := ht.limsup_eq
    _ ≤ μ V := hup
/-- Vague convergence gives an eventual real bound on the masses of a fixed
compact set. This bound controls errors of uniformly convergent test functions. -/
theorem eventually_measureReal_compact_le_of_vague
    (ν : ℕ → Measure ℂ) (μ : Measure ℂ)
    [∀ n, IsLocallyFiniteMeasure (ν n)] [IsLocallyFiniteMeasure μ]
    (h : ∀ f : ℂ → ℝ, Continuous f → HasCompactSupport f →
      Tendsto (fun n => ∫ x, f x ∂(ν n)) atTop (𝓝 (∫ x, f x ∂μ)))
    {K : Set ℂ} (hK : IsCompact K) :
    ∀ᶠ n in atTop, (ν n).real K ≤ μ.real K + 1 := by
  have hm : μ K ≠ ∞ := hK.measure_ne_top
  have hlim := limsup_measure_compact_le_of_tendsto_compactlySupported ν μ h hK
  have hlt : limsup (fun n => ν n K) atTop < ENNReal.ofReal (μ.real K + 1) := by
    apply lt_of_le_of_lt hlim
    rw [← ENNReal.ofReal_toReal hm]
    exact (ENNReal.ofReal_lt_ofReal_iff (by positivity : 0 < μ.real K + 1)).2
      (by simp only [measureReal_def]; linarith)
  filter_upwards [eventually_lt_of_limsup_lt hlt] with n hn
  have hr := ENNReal.toReal_mono (by simp) hn.le
  rw [ENNReal.toReal_ofReal (by positivity : 0 ≤ μ.real K + 1)] at hr
  simpa only [measureReal_def] using hr

/-- For vaguely convergent locally finite measures, uniformly small errors
supported in one compact set have integrals converging to zero. -/
theorem tendsto_integral_sub_zero_of_uniformOn_compact
    (ν : ℕ → Measure ℂ) (μ : Measure ℂ)
    [∀ n, IsLocallyFiniteMeasure (ν n)] [IsLocallyFiniteMeasure μ]
    (hvague : ∀ f : ℂ → ℝ, Continuous f → HasCompactSupport f →
      Tendsto (fun n => ∫ x, f x ∂(ν n)) atTop (𝓝 (∫ x, f x ∂μ)))
    {K : Set ℂ} (hK : IsCompact K) {g : ℕ → ℂ → ℝ} {f : ℂ → ℝ}
    (hunif : TendstoUniformlyOn g f atTop K)
    (hoff : ∀ n x, x ∉ K → g n x = f x) :
    Tendsto (fun n => ∫ x, (g n x - f x) ∂(ν n)) atTop (𝓝 0) := by
  rw [Metric.tendsto_nhds]
  intro ε hε
  let C : ℝ := μ.real K + 1
  have hC : 0 < C := by dsimp [C]; positivity
  have hδ : 0 < ε / (C + 1) := div_pos hε (by linarith)
  have hu := (Metric.tendstoUniformlyOn_iff.mp hunif) (ε / (C + 1)) hδ
  have hm := eventually_measureReal_compact_le_of_vague ν μ hvague hK
  filter_upwards [hu, hm] with n hn hmass
  have hbound : ‖∫ x in K, (g n x - f x) ∂(ν n)‖ ≤
      (ε / (C + 1)) * (ν n).real K := by
    apply norm_setIntegral_le_of_norm_le_const_ae' hK.measure_lt_top
    filter_upwards [] with x hx
    have hx' := hn x hx
    rw [Real.dist_eq] at hx'
    simpa only [Real.norm_eq_abs, abs_sub_comm] using hx'.le
  have heq : (∫ x, (g n x - f x) ∂(ν n)) =
      ∫ x in K, (g n x - f x) ∂(ν n) := by
    symm
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro x hx
    simp only [hoff n x hx, sub_self]
  rw [Real.dist_eq, sub_zero, heq]
  have hmass' : (ν n).real K ≤ C := by simpa only [C] using hmass
  have hnonneg : 0 ≤ (ν n).real K := measureReal_nonneg
  have hcalc : (ε / (C + 1)) * (ν n).real K < ε := by
    have hh : (ε / (C + 1)) * (C + 1) = ε := div_mul_cancel₀ ε (by linarith)
    nlinarith
  exact lt_of_le_of_lt hbound hcalc

/-- Uniformly convergent, integrable perturbations of a compactly supported
continuous test have the expected integral limit under vague convergence. -/
theorem tendsto_integral_of_uniformOn_compact
    (ν : ℕ → Measure ℂ) (μ : Measure ℂ)
    [∀ n, IsLocallyFiniteMeasure (ν n)] [IsLocallyFiniteMeasure μ]
    (hvague : ∀ f : ℂ → ℝ, Continuous f → HasCompactSupport f →
      Tendsto (fun n => ∫ x, f x ∂(ν n)) atTop (𝓝 (∫ x, f x ∂μ)))
    {K : Set ℂ} (hK : IsCompact K) {g : ℕ → ℂ → ℝ} {f : ℂ → ℝ}
    (hf : Continuous f) (hfc : HasCompactSupport f)
    (hgi : ∀ n, Integrable (g n) (ν n))
    (hunif : TendstoUniformlyOn g f atTop K)
    (hoff : ∀ n x, x ∉ K → g n x = f x) :
    Tendsto (fun n => ∫ x, g n x ∂(ν n)) atTop (𝓝 (∫ x, f x ∂μ)) := by
  have hsub := tendsto_integral_sub_zero_of_uniformOn_compact ν μ hvague hK hunif hoff
  have hsum := hsub.add (hvague f hf hfc)
  simp only [zero_add] at hsum
  convert hsum using 1
  funext n
  rw [integral_sub (hgi n) (hf.integrable_of_hasCompactSupport hfc), sub_add_cancel]

/-! ## Weyl scaling of the regularized measures (copied from `Proofs/Sec6/LQGWeylScaling.lean`, LP names) -/

/-- The regularized measure of a perturbed field is the original regularized
measure weighted by the exponential of the perturbation's circle average. -/
theorem lqgApprox_addCircleAverage (γ r : ℝ) (hr : 0 ≤ r)
    (hε : ℝ → ℂ → ℝ) (hh : Continuous (hε r))
    (f : ℂ → ℝ) (hf : Continuous f) :
    lqgApprox γ (addCircleAverage hε f) r =
      (lqgApprox γ hε r).withDensity
        (fun z => ENNReal.ofReal (Real.exp (γ * Real.circleAverage f z r))) := by
  have hav : Continuous (fun z => Real.circleAverage f z r) :=
    (continuous_circleAverage_radius_center hf).comp (continuous_const.prodMk continuous_id)
  have ha : Measurable (fun z => ENNReal.ofReal (r ^ (γ ^ 2 / 2) * Real.exp (γ * hε r z))) :=
    ENNReal.measurable_ofReal.comp (continuous_const.mul
      (Real.continuous_exp.comp (continuous_const.mul hh))).measurable
  have hb : Measurable (fun z => ENNReal.ofReal (Real.exp (γ * Real.circleAverage f z r))) :=
    ENNReal.measurable_ofReal.comp (Real.continuous_exp.comp (continuous_const.mul hav)).measurable
  simp only [lqgApprox]
  rw [← withDensity_mul volume ha hb]
  apply withDensity_congr_ae
  filter_upwards [] with z
  simp only [Pi.mul_apply, addCircleAverage]
  rw [← ENNReal.ofReal_mul (mul_nonneg (Real.rpow_nonneg hr _) (Real.exp_nonneg _))]
  congr 1
  rw [mul_add, Real.exp_add]
  ring

/-- Integrating against a continuous positive exponential density amounts to
multiplying the test function by the density. -/
theorem integral_withDensity_exp (μ : Measure ℂ) (γ : ℝ) (f φ : ℂ → ℝ)
    (hf : Continuous f) :
    (∫ z, φ z ∂(μ.withDensity fun z => ENNReal.ofReal (Real.exp (γ * f z)))) =
      ∫ z, φ z * Real.exp (γ * f z) ∂μ := by
  have hm : Measurable (fun z => ENNReal.ofReal (Real.exp (γ * f z))) :=
    ENNReal.measurable_ofReal.comp (Real.continuous_exp.comp (continuous_const.mul hf)).measurable
  rw [integral_withDensity_eq_integral_toReal_smul hm (by filter_upwards [] with z; simp) φ]
  congr 1
  funext z
  simp [Real.exp_nonneg, mul_comm]

/-- Multiplication by a continuous test preserves uniform convergence of the
exponential circle-average weights on compact sets. -/
theorem tendstoUniformlyOn_test_exp_circleAverage (γ : ℝ) (f φ : ℂ → ℝ)
    (hf : Continuous f) (hφ : Continuous φ) {K : Set ℂ} (hK : IsCompact K) :
    TendstoUniformlyOn (fun n z => φ z * Real.exp (γ * Real.circleAverage f z (dyadicScale n)))
      (fun z => φ z * Real.exp (γ * f z)) atTop K := by
  let U : Set ℝ := Icc (-1) 1
  have hU : U ∈ 𝓝 (0 : ℝ) := Icc_mem_nhds (by norm_num) (by norm_num)
  have hc : Continuous (fun p : ℝ × ℂ => φ p.2 * Real.exp (γ * Real.circleAverage f p.2 p.1)) :=
    (hφ.comp continuous_snd).mul
      (Real.continuous_exp.comp (continuous_const.mul (continuous_circleAverage_radius_center hf)))
  have hu : UniformContinuousOn
      (fun p : ℝ × ℂ => φ p.2 * Real.exp (γ * Real.circleAverage f p.2 p.1)) (U ×ˢ K) :=
    (isCompact_Icc.prod hK).uniformContinuousOn_of_continuous hc.continuousOn
  have ht := hu.tendstoUniformlyOn
    (F := fun r z => φ z * Real.exp (γ * Real.circleAverage f z r)) (mem_of_mem_nhds hU)
  have ht' : TendstoUniformlyOn (fun r z => φ z * Real.exp (γ * Real.circleAverage f z r))
      (fun z => φ z * Real.exp (γ * f z)) (𝓝 0) K := by
    simpa only [nhdsWithin_eq_nhds.mpr hU, Real.circleAverage_zero] using ht
  rw [Metric.tendstoUniformlyOn_iff] at ht' ⊢
  intro ε hε
  have hscale : Tendsto dyadicScale atTop (𝓝 0) := by
    change Tendsto (fun n : ℕ => ((2 : ℝ)⁻¹) ^ n) atTop (𝓝 0)
    exact tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 2⁻¹)
      (by norm_num : (2 : ℝ)⁻¹ < 1)
  exact hscale.eventually (ht' ε hε)

/-- Weyl scaling follows deterministically from vague convergence when the
regularized field has continuous profiles at the dyadic scales. -/
theorem isLQGLimit_addCircleAverage {γ : ℝ} {hε : ℝ → ℂ → ℝ} {μ : Measure ℂ}
    (hμ : IsLQGLimit γ hε μ) (hh : ∀ n, Continuous (hε (dyadicScale n)))
    (f : ℂ → ℝ) (hf : Continuous f) :
    IsLQGLimit γ (addCircleAverage hε f)
      (μ.withDensity fun z => ENNReal.ofReal (Real.exp (γ * f z))) := by
  let : IsLocallyFiniteMeasure μ := hμ.isLocallyFiniteMeasure
  let ν : ℕ → Measure ℂ := fun n => lqgApprox γ hε (dyadicScale n)
  let : ∀ n, IsLocallyFiniteMeasure (ν n) := fun n =>
    isLocallyFiniteMeasure_lqgApprox γ (hh n)
  have hfexp : Continuous (fun z => Real.exp (γ * f z)) :=
    Real.continuous_exp.comp (continuous_const.mul hf)
  constructor
  · exact IsLocallyFiniteMeasure.withDensity_ofReal hfexp
  · intro φ hφ hφc
    let K := tsupport φ
    have hK : IsCompact K := hφc
    let g : ℕ → ℂ → ℝ := fun n z => φ z * Real.exp (γ * Real.circleAverage f z (dyadicScale n))
    let g₀ : ℂ → ℝ := fun z => φ z * Real.exp (γ * f z)
    have hg : ∀ n, Integrable (g n) (ν n) := by
      intro n
      have hav : Continuous (fun z => Real.circleAverage f z (dyadicScale n)) :=
        (continuous_circleAverage_radius_center hf).comp (continuous_const.prodMk continuous_id)
      have hgc : Continuous (g n) := hφ.mul (Real.continuous_exp.comp (continuous_const.mul hav))
      exact hgc.integrable_of_hasCompactSupport hφc.mul_right
    have huni : TendstoUniformlyOn g g₀ atTop K :=
      tendstoUniformlyOn_test_exp_circleAverage γ f φ hf hφ hK
    have hoff : ∀ n z, z ∉ K → g n z = g₀ z := by
      intro n z hz
      have hz' : φ z = 0 := image_eq_zero_of_notMem_tsupport hz
      simp [g, g₀, hz']
    have hlim := tendsto_integral_of_uniformOn_compact ν μ hμ.tendsto_integral hK
      (hφ.mul hfexp) hφc.mul_right hg huni hoff
    have heq (n : ℕ) : (∫ z, φ z ∂(lqgApprox γ (addCircleAverage hε f) (dyadicScale n))) =
        ∫ z, g n z ∂(ν n) := by
      rw [lqgApprox_addCircleAverage γ (dyadicScale n) (dyadicScale_pos n).le hε (hh n) f hf]
      exact integral_withDensity_exp (ν n) γ (fun z => Real.circleAverage f z (dyadicScale n)) φ
        ((continuous_circleAverage_radius_center hf).comp (continuous_const.prodMk continuous_id))
    simp_rw [heq, integral_withDensity_exp μ γ f φ hf]
    exact hlim

/-- The circle averages `fieldCircleAverage α₀ (hcirc ω) r` of a whole-plane GFF are almost surely continuous in the
centre at each fixed radius `r > 0`, since the joint continuity on `(0, ∞) × ℂ` restricts to a continuous map of `z`,
and the logarithmic term `α₀ · circleAverage (log ‖·‖) z r` is continuous by Jensen's formula
(`ProfileDerived.continuous_circleAverage_log_norm`). -/
theorem ae_continuous_fieldCircleAverage_of_isWholePlaneGFF {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} (h : IsWholePlaneGFF P hC hcirc) (α₀ : ℝ) {r : ℝ}
    (hr : 0 < r) : ∀ᵐ ω ∂P, Continuous (fun z => fieldCircleAverage α₀ (hcirc ω) r z) := by
  filter_upwards [h.ae_continuousOn_circle] with ω hω
  have hc : Continuous (fun z : ℂ => hcirc ω r z) :=
    hω.comp_continuous (continuous_const.prodMk continuous_id) (fun z => ⟨hr, Set.mem_univ z⟩)
  unfold fieldCircleAverage
  exact hc.sub (continuous_const.mul (continuous_circleAverage_log_norm hr))

/-- **Fact 2.1 III (Weyl scaling), LP form** (`HarmonicBalls/Proposed/LQG.lean:107`). For a whole-plane GFF `hC`, `hcirc`
and a γ-LQG measure `μ` of `h^ℂ - α₀ log|·|` (`IsLQGMeasureOfField`), almost surely, for every continuous `f : ℂ → ℝ`,
the LQG measure of `h + f` (the vague limit with circle averages `addCircleAverage`) is `e^{γ f} · μ`
(`IsLQGLimit`). Intended for `0 < γ < 2` and `α₀ < lqgQ γ`. Source: Duplantier-Sheffield 2011, Prop. 1.1;
arXiv:2208.11795, Fact 2.1 III, p. 9. -/
def LQGMeasureWeylScalingLP {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (γ α₀ : ℝ)
    (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ) : Prop :=
  IsWholePlaneGFF P hC hcirc → 0 < γ → γ < 2 → α₀ < lqgQ γ → ∀ μ : Ω → Measure ℂ,
    IsLQGMeasureOfField P γ α₀ hcirc μ → ∀ᵐ ω ∂P, ∀ f : ℂ → ℝ, Continuous f →
      IsLQGLimit γ (addCircleAverage (fieldCircleAverage α₀ (hcirc ω)) f)
        ((μ ω).withDensity fun x => ENNReal.ofReal (Real.exp (γ * f x)))

/-- The LP form of the Weyl scaling statement `LQGMeasureWeylScalingLP` holds with no hypotheses on the field.
Proof: the almost-sure continuity at the dyadic radii, then `isLQGLimit_addCircleAverage` for each `ω`. -/
theorem lqgMeasureWeylScaling_lp {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (γ α₀ : ℝ)
    (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ) : LQGMeasureWeylScalingLP P γ α₀ hC hcirc := by
  intro hgff _ _ _ μ hμ
  have hc : ∀ᵐ ω ∂P, ∀ n, Continuous (fun z => fieldCircleAverage α₀ (hcirc ω) (dyadicScale n) z) :=
    ae_all_iff.mpr (fun n => ae_continuous_fieldCircleAverage_of_isWholePlaneGFF hgff α₀ (dyadicScale_pos n))
  filter_upwards [hμ, hc] with ω hω hωc
  intro f hf
  exact isLQGLimit_addCircleAverage hω hωc f hf

end LatticeProb.LQG.LQGWeylScalingDerived
