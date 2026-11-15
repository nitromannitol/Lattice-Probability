/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module BouRabeeGwynne.BrownianExitReference at commit fdb5cad; local imports and linter settings are adjusted. -/
import LatticeProb.Bonanno.BouRabeeGwynne.BrownianGaussianReference
import LatticeProb.Bonanno.BouRabeeGwynne.BrownianExcursionKernel
import LatticeProb.Bonanno.BouRabeeGwynne.BrownianExitRestart

set_option linter.style.haveILetI false
set_option linter.deprecated false

set_option linter.style.haveILetI false
set_option linter.deprecated false

/-!
# A common reference measure for the actual Brownian exit laws

The reference starts Brownian motion from an independent time-one Gaussian
point. The deterministic restart identity and positive Gaussian densities
transfer its null sets to every interior starting point.
-/

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology
namespace BouRabeeGwynne

noncomputable def brownianExitReferenceLaw {d : ℕ} (U : Set (Euc d))
    (μ : Measure (BrownianPath d)) : Measure (Euc d) :=
  ((μ.map (fun ω : BrownianPath d ↦ ω 1)).prod μ).map
    (fun p : Euc d × BrownianPath d ↦ stoppedBrownianRepresentative U p.1 p.2 1)

lemma measurable_brownianExitReferencePoint {d : ℕ} {U : Set (Euc d)} (hU : IsOpen U) :
    Measurable (fun p : Euc d × BrownianPath d ↦ stoppedBrownianRepresentative U p.1 p.2 1) :=
  (ContinuousMap.measurable_eval 1).comp (measurable_stoppedBrownianRepresentative_joint hU)

lemma brownianExitReferenceLaw_isProbability {d : ℕ} {U : Set (Euc d)} (hU : IsOpen U)
    (μ : Measure (BrownianPath d)) [IsProbabilityMeasure μ] :
    IsProbabilityMeasure (brownianExitReferenceLaw U μ) := by
  haveI : IsProbabilityMeasure (μ.map (fun ω : BrownianPath d ↦ ω 1)) :=
    (Measure.isProbabilityMeasure_map_iff (continuous_eval_const (1 : ℝ≥0)).measurable.aemeasurable).mpr
      inferInstance
  exact (Measure.isProbabilityMeasure_map_iff
    (measurable_brownianExitReferencePoint hU).aemeasurable).mpr inferInstance

lemma standardBrownianLaw_map_eval_shift {d : ℕ} {μ : Measure (BrownianPath d)}
    (hμ : IsStandardBrownianLaw μ) (z : Euc d) (t : ℝ≥0) :
    μ.map (fun ω : BrownianPath d ↦ (z + ω t, shiftedBrownianPath t ω)) =
      (μ.map (fun ω : BrownianPath d ↦ z + ω t)).prod μ := by
  letI : IsProbabilityMeasure μ := hμ.1
  have hind : IndepFun (shiftedBrownianPath t) (fun ω : BrownianPath d ↦ z + ω t) μ := by
    simpa only [Function.comp_def, id] using
      (standardBrownianLaw_indepFun_shiftedPath hμ t).comp measurable_id
        (show Measurable (fun p : Set.Iic t → Euc d ↦ z + p ⟨t, Set.mem_Iic.mpr le_rfl⟩) from
          measurable_const.add (measurable_pi_apply (⟨t, Set.mem_Iic.mpr le_rfl⟩ : Set.Iic t)))
  have h := hind.symm.map_prod_eq_prod_map_map
    (measurable_const.add (continuous_eval_const t).measurable).aemeasurable
    (measurable_shiftedBrownianPath t).aemeasurable
  rw [standardBrownianLaw_map_shift hμ t] at h
  exact h

/-- The restarted exit law at every positive deterministic time is dominated
by the one common Gaussian-start reference measure. -/
lemma standardBrownianLaw_restarted_exit_absolutelyContinuous {d : ℕ}
    {μ : Measure (BrownianPath d)} (hμ : IsStandardBrownianLaw μ)
    {U : Set (Euc d)} (hU : IsOpen U) (z : Euc d) {t : ℝ≥0} (ht : 0 < t) :
    μ.map (fun ω : BrownianPath d ↦
      stoppedBrownianRepresentative U (z + ω t) (shiftedBrownianPath t ω) 1) ≪
        brownianExitReferenceLaw U μ := by
  letI : IsProbabilityMeasure μ := hμ.1
  have h := ((standardBrownianLaw_translated_eval_absolutelyContinuous hμ z ht).prod
    (Measure.AbsolutelyContinuous.refl μ)).map (measurable_brownianExitReferencePoint hU)
  rw [← standardBrownianLaw_map_eval_shift hμ z t,
    Measure.map_map (measurable_brownianExitReferencePoint hU)
      (show Measurable (fun ω : BrownianPath d ↦ (z + ω t, shiftedBrownianPath t ω)) by
        exact (measurable_const.add (continuous_eval_const t).measurable).prodMk
          (measurable_shiftedBrownianPath t))] at h
  exact h

lemma standardBrownianLaw_early_exit_tendsto_zero {d : ℕ}
    {μ : Measure (BrownianPath d)} (hμ : IsStandardBrownianLaw μ)
    {U : Set (Euc d)} (hU : IsOpen U) {z : Euc d} (hz : z ∈ U) :
    Tendsto (fun n : ℕ ↦ μ {ω | continuousExitTime U z ω ≤
      ((1 / ((n : ℝ≥0) + 1) : ℝ≥0) : ℝ≥0∞)}) atTop (𝓝 0) := by
  letI : IsProbabilityMeasure μ := hμ.1
  let S : ℕ → Set (BrownianPath d) := fun n ↦ {ω | continuousExitTime U z ω ≤
    ((1 / ((n : ℝ≥0) + 1) : ℝ≥0) : ℝ≥0∞)}
  have ht : Tendsto (fun n : ℕ ↦ 1 / ((n : ℝ≥0) + 1)) atTop (𝓝 0) := by
    simpa only [Nat.cast_add, Nat.cast_one, Nat.cast_succ, Function.comp_def] using
      (tendsto_one_div_atTop_nhds_zero_nat (𝕜 := ℝ≥0)).comp
        (tendsto_atTop_mono (fun n : ℕ ↦ Nat.le_succ n) tendsto_id)
  have ht' : Tendsto (fun n : ℕ ↦ ((1 / ((n : ℝ≥0) + 1) : ℝ≥0) : ℝ≥0∞))
      atTop (𝓝 0) := by
    simpa only [ENNReal.coe_zero, Function.comp_def] using (ENNReal.continuous_coe.tendsto 0).comp ht
  have hmeas (n : ℕ) : MeasurableSet (S n) :=
    (isStoppingTime_continuousExitTime hU z).measurable' measurableSet_Iic
  have hanti : Antitone S := by
    intro n m hnm ω hω
    exact hω.trans (ENNReal.coe_le_coe.mpr
      (div_le_div_of_nonneg_left (by positivity) (by positivity)
        (by exact_mod_cast Nat.add_le_add_right hnm 1)))
  have hinter : (⋂ n, S n) = {ω | continuousExitTime U z ω = 0} := by
    ext ω
    simp only [mem_iInter, S, mem_setOf_eq]
    constructor
    · intro hω
      exact le_antisymm (le_of_tendsto_of_tendsto' tendsto_const_nhds ht' hω) bot_le
    · intro hω n
      rw [hω]
      exact bot_le
  have hzero : μ {ω | continuousExitTime U z ω = 0} = 0 := by
    apply measure_eq_zero_iff_ae_notMem.mpr
    filter_upwards [standardBrownianLaw_eval_zero_ae hμ] with ω hω
    exact (continuousExitTime_pos_of_mem hU (by simpa [hω] using hz)).ne'
  have hlim := tendsto_measure_iInter_atTop (fun n ↦ (hmeas n).nullMeasurableSet (μ := μ))
    hanti ⟨0, measure_ne_top _ _⟩
  simpa only [hinter, hzero, Function.comp_def, S] using hlim

/-- All actual Brownian exit laws from interior starts share the null sets of
one finite reference law. The reference concerns spatial endpoints only. -/
theorem standardBrownianLaw_exit_absolutelyContinuous_reference {d : ℕ} (hd : 1 ≤ d)
    {μ : Measure (BrownianPath d)} (hμ : IsStandardBrownianLaw μ)
    {U : Set (Euc d)} (hU : IsOpen U) (hUb : Bornology.IsBounded U)
    {z : Euc d} (hz : z ∈ U) :
    (stoppedBrownianLaw U z μ).map CurveSpace.endPoint ≪ brownianExitReferenceLaw U μ := by
  letI : IsProbabilityMeasure μ := hμ.1
  rw [stoppedBrownianLaw, Measure.map_map CurveSpace.continuous_endPoint.measurable
    (measurable_stoppedBrownianCurve hU z)]
  change μ.map (fun ω : BrownianPath d ↦ stoppedBrownianRepresentative U z ω 1) ≪ _
  apply Measure.AbsolutelyContinuous.mk
  intro A hA hnull
  have hm : Measurable (fun ω : BrownianPath d ↦ stoppedBrownianRepresentative U z ω 1) :=
    (ContinuousMap.measurable_eval 1).comp (measurable_stoppedBrownianRepresentative hU z)
  rw [Measure.map_apply hm hA]
  have hpoint (a : Euc d) (ω : BrownianPath d) :
      stoppedBrownianRepresentative U a ω 1 = a + ω (continuousExitTime U a ω).toNNReal := by
    change CurveSpace.endPoint (stoppedBrownianCurve U a ω) = _
    exact stoppedBrownianCurve_endPoint
  have hbound (n : ℕ) : μ {ω | stoppedBrownianRepresentative U z ω 1 ∈ A} ≤
      μ {ω | continuousExitTime U z ω ≤ ((1 / ((n : ℝ≥0) + 1) : ℝ≥0) : ℝ≥0∞)} := by
    let t : ℝ≥0 := 1 / ((n : ℝ≥0) + 1)
    have ht : 0 < t := by dsimp [t]; positivity
    let R : Set (BrownianPath d) := {ω |
      stoppedBrownianRepresentative U (z + ω t) (shiftedBrownianPath t ω) 1 ∈ A}
    have hmR : Measurable (fun ω : BrownianPath d ↦
        stoppedBrownianRepresentative U (z + ω t) (shiftedBrownianPath t ω) 1) :=
      (measurable_brownianExitReferencePoint hU).comp
        ((measurable_const.add (continuous_eval_const t).measurable).prodMk
          (measurable_shiftedBrownianPath t))
    have hR : μ R = 0 := by
      have h := standardBrownianLaw_restarted_exit_absolutelyContinuous hμ hU z ht hnull
      rwa [Measure.map_apply hmR hA] at h
    have hsub : {ω | stoppedBrownianRepresentative U z ω 1 ∈ A} ≤ᵐ[μ]
        {ω | continuousExitTime U z ω ≤ (t : ℝ≥0∞)} ∪ R := by
      filter_upwards [standardBrownianLaw_ae_finiteExit hd hμ hUb z] with ω hfinite
      intro hω
      by_cases hearly : continuousExitTime U z ω ≤ (t : ℝ≥0∞)
      · exact Or.inl hearly
      · apply Or.inr
        change stoppedBrownianRepresentative U (z + ω t) (shiftedBrownianPath t ω) 1 ∈ A
        rw [hpoint, continuousExitTime_shift_endpoint U z ω t (lt_of_not_ge hearly).le hfinite,
          ← hpoint z ω]
        exact hω
    exact (measure_mono_ae hsub).trans ((measure_union_le _ _).trans (by rw [hR, add_zero]))
  exact le_antisymm (le_of_tendsto_of_tendsto' tendsto_const_nhds
    (standardBrownianLaw_early_exit_tendsto_zero hμ hU hz) hbound) bot_le

end BouRabeeGwynne
