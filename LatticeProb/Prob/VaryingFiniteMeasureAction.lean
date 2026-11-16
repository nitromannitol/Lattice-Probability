import LatticeProb.Prob.ExtendedMappingAE

/-! # Pushforwards of varying finite measures -/

set_option autoImplicit false

open MeasureTheory Filter Topology

namespace LatticeProb

/-- A jointly continuous transformation sends a weakly continuous family of finite measures
  to a weakly continuous family of pushforward measures, including at zero mass. -/
theorem continuous_varyingFiniteMeasure_map_family
    {X Z Y : Type*} [PseudoMetricSpace X] [MeasurableSpace X] [OpensMeasurableSpace X]
    [Nonempty X] [SecondCountableTopology X] [PseudoMetricSpace Z] [MeasurableSpace Z] [OpensMeasurableSpace Z]
    [PseudoMetricSpace Y] [MeasurableSpace Y] [BorelSpace Y]
    {μ : Z → FiniteMeasure X} (hμ : Continuous μ)
    {F : X × Z → Y} (hF : Continuous F) :
    Continuous (fun z => (μ z).map (fun x => F (x, z))) := by
  classical
  rw [continuous_iff_seqContinuous]
  intro z z₀ hz
  change Tendsto (fun n => (μ (z n)).map (fun x => F (x, z n))) atTop
    (𝓝 ((μ z₀).map (fun x => F (x, z₀))))
  have hμlim : Tendsto (fun n => μ (z n)) atTop (𝓝 (μ z₀)) := (hμ.tendsto z₀).comp hz
  have hm (a : Z) : Measurable (fun x : X => F (x, a)) :=
    (hF.comp (continuous_id.prodMk continuous_const)).measurable
  by_cases hzero : μ z₀ = 0
  · have hmass : Tendsto (fun n => ((μ (z n)).map (fun x => F (x, z n))).mass)
        atTop (𝓝 0) := by
      have heq (a : Z) : ((μ a).map (fun x => F (x, a))).mass = (μ a).mass := by
        simpa only [FiniteMeasure.mass, Set.preimage_univ] using
          (FiniteMeasure.map_apply (μ a) (hm a) (A := Set.univ) MeasurableSet.univ)
      simp_rw [heq]
      simpa [hzero] using hμlim.mass
    have h := FiniteMeasure.tendsto_zero_of_tendsto_zero_mass hmass
    have hzmap : ((μ z₀).map (fun x => F (x, z₀))) = 0 := by
      apply FiniteMeasure.toMeasure_injective
      simp [hzero]
    simpa only [Function.comp_apply, hzmap] using h
  · have hnorm := FiniteMeasure.tendsto_normalize_of_tendsto hμlim hzero
    have hlim := ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mp hnorm
    let p : ℕ → ProbabilityMeasure Y := fun n =>
      ((μ (z n)).normalize).map (fun x => F (x, z n))
    let p₀ : ProbabilityMeasure Y := (μ z₀).normalize.map (fun x => F (x, z₀))
    have hp : Tendsto p atTop (𝓝 p₀) := by
      apply ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mpr
      intro g
      have hint := tendsto_integral_comp_of_ae_locally_uniform
        ((μ z₀).normalize : Measure X) (fun n => ((μ (z n)).normalize : Measure X))
        hlim (fun x => (x, z₀)) (fun n x => (x, z n))
        (fun _ => measurable_id.prodMk measurable_const) (measurable_id.prodMk measurable_const)
        (by
          refine Eventually.of_forall fun x ε hε => ?_
          obtain ⟨N, hN⟩ := Metric.tendsto_atTop.mp hz ε hε
          refine ⟨ε, hε, N, fun n hn y hy => ?_⟩
          rw [Prod.dist_eq]
          exact max_le hy.le (hN n hn).le)
        (g.compContinuous ⟨F, hF⟩)
      have hi (a : Z) :
          (∫ y, g y ∂(((μ a).normalize.map (fun x => F (x, a))) : Measure Y)) =
            ∫ x, g (F (x, a)) ∂((μ a).normalize : Measure X) := by
        rw [ProbabilityMeasure.toMeasure_map]
        exact integral_map (hm a).aemeasurable g.continuous.aestronglyMeasurable
      simpa only [p, p₀, hi, BoundedContinuousFunction.compContinuous_apply,
        ContinuousMap.coe_mk] using hint
    have hs := hμlim.mass.smul (ProbabilityMeasure.toFiniteMeasure_continuous.tendsto p₀ |>.comp hp)
    have heq (a : Z) : (μ a).map (fun x => F (x, a)) =
        (μ a).mass • (((μ a).normalize).map (fun x => F (x, a))).toFiniteMeasure := by
      conv_lhs => rw [(μ a).self_eq_mass_smul_normalize]
      rw [FiniteMeasure.map_smul _ (hm a).aemeasurable]
      rfl
    simpa only [heq, p, p₀, Function.comp_apply] using hs

end LatticeProb
