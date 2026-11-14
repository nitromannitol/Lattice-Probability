import LatticeProb.Prob.NormalizedPrefixCurve
import LatticeProb.Prob.ContinuousMappingAECont

/-! # Weak limits of normalized finite-prefix curves -/

set_option autoImplicit false

open MeasureTheory Filter Topology
open scoped ENNReal NNReal

namespace LatticeProb

/-- The normalized curve map is continuous at a finite extended duration. -/
theorem continuousAt_normalizedPrefixCurve_toNNReal {d : ℕ}
    (p : C(ℝ≥0, EuclideanSpace ℝ (Fin d)) × ℝ≥0∞) (hp : p.2 ≠ ⊤) :
    ContinuousAt (fun q : C(ℝ≥0, EuclideanSpace ℝ (Fin d)) × ℝ≥0∞ =>
      normalizedPrefixCurve q.1 q.2.toNNReal) p := by
  exact continuous_normalizedPrefixCurve.continuousAt.tendsto.comp
    (continuous_fst.continuousAt.tendsto.prodMk_nhds
      ((ENNReal.tendsto_toNNReal hp).comp continuous_snd.continuousAt.tendsto))

/-- Weak convergence of path-clock laws yields weak convergence of normalized curve laws
when the limiting clock is almost surely finite. -/
theorem tendsto_normalizedPrefixCurve_laws {d : ℕ} {I : Type*} {l : Filter I}
    [l.IsCountablyGenerated]
    {μ : I → ProbabilityMeasure (C(ℝ≥0, EuclideanSpace ℝ (Fin d)) × ℝ≥0∞)}
    {ν : ProbabilityMeasure (C(ℝ≥0, EuclideanSpace ℝ (Fin d)) × ℝ≥0∞)}
    (hμ : Tendsto μ l (𝓝 ν)) (hfin : ∀ᵐ p ∂(ν : Measure (C(ℝ≥0, EuclideanSpace ℝ (Fin d)) × ℝ≥0∞)), p.2 ≠ ⊤) :
    Tendsto (fun i => (μ i).map (fun p => normalizedPrefixCurve p.1 p.2.toNNReal)) l
      (𝓝 (ν.map (fun p => normalizedPrefixCurve p.1 p.2.toNNReal))) := by
  let f : C(ℝ≥0, EuclideanSpace ℝ (Fin d)) × ℝ≥0∞ → CurveSpace d :=
    fun p => normalizedPrefixCurve p.1 p.2.toNNReal
  have hf : Measurable f := measurable_normalizedPrefixCurve_toNNReal
  have hc : ∀ᵐ p ∂(ν : Measure (C(ℝ≥0, EuclideanSpace ℝ (Fin d)) × ℝ≥0∞)), ContinuousAt f p :=
    hfin.mono fun p hp => continuousAt_normalizedPrefixCurve_toNNReal p hp
  apply ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mpr
  intro g
  have h := tendsto_integral_of_ae_continuousAt hμ (g.continuous.measurable.comp hf)
    ⟨‖g‖, fun p => by simpa only [Real.norm_eq_abs, Function.comp_apply] using g.norm_coe_le_norm (f p)⟩
    (hc.mono fun p hp => g.continuous.continuousAt.comp hp)
  change Tendsto (fun i => ∫ y, g y ∂((μ i : Measure _).map f)) l
    (𝓝 (∫ y, g y ∂((ν : Measure _).map f)))
  simpa only [integral_map hf.aemeasurable
    g.continuous.measurable.aestronglyMeasurable, Function.comp_apply] using h

end LatticeProb
