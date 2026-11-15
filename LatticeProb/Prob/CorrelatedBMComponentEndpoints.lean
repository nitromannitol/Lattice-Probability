import LatticeProb.Prob.CorrelatedBMCompletedObservations
import LatticeProb.Prob.AEDetermined
import LatticeProb.Topology.ComponentVisitCodeEndpointGeneral

/-! # Component endpoints observed from correlated Brownian increments -/

set_option autoImplicit false

open MeasureTheory MeasurableSpace Set

namespace LatticeProb.CorrelatedBM

open MatedCRTHarmonic.MatedCRT

/-- If the rational visit code of a curve component is almost surely determined by both
centered half-paths, its bounded interval endpoints have versions measurable from the
intervening centered increments. -/
theorem exists_segment_measurable_component_endpoints
    {γ : ℝ} {μ : Measure Path2} (hμ : IsCorrelatedBM2 γ μ)
    {a b u : ℝ} (hab : a ≤ b) (f : Path2 → C(ℝ, ℂ)) (A B : Path2 → ℝ)
    (hpast : AELeSigma (MeasurableSpace.comap
      (fun ω (q : {q : ℚ // (q : ℝ) ∈ Icc a b}) =>
        curveComponentVisitCode (Icc a b) (f ω) (f ω u) q.1) inferInstance)
      (incrementSigma lrCoord (Iic b) b) μ)
    (hfuture : AELeSigma (MeasurableSpace.comap
      (fun ω (q : {q : ℚ // (q : ℝ) ∈ Icc a b}) =>
        curveComponentVisitCode (Icc a b) (f ω) (f ω u) q.1) inferInstance)
      (incrementSigma lrCoord (Ici a) a) μ)
    (hgood : ∀ᵐ ω ∂μ,
      a ≤ A ω ∧ A ω < B ω ∧ B ω ≤ b ∧
      ∀ᵐ r ∂volume, f ω r ∈ connectedComponentIn (interior (f ω '' Icc a b)) (f ω u) ↔
        r ∈ Ioo (A ω) (B ω)) :
    ∃ A' B' : Path2 → ℝ,
      Measurable[incrementSigma lrCoord (Icc a b) a] A' ∧
      Measurable[incrementSigma lrCoord (Icc a b) a] B' ∧
      (∀ᵐ ω ∂μ, A' ω = A ω ∧ B' ω = B ω) := by
  let V : Path2 → {q : ℚ // (q : ℝ) ∈ Icc a b} → Bool := fun ω q =>
    curveComponentVisitCode (Icc a b) (f ω) (f ω u) q.1
  have hV := aeLeSigma_increment_segment_of_two_sides hμ hab hpast hfuture
  obtain ⟨V', hV'm, hVV'⟩ := exists_ae_eq_measurable_of_aeDeterminedSigma hV
  apply @exists_observable_endpoints_of_restricted_component_visit_code_general
    Path2 ℂ (ContinuousMap.measurableSpace : MeasurableSpace Path2) inferInstance inferInstance
    (incrementSigma lrCoord (Icc a b) a) μ f (fun ω => f ω u) (Icc a b) a b hab
    V' A B hV'm ?_ hgood
  filter_upwards [hVV'] with ω hω q
  exact (congrFun hω q).symm

end LatticeProb.CorrelatedBM
