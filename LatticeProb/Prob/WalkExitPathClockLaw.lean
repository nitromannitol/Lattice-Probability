import LatticeProb.Prob.CellConfigWalkExitMeasurable
import LatticeProb.Prob.NormalizedPrefixCurveEndpointLaw

/-! # Joint path and exit-clock laws for interpolated walks -/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set BouRabeeGwynne ReflectedGMS ReflectedGMS.GMS
open scoped NNReal ENNReal

namespace LatticeProb.CellConfigWalk

/-- The joint law of an interpolated cell walk and its exit time from a set. -/
def walkExitPathClockLaw (H : CellConfig) (p : H.cells → Plane) (ε : ℝ≥0)
    (U : Set Plane) (Q : Measure (ℕ → H.cells)) :
    Measure (C(ℝ≥0, Plane) × ℝ≥0∞) :=
  Q.map (fun ω => (H.interpolatedWalk p ε ω,
    continuousExitTime U 0 (H.interpolatedWalk p ε ω)))

/-- The interpolated path and its exit clock form an almost everywhere
measurable pair for an open domain. -/
theorem aemeasurable_interpolatedWalk_exitPathClock
    {H : CellConfig} [Countable H.cells] (hrec : H.Recurrent)
    (hpos : ∀ K, 0 < H.holding K) {K₀ : H.cells}
    {Q : Measure (ℕ → H.cells)} (hQ : H.IsSRWLaw K₀ Q)
    (p : H.cells → Plane) (ε : ℝ≥0) {U : Set Plane} (hU : IsOpen U) :
    AEMeasurable (fun ω => (H.interpolatedWalk p ε ω,
      continuousExitTime U 0 (H.interpolatedWalk p ε ω))) Q := by
  have hpath := aemeasurable_interpolatedWalk_of_recurrent hrec hpos hQ p ε
  exact hpath.prodMk ((measurable_continuousExitTime hU 0).comp_aemeasurable hpath)

/-- The joint path-clock law of a recurrent walk is a probability measure. -/
theorem isProbabilityMeasure_walkExitPathClockLaw
    {H : CellConfig} [Countable H.cells] (hrec : H.Recurrent)
    (hpos : ∀ K, 0 < H.holding K) {K₀ : H.cells}
    {Q : Measure (ℕ → H.cells)} (hQ : H.IsSRWLaw K₀ Q)
    (p : H.cells → Plane) (ε : ℝ≥0) {U : Set Plane} (hU : IsOpen U) :
    IsProbabilityMeasure (walkExitPathClockLaw H p ε U Q) := by
  let : IsProbabilityMeasure Q := hQ.1
  exact (Measure.isProbabilityMeasure_map_iff
    (aemeasurable_interpolatedWalk_exitPathClock hrec hpos hQ p ε hU)).2 inferInstance

/-- Evaluating the joint law at the exit clock gives the walk's exit-position
law, including the convention that an infinite clock is evaluated at zero. -/
theorem map_walkExitPathClockLaw_endpoint
    {H : CellConfig} [Countable H.cells] (hrec : H.Recurrent)
    (hpos : ∀ K, 0 < H.holding K) {K₀ : H.cells}
    {Q : Measure (ℕ → H.cells)} (hQ : H.IsSRWLaw K₀ Q)
    (p : H.cells → Plane) (ε : ℝ≥0) {U : Set Plane} (hU : IsOpen U) :
    (walkExitPathClockLaw H p ε U Q).map (fun q => q.1 q.2.toNNReal) =
      Q.map (fun ω => (H.interpolatedWalk p ε ω)
        (continuousExitTime U 0 (H.interpolatedWalk p ε ω)).toNNReal) := by
  have heval : Measurable (fun q : C(ℝ≥0, Plane) × ℝ≥0∞ => q.1 q.2.toNNReal) := by
    simpa only [normalizedPrefixCurve_endPoint, Function.comp_def] using
      CurveSpace.continuous_endPoint.measurable.comp measurable_normalizedPrefixCurve_toNNReal
  exact AEMeasurable.map_map_of_aemeasurable heval.aemeasurable
    (aemeasurable_interpolatedWalk_exitPathClock hrec hpos hQ p ε hU)

/-- The endpoint of the normalized prefix has the walk's exit-position law. -/
theorem map_walkExitPathClockLaw_prefix_endpoint
    {H : CellConfig} [Countable H.cells] (hrec : H.Recurrent)
    (hpos : ∀ K, 0 < H.holding K) {K₀ : H.cells}
    {Q : Measure (ℕ → H.cells)} (hQ : H.IsSRWLaw K₀ Q)
    (p : H.cells → Plane) (ε : ℝ≥0) {U : Set Plane} (hU : IsOpen U) :
    ((walkExitPathClockLaw H p ε U Q).map
      (fun q => normalizedPrefixCurve q.1 q.2.toNNReal)).map CurveSpace.endPoint =
      Q.map (fun ω => (H.interpolatedWalk p ε ω)
        (continuousExitTime U 0 (H.interpolatedWalk p ε ω)).toNNReal) := by
  rw [map_endPoint_normalizedPrefixCurve,
    map_walkExitPathClockLaw_endpoint hrec hpos hQ p ε hU]

end LatticeProb.CellConfigWalk
end
