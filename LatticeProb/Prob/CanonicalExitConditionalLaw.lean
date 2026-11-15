import LatticeProb.Prob.CanonicalOpenExitHistory
import LatticeProb.Prob.ConditionalLawLowerBound

/-! # Conditional bounds for canonical open-exit histories -/

set_option autoImplicit false

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace LatticeProb

/-- A canonical open-exit conditional lower bound transfers to the history
of the stopped path observed through a measurable realization. -/
theorem conditional_lower_bound_of_canonical_openExit_map
    {Ω : Type*} [MeasurableSpace Ω] {d : ℕ}
    (P : Measure Ω) [IsFiniteMeasure P]
    (Φ : Ω → C(ℝ≥0, EuclideanSpace ℝ (Fin d))) (hΦ : Measurable Φ)
    {U : Set (EuclideanSpace ℝ (Fin d))} (hU : IsOpen U)
    (f : C(ℝ≥0, EuclideanSpace ℝ (Fin d)) → ℝ)
    (hf : Integrable f (P.map Φ)) (p : ℝ) :
    let X : ℝ≥0 → C(ℝ≥0, EuclideanSpace ℝ (Fin d)) → EuclideanSpace ℝ (Fin d) :=
      fun t w => w t
    let hm : ∀ t, StronglyMeasurable (X t) :=
      fun t => (ContinuousMapBorel.ContinuousMap.measurable_eval t).stronglyMeasurable
    let hc : ∀ w, Continuous fun t => X t w := fun w => w.continuous
    let τ := openExitTime X U
    let hτ := isStoppingTime_openExitTime hm hc hU
    (∀ᵐ w ∂(P.map Φ), p ≤ (P.map Φ)[f | hτ.measurableSpace] w) →
      ∀ᵐ ω ∂P, p ≤ P[fun ω => f (Φ ω) |
        MeasurableSpace.comap (fun ω => stoppedPath (τ (Φ ω)) (Φ ω)) inferInstance] ω := by
  dsimp only
  intro hp
  let X : ℝ≥0 → C(ℝ≥0, EuclideanSpace ℝ (Fin d)) → EuclideanSpace ℝ (Fin d) :=
    fun t w => w t
  let hm : ∀ t, StronglyMeasurable (X t) :=
    fun t => (ContinuousMapBorel.ContinuousMap.measurable_eval t).stronglyMeasurable
  let hc : ∀ w, Continuous fun t => X t w := fun w => w.continuous
  let τ := openExitTime X U
  let hτ := isStoppingTime_openExitTime hm hc hU
  change ∀ᵐ ω ∂P, p ≤ P[fun ω => f (Φ ω) |
    MeasurableSpace.comap (fun ω => stoppedPath (τ (Φ ω)) (Φ ω)) inferInstance] ω
  have heq : hτ.measurableSpace = MeasurableSpace.comap
      (fun w => stoppedPath (τ w) w) inferInstance :=
    canonical_openExit_stopped_history hU
  have hle : MeasurableSpace.comap (fun ω => stoppedPath (τ (Φ ω)) (Φ ω)) inferInstance ≤
      MeasurableSpace.comap Φ hτ.measurableSpace := by
    rw [heq, MeasurableSpace.comap_comp]
    rfl
  exact conditional_lower_bound_of_map hτ.measurableSpace_le P Φ hΦ hle f hf p hp

end LatticeProb
