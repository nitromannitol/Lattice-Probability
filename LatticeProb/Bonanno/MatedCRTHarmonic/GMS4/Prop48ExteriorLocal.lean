/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module MatedCRTHarmonic.GMS4.Prop48ExteriorLocal at commit fdb5cad; only the module paths of local imports are changed.
   Declarations, examples and checks that the copied results do not use are omitted. -/
import LatticeProb.Bonanno.MatedCRTHarmonic.GMS4.Prop48FarA3

/-!
# Exterior measurability of a distant local observation

For off-diagonal pairs in [18] (4.36), the local field restriction and its
circle averages at the distant point lie in the exterior sigma algebra at the
first point. This is the geometric locality needed to apply Appendix A.3.
-/

set_option autoImplicit false
noncomputable section

open MeasureTheory Metric Set LQGMetric LQGMetric.Blueprint

namespace MatedCRTHarmonic.GMS4

/-- The full local field observation at `w` is measurable in the exterior
field sigma algebra about `z` when its ball and averaging circle miss that
exterior ball. -/
theorem prop48_localObservation_exterior_measurable
    {Ω : Type} [MeasurableSpace Ω] (h hIG : Ω → DistC)
    (localRadius averageRadius r : ℝ) (z w : ℂ)
    (hball : (ballO w localRadius : Set ℂ) ⊆ (Metric.ball z r)ᶜ)
    (hsphere : Metric.sphere w |averageRadius| ⊆ (Metric.ball z r)ᶜ) :
    Measurable[prop48ExteriorSigma h hIG r z]
      (prop48LocalFieldObservation h hIG localRadius averageRadius w) := by
  let m := prop48ExteriorSigma h hIG r z
  have hhfield : Measurable[m]
      (fun ω => restrictTo (ballO w localRadius) (h ω)) := by
    have hbase : Measurable[fieldSigma h (ballO w localRadius)]
        (fun ω => restrictTo (ballO w localRadius) (h ω)) :=
      comap_measurable _
    exact hbase.mono
      ((LQGMetric.DFGPS.L217.fieldSigma_le_fieldSigmaClosed_of_subset h hball).trans
        (le_sup_left : fieldSigmaClosed h (Metric.ball z r)ᶜ ≤ m)) le_rfl
  have hhIGfield : Measurable[m]
      (fun ω => restrictTo (ballO w localRadius) (hIG ω)) := by
    have hbase : Measurable[fieldSigma hIG (ballO w localRadius)]
        (fun ω => restrictTo (ballO w localRadius) (hIG ω)) :=
      comap_measurable _
    exact hbase.mono
      ((LQGMetric.DFGPS.L217.fieldSigma_le_fieldSigmaClosed_of_subset hIG hball).trans
        (le_sup_right : fieldSigmaClosed hIG (Metric.ball z r)ᶜ ≤ m)) le_rfl
  have hhavg : Measurable[m] (fun ω => circleAvg (h ω) averageRadius w) :=
    (GM.measurable_circleAvg_fieldSigmaClosed h averageRadius w hsphere).mono
      (le_sup_left : fieldSigmaClosed h (Metric.ball z r)ᶜ ≤ m) le_rfl
  have hhIGavg : Measurable[m] (fun ω => circleAvg (hIG ω) averageRadius w) :=
    (GM.measurable_circleAvg_fieldSigmaClosed hIG averageRadius w hsphere).mono
      (le_sup_right : fieldSigmaClosed hIG (Metric.ball z r)ᶜ ≤ m) le_rfl
  exact (hhfield.prodMk hhIGfield).prodMk (hhavg.prodMk hhIGavg)

end MatedCRTHarmonic.GMS4

