/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module MatedCRTHarmonic.GMS4c.LocalConfiguration at commit fdb5cad; only the module paths of local imports are changed.
   Declarations, examples and checks that the copied results do not use are omitted. -/
import LatticeProb.Bonanno.MatedCRTHarmonic.GMS4c.Defs
import LatticeProb.Bonanno.MatedCRTHarmonic.GMSAppA.LemmaA1A2

/-!
# The local data of [18] Lemma 4.3

For an open set `V`, this module records the restricted LQG area measure, the restricted field,
and the Lebesgue-parametrized SLE excursion segments at rational points. The measure space is
Mathlib's Giry measurable space on `Measure ℂ`; the field and segment factors carry their
existing product measurable spaces. The excursion coordinate is zero outside `V`, since the
frozen S7 locality clause only specifies segments at rational points inside `V`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set
open LQGMetric LQGMetric.Blueprint

namespace MatedCRTHarmonic.GMS4c

attribute [local instance] Classical.propDecidable

/-- The source local configuration `(μ_h|_V, h|_V, η_L` excursions`) of [18] Lemma 4.3.
The product measurable space uses Giry evaluation for the measure component, the Borel space
of distributions on `V`, and the product space of rationally indexed curves. -/
abbrev LocalConfiguration (V : TopologicalSpace.Opens ℂ) : Type :=
  (Measure ℂ × DistOn V) × (ℚ × ℚ → ℝ → ℂ)

/-- The measure restriction, as a map between Giry measurable spaces. -/
theorem measurable_measureRestrict (V : TopologicalSpace.Opens ℂ) :
    Measurable fun μ : Measure ℂ => μ.restrict V := by
  refine Measure.measurable_of_measurable_coe _ fun s hs => ?_
  simp only [Measure.restrict_apply hs]
  exact Measure.measurable_coe (hs.inter V.isOpen.measurableSet)

/-- The local configuration map from a measure, field and continuous space-filling curve. -/
def localConfiguration (V : TopologicalSpace.Opens ℂ) (μ : Measure ℂ) (h : DistC)
    (ηL : C(ℝ, ℂ)) : LocalConfiguration V :=
  ((μ.restrict V, restrictTo V h),
    fun q => if ratPt q ∈ V then MatedCRT.excursionSegment ηL V (ratPt q) else 0)

end MatedCRTHarmonic.GMS4c
