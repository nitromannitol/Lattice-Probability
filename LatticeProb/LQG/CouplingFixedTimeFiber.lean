import LatticeProb.Prob.CorrelatedBMContourFiber
import LatticeProb.Bonanno.MatedCRTHarmonic.Frozen.IsMatingOfTreesCoupling

/-! # Fixed-time fibres in mating-of-trees couplings -/

set_option autoImplicit false

open MeasureTheory
open scoped NNReal

namespace MatedCRTHarmonic.MoTInput

open MatedCRTHarmonic.MatedCRT

/-- At each fixed time, the area-parametrized curve of a mating-of-trees
coupling almost surely has a singleton fibre. -/
theorem ae_fixedTime_singleton_fiber_of_coupling
    {γ : ℝ} {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    {X X₀ hIG₀ : Ω → Field} {B B' B₀ B₀' : ℝ≥0 → Ω → ℝ} {U : Ω → ℝ}
    {ηL η η₀ : Ω → C(ℝ, ℂ)} {bm : Ω → Path2}
    (D : IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm)
    (a : ℝ) :
    ∀ᵐ ω ∂P, ∀ t, η ω t = η ω a → t = a := by
  apply LatticeProb.CorrelatedBM.ae_singleton_fiber_of_contour_relation
    D.measurable_curves.2.2.2.aemeasurable D.boundaryLawBM a
  filter_upwards [D.onlyMerge] with ω hω t ht
  exact hω a t ht.symm

end MatedCRTHarmonic.MoTInput
