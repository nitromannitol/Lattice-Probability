import LatticeProb.Prob.CellConfigConductanceGapMeasurable
import LatticeProb.Prob.CellConfigRootedSlotMoment

/-! # Rooted finite expectation for pushforward laws -/

set_option autoImplicit false

open MeasureTheory
open scoped ENNReal
open ReflectedGMS ReflectedGMS.GMS

namespace LatticeProb.CellConfigCappedSquare

/-- A source-space rooted moment and conductance bound give finite expectation
for the law of an almost-everywhere measurable cell configuration. -/
theorem finiteExpectation_map_of_originRowSum
    {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω) (F : Ω → GMSSpace)
    (hF : AEMeasurable F μ)
    (hc : ∀ᵐ ω ∂μ, ∀ K K' : Cell,
      (F ω).1.c K K' = 0 ∨ 1 ≤ (F ω).1.c K K')
    (hfin : ∫⁻ ω, originRowSum id (F ω) ∂μ < ∞) :
    FiniteExpectation (μ.map F) := by
  apply finiteExpectation_of_originRowSum
  · exact LatticeProb.CellConfigWalk.ae_conductance_eq_zero_or_one_le_map μ F hF hc
  · rw [lintegral_map' (measurable_originRowSum measurable_id).aemeasurable hF]
    exact hfin

end LatticeProb.CellConfigCappedSquare
