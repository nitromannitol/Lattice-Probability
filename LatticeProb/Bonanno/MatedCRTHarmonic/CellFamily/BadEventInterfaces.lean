/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module MatedCRTHarmonic.CellFamily.BadEventInterfaces at commit fdb5cad; only the module paths of local imports are changed.
   Declarations, examples and checks that the copied results do not use are omitted.
   Imports of copied modules that this file does not need are replaced by their own imports. -/
import LatticeProb.Bonanno.MatedCRTHarmonic.CellFamily.BadEventCore
import LatticeProb.Bonanno.MatedCRTHarmonic.CellFamily.Interfaces
import Mathlib
import LatticeProb.Bonanno.MatedCRTHarmonic.GMSLemma27.CellModel

/-!
# Bad-event forms of the scaled-grid estimate probability interfaces

The event bounds are stated as upper bounds on outer measure of failure events. These
interfaces avoid measurability assumptions on the graph-dependent walk-law events.
-/

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Set Metric
open scoped ENNReal NNReal

namespace MatedCRTHarmonic.CellFamily

/-- Outer-measure tail bound for failure of the Lemma 2.7 cell-diameter event. -/
def Lemma27CellDiamBad (F : RandomCellFamily) (q ρ : ℝ) : Prop :=
  ∃ α : ℝ, 0 < α ∧ ∃ C : ℝ, ∀ k,
    F.P (DiameterGood F k q ρ)ᶜ ≤ ENNReal.ofReal (C * mesh k ^ α)

/-- Corrected [18] Lemma 3.8 stated as an outer-measure bound on failure of its environment event. -/
def Lemma38AnnulusHitBad (F : RandomCellFamily) (ρ : ℝ) : Prop :=
  ∃ α₈ : ℝ, 0 < α₈ ∧ ∃ β₈ : ℝ, 0 < β₈ ∧ ∃ A₈ C₈ : ℝ,
    ∀ k (z : ℂ) (r : ℝ), mesh k ^ β₈ ≤ r → r ≤ ρ → ball z r ⊆ ball (0 : ℂ) ρ →
      F.P (Lemma38EnvironmentGood F k z r β₈ A₈)ᶜ ≤
        ENNReal.ofReal (C₈ * mesh k ^ α₈)

/-- Outer-measure tail bound for failure of the finite polar-template itinerary event. -/
def ItineraryEstimateBad (F : RandomCellFamily) (ρ : ℝ) : Prop :=
  ∃ s₀ αᵢ βᵢ Cᵢ : ℝ, 0 < s₀ ∧ s₀ ≤ 1 / 10 ∧ 0 < αᵢ ∧ 0 < βᵢ ∧
    ∀ k (z : ℂ) (r : ℝ), mesh k ^ βᵢ ≤ r → r ≤ ρ → ball z (2 * r) ⊆ ball (0 : ℂ) ρ →
      F.P (PolarItineraryGood F k z r s₀)ᶜ ≤
        ENNReal.ofReal (Cᵢ * mesh k ^ αᵢ)

end MatedCRTHarmonic.CellFamily
