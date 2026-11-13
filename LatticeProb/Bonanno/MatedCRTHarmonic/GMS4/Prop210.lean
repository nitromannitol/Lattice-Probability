/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module MatedCRTHarmonic.GMS4.Prop210 at commit fdb5cad; only the module paths of local imports are changed.
   Declarations, examples and checks that the copied results do not use are omitted.
   Imports of copied modules that this file does not need are replaced by their own imports. -/
import LatticeProb.Bonanno.MatedCRTHarmonic.GMS4.Prop210Transfer
import LatticeProb.Bonanno.MatedCRTHarmonic.GMS4.Probability
import LatticeProb.Bonanno.MatedCRTHarmonic.GMSLemma27.CellModel
import LatticeProb.Bonanno.MatedCRTHarmonic.CellFamily.ProducersCellCoupling

/-!
# Fixed-scale probabilistic adapter for [18] Proposition 2.10

The deterministic implication `(4.20)` is proved in `Prop210Transfer`. This file applies it
outcome by outcome in a `CellFamily.RandomCellFamily`, and transfers an outer-measure estimate for
The localized bad event to G3's exact `Prop210Bound` bad event. No measurability of either event
is needed.

The current `GMSLemma27.CellModel` deliberately contains only the field, area measure, curve,
and curve-segment cells. Its source-faithful missing graph bridge is the named
`.CellModelGraphCoupling` from `CellGraphInterface.lean`, whose Brownian law comes from frozen
`IsCellCoupling` and whose mesh identifications are almost sure. This file contains no
Proposition 2.10 estimate.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace MatedCRTHarmonic.GMS4

open MatedCRTHarmonic.GMS3

/-- The fixed-scale domain/function assumptions in [18] Proposition 2.10
. The paper's notation
`B_r(partial D)` is represented by `Metric.thickening r (frontier D)`. -/
def Prop210Admissible (epsilon rho C beta : ℝ) (D : Set ℂ) (f : ℂ → ℝ) : Prop :=
  0 < epsilon ∧ epsilon < 1 ∧ 0 < rho ∧ rho < 1 ∧ 1 < C ∧ 0 < beta ∧
    IsOpen D ∧ IsConnected D ∧ D ⊆ Metric.ball 0 rho ∧
    (∀ r ∈ Set.Ioo (0 : ℝ) 1,
      volume (Metric.thickening r (frontier D)) ≤ ENNReal.ofReal (C * r)) ∧
    (∀ z ∈ D, 0 ≤ f z ∧ f z ≤ C * epsilon ^ (-beta)) ∧
    ∀ z ∈ D, ∀ w ∈ D,
      |f z - f w| ≤ C * epsilon ^ (-beta) * dist z w

/-- G3's exact Proposition 2.10 event for one scale and one fixed test pair `(D,f)`. -/
def Prop210Good (F : CellFamily.RandomCellFamily) (k : ℕ) (D : Set ℂ)
    (f : ℂ → ℝ) (A eta : ℝ) : Set F.Ω :=
  {omega | Prop210Bound (F.H k omega) D f A eta}

/-- Failure of G3's exact Proposition 2.10 estimate. -/
def Prop210Bad (F : CellFamily.RandomCellFamily) (k : ℕ) (D : Set ℂ)
    (f : ℂ → ℝ) (A eta : ℝ) : Set F.Ω :=
  (Prop210Good F k D f A eta)ᶜ

end MatedCRTHarmonic.GMS4

