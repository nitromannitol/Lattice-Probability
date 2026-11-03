/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module MatedCRTHarmonic.Frozen.AnnularEvent at commit 31e7483; only the module paths of local imports are changed. -/
import Mathlib
import LatticeProb.Bonanno.MatedCRTHarmonic.Frozen.LFMultigraph
import LatticeProb.Bonanno.MatedCRTHarmonic.Frozen.HitTime
import LatticeProb.Bonanno.MatedCRTHarmonic.Frozen.Annulus
import LatticeProb.Bonanno.MatedCRTHarmonic.Frozen.VerticesMeeting
import LatticeProb.Bonanno.MatedCRTHarmonic.Frozen.Disconnects

/-!
# Frozen definition: `LFMultigraph.AnnularEvent`

One shared definition: finite exit time; the visited set `{X_m : m < τ}` disconnects; the cells up to
and including the exit lie in `A_{r/3,5r/3}(z)`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set Metric
open scoped ENNReal NNReal

namespace MatedCRTHarmonic

namespace LFMultigraph

variable {V E : Type*} (G : LFMultigraph V E)

/-- The annular event: the exit time `τ`
from `V_K(A_{r/2,3r/2}(z))` is finite, the visited set `{X_m : m < τ}` disconnects `V_K(∂B_{3r/4}(z))` from
`V_K(∂B_{5r/4}(z))`, and `⋃_{m ≤ τ} J_{X_m} ⊆ A_{r/3,5r/3}(z)`. -/
def AnnularEvent (J : V → Set ℂ) (z : ℂ) (r : ℝ) (X : ℕ → V) : Prop :=
  ∃ τ : ℕ, Markov.hitTime (verticesMeeting J (annulus z (r / 2) (3 * r / 2)))ᶜ X = τ ∧
    G.Disconnects {y | ∃ m < τ, X m = y}
      (verticesMeeting J (sphere z (3 * r / 4))) (verticesMeeting J (sphere z (5 * r / 4))) ∧
    ∀ m ≤ τ, J (X m) ⊆ annulus z (r / 3) (5 * r / 3)

end LFMultigraph

end MatedCRTHarmonic
