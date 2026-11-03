/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module MatedCRTHarmonic.Frozen.IsTutteEmbedding at commit 31e7483; only the module paths of local imports are changed. -/
import Mathlib
import LatticeProb.Bonanno.MatedCRTHarmonic.Frozen.LFMultigraph
import LatticeProb.Bonanno.MatedCRTHarmonic.Frozen.Dart
import LatticeProb.Bonanno.MatedCRTHarmonic.Frozen.Dtgt
import LatticeProb.Bonanno.MatedCRTHarmonic.Frozen.OutDarts
import LatticeProb.Bonanno.MatedCRTHarmonic.Frozen.Deg
import LatticeProb.Bonanno.MatedCRTHarmonic.Frozen.State
import LatticeProb.Bonanno.MatedCRTHarmonic.Frozen.StateMeasurableSpace
import LatticeProb.Bonanno.MatedCRTHarmonic.Frozen.WalkLaw
import LatticeProb.Bonanno.MatedCRTHarmonic.Frozen.VertexPath
import LatticeProb.Bonanno.MatedCRTHarmonic.Frozen.HitTime
import LatticeProb.Bonanno.MatedCRTHarmonic.Frozen.Recurrent
import LatticeProb.Bonanno.MatedCRTHarmonic.Frozen.VerticesMeeting
import LatticeProb.Bonanno.MatedCRTHarmonic.Frozen.MatedCRTPath2
import LatticeProb.Bonanno.MatedCRTHarmonic.Frozen.MatedCRTEdge
import LatticeProb.Bonanno.MatedCRTHarmonic.Frozen.MatedCRTIsLocallyFinite
import LatticeProb.Bonanno.MatedCRTHarmonic.Frozen.MatedCRTGraph
import LatticeProb.Bonanno.MatedCRTHarmonic.Frozen.MatedCRTField
import LatticeProb.Bonanno.MatedCRTHarmonic.Frozen.IsMatingOfTreesCoupling
import LatticeProb.Bonanno.MatedCRTHarmonic.Frozen.IsHarmonicExtension

/-!
# Statement definition: `LFMultigraph.IsTutteEmbedding`

One of the seven definitions of the statement surface of the formalization of Gwynne–Miller–Sheffield,
*Harmonic functions on mated-CRT maps* (arXiv:1807.07511), here
called [18]. The definition is the frozen statement text, with the library namespace renamed.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set Metric
open scoped ENNReal NNReal

namespace MatedCRTHarmonic

namespace LFMultigraph

variable {V E : Type*} (G : LFMultigraph V E)

/-- **The Tutte embedding with identity boundary data** ([18] §1.6): `Φ = Φ₁ + iΦ₂ : V → ℂ ≅ ℝ²`, where `Φ₁`
(resp. `Φ₂`) is the function `f_ε` of (1.6) for `f(z) = Re z` (resp. `f(z) = Im z`). `ℂ` carries the Euclidean norm,
so `‖Φ x − Φ y‖` is the Euclidean length `|Φ^ε(x) − Φ^ε(y)|` of (1.10). -/
def IsTutteEmbedding (H : V → Set ℂ) (D : Set ℂ) (Φ : V → ℂ) : Prop :=
  G.IsHarmonicExtension H D (fun z => z.re) (fun x => (Φ x).re) ∧
    G.IsHarmonicExtension H D (fun z => z.im) (fun x => (Φ x).im)

end LFMultigraph

end MatedCRTHarmonic
