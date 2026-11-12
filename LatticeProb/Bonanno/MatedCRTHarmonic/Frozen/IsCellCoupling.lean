/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module MatedCRTHarmonic.Frozen.IsCellCoupling at commit fdb5cad; only the module paths of local imports are changed.
   Declarations, examples and checks that the copied results do not use are omitted. -/
import Mathlib
import LatticeProb.Bonanno.MatedCRTHarmonic.Frozen.CellularEmbedding
import LatticeProb.Bonanno.MatedCRTHarmonic.Frozen.MatedCRTPath2
import LatticeProb.Bonanno.MatedCRTHarmonic.Frozen.IsCorrelatedBM2
import LatticeProb.Bonanno.MatedCRTHarmonic.Frozen.MatedCRTEdge
import LatticeProb.Bonanno.MatedCRTHarmonic.Frozen.MatedCRTIsLocallyFinite
import LatticeProb.Bonanno.MatedCRTHarmonic.Frozen.MatedCRTGraph

/-!
A proposition describing a mated-CRT Brownian motion and cellular embedding coupling.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set Metric
open scoped ENNReal NNReal

namespace MatedCRTHarmonic

namespace MatedCRT

/-- A **mated-CRT cell coupling**: on `(Ω, P)`, `bm` is measurable with the Brownian law of [18] §1.1, and
almost surely `cell ω` are the cells of a cellular embedding (frozen `CellularEmbedding`) of the
unit-mesh mated-CRT map of `bm ω`, rooted at `0`. (The SLE/LQG realization `cell ω x = η([x − 1, x])` is one such coupling; only "adjacent ⇒ intersecting" and Euclidean-null overlaps are required.) -/
structure IsCellCoupling (γ : ℝ) {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (bm : Ω → Path2)
    (cell : Ω → ℤ → Set ℂ) : Prop where
  measurable_bm : Measurable bm
  law : IsCorrelatedBM2 γ (P.map bm)
  cellular : ∀ᵐ ω ∂P, ∃ h : IsLocallyFinite 1 (bm ω), ∃ H : CellularEmbedding (graph 1 (bm ω) h) 0,
    H.cell = cell ω

end MatedCRT

end MatedCRTHarmonic
