/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module MatedCRTHarmonic.CellFamily.ProducersCellCoupling at commit fdb5cad; only the module paths of local imports are changed.
   Declarations, examples and checks that the copied results do not use are omitted.
   Imports of copied modules that this file does not need are replaced by their own imports. -/
import LatticeProb.Bonanno.MatedCRTHarmonic.CellFamily.Interfaces
import LatticeProb.Bonanno.MatedCRTHarmonic.Frozen.IsCellCoupling
import Mathlib
import LatticeProb.Bonanno.MatedCRTHarmonic.Frozen.Adj
import LatticeProb.Bonanno.MatedCRTHarmonic.Frozen.MatedCRTPath2
import LatticeProb.Bonanno.MatedCRTHarmonic.Frozen.MatedCRTEdge
import LatticeProb.Bonanno.MatedCRTHarmonic.Frozen.MatedCRTIsLocallyFinite
import LatticeProb.Bonanno.MatedCRTHarmonic.Frozen.MatedCRTGraph

/-!
The frozen coupling supplies the unit-mesh Brownian path and almost-sure cellular embedding. The random-family
adapter `CellCoupledRandomFamily` also records the mesh graph identification asserted by the cell model and
transported by Brownian scaling, in adjacency-only form. Walk laws, degrees and
looplessness need the **multigraph** identity, so the mesoscopic proof uses `MultigraphCoupledRandomFamily`, which
adds `meshGraph_eq` identity (`MatedCRTMultigraphIdentification`) and from which the adjacency field is derived
(`MultigraphCoupledRandomFamily.ofMultigraph`). The graph-connectivity conclusion is the frozen theorem's checked
provider, imported directly without importing the frozen theorem anchor; looplessness comes from the multigraph
identity.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal

namespace MatedCRTHarmonic.CellFamily

open MatedCRTHarmonic

/-- A random-cell family packaged with its frozen unit-mesh coupling and the graph identifications at all dyadic
meshes. The latter are the cell-model version of [18] (1.1), transported from unit mesh
by `MesoModel.TransferScaling`; the cell model provider is responsible for the a.e.-to-version choice. The identification
here is adjacency-only (enough for connectivity, (CAL) and template separation); walk- and degree-dependent consumers
use `MultigraphCoupledRandomFamily`. -/
structure CellCoupledRandomFamily (γ : ℝ) where
  family : RandomCellFamily
  bm : family.Ω → MatedCRT.Path2
  cell : family.Ω → ℤ → Set ℂ
  coupling : MatedCRT.IsCellCoupling γ family.P bm cell
  graphIdentification : MatedCRTGraphIdentification family bm

namespace RandomCellFamily

end RandomCellFamily

/-- A cell-coupled random family whose mesh graphs are, almost surely, the mated-CRT **multigraphs** of its Brownian
path. This is the family the
mesoscopic proof consumes: the multigraph identity determines the walk laws and degrees of every mesh graph and
gives looplessness (`MultigraphCoupledRandomFamily.ae_loopless`). The inherited adjacency field is implied by
`meshGraph_eq` (`ofMultigraph` builds the structure from the multigraph identity alone). -/
structure MultigraphCoupledRandomFamily (γ : ℝ) extends CellCoupledRandomFamily γ where
  meshGraph_eq : MatedCRTMultigraphIdentification family bm

namespace MultigraphCoupledRandomFamily

end MultigraphCoupledRandomFamily

end MatedCRTHarmonic.CellFamily
