/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module ReflectedGMS.Spatial.CoveredOrigin at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.ReflectedGMS.Environment.UncoveredFacts
import LatticeProb.Bonanno.ReflectedGMS.Spatial.UncoveredRootTransport

/-!
# The origin is covered, almost surely

The covering clause of `ReflectedGMS.Geometry` was weakened from `⋃ v, cell v = Set.univ` to
`μH[1] (uncoveredSet F) = 0`, so a *prescribed* point of the plane need no longer lie in a cell.
Several arguments genuinely need a cell **at the origin** rather than merely near it — the block
index `κ` of the origin dyadic chain tends to `0` only through a point that lies in a cell
(`Spatial/GoodEnvironmentSet.exists_blockIndex_originIndex_le`,
`Corrector/EventuallySelectedEngulfing.eventually_exists_selected_engulfing`), and the manuscript
says exactly this: *"Along a decreasing chain containing a point `z ∈ H` one has `D(S) ≥ d_H` and
hence `κ(S) ≤ 2 ℓ(S)/d_H → 0`. … No claim is needed about an uncovered singular point."*

`Spatial.ae_zero_mem_iUnion_cell` (the manuscript's Lemma 2.4) supplies the missing input almost
surely under spatial mass transport.  This module restates it in the form those consumers take,
`(0 : Plane) ∉ uncoveredSet (decode e)`, and discharges its nullity hypothesis from the covering
clause itself, so that the consumers need nothing beyond `MassTransport ν`.

The restriction to the origin is essential and is not a defect of the proof: the statement
`∀ᵐ e ∂ν, uncoveredSet (decode e) = ∅` is *not* available — it is exactly what the singular-set
manuscript declines to assume — so the covered-origin fact cannot be upgraded to a statement about
all points by any amount of work here.

A strictly stronger sibling already exists,
`Spatial.NullBoundaryRoots.ae_notMem_boundaryMask_of_massTransport`, which also excludes the cell
frontiers; it is not used here only because it carries the heavier frontier transport, and it
already discharges its covering half through `Spatial.ae_zero_mem_iUnion_cell` in exactly the way
`ae_zero_notMem_uncoveredSet` does.  Anyone needing the frontier too should reuse that one instead
of strengthening this.
-/

set_option autoImplicit false

open MeasureTheory Set

namespace ReflectedGMS

open Code EnvironmentLaws

/-- A point lying in some cell lies outside the uncovered set.  `uncoveredSet F` is by definition
the complement of the union of the cells, so this only removes a double negation. -/
theorem notMem_uncoveredSet_of_mem_iUnion {V : Type*} (F : IndexedCells V) {z : Plane}
    (hz : z ∈ ⋃ v, (F.cell v : Set Plane)) : z ∉ uncoveredSet F := by
  intro hc
  exact hc hz

/-- **The origin lies in a cell, almost surely** — the manuscript's Lemma 2.4 in the form its
consumers take.

Under the earlier manuscript's covering clause `⋃ v, cell v = Set.univ` this held at every point
of every environment and no mass transport was involved.  Under the weakened clause it is a
genuinely probabilistic statement: `Spatial.ae_zero_mem_iUnion_cell` transports the mass of the
uncovered set to the origin through the kernel `|w - z|⁻²`, and the `H¹`-nullity of the uncovered
set of each environment — hence its Lebesgue nullity, `volume_uncoveredSet` — makes the incoming
side vanish. -/
theorem ae_zero_notMem_uncoveredSet (ν : Measure Env) (hν : MassTransport ν) :
    ∀ᵐ e : Env ∂ν, (0 : Plane) ∉ uncoveredSet (decode e) := by
  have huncov : ∀ᵐ e : Env ∂ν, volume ((⋃ v, ((decode e).cell v : Set Plane))ᶜ) = 0 :=
    Filter.Eventually.of_forall fun e => volume_uncoveredSet (decode_geometry e)
  filter_upwards [Spatial.ae_zero_mem_iUnion_cell ν hν huncov] with e he
  exact notMem_uncoveredSet_of_mem_iUnion (decode e) he

end ReflectedGMS
