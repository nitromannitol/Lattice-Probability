/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module MatedCRTHarmonic.GMS4.CellGraphInterface at commit fdb5cad; only the module paths of local imports are changed.
   Declarations, examples and checks that the copied results do not use are omitted. -/
import LatticeProb.Bonanno.MatedCRTHarmonic.GMSLemma27.CellModel
import LatticeProb.Bonanno.MatedCRTHarmonic.CellFamily.ProducersCellCoupling

/-!
# Cell-model to random-cell-family interface

This is the structural part of the mating-of-trees input used by [18] Proposition 2.10. The
source says “Z evolves as a correlated two-dimensional Brownian motion”
([18]) and identifies Brownian adjacency with
shared cell-boundary arcs ([18]; DMS14 §8.2). Its multigraph convention says that
“x₁ and x₂ are connected by two edges” when both boundary-length criteria hold and the indices are more than ε apart ([18]); the maps at all ε are coupled using the same Brownian motion. The cell
convention is `H_x^ε = η([x − ε, x])` ([18]).

These source facts are represented here by separate outputs: unit `IsCellCoupling`, the
all-dyadic-mesh multigraph identity, and the all-dyadic-mesh cell identity. The source does not
state Lean's complete frozen `CellularEmbedding` predicate verbatim; its realization as that exact
predicate remains part of the named coupling output. In particular, the unit frozen coupling
does not imply either all-mesh identity. The theorems below only adapt those supplied outputs to
CellFamily/L27 APIs; they are bridge constructions, not proofs of the SLE inputs. A total
`CellFamily.RandomCellFamily` records a chosen version on exceptional outcomes and makes no geometric
assertion there.

The concrete producer route is already named elsewhere: `MoTInput.matedMeshFamily` builds the
all-mesh multigraph-coupled family from the mating-of-trees bundle, and
`CellScaling.ConeRealization.toCellModelGraphCoupling` packages that family here. These are
SLE/LQG coupling outputs. The SLE-free DMS14 inputs Lemma A.10 and Proposition 4.13(i) do not
belong to this structure; their producer paths are respectively `ConeLemmaA10/*` and
`ConeScaling/*`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set

namespace MatedCRTHarmonic.GMS4.MoTAdapter

open MatedCRTHarmonic

/-- The output bundle connecting an L27 SLE/LQG `CellModel` to the mesh-indexed graph family
used by Proposition 2.10.

* `coupling` is the unit-mesh source input. [18] says that the boundary-length pair has correlated
  Brownian law, and that the mated-CRT graph is the cell structure graph with
  boundary-arc adjacency. The frozen `MatedCRT.IsCellCoupling` also requires the
  exact Lean `CellularEmbedding`; [18] calls the map an embedding but does not enumerate that full
  predicate. Supplying that frozen proposition is therefore explicitly part of this output.
* `meshGraph_eq` is a separate all-dyadic-mesh source input. [18] couples the whole collection
  using one Brownian motion; its graph convention includes two edges for a pair
  satisfying both criteria at separation greater than ε. This field asserts the
  corresponding almost-sure equality of complete multigraphs, including multiplicities.
* `meshCell_eq` is another separate all-mesh source input: [18] defines
  `H_x^ε := η([x − ε, x])`. It identifies the family cells with these curve
  segments on the coupled realization.

The same-outcome, all-mesh equalities and the measure-preserving `modelMap` are named bundle
outputs, not consequences of the frozen unit coupling alone. The theorems below merely transport
these supplied outputs to CellFamily/L27 APIs; they are bridge constructions, not SLE proofs. -/
structure CellModelGraphCoupling {gamma : ℝ} (M : GMSLemma27.CellModel gamma) where
  family : CellFamily.RandomCellFamily
  modelMap : family.Ω → M.Ω
  measurePreserving_modelMap : MeasurePreserving modelMap family.P M.P
  bm : family.Ω → MatedCRT.Path2
  /-- Unit-mesh output: the source's boundary-length Brownian law and
  boundary-arc cell-graph identification, packaged as the frozen interface. The
  latter's full `CellularEmbedding` fields are a formalization-strengthening supplied by. -/
  coupling : MatedCRT.IsCellCoupling gamma family.P bm
    (fun omega x => M.cell 1 (modelMap omega) x)
  /-- Separate all-mesh output: [18] couples its whole family of maps with the same Brownian
  motion and says “x₁ and x₂ are connected by two edges” when both criteria hold at distance
  greater than ε. This is full multigraph equality, including multiplicity. -/
  meshGraph_eq : CellFamily.MatedCRTMultigraphIdentification family bm
  /-- Separate all-mesh output for the source convention `H_x^ε = η([x − ε, x])`. -/
  meshCell_eq : ∀ k, ∀ᵐ omega ∂family.P, ∀ x,
    (family.H k omega).cell x = M.cell (CellFamily.mesh k) (modelMap omega) x

namespace CellModelGraphCoupling

variable {gamma : ℝ} {M : GMSLemma27.CellModel gamma}

/-- The full multigraph identification implies the adjacency-only view used by the annulus-disconnection estimate. -/
theorem graphIdentification (S : CellModelGraphCoupling M) :
    CellFamily.MatedCRTGraphIdentification S.family S.bm :=
  S.meshGraph_eq.graphIdentification

/-- Forget the L27 realization and retain the graph/cell package used by the cell-family estimate. -/
def toCellCoupledRandomFamily (S : CellModelGraphCoupling M) :
    CellFamily.CellCoupledRandomFamily gamma where
  family := S.family
  bm := S.bm
  cell := fun omega x => M.cell 1 (S.modelMap omega) x
  coupling := S.coupling
  graphIdentification := S.graphIdentification

/-- The random cellular-embedding family consumed by the family-level Proposition 2.10 event. -/
def toRandomCellFamily (S : CellModelGraphCoupling M) : CellFamily.RandomCellFamily :=
  CellFamily.RandomCellFamily.ofCellCoupling S.toCellCoupledRandomFamily

/-- The adapter preserves the underlying family definitionally. -/
theorem toRandomCellFamily_eq (S : CellModelGraphCoupling M) :
    S.toRandomCellFamily = S.family := rfl

/-- The curve-segment cell identification in the exact shape used by L27 consumers. -/
theorem ae_cell_eq (S : CellModelGraphCoupling M) (k : ℕ) :
    ∀ᵐ omega ∂S.toRandomCellFamily.P, ∀ x,
      (S.toRandomCellFamily.H k omega).cell x =
        M.cell (CellFamily.mesh k) (S.modelMap omega) x :=
  S.meshCell_eq k

/-- At each mesh, the cell and full-multigraph identifications hold on one common full-measure
event. This is the aligned input needed by density statements, whose degree term sees edge
multiplicities and loops. -/
theorem ae_cell_graph_eq (S : CellModelGraphCoupling M) (k : ℕ) :
    ∀ᵐ omega ∂S.toRandomCellFamily.P,
      (∀ x, (S.toRandomCellFamily.H k omega).cell x =
        M.cell (CellFamily.mesh k) (S.modelMap omega) x) ∧
      ∃ (hE : S.toRandomCellFamily.E k omega =
          MatedCRT.Edge (CellFamily.mesh k) (S.bm omega))
        (hlf : MatedCRT.IsLocallyFinite (CellFamily.mesh k) (S.bm omega)),
        cast (congrArg (LFMultigraph ℤ) hE) (S.toRandomCellFamily.G k omega) =
          MatedCRT.graph (CellFamily.mesh k) (S.bm omega) hlf :=
  (S.meshCell_eq k).and (S.meshGraph_eq k)

end CellModelGraphCoupling

end MatedCRTHarmonic.GMS4.MoTAdapter

