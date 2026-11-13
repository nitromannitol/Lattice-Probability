/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module MatedCRTHarmonic.GMS4.CellScalingCellModelCoupling at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.MatedCRTHarmonic.GMS4.CellGraphInterface
import LatticeProb.Bonanno.MatedCRTHarmonic.CellScaling.L27Bridge

/-!
# Cone realization to the cell-graph coupling interface

The cone realization already has the cell model structure, the coupled Brownian path, and the
all-mesh multigraph identity. This adapter packages those existing fields in
`GMS4..CellModelGraphCoupling`; the only transport is the unit-cell equality needed to restate
The frozen coupling for L27's cell function. It consumes no Proposition 2.10 or Proposition 4.10
probability estimate: `coupling`, `meshGraph_eq`, `cell_eq`, and `meshCell_eq` are structural fields
of the existing cell model and cone realization.
-/

set_option autoImplicit false

noncomputable section

namespace MatedCRTHarmonic.CellScaling

open MatedCRTHarmonic
open MeasureTheory

variable {γ : ℝ} {M : MesoModel.MatedCRTUnitMesoModel γ}

/-- Package a cone realization as the cell-model graph coupling, using the identity map on
The shared sample space. -/
def ConeRealization.toCellModelGraphCoupling (D : ConeRealization M)
    (hpar : AreaParametrization D) :
    GMS4.MoTAdapter.CellModelGraphCoupling (D.toCellModel hpar) := by
  refine
    { family := M.coupled.family
      modelMap := fun ω => ω
      measurePreserving_modelMap := MeasurePreserving.id M.coupled.family.P
      bm := M.coupled.bm
      coupling := ?_
      meshGraph_eq := M.coupled.meshGraph_eq
      meshCell_eq := ?_ }
  · refine
      { measurable_bm := M.coupled.coupling.measurable_bm
        law := M.coupled.coupling.law
        cellular := ?_ }
    filter_upwards [M.coupled.coupling.cellular, D.cell_eq] with ω hcoupling hcell
    obtain ⟨hlf, H, hH⟩ := hcoupling
    refine ⟨hlf, H, ?_⟩
    rw [hH]
    funext x
    rw [ConeRealization.toCellModel_cell]
    simpa [meshCells] using hcell x
  · exact D.ae_familyCell_eq_toCellModel hpar

end MatedCRTHarmonic.CellScaling

