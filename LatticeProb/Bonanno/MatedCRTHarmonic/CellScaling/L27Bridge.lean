/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module MatedCRTHarmonic.CellScaling.L27Bridge at commit fdb5cad; only the module paths of local imports are changed.
   Declarations, examples and checks that the copied results do not use are omitted. -/
import Mathlib
import LatticeProb.Bonanno.MatedCRTHarmonic.GMSLemma27.CellModel
import LatticeProb.Bonanno.MatedCRTHarmonic.GMSLemma27.Consumers
import LatticeProb.Bonanno.MatedCRTHarmonic.CellFamily.BadEventInterfaces
import LatticeProb.Bonanno.MatedCRTHarmonic.CellScaling.Model

/-!
# Bridge to Lemma 2.7's cell-model structure

`GMSLemma27.CellModel γ` ([18] §1.4: field, LQG area, area-parameterized curve with `η(0) = 0`) is
the abstract cell model on which [18] Lemmas 2.7 and 2.8 are proved. A cone realization of the mesoscopic construction's unit-mesh model,
with its area parameterization, *is* such a cell model: field `h = coneFieldOf γ X B B'`, area `A^γ_h`, curve `η`.
Its mesh-`2^{-k}` cells are the cells of `M`'s random family (a.s.), so Lemma 2.7's Lemma 2.7 for `toCellModel` speaks about
the cells the scaled-grid estimate and the mesoscopic construction use. Since the scaled-grid estimate bundle consumes Lemma 2.7 in bad-event form;
`lemma27CellDiamBad_of_cone` produces exactly that bundle field from Lemma 2.7's inputs.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set Metric
open scoped ENNReal NNReal

namespace MatedCRTHarmonic.CellScaling

open MatedCRTHarmonic

namespace ConeRealization

variable {γ : ℝ} {M : MesoModel.MatedCRTUnitMesoModel γ}

/-- The cone realization as an Lemma 2.7 cell model (needs the area parameterization). -/
def toCellModel (D : ConeRealization M) (hpar : AreaParametrization D) : GMSLemma27.CellModel γ where
  Ω := M.coupled.family.Ω
  P := M.coupled.family.P
  field := D.field
  area := D.area
  curve := fun ω => D.curve ω
  ae_continuous_curve := Filter.Eventually.of_forall fun ω => (D.curve ω).continuous
  ae_curve_zero := by
    filter_upwards [hpar] with ω hω
    exact hω.1
  ae_area_curve := by
    filter_upwards [hpar] with ω hω
    exact hω.2

theorem toCellModel_cell (D : ConeRealization M) (hpar : AreaParametrization D) (ε : ℝ)
    (ω : M.coupled.family.Ω) (x : ℤ) :
    (D.toCellModel hpar).cell ε ω x = meshCells ε (D.curve ω) x := rfl

/-- The cells of `M`'s mesh-`2^{-k}` random family are, a.s., the Lemma 2.7 cells of mesh `2^{-k}`. -/
theorem ae_familyCell_eq_toCellModel (D : ConeRealization M) (hpar : AreaParametrization D) (k : ℕ) :
    ∀ᵐ ω ∂M.coupled.family.P, ∀ x : ℤ,
      (M.coupled.family.H k ω).cell x = (D.toCellModel hpar).cell (CellFamily.mesh k) ω x := by
  filter_upwards [D.meshCell_eq k] with ω hω x
  rw [hω x, toCellModel_cell]

end ConeRealization

variable {γ : ℝ}

/-- **Bad-event producer of `Lemma27CellDiamBad F q ρ`** : [18] Lemma 2.7 on the closed
disk `B̄_ρ(0)` (applied at `ρ' = (1+ρ)/2`, the interface analysis note N1) as an outer-measure bound on the failure event, for a random
cell family whose cells are, along a measure-preserving map `e`, almost surely the cells of an Lemma 2.7 cell model. It is
`GMSLemma27.lemma27CellDiam_of_cellModel` without the final good-event step: `lemma27_cells_transfer` already
bounds the failure event. Inputs: those of `lemma27` (`SegmentsContainBalls`: ; `GMCLowerTail`,
`AreaDominatesWholePlaneGFF`: SLE-free). -/
theorem lemma27CellDiamBad_of_cellModel {M : GMSLemma27.CellModel γ}
    (hSLE : GMSLemma27.SegmentsContainBalls M) (hGMC : GMSLemma27.GMCLowerTail γ)
    (hdom : GMSLemma27.AreaDominatesWholePlaneGFF M) (hγ : 0 < γ)
    (F : CellFamily.RandomCellFamily) (e : F.Ω → M.Ω) (he : MeasurePreserving e F.P M.P)
    (hcell : ∀ k, ∀ᵐ ω ∂F.P, ∀ x, (F.H k ω).cell x = M.cell (CellFamily.mesh k) (e ω) x)
    {q ρ : ℝ} (hq : 0 < q) (hq' : q < 2 / (2 + γ) ^ 2) (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1) :
    CellFamily.Lemma27CellDiamBad F q ρ := by
  have hpos := GMSLemma27.lemma27Exponent_pos hγ hq hq'
  obtain ⟨C, -, hC⟩ := GMSLemma27.lemma27_cells_transfer M hSLE hGMC hdom hγ e he
    (fun k ω x => (F.H k ω).cell x) hcell hq hq' (ρ := (1 + ρ) / 2) ⟨by linarith, by linarith⟩
    (α := GMSLemma27.lemma27Exponent q γ / 2) (by linarith)
  refine ⟨GMSLemma27.lemma27Exponent q γ / 2, by linarith, C, fun k => (measure_mono ?_).trans (hC k)⟩
  refine compl_subset_compl.mpr ?_
  intro ω hω x hx
  refine hω x ?_
  obtain ⟨w, hw1, hw2⟩ := hx
  refine ⟨w, hw1, ?_⟩
  rw [mem_closedBall, dist_zero_right] at hw2
  rw [mem_ball, dist_zero_right]
  linarith

end MatedCRTHarmonic.CellScaling
