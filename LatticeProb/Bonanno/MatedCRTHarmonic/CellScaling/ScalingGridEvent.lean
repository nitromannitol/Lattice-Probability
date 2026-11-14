/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source modules MatedCRTHarmonic.CellScaling.Model and Scaling at commit fdb5cad;
   selected declarations with local imports adapted. -/
import LatticeProb.Bonanno.MatedCRTHarmonic.CellScaling.ScalingDilation
import LatticeProb.Bonanno.MatedCRTHarmonic.CellScaling.ScalingDeterministic
import LatticeProb.Bonanno.MatedCRTHarmonic.MesoModel.TransferScalingGraph

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set Metric
open scoped ENNReal NNReal Pointwise

namespace MatedCRTHarmonic.CellScaling

open MatedCRTHarmonic

/-- The data event "the mesh-`2^{-k}` configuration of `(bm, η)` satisfies the scaled-grid estimate event at scale 1":
`G^{2^{-k}}(bm)` is locally finite and `RawScaledGridControl` holds for it with the cells `η([2^{-k}(x−1), 2^{-k}x])`. -/
def meshGridGood (k : ℕ) (χ β q ρ p : ℝ) : Set (MatedCRT.Path2 × C(ℝ, ℂ)) :=
  {d | ∃ hlf : MatedCRT.IsLocallyFinite (CellFamily.mesh k) d.1,
    RawScaledGridControl (MatedCRT.graph (CellFamily.mesh k) d.1 hlf) (meshCells (CellFamily.mesh k) d.2)
      1 (CellFamily.mesh k) χ β q ρ p}

/-- **Cell-configuration identity, event form** (deterministic): the unit-mesh scaled-grid event of `(Z, η)` at scale
`c` is the mesh-`2^{-k}` event at scale `1` of the rescaled data `(2^{-k/2} Z(2^k ·), c⁻¹ η(2^k ·))`. -/
theorem rawScaledGridControl_unit_iff_meshGridGood (k : ℕ) (Z : MatedCRT.Path2)
    (hlf : MatedCRT.IsLocallyFinite 1 Z) (η : C(ℝ, ℂ)) {c : ℝ} (hc : 0 < c) (χ β q ρ p : ℝ) :
    RawScaledGridControl (MatedCRT.graph 1 Z hlf) (fun x => η '' Icc ((x : ℝ) - 1) x) c
        (CellFamily.mesh k) χ β q ρ p ↔
      (brownRescale ((2 : ℝ) ^ k) Z, coneRescaleCurve c ((2 : ℝ) ^ k) η) ∈ meshGridGood k χ β q ρ p := by
  set Zb := brownRescale ((2 : ℝ) ^ k) Z with hZb
  have hpath : MesoModel.unitRescalePath (CellFamily.mesh k) Zb = Z := unitRescalePath_brownRescale k Z
  have hlfb : MatedCRT.IsLocallyFinite (CellFamily.mesh k) Zb := by
    rw [MesoModel.isLocallyFinite_unitRescalePath_iff (mesh_pos k), hpath]
    exact hlf
  have hlf1 : MatedCRT.IsLocallyFinite 1 (MesoModel.unitRescalePath (CellFamily.mesh k) Zb) := by
    rw [hpath]; exact hlf
  have hgraph := MesoModel.graphCast_eq_unitRescalePath (mesh_pos k) Zb hlfb hlf1
  have hcells := meshCells_coneRescaleCurve k c η
  constructor
  · intro h
    refine ⟨hlfb, ?_⟩
    rw [hcells, rawScaledGridControl_cast_iff (MesoModel.edgeTypeEq_unitRescalePath (mesh_pos k) Zb) hgraph,
      rawScaledGridControl_graph_congr hpath hlf1 hlf, rawScaledGridControl_smul_iff _ _ hc, mul_one]
    exact h
  · rintro ⟨hlfb', h⟩
    rw [hcells, rawScaledGridControl_cast_iff (MesoModel.edgeTypeEq_unitRescalePath (mesh_pos k) Zb)
      (MesoModel.graphCast_eq_unitRescalePath (mesh_pos k) Zb hlfb' hlf1),
      rawScaledGridControl_graph_congr hpath hlf1 hlf, rawScaledGridControl_smul_iff _ _ hc, mul_one] at h
    exact h

end MatedCRTHarmonic.CellScaling
