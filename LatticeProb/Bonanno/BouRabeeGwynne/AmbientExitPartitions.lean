/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module BouRabeeGwynne.AmbientExitPartitions at commit fdb5cad17d11550228cf8dbaf6216e69fc3d2d82;
   selected declaration, with local imports adapted. -/
import LatticeProb.Bonanno.BouRabeeGwynne.Section4BallExitLevyProkhorov
import LatticeProb.Bonanno.BouRabeeGwynne.TilingClockedExcursion

open MeasureTheory ProbabilityTheory Set Filter Metric
open scoped Classical Topology

namespace BouRabeeGwynne
namespace OrthogonalTiling

set_option linter.style.haveILetI false

theorem spatialExitProbability_eq_ambient_discreteHarmonicMeasure {d : ℕ}
    (T : OrthogonalTiling d) {U W : Set (Euc d)} (hUW : U ⊆ W)
    (hg : T.HasFiniteAccessibleRegion U)
    [Fintype (T.closedVertices W)] [MeasurableSpace (T.closedVertices W)]
    [MeasurableSingletonClass (T.closedVertices W)]
    (hB : ∀ v ∈ ({v : T.closedVertices W | T.pos v ∈ U}),
      0 < (T.finiteNetwork (T.closedVertices W)).totalConductance v)
    (v : T.closedVertices W) (hv : T.pos v ∈ U) :
    (T.spatialExitProbability U hg v
      (T.interiorVertices_subset_closedVertices U hv) : Measure (Euc d)) =
      ((T.finiteNetwork (T.closedVertices W)).discreteHarmonicMeasure
        {w : T.closedVertices W | T.pos w ∈ U} hB v).map
          (fun w : T.closedVertices W => T.pos w) := by
  letI : Fintype (T.closedVertices U) := hg.choose.fintype
  letI : MeasurableSpace (T.closedVertices U) := ⊤
  let hR := (T.finiteNetwork (T.closedVertices U)).totalConductance_pos_of_boundaryAccessible
    (T.finiteInterior U) hg.choose_spec
  let vR : T.closedVertices U := ⟨v.val, T.interiorVertices_subset_closedVertices U hv⟩
  have hfull := T.finiteNetwork_clockedExcursion_inclusion (T.closedVertices_mono hUW)
    (T.interiorVertices U) (fun w hw _ hwa => T.neighbor_mem_closedVertices hw hwa) hR hB vR
  have hend := congrArg (fun ν : Measure (ClockedWalkExcursion d) =>
    ν.map ClockedWalkExcursion.endPoint) hfull
  rw [(T.finiteNetwork (T.closedVertices U)).clockedWalkExcursionKernel_endPoint
      (d := d) (fun w : T.closedVertices U => T.pos w)
      (Subtype.val ⁻¹' T.interiorVertices U) hR vR,
    (T.finiteNetwork (T.closedVertices W)).clockedWalkExcursionKernel_endPoint
      (d := d) (fun w : T.closedVertices W => T.pos w)
      (Subtype.val ⁻¹' T.interiorVertices U) hB (T.regionInclusion (T.closedVertices_mono hUW) vR)] at hend
  exact hend

end OrthogonalTiling
end BouRabeeGwynne
