/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module BouRabeeGwynne.TilingClockedExcursion at commit fdb5cad;
   only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.BouRabeeGwynne.TilingWalkRegionEmbedding

/-! The actual ball excursion of the ambient tiling walk has the full
clocked excursion law in the ball's own finite closed graph region. -/

open MeasureTheory ProbabilityTheory Set

namespace BouRabeeGwynne

namespace FiniteConductanceNetwork

lemma exitTime_comp {X Y : Type*} (f : X → Y) (B : Set Y) (ω : ℕ → X) :
    exitTime B (fun n => f (ω n)) = exitTime (f ⁻¹' B) ω := rfl

end FiniteConductanceNetwork

namespace ClockedWalkExcursion

lemma ofWalk_comp {d : ℕ} {X Y : Type*}
    [Fintype X] [MeasurableSpace X] [MeasurableSingletonClass X]
    [Fintype Y] [MeasurableSpace Y] [MeasurableSingletonClass Y]
    (pos : Y → Euc d) (f : X → Y) (B : Set Y) (ω : ℕ → X) :
    ofWalk pos B (fun n => f (ω n)) = ofWalk (pos ∘ f) (f ⁻¹' B) ω := by
  unfold ofWalk
  rw [FiniteConductanceNetwork.exitTime_comp]
  rfl

end ClockedWalkExcursion

namespace OrthogonalTiling

variable {d : ℕ} (T : OrthogonalTiling d) {R S : Set T.V}
  [Fintype R] [Fintype S]
  [MeasurableSpace R] [MeasurableSingletonClass R]
  [MeasurableSpace S] [MeasurableSingletonClass S]

theorem finiteNetwork_clockedExcursion_inclusion (hRS : R ⊆ S) (B : Set T.V)
    (hneighbors : ∀ v : R, (v : T.V) ∈ B → T.neighbors v ⊆ R)
    (hR : ∀ v ∈ (Subtype.val ⁻¹' B : Set R),
      0 < (T.finiteNetwork R).totalConductance v)
    (hS : ∀ v ∈ (Subtype.val ⁻¹' B : Set S),
      0 < (T.finiteNetwork S).totalConductance v) (v : R) :
    (T.finiteNetwork R).clockedWalkExcursionKernel (fun w => T.pos w)
      (Subtype.val ⁻¹' B) hR v =
      (T.finiteNetwork S).clockedWalkExcursionKernel (fun w => T.pos w)
        (Subtype.val ⁻¹' B) hS (T.regionInclusion hRS v) := by
  change ((T.finiteNetwork R).trajectoryLaw (Subtype.val ⁻¹' B) hR v).map
      (ClockedWalkExcursion.ofWalk (fun w : R => T.pos w) (Subtype.val ⁻¹' B)) =
    ((T.finiteNetwork S).trajectoryLaw (Subtype.val ⁻¹' B) hS
      (T.regionInclusion hRS v)).map
      (ClockedWalkExcursion.ofWalk (fun w : S => T.pos w) (Subtype.val ⁻¹' B))
  have hpath : Measurable (fun ω : ℕ → R => fun n => T.regionInclusion hRS (ω n)) :=
    Measurable.of_eval fun n =>
      (measurable_of_finite (T.regionInclusion hRS)).comp (measurable_pi_apply n)
  rw [← T.finiteNetwork_trajectoryLaw_inclusion hRS B hneighbors hR hS v,
    Measure.map_map (ClockedWalkExcursion.measurable_ofWalk
      (fun w : S => T.pos w) (Subtype.val ⁻¹' B)) hpath]
  congr 1

/-- Actual sampled excursions in an ambient region, identified with the
ball-region kernel including their integer duration and visited vertices.
The geometric argument applies to any nested domains. -/
theorem ambient_trajectoryLaw_map_clockedExcursion
    {U W : Set (Euc d)} (hUW : U ⊆ W)
    [Fintype (T.closedVertices U)] [Fintype (T.closedVertices W)]
    [MeasurableSpace (T.closedVertices U)] [MeasurableSingletonClass (T.closedVertices U)]
    [MeasurableSpace (T.closedVertices W)] [MeasurableSingletonClass (T.closedVertices W)]
    (hU : ∀ v ∈ T.finiteInterior U,
      0 < (T.finiteNetwork (T.closedVertices U)).totalConductance v)
    (hW : ∀ v ∈ T.finiteInterior W,
      0 < (T.finiteNetwork (T.closedVertices W)).totalConductance v)
    (v : T.closedVertices U) :
    ((T.finiteNetwork (T.closedVertices W)).trajectoryLaw (T.finiteInterior W) hW
      (T.regionInclusion (T.closedVertices_mono hUW) v)).map
        (ClockedWalkExcursion.ofWalk (fun w : T.closedVertices W => T.pos w)
          {w | T.pos w ∈ U}) =
      (T.finiteNetwork (T.closedVertices U)).clockedWalkExcursionKernel
        (fun w => T.pos w) (T.finiteInterior U) hU v := by
  let hB : ∀ w ∈ ({w : T.closedVertices W | T.pos w ∈ U}),
      0 < (T.finiteNetwork (T.closedVertices W)).totalConductance w :=
    fun w hw => hW w (hUW hw)
  calc
    _ = (T.finiteNetwork (T.closedVertices W)).clockedWalkExcursionKernel
        (fun w => T.pos w) {w | T.pos w ∈ U} hB
        (T.regionInclusion (T.closedVertices_mono hUW) v) :=
      (T.finiteNetwork (T.closedVertices W)).trajectoryLaw_map_clockedExcursion
        (fun w => T.pos w) (A := T.finiteInterior W) (B := {w | T.pos w ∈ U})
        (fun _ hw => hUW hw) hW hB _
    _ = _ := (T.finiteNetwork_clockedExcursion_inclusion
      (T.closedVertices_mono hUW) (T.interiorVertices U)
      (fun w hw _ hwa => T.neighbor_mem_closedVertices hw hwa) hU hB v).symm

end OrthogonalTiling
end BouRabeeGwynne
