/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module BouRabeeGwynne.AmbientStoppedWalkLaw at commit fdb5cad;
   local imports are relocated and StoppedCurveLaws supplies the stopped-law predicate. -/
import LatticeProb.Bonanno.BouRabeeGwynne.TilingClockedExcursion
import LatticeProb.Bonanno.BouRabeeGwynne.StoppedCurveLaws

/-! Identify the theorem's stopped tiling-walk law with the stopped curve
extracted from the finite ambient walk used in the actual coupling. -/

open MeasureTheory ProbabilityTheory Set

namespace BouRabeeGwynne

namespace ClockedWalkExcursion

lemma map_project_ofWalk {d : ℕ} {V : Type*} [Fintype V]
    [MeasurableSpace V] [MeasurableSingletonClass V]
    (ρ : Measure (ℕ → V)) (pos : V → Euc d) (A : Set V) :
    (ρ.map (ofWalk pos A)).map (CurveSpace.project ∘ curve) =
      ρ.map (stoppedPolygonalCurve pos A) := by
  rw [Measure.map_map (CurveSpace.continuous_project.measurable.comp measurable_curve)
    (measurable_ofWalk pos A)]
  congr 1
  funext ω
  change CurveSpace.project (curve (ofWalk pos A ω)) = _
  rw [curve_ofWalk]
  rfl

end ClockedWalkExcursion

namespace OrthogonalTiling

theorem isStoppedTilingWalkLaw_eq_ambient {d : ℕ} (T : OrthogonalTiling d)
    (U : Set (Euc d)) (S : Set T.V) [Fintype S]
    [MeasurableSpace S] [MeasurableSingletonClass S]
    (hUS : T.closedVertices U ⊆ S) (A : Set S)
    (hUA : {v : S | T.pos v ∈ U} ⊆ A)
    (hA : ∀ v ∈ A, 0 < (T.finiteNetwork S).totalConductance v)
    (v : S) {μ : Measure (CurveSpace d)}
    (hμ : IsStoppedTilingWalkLaw T U v.val μ) :
    μ = ((T.finiteNetwork S).trajectoryLaw A hA v).map
      (stoppedPolygonalCurve (fun w : S => T.pos w) {w : S | T.pos w ∈ U}) := by
  obtain ⟨R, hR, h⟩ := hμ
  let : MeasurableSpace R := ⊤
  obtain ⟨hpos, start, hstart, _, _, _, hmap⟩ := h
  have hRS : (R : Set T.V) ⊆ S := by
    rw [hR]
    rintro w (hw | hw)
    · exact hUS hw
    · have hwv : w = v.val := Set.mem_singleton_iff.mp hw
      exact hwv.symm ▸ v.property
  let hB : ∀ w ∈ ({w : S | T.pos w ∈ U}),
      0 < (T.finiteNetwork S).totalConductance w :=
    fun w hw => hA w (hUA hw)
  have hneighbors : ∀ w : R, (w : T.V) ∈ T.interiorVertices U → T.neighbors w ⊆ (R : Set T.V) := by
    intro w hw u hwu
    rw [hR]
    exact Or.inl (T.neighbor_mem_closedVertices hw hwu)
  have hfull := T.finiteNetwork_clockedExcursion_inclusion hRS (T.interiorVertices U)
    hneighbors hpos hB start
  have hstartS : T.regionInclusion hRS start = v := Subtype.ext hstart
  rw [hstartS] at hfull
  have habs := (T.finiteNetwork S).trajectoryLaw_map_clockedExcursion
    (fun w : S => T.pos w) hUA hA hB v
  calc
    μ = (((T.finiteNetwork (R : Set T.V)).trajectoryLaw
        {w : R | T.pos w ∈ U} hpos start).map
          (ClockedWalkExcursion.ofWalk (fun w : R => T.pos w) {w : R | T.pos w ∈ U})).map
            (CurveSpace.project ∘ ClockedWalkExcursion.curve) := by
      rw [ClockedWalkExcursion.map_project_ofWalk]
      exact hmap
    _ = ((T.finiteNetwork S).clockedWalkExcursionKernel (fun w : S => T.pos w)
        {w : S | T.pos w ∈ U} hB v).map
          (CurveSpace.project ∘ ClockedWalkExcursion.curve) :=
      congrArg (fun ν : Measure (ClockedWalkExcursion d) =>
        ν.map (CurveSpace.project ∘ ClockedWalkExcursion.curve)) hfull
    _ = (((T.finiteNetwork S).trajectoryLaw A hA v).map
        (ClockedWalkExcursion.ofWalk (fun w : S => T.pos w) {w : S | T.pos w ∈ U})).map
          (CurveSpace.project ∘ ClockedWalkExcursion.curve) :=
      congrArg (fun ν : Measure (ClockedWalkExcursion d) =>
        ν.map (CurveSpace.project ∘ ClockedWalkExcursion.curve)) habs.symm
    _ = _ := ClockedWalkExcursion.map_project_ofWalk _ _ _

end OrthogonalTiling
end BouRabeeGwynne
