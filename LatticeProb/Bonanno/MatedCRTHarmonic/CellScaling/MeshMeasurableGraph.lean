/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module MatedCRTHarmonic.CellScaling.MeshMeasurableGraph at commit fdb5cad; local imports and deprecated lemma names are updated. -/
import LatticeProb.Bonanno.MatedCRTHarmonic.CellScaling.Model
import LatticeProb.Bonanno.MatedCRTHarmonic.MatedCRT.GraphMeasurability

/-!
# Measurability of local finiteness for the mesh graph

The finite-degree condition is a countable union of finite candidate-edge certificates. The
candidate edges are the fixed countable labels used by `edgePredicate`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set

namespace MatedCRTHarmonic.CellScaling

private abbrev MeshEdgeCode := ℤ × ℤ × Bool

private def meshIncidentCode (x : ℤ) (e : MeshEdgeCode) : Prop :=
  e.1 = x ∨ e.2.1 = x

private def rawIncidentEdges (ε : ℝ) (ω : MatedCRT.Path2) (x : ℤ) : Set MeshEdgeCode :=
  {e | MatedCRT.IsEdge ε ω e ∧ meshIncidentCode x e}

private theorem rawIncidentEdges_finite_iff (ε : ℝ) (ω : MatedCRT.Path2) (x : ℤ) :
    (rawIncidentEdges ε ω x).Finite ↔
      ∃ T : Finset MeshEdgeCode, ∀ e, e ∈ rawIncidentEdges ε ω x → e ∈ T := by
  constructor
  · intro h
    exact ⟨h.toFinset, fun e he => h.mem_toFinset.mpr he⟩
  · rintro ⟨T, hT⟩
    exact (T.finite_toSet).subset hT

private theorem meshIncident_subtype_finite_iff (ε : ℝ) (ω : MatedCRT.Path2) (x : ℤ) :
    {e : MatedCRT.Edge ε ω | meshIncidentCode x e.1}.Finite ↔
      (rawIncidentEdges ε ω x).Finite := by
  have himage : Subtype.val '' {e : MatedCRT.Edge ε ω | meshIncidentCode x e.1} =
      rawIncidentEdges ε ω x := by
    ext e
    constructor
    · rintro ⟨⟨e, he⟩, hinc, rfl⟩
      exact ⟨he, hinc⟩
    · rintro ⟨he, hinc⟩
      exact ⟨⟨e, he⟩, hinc, rfl⟩
  constructor
  · intro h
    rw [← himage]
    exact h.image Subtype.val
  · intro h
    apply Set.Finite.of_finite_image (f := Subtype.val) (s := {e : MatedCRT.Edge ε ω |
      meshIncidentCode x e.1}) ?_ ?_
    · simpa only [himage] using h
    · intro a ha b hb hab
      exact Subtype.ext hab

private theorem measurableSet_meshIsEdge (ε : ℝ) (e : MeshEdgeCode) :
    MeasurableSet {ω : MatedCRT.Path2 | MatedCRT.IsEdge ε ω e} := by
  have hEval : Measurable (fun ω : MatedCRT.Path2 => MatedCRT.edgePredicate ε ω e) :=
    (MatedCRT.matedCRT_edgePredicate_measurable_holds ε).eval (a := e)
  have hSet : {ω : MatedCRT.Path2 | MatedCRT.IsEdge ε ω e} =
      {ω | MatedCRT.edgePredicate ε ω e = true} := by
    ext ω
    simp [MatedCRT.edgePredicate]
  rw [hSet]
  exact (measurableSet_singleton true).preimage hEval

/-- Local finiteness of the mated-CRT graph at fixed mesh is a Borel property of the
path, independently of whether local finiteness holds almost surely for a chosen path law. -/
theorem measurableSet_matedCRT_isLocallyFinite (ε : ℝ) :
    MeasurableSet {ω : MatedCRT.Path2 | MatedCRT.IsLocallyFinite ε ω} := by
  classical
  rw [show {ω : MatedCRT.Path2 | MatedCRT.IsLocallyFinite ε ω} =
      ⋂ x : ℤ, ⋃ T : Finset MeshEdgeCode, ⋂ e : MeshEdgeCode,
        {ω : MatedCRT.Path2 | ¬(MatedCRT.IsEdge ε ω e ∧ meshIncidentCode x e) ∨ e ∈ T} by
      ext ω
      simp only [Set.mem_ofPred_eq, Set.mem_iInter, Set.mem_iUnion]
      constructor
      · intro h x
        have hfinite := (meshIncident_subtype_finite_iff ε ω x).mp (h x)
        obtain ⟨T, hT⟩ := (rawIncidentEdges_finite_iff ε ω x).mp hfinite
        exact ⟨T, fun e => by
          by_cases he : MatedCRT.IsEdge ε ω e ∧ meshIncidentCode x e
          · exact Or.inr (hT e he)
          · exact Or.inl he⟩
      · intro h x
        obtain ⟨T, hT⟩ := h x
        apply (meshIncident_subtype_finite_iff ε ω x).mpr
        apply (rawIncidentEdges_finite_iff ε ω x).mpr
        refine ⟨T, ?_⟩
        intro e he
        exact (hT e).resolve_left (fun hn => hn (by
          simpa only [rawIncidentEdges, Set.mem_ofPred_eq] using he))
    ]
  apply MeasurableSet.iInter
  intro x
  apply MeasurableSet.iUnion
  intro T
  apply MeasurableSet.iInter
  intro e
  have hEdge := measurableSet_meshIsEdge ε e
  by_cases hinc : meshIncidentCode x e
  · by_cases hT : e ∈ T
    · simp [hinc, hT]
    · have hcompl : MeasurableSet {ω : MatedCRT.Path2 | ¬MatedCRT.IsEdge ε ω e} := hEdge.compl
      simpa [hinc, hT] using hcompl
  · simp [hinc]

end MatedCRTHarmonic.CellScaling
