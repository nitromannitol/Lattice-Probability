/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module ReflectedGMS.Corrector.PatchLabelMeasurability at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.ReflectedGMS.Corrector.PatchSolvableEventMeasurability
import LatticeProb.Bonanno.ReflectedGMS.Corrector.VaryingVertexIndexing
import LatticeProb.Bonanno.ReflectedGMS.Spatial.MeasurableSelectedBlocks

/-!
# The patch and spatial-boundary labels of a dyadic square are measurable events

`Corrector/PatchSolvableEventMeasurability.lean` leaves exactly one measurability statement
open: that of the per-square solvability event.  Every route to it has to say, measurably in
the marked environment, *which code labels belong to the patch of the square* and *which of
those meet the square's spatial boundary*.  This module supplies both.

`Spatial/MeasurableSelectedBlocks.lean` already proves that
`{(slot, box) | the slot is present and its cell meets the closed box}` is a measurable set
(`SlotMeetsBoxSet`), for an **arbitrary** closed box `[l, u]` — no nondegeneracy is used.
The patch condition is that set at the square's own box, so the patch label event is
immediate.

The boundary condition is not, because `boundaryVertices` is stated with
`frontier Q.carrier`, which is not a box.  The first half of this module computes that
frontier:

  `interior (boxCarrier l u) = {z | ∀ i, l i < z i ∧ z i < u i}`

(the nontrivial inclusion uses that the coordinate projections of `PiLp` are open maps, so
the coordinate image of an open subset of the box is an open subset of `Icc (l i) (u i)`),
whence

  `frontier (boxCarrier l u) = ⋃ i, (boxCarrier l (update u i (l i)) ∪
                                     boxCarrier (update l i (u i)) u)`,

the union of the four closed faces, each of which is again a (degenerate) closed box.  So
the boundary label event is a finite union of patch-style events at measurably varying
boxes, and it is measurable for the same reason.

Both events are then identified with the actual membership statements
`v ∈ patchVertices (decode ω.1) (square ω.2 s)` and
`v ∈ boundaryVertices (decode ω.1) (square ω.2 s)` at every active label.

**This file proves no main theorem.**
-/

set_option autoImplicit false
set_option maxHeartbeats 800000

open MeasureTheory Set TopologicalSpace
open scoped ENNReal Classical

namespace ReflectedGMS.PatchLabelMeasurability

open Code StatementIngredients DyadicApproximation HarmonicMainStatement
open MeasurableSelectedBlocks Spatial

/-! ### The interior and the frontier of a plane box -/

theorem isClosed_boxCarrier (l u : Fin 2 → ℝ) : IsClosed (boxCarrier l u) := by
  have hEq : boxCarrier l u
      = ⋂ i : Fin 2, (fun z : Plane => z i) ⁻¹' Set.Icc (l i) (u i) := by
    refine Set.ext fun z => ?_
    simp only [boxCarrier, Set.mem_setOf_eq, Set.mem_iInter, Set.mem_preimage, Set.mem_Icc]
  rw [hEq]
  exact isClosed_iInter fun i => isClosed_Icc.preimage (continuous_planeCoord i)

theorem isOpen_openBox (l u : Fin 2 → ℝ) :
    IsOpen {z : Plane | ∀ i, l i < z i ∧ z i < u i} := by
  have hEq : {z : Plane | ∀ i, l i < z i ∧ z i < u i}
      = ⋂ i : Fin 2, (fun z : Plane => z i) ⁻¹' Set.Ioo (l i) (u i) := by
    refine Set.ext fun z => ?_
    simp only [Set.mem_setOf_eq, Set.mem_iInter, Set.mem_preimage, Set.mem_Ioo]
  rw [hEq]
  exact isOpen_iInter_of_finite fun i => isOpen_Ioo.preimage (continuous_planeCoord i)

/-- **The interior of a closed plane box is the open box.**  The inclusion `⊆` is the only
substantive one: the `i`-th coordinate image of the interior is an *open* subset of
`Icc (l i) (u i)`, because coordinate projections of an `L^p` product are open maps. -/
theorem interior_boxCarrier (l u : Fin 2 → ℝ) :
    interior (boxCarrier l u) = {z : Plane | ∀ i, l i < z i ∧ z i < u i} := by
  refine Set.Subset.antisymm (fun z hz => ?_) ?_
  · intro i
    have hopen : IsOpen ((fun w : Plane => w i) '' interior (boxCarrier l u)) :=
      PiLp.isOpenMap_apply (p := 2) (β := fun _ : Fin 2 => ℝ) i _ isOpen_interior
    have hsub : (fun w : Plane => w i) '' interior (boxCarrier l u)
        ⊆ Set.Icc (l i) (u i) := by
      rintro _ ⟨w, hw, rfl⟩
      exact ⟨(interior_subset hw i).1, (interior_subset hw i).2⟩
    have hmem : z i ∈ interior (Set.Icc (l i) (u i)) :=
      interior_maximal hsub hopen ⟨z, hz, rfl⟩
    rw [interior_Icc] at hmem
    exact ⟨hmem.1, hmem.2⟩
  · refine interior_maximal ?_ (isOpen_openBox l u)
    intro z hz i
    exact ⟨(hz i).1.le, (hz i).2.le⟩

/-- **The frontier of a closed plane box is the union of its four closed faces**, each of
which is again a closed box (with one degenerate side). -/
theorem frontier_boxCarrier_eq_iUnion (l u : Fin 2 → ℝ) (hlu : ∀ i, l i ≤ u i) :
    frontier (boxCarrier l u)
      = ⋃ i : Fin 2, (boxCarrier l (Function.update u i (l i))
          ∪ boxCarrier (Function.update l i (u i)) u) := by
  have hfr : frontier (boxCarrier l u)
      = boxCarrier l u \ {z : Plane | ∀ i, l i < z i ∧ z i < u i} := by
    rw [frontier, (isClosed_boxCarrier l u).closure_eq, interior_boxCarrier]
  rw [hfr]
  refine Set.ext fun z => ?_
  constructor
  · rintro ⟨hz, hnot⟩
    simp only [Set.mem_setOf_eq, not_forall] at hnot
    obtain ⟨i, hi⟩ := hnot
    have hzi := hz i
    have hcase : z i ≤ l i ∨ u i ≤ z i := by
      by_contra hcon
      push_neg at hcon
      exact hi ⟨hcon.1, hcon.2⟩
    refine Set.mem_iUnion.2 ⟨i, ?_⟩
    rcases hcase with hlow | hupp
    · refine Or.inl fun j => ⟨(hz j).1, ?_⟩
      by_cases hj : j = i
      · subst hj
        rw [Function.update_self]
        exact hlow
      · rw [Function.update_of_ne hj]
        exact (hz j).2
    · refine Or.inr fun j => ⟨?_, (hz j).2⟩
      by_cases hj : j = i
      · subst hj
        rw [Function.update_self]
        exact hupp
      · rw [Function.update_of_ne hj]
        exact (hz j).1
  · intro hz
    obtain ⟨i, hi⟩ := Set.mem_iUnion.1 hz
    rcases hi with hlow | hupp
    · refine ⟨fun j => ⟨(hlow j).1, ?_⟩, ?_⟩
      · by_cases hj : j = i
        · subst hj
          have := (hlow j).2
          rw [Function.update_self] at this
          exact this.trans (hlu j)
        · have := (hlow j).2
          rw [Function.update_of_ne hj] at this
          exact this
      · intro hmem
        have h1 := (hlow i).2
        rw [Function.update_self] at h1
        exact absurd (hmem i).1 (not_lt.2 h1)
    · refine ⟨fun j => ⟨?_, (hupp j).2⟩, ?_⟩
      · by_cases hj : j = i
        · subst hj
          have := (hupp j).1
          rw [Function.update_self] at this
          exact (hlu j).trans this
        · have := (hupp j).1
          rw [Function.update_of_ne hj] at this
          exact this
      · intro hmem
        have h1 := (hupp i).1
        rw [Function.update_self] at h1
        exact absurd (hmem i).2 (not_lt.2 h1)

/-! ### Cells meeting a box, read at a code slot -/

/-- The event that code slot `n` is present and its cell meets the closed box with the given
measurably varying corners. -/
def slotMeetsEvent (lo hi : Grid → (Fin 2 → ℝ)) (n : ℕ) : Set MarkedEnvironment :=
  {ω : MarkedEnvironment | (ω.1.val.1 n, (lo ω.2, hi ω.2)) ∈ SlotMeetsBoxSet}

theorem measurableSet_slotMeetsEvent {lo hi : Grid → (Fin 2 → ℝ)} (hlo : Measurable lo)
    (hhi : Measurable hi) (n : ℕ) : MeasurableSet (slotMeetsEvent lo hi n) :=
  ((measurable_envSlot n).prodMk
    ((hlo.comp measurable_snd).prodMk (hhi.comp measurable_snd)))
      measurableSet_slotMeetsBoxSet

/-- At an active label, the slot event is exactly the geometric hitting statement. -/
theorem mem_slotMeetsEvent_iff {lo hi : Grid → (Fin 2 → ℝ)} {n : ℕ} {ω : MarkedEnvironment}
    (hsome : (ω.1.val.1 n).isSome) :
    ω ∈ slotMeetsEvent lo hi n ↔
      Hits (decode ω.1) (boxCarrier (lo ω.2) (hi ω.2)) (⟨n, hsome⟩ : Vertex ω.1.val) := by
  have hcell : ((ω.1.val.1 n).getD referenceCell : CompactCell)
      = (decode ω.1).cell ⟨n, hsome⟩ := getD_eq_get _ hsome
  constructor
  · rintro ⟨-, hne⟩
    rw [hcell] at hne
    exact hne
  · intro hne
    refine ⟨hsome, ?_⟩
    rw [hcell]
    exact hne

/-! ### The patch labels -/

/-- The event that label `n` belongs to the patch of the square `s`. -/
def patchLabelEvent (s : SquareIndex) (n : ℕ) : Set MarkedEnvironment :=
  slotMeetsEvent (fun D => (square D s).lower) (fun D => (square D s).upper) n

theorem measurableSet_patchLabelEvent (s : SquareIndex) (n : ℕ) :
    MeasurableSet (patchLabelEvent s n) :=
  measurableSet_slotMeetsEvent (measurable_squareLowerVec s) (measurable_squareUpperVec s) n

theorem mem_patchLabelEvent_iff {s : SquareIndex} {n : ℕ} {ω : MarkedEnvironment}
    (hsome : (ω.1.val.1 n).isSome) :
    ω ∈ patchLabelEvent s n ↔
      (⟨n, hsome⟩ : Vertex ω.1.val) ∈ patchVertices (decode ω.1) (square ω.2 s) :=
  mem_slotMeetsEvent_iff hsome

/-! ### The spatial-boundary labels -/

/-- The lower `i`-face of the square, as a degenerate closed box. -/
noncomputable def lowerFace (s : SquareIndex) (i : Fin 2) (D : Grid) : Fin 2 → ℝ :=
  Function.update (square D s).upper i ((square D s).lower i)

/-- The upper `i`-face of the square, as a degenerate closed box. -/
noncomputable def upperFace (s : SquareIndex) (i : Fin 2) (D : Grid) : Fin 2 → ℝ :=
  Function.update (square D s).lower i ((square D s).upper i)

theorem measurable_lowerFace (s : SquareIndex) (i : Fin 2) :
    Measurable (lowerFace s i) := by
  refine Measurable.of_eval fun j => ?_
  by_cases hj : j = i
  · subst hj
    have hEq : (fun D : Grid => lowerFace s j D j)
        = fun D : Grid => (square D s).lower j := by
      funext D
      simp only [lowerFace, Function.update_self]
    rw [hEq]
    exact measurable_squareLower s j
  · have hEq : (fun D : Grid => lowerFace s i D j)
        = fun D : Grid => (square D s).upper j := by
      funext D
      simp only [lowerFace, Function.update_of_ne hj]
    rw [hEq]
    exact measurable_squareUpper s j

theorem measurable_upperFace (s : SquareIndex) (i : Fin 2) :
    Measurable (upperFace s i) := by
  refine Measurable.of_eval fun j => ?_
  by_cases hj : j = i
  · subst hj
    have hEq : (fun D : Grid => upperFace s j D j)
        = fun D : Grid => (square D s).upper j := by
      funext D
      simp only [upperFace, Function.update_self]
    rw [hEq]
    exact measurable_squareUpper s j
  · have hEq : (fun D : Grid => upperFace s i D j)
        = fun D : Grid => (square D s).lower j := by
      funext D
      simp only [upperFace, Function.update_of_ne hj]
    rw [hEq]
    exact measurable_squareLower s j

/-- The event that label `n` meets the spatial boundary of the square `s`: a union over the
four closed faces. -/
def boundaryLabelEvent (s : SquareIndex) (n : ℕ) : Set MarkedEnvironment :=
  ⋃ i : Fin 2,
    (slotMeetsEvent (fun D => (square D s).lower) (lowerFace s i) n ∪
      slotMeetsEvent (upperFace s i) (fun D => (square D s).upper) n)

theorem measurableSet_boundaryLabelEvent (s : SquareIndex) (n : ℕ) :
    MeasurableSet (boundaryLabelEvent s n) :=
  MeasurableSet.iUnion fun i =>
    (measurableSet_slotMeetsEvent (measurable_squareLowerVec s)
      (measurable_lowerFace s i) n).union
    (measurableSet_slotMeetsEvent (measurable_upperFace s i)
      (measurable_squareUpperVec s) n)

theorem mem_boundaryLabelEvent_iff {s : SquareIndex} {n : ℕ} {ω : MarkedEnvironment}
    (hsome : (ω.1.val.1 n).isSome) :
    ω ∈ boundaryLabelEvent s n ↔
      (⟨n, hsome⟩ : Vertex ω.1.val) ∈ boundaryVertices (decode ω.1) (square ω.2 s) := by
  have hlu : ∀ i, (square ω.2 s).lower i ≤ (square ω.2 s).upper i := fun i =>
    ((square ω.2 s).nondegenerate i).le
  have hfront : frontier (square ω.2 s).carrier
      = ⋃ i : Fin 2,
        (boxCarrier (square ω.2 s).lower (lowerFace s i ω.2) ∪
          boxCarrier (upperFace s i ω.2) (square ω.2 s).upper) := by
    rw [rectangle_carrier_eq_boxCarrier, frontier_boxCarrier_eq_iUnion _ _ hlu]
    simp only [lowerFace, upperFace]
  constructor
  · intro hmem
    obtain ⟨i, hi⟩ := Set.mem_iUnion.1 hmem
    have hkey : ((( decode ω.1).cell ⟨n, hsome⟩ : Set Plane)
        ∩ frontier (square ω.2 s).carrier).Nonempty := by
      rw [hfront]
      rcases hi with h | h
      · obtain ⟨x, hx1, hx2⟩ := (mem_slotMeetsEvent_iff hsome).1 h
        exact ⟨x, hx1, Set.mem_iUnion.2 ⟨i, Or.inl hx2⟩⟩
      · obtain ⟨x, hx1, hx2⟩ := (mem_slotMeetsEvent_iff hsome).1 h
        exact ⟨x, hx1, Set.mem_iUnion.2 ⟨i, Or.inr hx2⟩⟩
    exact hkey
  · intro hmem
    have hkey : (((decode ω.1).cell ⟨n, hsome⟩ : Set Plane)
        ∩ frontier (square ω.2 s).carrier).Nonempty := hmem
    rw [hfront] at hkey
    obtain ⟨x, hx1, hx2⟩ := hkey
    obtain ⟨i, hi⟩ := Set.mem_iUnion.1 hx2
    refine Set.mem_iUnion.2 ⟨i, ?_⟩
    rcases hi with h | h
    · exact Or.inl ((mem_slotMeetsEvent_iff hsome).2 ⟨x, hx1, h⟩)
    · exact Or.inr ((mem_slotMeetsEvent_iff hsome).2 ⟨x, hx1, h⟩)

end ReflectedGMS.PatchLabelMeasurability
