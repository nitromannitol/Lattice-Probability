/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module ReflectedGMS.Corrector.BlockInterpolantExistence at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.ReflectedGMS.Corrector.NestedProjectionProducers
import LatticeProb.Bonanno.ReflectedGMS.Forms.VectorTraceMinimizer

/-!
# Existence of the actual block interpolant

`Geometry/DyadicApproximation.IsBlockInterpolation F D m f` is the manuscript's Section 4
blockwise interpolation specification: for `m = 0` the map is the centroid embedding, and
for `m ≠ 0` it is *simultaneously*

* pinned to the centroid embedding on the whole skeleton `skel_m`, and
* the full finite-energy centroid-trace minimizer on **every** `κ`-selected dyadic square.

`HarmonicMainStatement.ApproximationConclusions` asserts this for the canonical choice
`DyadicApproximation.phi F D m`, which defaults to the centroid embedding unless
`∃ f, IsBlockInterpolation F D m f` is available; `DyadicApproximation.phi_spec_of_exists`
then substitutes the real object.  Until now that existential had no producer, so every
downstream statement had to quantify over an abstract `f` meeting the spec.

This module supplies the **gluing** step, which is the only genuinely simultaneous part of
the specification.  The per-square Dirichlet problem is already solved by
`Forms/VectorTraceMinimizer.exists_vector_trace_minimizer`; what is new here is that the
separate per-square solutions can be assembled into a *single* field on all of `V`.  The
mechanism is the checked ownership lemma
`Corrector/ActiveBlockEdges.mem_boundaryVertices_of_mem_two_selected`: a cell meeting two
distinct selected squares meets the spatial boundary of each of them, where every patch
solution is pinned to the same centroid value.  Consequently the value chosen at a vertex
does not depend on which selected square is used to compute it, and the glued field
restricts on each selected patch to that patch's own minimizer.

No finiteness of a patch, of the skeleton, or of the number of cells is used; cells may be
arbitrarily large and the patches may be infinite.  The only geometric input of the gluing
is connectedness of the individual cells.

## What is discharged and what is not

* `exists_isBlockInterpolation` — the gluing theorem, from per-selected-square existence of a
  `CentroidTraceMinimizer`.
* `exists_isBlockInterpolation_of_geometry` — the same with the per-square Dirichlet problem
  solved: under `Geometry F` the patch anchoring is discharged by
  `Geometry/BoundaryAnchoring.boundaryAnchored_restrictGraph_cells_hitting`, leaving exactly
  one per-square analytic input, namely that **some** finite-vector-energy field on the patch
  carries the centroid trace on the patch's spatial boundary.  That input is strictly weaker
  than finiteness of the centroid trace's own patch energy, which is the hypothesis
  `hcentroid` of the existing `Forms/VectorTraceMinimizer.exists_centroidTraceMinimizer`, and
  it is *not* proved here.
* `isBlockInterpolation_phi_of_geometry` — the consumer form: the canonical
  `DyadicApproximation.phi F D m` really does satisfy the specification.
-/

set_option autoImplicit false

open MeasureTheory Set
open scoped ENNReal

namespace ReflectedGMS.BlockInterpolantExistence

open StatementIngredients DyadicApproximation ActiveBlockEdges NestedProjectionProducers

variable {V : Type*}

/-! ### Elementary patch facts -/

/-- A cell meeting the spatial boundary of a rectangle meets the rectangle. -/
theorem boundaryVertices_subset_patchVertices (F : IndexedCells V) (Q : Rectangle) :
    boundaryVertices F Q ⊆ patchVertices F Q := by
  rintro v ⟨z, hzc, hzf⟩
  exact ⟨z, hzc, mem_carrier_of_mem_frontier Q hzf⟩

/-- A closed axis-parallel rectangle carrier is a bounded planar set: it is the continuous
image of a compact product of intervals, exactly as for `axisAlignedRectangle`. -/
theorem isBounded_carrier (Q : Rectangle) : Bornology.IsBounded Q.carrier := by
  have hcompact : IsCompact
      (Set.pi Set.univ fun i : Fin 2 => Set.Icc (Q.lower i) (Q.upper i)) :=
    isCompact_univ_pi fun _ => isCompact_Icc
  let e : (Fin 2 → ℝ) ≃ₜ Plane := (PiLp.homeomorph 2 (fun _ : Fin 2 => ℝ)).symm
  apply (hcompact.image e.continuous).isBounded.subset
  intro z hz
  exact ⟨fun i => z i, fun i _ => hz i, e.apply_symm_apply z⟩

/-! ### The glued field -/

/-- **The glued block interpolant.**  At a vertex whose cell meets some `m`-selected square,
the value of the supplied patch field of one such square; at every other vertex the cell
centroid.  Which selected square is used is irrelevant by
`glue_eq_of_mem_patch` below. -/
noncomputable def glue (F : IndexedCells V) (D : Grid) (m : ℝ)
    (g : SquareIndex → V → Plane) (v : V) : Plane :=
  @dite Plane (∃ s : SquareIndex, Selected F D m s ∧ v ∈ patchVertices F (square D s))
    (Classical.propDecidable _) (fun h => g h.choose v) (fun _ => cellCentroid F v)

/-- Off every selected square the glued field is the centroid embedding. -/
theorem glue_of_not_exists (F : IndexedCells V) (D : Grid) (m : ℝ)
    (g : SquareIndex → V → Plane) {v : V}
    (h : ¬ ∃ s : SquareIndex, Selected F D m s ∧ v ∈ patchVertices F (square D s)) :
    glue F D m g v = cellCentroid F v := by
  simp only [glue]
  rw [dif_neg h]

/-- **The glued field agrees with every patch field on that patch.**  If two distinct
selected squares both meet the cell of `v`, then `v` lies on the spatial boundary of both,
where both patch fields take the centroid value, so the choice made by `glue` is immaterial.
-/
theorem glue_eq_of_mem_patch (F : IndexedCells V)
    (hcell : ∀ v : V, IsConnected (F.cell v : Set Plane)) (D : Grid) (m : ℝ)
    {g : SquareIndex → V → Plane}
    (hg : ∀ s : SquareIndex, Selected F D m s → CentroidTraceMinimizer F (square D s) (g s))
    {s : SquareIndex} (hs : Selected F D m s) {v : V}
    (hv : v ∈ patchVertices F (square D s)) :
    glue F D m g v = g s v := by
  have h : ∃ t : SquareIndex, Selected F D m t ∧ v ∈ patchVertices F (square D t) :=
    ⟨s, hs, hv⟩
  simp only [glue]
  rw [dif_pos h]
  obtain ⟨ht, hvt⟩ := h.choose_spec
  by_cases hst : h.choose = s
  · rw [hst]
  · have hb1 : v ∈ boundaryVertices F (square D h.choose) :=
      mem_boundaryVertices_of_mem_two_selected F hcell D m ht hs hst hvt hv
    have hb2 : v ∈ boundaryVertices F (square D s) :=
      mem_boundaryVertices_of_mem_two_selected F hcell D m hs ht (Ne.symm hst) hv hvt
    rw [(hg _ ht).2.1 ⟨v, hvt⟩ hb1, (hg s hs).2.1 ⟨v, hv⟩ hb2]

/-- The glued field is pinned to the centroid embedding on the whole skeleton. -/
theorem glue_eq_centroid_of_mem_skeleton (F : IndexedCells V)
    (hcell : ∀ v : V, IsConnected (F.cell v : Set Plane)) (D : Grid) (m : ℝ)
    {g : SquareIndex → V → Plane}
    (hg : ∀ s : SquareIndex, Selected F D m s → CentroidTraceMinimizer F (square D s) (g s))
    {v : V} (hv : v ∈ skeleton F D m) :
    glue F D m g v = cellCentroid F v := by
  obtain ⟨t, ht, hvt⟩ := hv
  have hpt : v ∈ patchVertices F (square D t) :=
    boundaryVertices_subset_patchVertices F (square D t) hvt
  rw [glue_eq_of_mem_patch F hcell D m hg ht hpt]
  exact (hg t ht).2.1 ⟨v, hpt⟩ hvt

/-- The glued field is the full centroid-trace minimizer on every selected square. -/
theorem centroidTraceMinimizer_glue (F : IndexedCells V)
    (hcell : ∀ v : V, IsConnected (F.cell v : Set Plane)) (D : Grid) (m : ℝ)
    {g : SquareIndex → V → Plane}
    (hg : ∀ s : SquareIndex, Selected F D m s → CentroidTraceMinimizer F (square D s) (g s))
    {s : SquareIndex} (hs : Selected F D m s) :
    CentroidTraceMinimizer F (square D s) (glue F D m g) := by
  obtain ⟨h1, h2, h3⟩ := hg s hs
  have heq : (fun v : patchVertices F (square D s) => glue F D m g v.1)
      = fun v : patchVertices F (square D s) => g s v.1 :=
    funext fun v => glue_eq_of_mem_patch F hcell D m hg hs v.2
  refine ⟨?_, ?_, ?_⟩
  · rw [heq]
    exact h1
  · intro v hv
    rw [glue_eq_of_mem_patch F hcell D m hg hs v.2]
    exact h2 v hv
  · intro w hw
    rw [heq]
    exact h3 w hw

/-! ### The interpolant -/

/-- **Existence of the actual block interpolant, from the per-square Dirichlet problems.**

Given, for every `κ`-selected dyadic square, *some* full finite-energy minimizer with the
centroid trace on that square's patch, there is a **single** field on all of `V` satisfying
the whole of `DyadicApproximation.IsBlockInterpolation F D m`: it is pinned to the centroid
embedding on the entire skeleton and is simultaneously the centroid-trace minimizer on every
selected square.

Only connectedness of the individual cells is used; no patch, skeleton or cell-count
finiteness, and no finite-support closure of the energy space. -/
theorem exists_isBlockInterpolation (F : IndexedCells V)
    (hcell : ∀ v : V, IsConnected (F.cell v : Set Plane)) (D : Grid) (m : ℕ)
    (hmin : ∀ s : SquareIndex, Selected F D (m : ℝ) s →
      ∃ f : V → Plane, CentroidTraceMinimizer F (square D s) f) :
    ∃ f : V → Plane, IsBlockInterpolation F D m f := by
  classical
  by_cases hm : m = 0
  · exact ⟨cellCentroid F, by simp [IsBlockInterpolation, hm]⟩
  have hmin' : ∀ s : SquareIndex, ∃ f : V → Plane,
      Selected F D (m : ℝ) s → CentroidTraceMinimizer F (square D s) f := by
    intro s
    by_cases hs : Selected F D (m : ℝ) s
    · obtain ⟨f, hf⟩ := hmin s hs
      exact ⟨f, fun _ => hf⟩
    · exact ⟨cellCentroid F, fun h => absurd h hs⟩
  choose g hg using hmin'
  refine ⟨glue F D (m : ℝ) g, ?_⟩
  rw [IsBlockInterpolation, if_neg hm]
  exact ⟨fun v hv => glue_eq_centroid_of_mem_skeleton F hcell D (m : ℝ) hg hv,
    fun s hs => centroidTraceMinimizer_glue F hcell D (m : ℝ) hg hs⟩

/-- **Existence of the actual block interpolant under the geometry hypothesis.**

Under `Geometry F` the patch anchoring needed by the per-square Dirichlet problem is
discharged by `boundaryAnchored_restrictGraph_cells_hitting`, so the only remaining input is
that on each selected patch *some* finite-vector-energy field carries the centroid trace on
the patch's spatial boundary.  The comparison class of the conclusion is the full one: every
plane-valued field on the patch with the centroid boundary trace. -/
theorem exists_isBlockInterpolation_of_geometry [Countable V] (F : IndexedCells V)
    (hF : Geometry F) (D : Grid) (m : ℕ)
    (hfin : ∀ s : SquareIndex, Selected F D (m : ℝ) s →
      ∃ u : patchVertices F (square D s) → Plane,
        vectorEnergy (restrictGraph F.graph (patchVertices F (square D s))) u < ∞ ∧
        ∀ v : patchVertices F (square D s), v.1 ∈ boundaryVertices F (square D s) →
          u v = cellCentroid F v.1) :
    ∃ f : V → Plane, IsBlockInterpolation F D m f := by
  refine exists_isBlockInterpolation F hF.1 D m ?_
  intro s hs
  obtain ⟨u, hu, hutr⟩ := hfin s hs
  have hA : BoundaryAnchored (restrictGraph F.graph (patchVertices F (square D s)))
      {v : patchVertices F (square D s) | v.1 ∈ boundaryVertices F (square D s)} :=
    boundaryAnchored_restrictGraph_cells_hitting F hF (square D s).carrier
      (isBounded_carrier (square D s))
  obtain ⟨f₀, hf₀fin, hf₀trace, hf₀min⟩ :=
    exists_vector_trace_minimizer (restrictGraph F.graph (patchVertices F (square D s))) hA hu
  refine ⟨subtypeExtend f₀, ?_, ?_, ?_⟩
  · rw [subtypeExtend_comp]
    exact hf₀fin
  · intro v hv
    rw [subtypeExtend_apply, hf₀trace v hv]
    exact hutr v hv
  · intro w hw
    rw [subtypeExtend_comp]
    refine hf₀min w fun v hv => ?_
    rw [hw v hv, ← hutr v hv]

end ReflectedGMS.BlockInterpolantExistence
