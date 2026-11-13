/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module ReflectedGMS.Corrector.RectangleInSelectedBlock at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.ReflectedGMS.Corrector.MarkedRectangleHarmonicity
import LatticeProb.Bonanno.ReflectedGMS.Corrector.NestedEnergyProjections
import LatticeProb.Bonanno.ReflectedGMS.Corrector.NestedProjectionProducers
import LatticeProb.Bonanno.ReflectedGMS.Corrector.PatchCentroidTraceFiniteEnergy
import LatticeProb.Bonanno.ReflectedGMS.Geometry.DiameterBlockIndex

/-!
# A rectangle strictly inside a block inherits the block's free orthogonality

This module proves the **deterministic half** of the open input
`MarkedRectangleHarmonicity.MarkedApproximantRectangleOrthogonality`: once a bounded
rectangle `Q` sits inside the *interior* of a rectangle `Q'` on which a field `f` is the
full-energy centroid-trace minimizer (`DyadicApproximation.CentroidTraceMinimizer`), the
field has finite patch energy on `Q` and is orthogonal to **every** finite-energy variation
vanishing on the spatial boundary of `Q`.

The two ingredients are:

* `mem_boundaryVertices_of_engulfed` — a cell meeting `Q` and meeting `∂Q'` must meet `∂Q`.
  This is the only place the geometry of the cells enters: cells are connected
  (`Geometry.1`), so a cell missing `∂Q` but meeting `Q ⊆ int Q'` lies inside `int Q`, hence
  inside `int Q'`, and therefore cannot meet `∂Q'`.  It is what makes the zero extension of
  a `Q`-variation an admissible `Q'`-variation.
* `vectorPairing_restrictGraph_eq` — the pairing against a variation supported strictly
  inside `Q` is the same computed on the patch of `Q` and on any larger patch.  This is the
  plane-valued form of the checked scalar localisation
  `LimitingPotentialFreeOrthogonality.dirichletForm_eq_restricted`, applied twice to the
  same ambient Dirichlet form.

Nothing here is probabilistic and nothing here produces the geometric containment
`Q.carrier ⊆ interior Q'.carrier`; that is the content of
`Corrector/EventuallySelectedEngulfing`.

## Why the competitor class is not shrunk

`FullZeroBoundaryVariation F Q u` is the *full* finite-energy class on the — possibly
infinite — patch of `Q`, with no finite-support and no decay condition, and the conclusion
quantifies over all of it.  The extension used below is the zero extension, which is
admissible for `Q'` precisely because of `mem_boundaryVertices_of_engulfed`; no cut-off and
no approximation by finitely supported variations is performed.
-/

set_option autoImplicit false

open MeasureTheory Set Filter Topology
open scoped ENNReal

namespace ReflectedGMS

namespace RectangleInSelectedBlock

open StatementIngredients DyadicApproximation

variable {V : Type*}

/-! ### The plane-valued zero extension -/

/-- The extension of a plane-valued field on a vertex subset by zero. -/
noncomputable def extendZeroPlane (S : Set V) (u : S → Plane) : V → Plane :=
  Function.extend (fun z : S => (z : V)) u fun _ => 0

theorem extendZeroPlane_apply_coe (S : Set V) (u : S → Plane) (z : S) :
    extendZeroPlane S u (z : V) = u z :=
  Subtype.coe_injective.extend_apply u (fun _ => 0) z

theorem extendZeroPlane_eq_zero_of_notMem (S : Set V) (u : S → Plane) {x : V} (hx : x ∉ S) :
    extendZeroPlane S u x = 0 :=
  Function.extend_apply' u (fun _ => 0) x (by rintro ⟨z, rfl⟩; exact hx z.2)

/-- The coordinates of the plane-valued zero extension are the scalar zero extensions of the
coordinates. -/
theorem extendZeroPlane_coord (S : Set V) (u : S → Plane) (x : V) (i : Fin 2) :
    extendZeroPlane S u x i
      = LimitingPotentialFreeOrthogonality.extendZero S (fun z : S => u z i) x := by
  by_cases hx : x ∈ S
  · have h1 : extendZeroPlane S u x = u ⟨x, hx⟩ := extendZeroPlane_apply_coe S u ⟨x, hx⟩
    have h2 : LimitingPotentialFreeOrthogonality.extendZero S (fun z : S => u z i) x
        = u ⟨x, hx⟩ i :=
      LimitingPotentialFreeOrthogonality.extendZero_apply_coe S (fun z : S => u z i) ⟨x, hx⟩
    rw [h1, h2]
  · rw [extendZeroPlane_eq_zero_of_notMem S u hx,
      LimitingPotentialFreeOrthogonality.extendZero_eq_zero_of_not_mem S _ hx]
    simp

/-- A field vanishing off `R` has a zero extension vanishing off `R`. -/
theorem extendZeroPlane_eq_zero_of_notMem_sub {R S : Set V} (u : S → Plane)
    (hu0 : ∀ z : S, (z : V) ∉ R → u z = 0) :
    ∀ x : V, x ∉ R → extendZeroPlane S u x = 0 := by
  intro x hx
  by_cases hxS : x ∈ S
  · have h1 : extendZeroPlane S u x = u ⟨x, hxS⟩ := extendZeroPlane_apply_coe S u ⟨x, hxS⟩
    rw [h1, hu0 ⟨x, hxS⟩ hx]
  · exact extendZeroPlane_eq_zero_of_notMem S u hxS

/-! ### The pairing against a variation supported strictly inside is a patch quantity -/

/-- **The vector pairing against a variation supported in `R` is the same on every vertex
set containing `R` together with all its neighbours.**  Plane-valued form of the checked
`LimitingPotentialFreeOrthogonality.dirichletForm_eq_restricted`; no energy of `f` is used. -/
theorem vectorPairing_restrictGraph_eq (G : ReflectedWalk.ConductanceGraph V)
    {R A B : Set V} (hRA : R ⊆ A) (hRB : R ⊆ B)
    (hnbrA : ∀ x ∈ R, ∀ y : V, G.Adj x y → y ∈ A)
    (hnbrB : ∀ x ∈ R, ∀ y : V, G.Adj x y → y ∈ B)
    {u : A → Plane} (hu0 : ∀ z : A, (z : V) ∉ R → u z = 0) (f : V → Plane) :
    vectorPairing (restrictGraph G A) (fun z : A => f (z : V)) u
      = vectorPairing (restrictGraph G B) (fun z : B => f (z : V))
          fun z : B => extendZeroPlane A u (z : V) := by
  have hv0 : ∀ x : V, x ∉ R → extendZeroPlane A u x = 0 :=
    extendZeroPlane_eq_zero_of_notMem_sub u hu0
  refine Finset.sum_congr rfl fun i _ => ?_
  have hz0 : ∀ x : V, x ∉ R →
      LimitingPotentialFreeOrthogonality.extendZero A (fun z : A => u z i) x = 0 := by
    intro x hx
    rw [← extendZeroPlane_coord A u x i, hv0 x hx]
    simp
  have hres : (fun z : A =>
        LimitingPotentialFreeOrthogonality.extendZero A (fun z : A => u z i) (z : V))
      = fun z : A => u z i :=
    LimitingPotentialFreeOrthogonality.extendZero_restrict A fun z : A => u z i
  have hA := LimitingPotentialFreeOrthogonality.dirichletForm_eq_restricted G hRA hnbrA hz0
    fun x : V => f x i
  have hB := LimitingPotentialFreeOrthogonality.dirichletForm_eq_restricted G hRB hnbrB hz0
    fun x : V => f x i
  rw [hres] at hA
  rw [← hA, hB]
  congr 1
  funext z
  exact (extendZeroPlane_coord A u (z : V) i).symm

/-! ### The geometry of a strictly engulfed rectangle -/

/-- **A cell meeting `Q` and meeting `∂Q'` meets `∂Q`**, when `Q` sits in the interior of
`Q'`.  Only connectedness of the cells is used. -/
theorem mem_boundaryVertices_of_engulfed [Countable V] {F : IndexedCells V} (hF : Geometry F)
    {Q Q' : Rectangle} (hQQ' : Q.carrier ⊆ interior Q'.carrier) {v : V}
    (hv : v ∈ patchVertices F Q) (hv' : v ∈ boundaryVertices F Q') :
    v ∈ boundaryVertices F Q := by
  by_contra hvb
  have hdisj : Disjoint (F.cell v : Set Plane) (frontier Q.carrier) := by
    rw [Set.disjoint_iff_inter_eq_empty]
    exact Set.not_nonempty_iff_eq_empty.mp hvb
  have hsub : (F.cell v : Set Plane) ⊆ interior Q.carrier :=
    connected_subset_interior_of_inter_nonempty_of_disjoint_frontier (hF.1 v) hv hdisj
  obtain ⟨z, hzc, hzf⟩ := hv'
  exact hzf.2 (hQQ' (interior_subset (hsub hzc)))

/-- The patch of an engulfed rectangle is contained in the patch of the engulfing one. -/
theorem patchVertices_subset_of_engulfed (F : IndexedCells V) {Q Q' : Rectangle}
    (hQQ' : Q.carrier ⊆ interior Q'.carrier) :
    patchVertices F Q ⊆ patchVertices F Q' :=
  DiameterBlockIndex.patchVertices_mono F (hQQ'.trans interior_subset)

/-- Finite patch energy is inherited by a smaller rectangle. -/
theorem vectorEnergy_patch_lt_top_of_subset (F : IndexedCells V) {Q Q' : Rectangle}
    (hQQ' : Q.carrier ⊆ Q'.carrier) {f : V → Plane}
    (hf : vectorEnergy (restrictGraph F.graph (patchVertices F Q'))
      (fun v : patchVertices F Q' => f v.1) < ∞) :
    vectorEnergy (restrictGraph F.graph (patchVertices F Q))
      (fun v : patchVertices F Q => f v.1) < ∞ := by
  have hAB : patchVertices F Q ⊆ patchVertices F Q' :=
    DiameterBlockIndex.patchVertices_mono F hQQ'
  refine lt_of_le_of_lt ?_ hf
  exact PatchCentroidTraceFiniteEnergy.vectorEnergy_restrictGraph_mono F.graph hAB
    fun v : patchVertices F Q' => f v.1

/-! ### The orthogonality transfer -/

/-- **The deterministic content of `MarkedApproximantRectangleOrthogonality`.**  If `f` is
the full-energy centroid-trace minimizer of the block `Q'` and the rectangle `Q` lies in the
interior of `Q'`, then `f` is free-orthogonal on `Q`: it pairs to zero with every
finite-energy variation vanishing on the spatial boundary of `Q`.

The proof is the first variation of the blockwise minimality: the zero extension of the
variation is admissible for `Q'` because a cell meeting `Q` and `∂Q'` would have to meet
`∂Q`, where the variation vanishes. -/
theorem vectorPairing_eq_zero_of_engulfed [Countable V] {F : IndexedCells V} (hF : Geometry F)
    {Q Q' : Rectangle} (hQQ' : Q.carrier ⊆ interior Q'.carrier)
    {f : V → Plane} (hf : CentroidTraceMinimizer F Q' f)
    {u : patchVertices F Q → Plane} (hu : FullZeroBoundaryVariation F Q u) :
    vectorPairing (restrictGraph F.graph (patchVertices F Q))
      (fun v : patchVertices F Q => f v.1) u = 0 := by
  classical
  have hAB : patchVertices F Q ⊆ patchVertices F Q' :=
    patchVertices_subset_of_engulfed F hQQ'
  have hRA : patchVertices F Q \ boundaryVertices F Q ⊆ patchVertices F Q := Set.diff_subset
  have hRB : patchVertices F Q \ boundaryVertices F Q ⊆ patchVertices F Q' := hRA.trans hAB
  have hnbrA : ∀ x ∈ patchVertices F Q \ boundaryVertices F Q, ∀ y : V,
      F.graph.Adj x y → y ∈ patchVertices F Q := by
    intro x hx y hxy
    exact MarkedRectangleHarmonicity.mem_patchVertices_of_adj F hF hx.1 hx.2 hxy
  have hnbrB : ∀ x ∈ patchVertices F Q \ boundaryVertices F Q, ∀ y : V,
      F.graph.Adj x y → y ∈ patchVertices F Q' := fun x hx y hxy => hAB (hnbrA x hx y hxy)
  have hu0 : ∀ z : patchVertices F Q,
      (z : V) ∉ patchVertices F Q \ boundaryVertices F Q → u z = 0 := by
    intro z hz
    refine hu.2 z ?_
    by_contra hb
    exact hz ⟨z.2, hb⟩
  -- the zero extension has finite energy on the big patch
  have hwB : vectorEnergy (restrictGraph F.graph (patchVertices F Q'))
      (fun z : patchVertices F Q' =>
        extendZeroPlane (patchVertices F Q) u (z : V)) < ∞ := by
    refine vectorEnergy_lt_top_of_coord _ fun i => ?_
    have hcoord : (fun z : patchVertices F Q' =>
          extendZeroPlane (patchVertices F Q) u (z : V) i)
        = fun z : patchVertices F Q' =>
          LimitingPotentialFreeOrthogonality.extendZero (patchVertices F Q)
            (fun z : patchVertices F Q => u z i) (z : V) := by
      funext z
      exact extendZeroPlane_coord (patchVertices F Q) u (z : V) i
    rw [hcoord]
    refine LimitingPotentialFreeOrthogonality.hasFiniteEnergy_restrict F.graph
      (patchVertices F Q') ?_
    refine LimitingPotentialFreeOrthogonality.hasFiniteEnergy_extendZero F.graph hRA hnbrA
      (hasFiniteEnergy_coord _ hu.1 i) ?_
    intro z hz
    rw [hu0 z hz]
    simp
  -- the competitor
  have hgE : vectorEnergy (restrictGraph F.graph (patchVertices F Q'))
      ((fun z : patchVertices F Q' => f (z : V))
        + fun z : patchVertices F Q' =>
          extendZeroPlane (patchVertices F Q) u (z : V)) < ∞ := by
    refine vectorEnergy_lt_top_of_coord _ fun i => ?_
    have hrw : (fun z : patchVertices F Q' =>
          ((fun z : patchVertices F Q' => f (z : V))
            + fun z : patchVertices F Q' =>
              extendZeroPlane (patchVertices F Q) u (z : V)) z i)
        = (fun z : patchVertices F Q' => f (z : V) i)
          + fun z : patchVertices F Q' =>
            extendZeroPlane (patchVertices F Q) u (z : V) i := by
      funext z
      simp only [Pi.add_apply, PiLp.add_apply]
    rw [hrw]
    exact (hasFiniteEnergy_coord _ hf.1 i).add (hasFiniteEnergy_coord _ hwB i)
  have hgtr : ∀ z : patchVertices F Q', (z : V) ∈ boundaryVertices F Q' →
      ((fun z : patchVertices F Q' => f (z : V))
        + fun z : patchVertices F Q' =>
          extendZeroPlane (patchVertices F Q) u (z : V)) z = cellCentroid F (z : V) := by
    intro z hz
    have hw0 : extendZeroPlane (patchVertices F Q) u (z : V) = 0 := by
      refine extendZeroPlane_eq_zero_of_notMem_sub u hu0 (z : V) ?_
      intro hmem
      exact hmem.2 (mem_boundaryVertices_of_engulfed hF hQQ' hmem.1 hz)
    simp only [Pi.add_apply, hw0, add_zero]
    exact hf.2.1 z hz
  have hzero := NestedEnergyProjections.vectorPairing_sub_eq_zero_of_centroidTraceMinimizer
    F Q' hf _ hgE hgtr
  have hsub : ((fun z : patchVertices F Q' => f (z : V))
        + fun z : patchVertices F Q' => extendZeroPlane (patchVertices F Q) u (z : V))
      - (fun z : patchVertices F Q' => f (z : V))
      = fun z : patchVertices F Q' => extendZeroPlane (patchVertices F Q) u (z : V) := by
    funext z
    simp only [Pi.sub_apply, Pi.add_apply]
    abel
  rw [hsub] at hzero
  rw [vectorPairing_restrictGraph_eq F.graph hRA hRB hnbrA hnbrB hu0 f]
  exact hzero

/-! ### The selected-block specialisation -/

/-- **Free orthogonality of the block interpolant on every rectangle engulfed by a selected
square.**  Both clauses of the approximant-level input are supplied at once: finite patch
energy and orthogonality to the full zero-boundary variation class. -/
theorem finiteEnergy_and_orthogonality_of_selected_engulfing [Countable V]
    {F : IndexedCells V} (hF : Geometry F) (D : Grid) {m : ℕ} (hm : m ≠ 0)
    {f : V → Plane} (hf : IsBlockInterpolation F D m f) {Q : Rectangle} {s : SquareIndex}
    (hs : Selected F D (m : ℝ) s) (hQ : Q.carrier ⊆ interior (square D s).carrier) :
    vectorEnergy (restrictGraph F.graph (patchVertices F Q))
        (fun v : patchVertices F Q => f v.1) < ∞ ∧
      ∀ u : patchVertices F Q → Plane, FullZeroBoundaryVariation F Q u →
        vectorPairing (restrictGraph F.graph (patchVertices F Q))
          (fun v : patchVertices F Q => f v.1) u = 0 := by
  have hmin : CentroidTraceMinimizer F (square D s) f :=
    NestedProjectionProducers.centroidTraceMinimizer_of_isBlockInterpolation F D hm hf hs
  refine ⟨vectorEnergy_patch_lt_top_of_subset F (hQ.trans interior_subset) hmin.1,
    fun u hu => vectorPairing_eq_zero_of_engulfed hF hQ hmin hu⟩

end RectangleInSelectedBlock

end ReflectedGMS
