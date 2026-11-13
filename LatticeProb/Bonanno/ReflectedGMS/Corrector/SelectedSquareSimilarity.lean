/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module ReflectedGMS.Corrector.SelectedSquareSimilarity at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.ReflectedGMS.Spatial.DilatedSelectedBlocks
import LatticeProb.Bonanno.ReflectedGMS.Geometry.DiameterBlockIndex

/-!
# The selected-square correspondence along a physical similarity

`Corrector/ApproximantCovarianceFromBlockTransport` reduces the `hcov` input of the harmonic
main theorem to `BlockInterpolationSimilarityCovariant`, whose geometric content is the
correspondence of the dyadic squares, of the selection statistic `κ`, of the selected squares and
of the skeleton, along a physical similarity `z ↦ s • (z - u)` paired with the grid action
`dilate s hs (translate u D)` (which is `ApproximantCovarianceFromBlockTransport.gridSimilarity`
by definition).

`Spatial/DilatedSelectedBlocks` had this for the **origin chain and the dilation factor only**
(`blockIndex_originIndex_dilate`, `originSelected_dilate_iff`), and
`Spatial/ActualMarkedBlockTransport` for the origin chain and the translation factor only.  This
module proves it for **every** `SquareIndex` and the composite similarity.

## The reindexing

`squareMap s u D (k, n) = (k + levelShift s (translate u D), n - latticeShift D u k)`.  Its
inverse is `squareUnmap`, packaged as `squareEquiv`.  Both the level shift (from the dilation,
grid dependent through the phase) and the lattice shift (from the translation, level dependent)
are genuinely present.

## What is proved

* `square_lower_squareMap`, `square_upper_squareMap`, `side_squareMap` — the corners and side of
  the image square are the similarity images of the original ones;
  `preimage_square_squareMap` and `preimage_frontier_square_squareMap` — the carriers and their
  frontiers correspond exactly under `positiveSimilarity s u`.
* `parent_squareMap` — **`σ` commutes with `parent`.**  The parent is defined by integer
  division with the grid digits, and the image grid has different digits, so this is not a
  computation: it is proved geometrically.  The lower corner of a square lies in the half-open
  lower bracket of its parent (`lower_bracket_parent`), and at a fixed level a lower bracket
  determines the lattice index (`snd_eq_of_lower_bracket`); the similarity carries brackets to
  brackets.  `ancestor_squareMap` follows.
* `hits_relabel_iff` — the cell of `relabel v` meets `A'` iff the cell of `v` meets
  `positiveSimilarity s u ⁻¹' A'`; hence patch and boundary vertices correspond.
* `maxCellDiameter_squareMap` (factor `s`), `ancestorRatio_squareMap`,
  `inverseRatio_squareMap`, `blockIndex_squareMap` (invariant: `s` cancels against the side),
  `selected_squareMap_iff`, `mem_skeleton_relabel_iff`.

Every statement is pathwise, for one `IsSimilarityRelabel` witness; no law, no good event, no
finiteness hypothesis.
-/

set_option autoImplicit false

open MeasureTheory Set
open scoped ENNReal

namespace ReflectedGMS.SelectedSquareSimilarity

open StatementIngredients DyadicApproximation Code EnvironmentLaws
open UniformGridDilationInvariance DyadicGridTranslation

/-! ### The square reindexing -/

/-- The reindexing of dyadic squares induced by the similarity `z ↦ s • (z - u)` and the grid
action `dilate s hs (translate u D)`. -/
noncomputable def squareMap (s : ℝ) (u : Plane) (D : Grid) (c : SquareIndex) : SquareIndex :=
  (c.1 + levelShift s (translate u D), fun i => c.2 i - latticeShift D u c.1 i)

/-- The inverse reindexing. -/
noncomputable def squareUnmap (s : ℝ) (u : Plane) (D : Grid) (c : SquareIndex) : SquareIndex :=
  (c.1 - levelShift s (translate u D),
    fun i => c.2 i + latticeShift D u (c.1 - levelShift s (translate u D)) i)

theorem squareMap_squareUnmap (s : ℝ) (u : Plane) (D : Grid) (c : SquareIndex) :
    squareMap s u D (squareUnmap s u D c) = c := by
  have h1 : c.1 - levelShift s (translate u D) + levelShift s (translate u D) = c.1 :=
    sub_add_cancel _ _
  refine MarkedBlockAveraging.squareIndex_ext h1 fun i => ?_
  show c.2 i + latticeShift D u (c.1 - levelShift s (translate u D)) i
      - latticeShift D u (c.1 - levelShift s (translate u D)) i = c.2 i
  rw [add_sub_cancel_right]

theorem exists_squareMap_eq (s : ℝ) (u : Plane) (D : Grid) (c' : SquareIndex) :
    ∃ c : SquareIndex, squareMap s u D c = c' :=
  ⟨squareUnmap s u D c', squareMap_squareUnmap s u D c'⟩

/-! ### Corners, sides and carriers -/

/-- The side of the image square is `s` times the original side. -/
theorem side_squareMap {s : ℝ} (hs : 0 < s) (u : Plane) (D : Grid) (c : SquareIndex) :
    side (dilate s hs (translate u D)) (squareMap s u D c).1 = s * side D c.1 :=
  DilatedSelectedBlocks.side_dilate_add hs (translate u D) c.1

/-- The lower corner of the image square is the similarity image of the lower corner. -/
theorem square_lower_squareMap {s : ℝ} (hs : 0 < s) (u : Plane) (D : Grid) (c : SquareIndex)
    (i : Fin 2) :
    (square (dilate s hs (translate u D)) (squareMap s u D c)).lower i
      = s * ((square D c).lower i - u i) := by
  have hL : c.1 + levelShift s (translate u D) - levelShift s (translate u D) = c.1 :=
    add_sub_cancel_right _ _
  have horig : (dilate s hs (translate u D)).origin (squareMap s u D c).1 i
      = s * translatedOrigin D u c.1 i := by
    show s * translatedOrigin D u
        (c.1 + levelShift s (translate u D) - levelShift s (translate u D)) i
      = s * translatedOrigin D u c.1 i
    rw [hL]
  have hcast : (((squareMap s u D c).2 i : ℤ) : ℝ)
      = ((c.2 i : ℤ) : ℝ) - ((latticeShift D u c.1 i : ℤ) : ℝ) :=
    Int.cast_sub (c.2 i) (latticeShift D u c.1 i)
  show (dilate s hs (translate u D)).origin (squareMap s u D c).1 i
      + side (dilate s hs (translate u D)) (squareMap s u D c).1
        * (((squareMap s u D c).2 i : ℤ) : ℝ)
    = s * (D.origin c.1 i + side D c.1 * ((c.2 i : ℤ) : ℝ) - u i)
  rw [horig, side_squareMap hs u D c, hcast, translatedOrigin_eq D u c.1 i]
  ring

/-- The upper corner of the image square is the similarity image of the upper corner. -/
theorem square_upper_squareMap {s : ℝ} (hs : 0 < s) (u : Plane) (D : Grid) (c : SquareIndex)
    (i : Fin 2) :
    (square (dilate s hs (translate u D)) (squareMap s u D c)).upper i
      = s * ((square D c).upper i - u i) := by
  show (square (dilate s hs (translate u D)) (squareMap s u D c)).lower i
      + side (dilate s hs (translate u D)) (squareMap s u D c).1
    = s * ((square D c).lower i + side D c.1 - u i)
  rw [square_lower_squareMap hs u D c i, side_squareMap hs u D c]
  ring

/-- A point lies in a square exactly when its similarity image lies in the image square. -/
theorem positiveSimilarity_mem_square_squareMap_iff {s : ℝ} (hs : 0 < s) (u : Plane) (D : Grid)
    (c : SquareIndex) (z : Plane) :
    positiveSimilarity s u z ∈ (square (dilate s hs (translate u D)) (squareMap s u D c)).carrier
      ↔ z ∈ (square D c).carrier := by
  have hz : ∀ i : Fin 2, positiveSimilarity s u z i = s * (z i - u i) := fun i => by
    simp [positiveSimilarity]
  simp only [Rectangle.carrier, Set.mem_setOf_eq, hz, square_lower_squareMap hs u D c,
    square_upper_squareMap hs u D c]
  refine forall_congr' fun i => ?_
  constructor
  · rintro ⟨h1, h2⟩
    have h1' := le_of_mul_le_mul_left h1 hs
    have h2' := le_of_mul_le_mul_left h2 hs
    exact ⟨by linarith, by linarith⟩
  · rintro ⟨h1, h2⟩
    exact ⟨mul_le_mul_of_nonneg_left (by linarith) hs.le,
      mul_le_mul_of_nonneg_left (by linarith) hs.le⟩

/-- **The carriers correspond exactly.** -/
theorem preimage_square_squareMap {s : ℝ} (hs : 0 < s) (u : Plane) (D : Grid)
    (c : SquareIndex) :
    positiveSimilarity s u ⁻¹' (square (dilate s hs (translate u D)) (squareMap s u D c)).carrier
      = (square D c).carrier :=
  Set.ext fun z => positiveSimilarity_mem_square_squareMap_iff hs u D c z

/-- Preimages of frontiers under a positive similarity are frontiers of preimages. -/
theorem preimage_frontier_eq {s : ℝ} (hs : 0 < s) {u : Plane} {A A' : Set Plane}
    (hA : positiveSimilarity s u ⁻¹' A' = A) :
    positiveSimilarity s u ⁻¹' frontier A' = frontier A := by
  have h1 : positiveSimilarity s u ⁻¹' frontier A'
      = frontier (positiveSimilarity s u ⁻¹' A') :=
    (positiveSimilarityHomeomorph s u hs).preimage_frontier A'
  rw [h1, hA]

/-- **The frontiers correspond exactly.** -/
theorem preimage_frontier_square_squareMap {s : ℝ} (hs : 0 < s) (u : Plane) (D : Grid)
    (c : SquareIndex) :
    positiveSimilarity s u ⁻¹'
        frontier (square (dilate s hs (translate u D)) (squareMap s u D c)).carrier
      = frontier (square D c).carrier :=
  preimage_frontier_eq hs (preimage_square_squareMap hs u D c)

/-! ### The parent commutes with the reindexing -/

/-- The lower corner of a square lies in the half-open lower bracket of its parent. -/
theorem lower_bracket_parent (G : Grid) (c : SquareIndex) (i : Fin 2) :
    (square G (parent G c)).lower i ≤ (square G c).lower i ∧
      (square G c).lower i < (square G (parent G c)).lower i + side G (parent G c).1 := by
  have hside : (0 : ℝ) < side G c.1 := side_pos G c.1
  have hcomp : G.origin c.1 i =
      G.origin (c.1 + 1) i + side G c.1 * ((G.digit c.1 i).val : ℝ) := G.compatible c.1 i
  have hq1 : 2 * ((c.2 i + ((G.digit c.1 i).val : ℤ)) / 2) ≤
      c.2 i + ((G.digit c.1 i).val : ℤ) := by omega
  have hq2 : c.2 i + ((G.digit c.1 i).val : ℤ) ≤
      2 * ((c.2 i + ((G.digit c.1 i).val : ℤ)) / 2) + 1 := by omega
  have hq1' : 2 * ((((c.2 i + ((G.digit c.1 i).val : ℤ)) / 2 : ℤ) : ℝ)) ≤
      (c.2 i : ℝ) + ((G.digit c.1 i).val : ℝ) := by exact_mod_cast hq1
  have hq2' : (c.2 i : ℝ) + ((G.digit c.1 i).val : ℝ) ≤
      2 * ((((c.2 i + ((G.digit c.1 i).val : ℤ)) / 2 : ℤ) : ℝ)) + 1 := by exact_mod_cast hq2
  have m1 := mul_le_mul_of_nonneg_left hq1' hside.le
  have m2 := mul_le_mul_of_nonneg_left hq2' hside.le
  rw [DiameterBlockIndex.square_lower_apply G (parent G c),
    DiameterBlockIndex.square_lower_apply G c, DiameterBlockIndex.side_parent,
    DiameterBlockIndex.parent_fst, DiameterBlockIndex.parent_snd, hcomp]
  constructor
  · push_cast at m1 ⊢
    linarith
  · push_cast at m2 ⊢
    linarith

/-- At a fixed level, a half-open lower bracket determines the lattice index. -/
theorem snd_eq_of_lower_bracket (G : Grid) {a b : SquareIndex} (h1 : a.1 = b.1) (i : Fin 2)
    {x : ℝ} (ha1 : (square G a).lower i ≤ x) (ha2 : x < (square G a).lower i + side G a.1)
    (hb1 : (square G b).lower i ≤ x) (hb2 : x < (square G b).lower i + side G b.1) :
    a.2 i = b.2 i := by
  have hside : (0 : ℝ) < side G a.1 := side_pos G a.1
  rw [DiameterBlockIndex.square_lower_apply] at ha1 ha2 hb1 hb2
  rw [← h1] at hb1 hb2
  have hab : (a.2 i : ℝ) < (b.2 i : ℝ) + 1 := by
    by_contra hcon
    have hle : (b.2 i : ℝ) + 1 ≤ (a.2 i : ℝ) := not_lt.1 hcon
    have hm := mul_le_mul_of_nonneg_left hle hside.le
    linarith
  have hba : (b.2 i : ℝ) < (a.2 i : ℝ) + 1 := by
    by_contra hcon
    have hle : (a.2 i : ℝ) + 1 ≤ (b.2 i : ℝ) := not_lt.1 hcon
    have hm := mul_le_mul_of_nonneg_left hle hside.le
    linarith
  have hab' : a.2 i < b.2 i + 1 := by exact_mod_cast hab
  have hba' : b.2 i < a.2 i + 1 := by exact_mod_cast hba
  omega

/-- **The parent commutes with the square reindexing.**  Proved geometrically: the image grid
has its own digits, so the integer-division formula for `parent` does not transport directly. -/
theorem parent_squareMap {s : ℝ} (hs : 0 < s) (u : Plane) (D : Grid) (c : SquareIndex) :
    parent (dilate s hs (translate u D)) (squareMap s u D c) = squareMap s u D (parent D c) := by
  have hfst : (parent (dilate s hs (translate u D)) (squareMap s u D c)).1
      = (squareMap s u D (parent D c)).1 := by
    show c.1 + levelShift s (translate u D) + 1 = c.1 + 1 + levelShift s (translate u D)
    ring
  refine MarkedBlockAveraging.squareIndex_ext hfst fun i => ?_
  obtain ⟨hP1, hP2⟩ := lower_bracket_parent (dilate s hs (translate u D)) (squareMap s u D c) i
  obtain ⟨hD1, hD2⟩ := lower_bracket_parent D c i
  refine snd_eq_of_lower_bracket (dilate s hs (translate u D)) hfst i hP1 hP2 ?_ ?_
  · rw [square_lower_squareMap hs u D (parent D c) i, square_lower_squareMap hs u D c i]
    exact mul_le_mul_of_nonneg_left (by linarith) hs.le
  · rw [square_lower_squareMap hs u D (parent D c) i, square_lower_squareMap hs u D c i,
      side_squareMap hs u D (parent D c)]
    have hlt : s * ((square D c).lower i - u i)
        < s * ((square D (parent D c)).lower i - u i + side D (parent D c).1) :=
      mul_lt_mul_of_pos_left (by linarith) hs
    linarith

/-- The whole ancestor chain commutes with the square reindexing. -/
theorem ancestor_squareMap {s : ℝ} (hs : 0 < s) (u : Plane) (D : Grid) (c : SquareIndex)
    (j : ℕ) :
    ancestor (dilate s hs (translate u D)) (squareMap s u D c) j
      = squareMap s u D (ancestor D c j) := by
  induction j with
  | zero => rfl
  | succ j ih =>
    rw [DiameterBlockIndex.ancestor_succ', DiameterBlockIndex.ancestor_succ', ih,
      parent_squareMap hs u D]

/-! ### Cells, patches and the selection statistic -/

section Relabel

variable {s : ℝ} {u : Plane} {hs : 0 < s} {e e' : Env}
  {relabel : Vertex e.val ≃ Vertex e'.val}

/-- The cell of `relabel v` meets `A'` exactly when the cell of `v` meets the similarity
preimage of `A'`. -/
theorem hits_relabel_iff (h : IsSimilarityRelabel s u hs e e' relabel) {A A' : Set Plane}
    (hA : positiveSimilarity s u ⁻¹' A' = A) (v : Vertex e.val) :
    Hits (decode e') A' (relabel v) ↔ Hits (decode e) A v := by
  unfold Hits
  rw [h.1 v, coe_transformCell, Set.image_inter_nonempty_iff, hA]

theorem hits_square_squareMap_iff (h : IsSimilarityRelabel s u hs e e' relabel) (D : Grid)
    (c : SquareIndex) (v : Vertex e.val) :
    Hits (decode e') (square (dilate s hs (translate u D)) (squareMap s u D c)).carrier
        (relabel v)
      ↔ Hits (decode e) (square D c).carrier v :=
  hits_relabel_iff h (preimage_square_squareMap hs u D c) v

theorem mem_patchVertices_squareMap_iff (h : IsSimilarityRelabel s u hs e e' relabel)
    (D : Grid) (c : SquareIndex) (v : Vertex e.val) :
    relabel v ∈ patchVertices (decode e') (square (dilate s hs (translate u D)) (squareMap s u D c))
      ↔ v ∈ patchVertices (decode e) (square D c) :=
  hits_square_squareMap_iff h D c v

theorem mem_boundaryVertices_squareMap_iff (h : IsSimilarityRelabel s u hs e e' relabel)
    (D : Grid) (c : SquareIndex) (v : Vertex e.val) :
    relabel v ∈ boundaryVertices (decode e')
        (square (dilate s hs (translate u D)) (squareMap s u D c))
      ↔ v ∈ boundaryVertices (decode e) (square D c) :=
  hits_relabel_iff h (preimage_frontier_square_squareMap hs u D c) v

/-- The maximal cell diameter of the image square is `s` times the original one. -/
theorem maxCellDiameter_squareMap (h : IsSimilarityRelabel s u hs e e' relabel) (D : Grid)
    (c : SquareIndex) :
    maxCellDiameter (decode e') (dilate s hs (translate u D)) (squareMap s u D c)
      = ENNReal.ofReal s * maxCellDiameter (decode e) D c := by
  refine DilatedSelectedBlocks.maxCellDiameter_congr_map_mul (decode e) (decode e') D
    (dilate s hs (translate u D)) c (squareMap s u D c) relabel (ENNReal.ofReal s)
    (fun v => hits_square_squareMap_iff h D c v) (fun v => ?_)
  rw [h.1 v, coe_transformCell, Spatial.diam_image_positiveSimilarity s u hs,
    ENNReal.ofReal_mul hs.le]

/-- The ancestor ratio `a` is invariant: `s` cancels between diameters and sides. -/
theorem ancestorRatio_squareMap (h : IsSimilarityRelabel s u hs e e' relabel) (D : Grid)
    (c : SquareIndex) :
    ancestorRatio (decode e') (dilate s hs (translate u D)) (squareMap s u D c)
      = ancestorRatio (decode e) D c := by
  have hs0 : ENNReal.ofReal s ≠ 0 := (ENNReal.ofReal_pos.2 hs).ne'
  unfold ancestorRatio
  refine iSup_congr fun j => ?_
  rw [ancestor_squareMap hs u D c j, maxCellDiameter_squareMap h D, side_squareMap hs u D,
    ENNReal.ofReal_mul hs.le, ENNReal.mul_div_mul_left _ _ hs0 ENNReal.ofReal_ne_top]

theorem inverseRatio_squareMap (h : IsSimilarityRelabel s u hs e e' relabel) (D : Grid)
    (c : SquareIndex) :
    inverseRatio (decode e') (dilate s hs (translate u D)) (squareMap s u D c)
      = inverseRatio (decode e) D c := by
  unfold inverseRatio
  rw [ancestorRatio_squareMap h D c]

/-- **The manuscript's `κ` is invariant** under the joint similarity, at every square. -/
theorem blockIndex_squareMap (h : IsSimilarityRelabel s u hs e e' relabel) (D : Grid)
    (c : SquareIndex) :
    blockIndex (decode e') (dilate s hs (translate u D)) (squareMap s u D c)
      = blockIndex (decode e) D c := by
  unfold blockIndex
  refine tsum_congr fun j => ?_
  rw [ancestor_squareMap hs u D c j, inverseRatio_squareMap h D]

/-- **The selected squares correspond.** -/
theorem selected_squareMap_iff (h : IsSimilarityRelabel s u hs e e' relabel) (D : Grid)
    (m : ℝ) (c : SquareIndex) :
    Selected (decode e') (dilate s hs (translate u D)) m (squareMap s u D c)
      ↔ Selected (decode e) D m c := by
  unfold Selected
  rw [blockIndex_squareMap h D c, parent_squareMap hs u D c, blockIndex_squareMap h D (parent D c)]

/-- **The skeletons correspond.** -/
theorem mem_skeleton_relabel_iff (h : IsSimilarityRelabel s u hs e e' relabel) (D : Grid)
    (m : ℝ) (v : Vertex e.val) :
    relabel v ∈ skeleton (decode e') (dilate s hs (translate u D)) m
      ↔ v ∈ skeleton (decode e) D m := by
  constructor
  · rintro ⟨c', hsel, hb⟩
    obtain ⟨c, rfl⟩ := exists_squareMap_eq s u D c'
    exact ⟨c, (selected_squareMap_iff h D m c).1 hsel,
      (mem_boundaryVertices_squareMap_iff h D c v).1 hb⟩
  · rintro ⟨c, hsel, hb⟩
    exact ⟨squareMap s u D c, (selected_squareMap_iff h D m c).2 hsel,
      (mem_boundaryVertices_squareMap_iff h D c v).2 hb⟩

end Relabel

end ReflectedGMS.SelectedSquareSimilarity
