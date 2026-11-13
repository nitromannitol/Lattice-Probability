/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module ReflectedGMS.Corrector.UniformCorrectorSublinearity at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.ReflectedGMS.Corrector.LocalPatchLineBounds
import LatticeProb.Bonanno.ReflectedGMS.Environment.UncoveredFacts
import Mathlib.Topology.Order.IntermediateValue

/-!
# From a good grid of lines to uniform interior control

This module proves the *deterministic* step of the uniform-sublinearity argument of the
manuscript (`s:thm:main`, display `s:eq:sublinear`), namely the subsection "From good
lines to all cells": the passage from oscillation control along the selected horizontal
and vertical line segments to control over the whole grid skeleton `𝒯_R`, and the
geometric confinement of the remaining cells to a single grid rectangle whose boundary
cells all belong to `𝒯_R`.

Two conclusions are proved here, both unconditional on any probabilistic input.

* `ReflectedGMS.gridCellOscillation_le` is `s:eq:gridresidual`: if every selected
  horizontal segment `[A,B] × {y}`, `y ∈ ys`, and every selected vertical segment
  `{x} × [C,D]`, `x ∈ xs`, carries oscillation at most `t`, then *any* two cells of the
  grid skeleton `𝒯 = gridCells` differ by at most `3 t`.  The constant `3` is the
  manuscript's: it comes from connecting through at most three lines.  The only geometric
  input is that each selected horizontal offset `y` avoids the projection of the uncovered
  set to the second coordinate axis — a Lebesgue-null subset of `ℝ`, by the `H¹`-nullity of
  the uncovered set — so that the whole selected horizontal line is covered and there is an
  actual cell containing each crossing point `(x,y)`, therefore meeting both segments; this
  is the manuscript's "any horizontal and vertical lines meet at a point of a cell, so their
  cell subgraphs intersect".

* `ReflectedGMS.exists_gridRectangle_of_notMem_gridCells` is the geometric half of the
  last step: a *connected* cell which lies in the patch `[A,B] × [C,D]` and meets none of
  the selected segments is confined to the open rectangle cut out by two consecutive
  selected coordinates in each direction; the rectangle has both sides at most `2 g`, and
  every cell meeting its boundary frame is a grid cell.  This is exactly the input of the
  variational maximum principle in the manuscript's final paragraph, including
  `s:eq:boundarycentroid`'s `diam(Q') ≤ 2 √2 α R` bookkeeping in the form `sides ≤ 2 g`.
  Arbitrary connected cells are allowed: no cell is assumed to be a square, a polygon or
  to have any relation to the grid other than being connected and inside the patch.

Nothing here selects the offsets, and no selection theorem is declared below: the
selection from a small patch energy is
`ReflectedGMS.exists_good_offsets_lineOscillation_le_rectanglePatch`, whose conclusion
shape (`oscillation ≤ t` on one segment) is exactly the hypothesis shape consumed by
`gridCellOscillation_le`.  Applying it window by window on the `4N` intervals of length
`α R`, to produce the two offset sets `xs` and `ys` with `g = α R`, belongs to the packet
that owns the residual energy bound `s:eq:smallmeanTV`.

The maximum principle for the blockwise harmonic coordinate on a grid rectangle, which
converts the confinement statement into the bound `|χ(H) - c_R| ≤ 12 α R + o(R)` for
interior cells, is *not* proved here and is not assumed here: no statement of this module
has a harmonicity or minimization hypothesis.
-/

set_option autoImplicit false

open MeasureTheory Set
open scoped ENNReal NNReal

namespace ReflectedGMS

variable {V : Type*}

/-! ### Elementary increment estimates -/

/-- The triangle inequality for the `ℝ≥0∞`-valued increment of `f`. -/
theorem ofReal_abs_sub_trans (f : V → ℝ) (u v w : V) :
    ENNReal.ofReal |f w - f u|
      ≤ ENNReal.ofReal |f v - f u| + ENNReal.ofReal |f w - f v| := by
  rw [← ENNReal.ofReal_add (abs_nonneg _) (abs_nonneg _)]
  refine ENNReal.ofReal_le_ofReal ?_
  linarith [abs_sub_le (f w) (f v) (f u)]

/-- Reading off an increment bound from a bound on the horizontal line oscillation. -/
theorem ofReal_abs_sub_le_of_horizontalLineOscillation_le (F : IndexedCells V) (f : V → ℝ)
    {A B y : ℝ} {t : ℝ≥0∞} (ht : horizontalLineOscillation F f A B y ≤ t) {v w : V}
    (hv : Hits F (horizontal A B y) v) (hw : Hits F (horizontal A B y) w) :
    ENNReal.ofReal |f w - f v| ≤ t := by
  refine le_trans ?_ ht
  rw [horizontalLineOscillation]
  exact le_iSup_of_le ⟨v, hv⟩ (le_iSup_of_le ⟨w, hw⟩ le_rfl)

/-- Reading off an increment bound from a bound on the vertical line oscillation. -/
theorem ofReal_abs_sub_le_of_verticalLineOscillation_le (F : IndexedCells V) (f : V → ℝ)
    {C D x : ℝ} {t : ℝ≥0∞} (ht : verticalLineOscillation F f C D x ≤ t) {v w : V}
    (hv : Hits F (vertical x C D) v) (hw : Hits F (vertical x C D) w) :
    ENNReal.ofReal |f w - f v| ≤ t := by
  refine le_trans ?_ ht
  rw [verticalLineOscillation]
  exact le_iSup_of_le ⟨v, hv⟩ (le_iSup_of_le ⟨w, hw⟩ le_rfl)

/-! ### The crossing cell of a horizontal and a vertical selected segment -/

/-- **Two selected segments always meet inside a cell.**  The crossing point `(x, y)` of
the horizontal segment `[A,B] × {y}` and the vertical segment `{x} × [C,D]` lies in some
cell, and that cell meets both segments.  This is the manuscript's "any horizontal and
vertical lines meet at a point of a cell, so their cell subgraphs intersect".

The covering clause of `Geometry` only asks that the uncovered set be `H¹`-null, so the
crossing point of two arbitrary lines need no longer be covered.  What replaces full
coverage is the hypothesis that the *height* `y` avoids the projection of the uncovered set
to the second coordinate axis: that projection is Lebesgue-null in `ℝ`
(`ReflectedGMS.volume_coordProj_uncoveredSet`), so almost every horizontal line is covered
in its entirety, and the offsets the grid construction selects are chosen off it. -/
theorem exists_hits_horizontal_and_vertical (F : IndexedCells V) {A B C D x y : ℝ}
    (hygood : y ∉ coordProj 1 '' uncoveredSet F)
    (hx : x ∈ Set.Icc A B) (hy : y ∈ Set.Icc C D) :
    ∃ v : V, Hits F (horizontal A B y) v ∧ Hits F (vertical x C D) v := by
  have hmem : (WithLp.toLp 2 ![x, y] : Plane) ∈ (⋃ v, (F.cell v : Set Plane)) := by
    by_contra hcon
    refine hygood ⟨WithLp.toLp 2 ![x, y], ?_, ?_⟩
    · simpa [uncoveredSet] using hcon
    · simp [coordProj]
  obtain ⟨v, hv⟩ := Set.mem_iUnion.mp hmem
  refine ⟨v, ⟨WithLp.toLp 2 ![x, y], hv, ?_⟩, ⟨WithLp.toLp 2 ![x, y], hv, ?_⟩⟩
  · simp [horizontal, hx.1, hx.2]
  · simp [vertical, hy.1, hy.2]

/-! ### The grid skeleton -/

/-- `𝒯`: the cells met by at least one selected segment of the grid.  The horizontal
segments are `[A,B] × {y}` for `y ∈ ys`, the vertical ones `{x} × [C,D]` for `x ∈ xs`. -/
def gridCells (F : IndexedCells V) (A B C D : ℝ) (xs ys : Set ℝ) : Set V :=
  {v | (∃ y ∈ ys, Hits F (horizontal A B y) v) ∨ ∃ x ∈ xs, Hits F (vertical x C D) v}

theorem mem_gridCells_of_hits_horizontal (F : IndexedCells V) {A B C D : ℝ}
    {xs ys : Set ℝ} {y : ℝ} (hy : y ∈ ys) {v : V} (hv : Hits F (horizontal A B y) v) :
    v ∈ gridCells F A B C D xs ys := Or.inl ⟨y, hy, hv⟩

theorem mem_gridCells_of_hits_vertical (F : IndexedCells V) {A B C D : ℝ}
    {xs ys : Set ℝ} {x : ℝ} (hx : x ∈ xs) {v : V} (hv : Hits F (vertical x C D) v) :
    v ∈ gridCells F A B C D xs ys := Or.inr ⟨x, hx, hv⟩

/-! ### From good lines to the whole grid skeleton -/

/-- **Crossing from a horizontal segment to a vertical segment costs `2 t`.**  A cell on a
selected horizontal segment and a cell on a selected vertical segment are joined through
the cell containing their crossing point. -/
theorem ofReal_abs_sub_le_two_mul_of_horizontal_vertical (F : IndexedCells V) (f : V → ℝ)
    {A B C D : ℝ} {xs ys : Set ℝ}
    {t : ℝ≥0∞} (hysgood : ∀ y ∈ ys, y ∉ coordProj 1 '' uncoveredSet F)
    (hxs : xs ⊆ Set.Icc A B) (hys : ys ⊆ Set.Icc C D)
    (hhor : ∀ y ∈ ys, horizontalLineOscillation F f A B y ≤ t)
    (hver : ∀ x ∈ xs, verticalLineOscillation F f C D x ≤ t)
    {y : ℝ} (hy : y ∈ ys) {x : ℝ} (hx : x ∈ xs) {v w : V}
    (hv : Hits F (horizontal A B y) v) (hw : Hits F (vertical x C D) w) :
    ENNReal.ofReal |f w - f v| ≤ 2 * t := by
  obtain ⟨a, ha1, ha2⟩ :=
    exists_hits_horizontal_and_vertical F (hysgood y hy) (hxs hx) (hys hy)
  have h1 : ENNReal.ofReal |f a - f v| ≤ t :=
    ofReal_abs_sub_le_of_horizontalLineOscillation_le F f (hhor y hy) hv ha1
  have h2 : ENNReal.ofReal |f w - f a| ≤ t :=
    ofReal_abs_sub_le_of_verticalLineOscillation_le F f (hver x hx) ha2 hw
  calc ENNReal.ofReal |f w - f v|
      ≤ ENNReal.ofReal |f a - f v| + ENNReal.ofReal |f w - f a| :=
        ofReal_abs_sub_trans f v a w
    _ ≤ t + t := add_le_add h1 h2
    _ = 2 * t := by ring

/-- **`s:eq:gridresidual`.**  If every selected line carries oscillation at most `t`, then
any two cells of the grid skeleton differ by at most `3 t`.  Both offset sets must be
nonempty: the connection is made through at most three selected lines. -/
theorem ofReal_abs_sub_le_three_mul_of_mem_gridCells (F : IndexedCells V) (f : V → ℝ)
    {A B C D : ℝ} {xs ys : Set ℝ}
    {t : ℝ≥0∞} (hysgood : ∀ y ∈ ys, y ∉ coordProj 1 '' uncoveredSet F)
    (hxs : xs ⊆ Set.Icc A B) (hys : ys ⊆ Set.Icc C D)
    (hxne : xs.Nonempty) (hyne : ys.Nonempty)
    (hhor : ∀ y ∈ ys, horizontalLineOscillation F f A B y ≤ t)
    (hver : ∀ x ∈ xs, verticalLineOscillation F f C D x ≤ t)
    {v w : V} (hv : v ∈ gridCells F A B C D xs ys) (hw : w ∈ gridCells F A B C D xs ys) :
    ENNReal.ofReal |f w - f v| ≤ 3 * t := by
  obtain ⟨xstar, hxstar⟩ := hxne
  obtain ⟨ystar, hystar⟩ := hyne
  rcases hv with ⟨y₁, hy₁, hv₁⟩ | ⟨x₁, hx₁, hv₁⟩
  · rcases hw with ⟨y₂, hy₂, hw₂⟩ | ⟨x₂, hx₂, hw₂⟩
    · -- both on horizontal segments: go through a vertical segment
      obtain ⟨a, ha1, ha2⟩ :=
        exists_hits_horizontal_and_vertical F (hysgood y₂ hy₂) (hxs hxstar) (hys hy₂)
      have h1 : ENNReal.ofReal |f a - f v| ≤ 2 * t :=
        ofReal_abs_sub_le_two_mul_of_horizontal_vertical F f hysgood hxs hys hhor hver hy₁
          hxstar hv₁ ha2
      have h2 : ENNReal.ofReal |f w - f a| ≤ t :=
        ofReal_abs_sub_le_of_horizontalLineOscillation_le F f (hhor y₂ hy₂) ha1 hw₂
      calc ENNReal.ofReal |f w - f v|
          ≤ ENNReal.ofReal |f a - f v| + ENNReal.ofReal |f w - f a| :=
            ofReal_abs_sub_trans f v a w
        _ ≤ 2 * t + t := add_le_add h1 h2
        _ = 3 * t := by ring
    · -- horizontal to vertical
      refine le_trans
        (ofReal_abs_sub_le_two_mul_of_horizontal_vertical F f hysgood hxs hys hhor hver hy₁
          hx₂ hv₁ hw₂) ?_
      exact mul_le_mul' (by norm_num : (2 : ℝ≥0∞) ≤ 3) le_rfl
  · rcases hw with ⟨y₂, hy₂, hw₂⟩ | ⟨x₂, hx₂, hw₂⟩
    · -- vertical to horizontal: use the symmetric estimate and `|a - b| = |b - a|`
      have h := ofReal_abs_sub_le_two_mul_of_horizontal_vertical F f hysgood hxs hys hhor hver
        hy₂ hx₁ hw₂ hv₁
      rw [abs_sub_comm] at h
      exact le_trans h (mul_le_mul' (by norm_num : (2 : ℝ≥0∞) ≤ 3) le_rfl)
    · -- both on vertical segments: go through a horizontal segment
      obtain ⟨a, ha1, ha2⟩ :=
        exists_hits_horizontal_and_vertical F (hysgood ystar hystar) (hxs hx₁) (hys hystar)
      have h1 : ENNReal.ofReal |f a - f v| ≤ t :=
        ofReal_abs_sub_le_of_verticalLineOscillation_le F f (hver x₁ hx₁) hv₁ ha2
      have h2 : ENNReal.ofReal |f w - f a| ≤ 2 * t :=
        ofReal_abs_sub_le_two_mul_of_horizontal_vertical F f hysgood hxs hys hhor hver hystar
          hx₂ ha1 hw₂
      calc ENNReal.ofReal |f w - f v|
          ≤ ENNReal.ofReal |f a - f v| + ENNReal.ofReal |f w - f a| :=
            ofReal_abs_sub_trans f v a w
        _ ≤ t + 2 * t := add_le_add h1 h2
        _ = 3 * t := by ring

/-- The real-valued form used downstream: at a finite `t` the increment of `f` between any
two grid cells is at most `3 t`. -/
theorem abs_sub_le_three_mul_of_mem_gridCells (F : IndexedCells V) (f : V → ℝ)
    {A B C D : ℝ} {xs ys : Set ℝ}
    {t : ℝ} (hysgood : ∀ y ∈ ys, y ∉ coordProj 1 '' uncoveredSet F)
    (ht : 0 ≤ t) (hxs : xs ⊆ Set.Icc A B) (hys : ys ⊆ Set.Icc C D)
    (hxne : xs.Nonempty) (hyne : ys.Nonempty)
    (hhor : ∀ y ∈ ys, horizontalLineOscillation F f A B y ≤ ENNReal.ofReal t)
    (hver : ∀ x ∈ xs, verticalLineOscillation F f C D x ≤ ENNReal.ofReal t)
    {v w : V} (hv : v ∈ gridCells F A B C D xs ys) (hw : w ∈ gridCells F A B C D xs ys) :
    |f w - f v| ≤ 3 * t := by
  have h := ofReal_abs_sub_le_three_mul_of_mem_gridCells F f hysgood hxs hys hxne hyne hhor
    hver hv hw
  have h3 : (3 : ℝ≥0∞) * ENNReal.ofReal t = ENNReal.ofReal (3 * t) := by
    rw [ENNReal.ofReal_mul (by norm_num : (0:ℝ) ≤ 3)]
    simp
  rw [h3] at h
  have := ENNReal.toReal_mono ENNReal.ofReal_ne_top h
  rwa [ENNReal.toReal_ofReal (abs_nonneg _),
    ENNReal.toReal_ofReal (by positivity : (0:ℝ) ≤ 3 * t)] at this

/-! ### Confinement of the remaining cells to one grid rectangle -/

/-- The closed axis-parallel patch `[A,B] × [C,D]`. -/
def closedPatch (A B C D : ℝ) : Set Plane :=
  {z | A ≤ z 0 ∧ z 0 ≤ B ∧ C ≤ z 1 ∧ z 1 ≤ D}

/-- The open grid rectangle `(x₁,x₂) × (y₁,y₂)`. -/
def openRectangle (x₁ x₂ y₁ y₂ : ℝ) : Set Plane :=
  {z | x₁ < z 0 ∧ z 0 < x₂ ∧ y₁ < z 1 ∧ z 1 < y₂}

/-- The boundary frame `∂Q'` of the grid rectangle `[x₁,x₂] × [y₁,y₂]`, as the union of
its four closed sides. -/
def rectangleFrame (x₁ x₂ y₁ y₂ : ℝ) : Set Plane :=
  horizontal x₁ x₂ y₁ ∪ horizontal x₁ x₂ y₂ ∪ vertical x₁ y₁ y₂ ∪ vertical x₂ y₁ y₂

/-- A cell inside the patch which meets no selected vertical segment has a horizontal
coordinate projection avoiding every selected abscissa. -/
theorem notMem_image_coord_zero_of_notMem_gridCells (F : IndexedCells V) {A B C D : ℝ}
    {xs ys : Set ℝ} {v : V} (hv : v ∉ gridCells F A B C D xs ys)
    (hcell : (F.cell v : Set Plane) ⊆ closedPatch A B C D) {x : ℝ} (hx : x ∈ xs) :
    x ∉ (fun z : Plane => z 0) '' (F.cell v : Set Plane) := by
  rintro ⟨z, hz, rfl⟩
  exact hv (mem_gridCells_of_hits_vertical F hx ⟨z, hz, rfl, (hcell hz).2.2.1, (hcell hz).2.2.2⟩)

/-- A cell inside the patch which meets no selected horizontal segment has a vertical
coordinate projection avoiding every selected ordinate. -/
theorem notMem_image_coord_one_of_notMem_gridCells (F : IndexedCells V) {A B C D : ℝ}
    {xs ys : Set ℝ} {v : V} (hv : v ∉ gridCells F A B C D xs ys)
    (hcell : (F.cell v : Set Plane) ⊆ closedPatch A B C D) {y : ℝ} (hy : y ∈ ys) :
    y ∉ (fun z : Plane => z 1) '' (F.cell v : Set Plane) := by
  rintro ⟨z, hz, rfl⟩
  exact hv (mem_gridCells_of_hits_horizontal F hy ⟨z, hz, (hcell hz).1, (hcell hz).2.1, rfl⟩)

/-- **The one-dimensional confinement step.**  A preconnected set of reals which avoids
`S`, contains the point `u`, and is squeezed between a point of `S` in `[u - g, u]` and a
point of `S` in `[u, u + g]`, lies strictly between those two points, which are at
distance at most `2 g`. -/
theorem exists_strict_bounds_of_isPreconnected {S P : Set ℝ} {u g : ℝ}
    (hP : IsPreconnected P) (hu : u ∈ P) (hPS : ∀ s ∈ S, s ∉ P)
    (hfwd : ∃ s ∈ S, u ≤ s ∧ s ≤ u + g) (hbwd : ∃ s ∈ S, u - g ≤ s ∧ s ≤ u) :
    ∃ s₁ ∈ S, ∃ s₂ ∈ S, s₂ - s₁ ≤ 2 * g ∧ ∀ p ∈ P, s₁ < p ∧ p < s₂ := by
  obtain ⟨s₂, hs₂S, hs₂u, hs₂g⟩ := hfwd
  obtain ⟨s₁, hs₁S, hs₁g, hs₁u⟩ := hbwd
  have hs₁ne : s₁ ≠ u := fun h => hPS s₁ hs₁S (h ▸ hu)
  have hs₂ne : s₂ ≠ u := fun h => hPS s₂ hs₂S (h ▸ hu)
  have hs₁lt : s₁ < u := lt_of_le_of_ne hs₁u hs₁ne
  have hs₂gt : u < s₂ := lt_of_le_of_ne hs₂u (Ne.symm hs₂ne)
  refine ⟨s₁, hs₁S, s₂, hs₂S, by linarith, fun p hp => ⟨?_, ?_⟩⟩
  · by_contra hcon
    push_neg at hcon
    have hmem : s₁ ∈ Set.Icc p u := ⟨hcon, hs₁u⟩
    exact hPS s₁ hs₁S (hP.Icc_subset hp hu hmem)
  · by_contra hcon
    push_neg at hcon
    have hmem : s₂ ∈ Set.Icc u p := ⟨hs₂u, hcon⟩
    exact hPS s₂ hs₂S (hP.Icc_subset hu hp hmem)

/-- **The grid rectangle of an off-grid cell.**  A connected cell contained in the patch
`[A,B] × [C,D]` which meets none of the selected segments is confined to an open grid
rectangle whose two sides are at most `2 g`, and every cell meeting the boundary frame of
that rectangle belongs to the grid skeleton.  This is the geometric content of the
manuscript's "it is contained in the interior of one grid rectangle `Q'`, because it is
connected and cannot leave that rectangle without meeting its boundary", together with
"every cell `H'` meeting `∂Q'` is in `𝒯_R`" and "the sides of `Q'` are at most `2 α R`".
The cells are arbitrary connected compact sets. -/
theorem exists_gridRectangle_of_notMem_gridCells (F : IndexedCells V)
    (hconn : ∀ u : V, IsConnected (F.cell u : Set Plane)) {A B C D g : ℝ} {xs ys : Set ℝ}
    (hxs : xs ⊆ Set.Icc A B) (hys : ys ⊆ Set.Icc C D)
    (hxfwd : ∀ u ∈ Set.Icc A B, ∃ x ∈ xs, u ≤ x ∧ x ≤ u + g)
    (hxbwd : ∀ u ∈ Set.Icc A B, ∃ x ∈ xs, u - g ≤ x ∧ x ≤ u)
    (hyfwd : ∀ u ∈ Set.Icc C D, ∃ y ∈ ys, u ≤ y ∧ y ≤ u + g)
    (hybwd : ∀ u ∈ Set.Icc C D, ∃ y ∈ ys, u - g ≤ y ∧ y ≤ u)
    {v : V} (hv : v ∉ gridCells F A B C D xs ys)
    (hcell : (F.cell v : Set Plane) ⊆ closedPatch A B C D) :
    ∃ x₁ ∈ xs, ∃ x₂ ∈ xs, ∃ y₁ ∈ ys, ∃ y₂ ∈ ys,
      x₂ - x₁ ≤ 2 * g ∧ y₂ - y₁ ≤ 2 * g ∧
      (F.cell v : Set Plane) ⊆ openRectangle x₁ x₂ y₁ y₂ ∧
      ∀ w : V, Hits F (rectangleFrame x₁ x₂ y₁ y₂) w → w ∈ gridCells F A B C D xs ys := by
  obtain ⟨z, hz⟩ := (hconn v).nonempty
  have hzp := hcell hz
  -- the two coordinate projections of the cell
  have hP₀ : IsPreconnected ((fun w : Plane => w 0) '' (F.cell v : Set Plane)) :=
    (hconn v).isPreconnected.image _ (PiLp.continuous_apply 2 _ (0 : Fin 2)).continuousOn
  have hP₁ : IsPreconnected ((fun w : Plane => w 1) '' (F.cell v : Set Plane)) :=
    (hconn v).isPreconnected.image _ (PiLp.continuous_apply 2 _ (1 : Fin 2)).continuousOn
  obtain ⟨x₁, hx₁, x₂, hx₂, hxlen, hxsep⟩ :=
    exists_strict_bounds_of_isPreconnected hP₀ ⟨z, hz, rfl⟩
      (fun s hs => notMem_image_coord_zero_of_notMem_gridCells F hv hcell hs)
      (hxfwd (z 0) ⟨hzp.1, hzp.2.1⟩) (hxbwd (z 0) ⟨hzp.1, hzp.2.1⟩)
  obtain ⟨y₁, hy₁, y₂, hy₂, hylen, hysep⟩ :=
    exists_strict_bounds_of_isPreconnected hP₁ ⟨z, hz, rfl⟩
      (fun s hs => notMem_image_coord_one_of_notMem_gridCells F hv hcell hs)
      (hyfwd (z 1) ⟨hzp.2.2.1, hzp.2.2.2⟩) (hybwd (z 1) ⟨hzp.2.2.1, hzp.2.2.2⟩)
  have hx₁AB := hxs hx₁
  have hx₂AB := hxs hx₂
  have hy₁CD := hys hy₁
  have hy₂CD := hys hy₂
  refine ⟨x₁, hx₁, x₂, hx₂, y₁, hy₁, y₂, hy₂, hxlen, hylen, ?_, ?_⟩
  · intro w hw
    exact ⟨(hxsep _ ⟨w, hw, rfl⟩).1, (hxsep _ ⟨w, hw, rfl⟩).2,
      (hysep _ ⟨w, hw, rfl⟩).1, (hysep _ ⟨w, hw, rfl⟩).2⟩
  · intro w hw
    obtain ⟨p, hp, hpf⟩ := hw
    simp only [rectangleFrame, Set.mem_union] at hpf
    rcases hpf with ((hs | hs) | hs) | hs
    · exact mem_gridCells_of_hits_horizontal F hy₁
        ⟨p, hp, le_trans hx₁AB.1 hs.1, le_trans hs.2.1 hx₂AB.2, hs.2.2⟩
    · exact mem_gridCells_of_hits_horizontal F hy₂
        ⟨p, hp, le_trans hx₁AB.1 hs.1, le_trans hs.2.1 hx₂AB.2, hs.2.2⟩
    · exact mem_gridCells_of_hits_vertical F hx₁
        ⟨p, hp, hs.1, le_trans hy₁CD.1 hs.2.1, le_trans hs.2.2 hy₂CD.2⟩
    · exact mem_gridCells_of_hits_vertical F hx₂
        ⟨p, hp, hs.1, le_trans hy₁CD.1 hs.2.1, le_trans hs.2.2 hy₂CD.2⟩

/-! ### The deterministic good-grid step under the geometry hypothesis -/

end ReflectedGMS
