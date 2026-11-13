/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module ReflectedGMS.Corrector.VerticalLineVariation at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.ReflectedGMS.Corrector.GoodLineOscillation

/-!
# The vertical line lemma, by coordinate swap

`ReflectedGMS.Corrector.LineVariation` and `ReflectedGMS.Corrector.GoodLineOscillation`
prove the two halves of the manuscript lemma `s:lem:lines` for *horizontal* segments
`[a,b] × {y}`.  The uniform sublinear-corrector argument needs the same two bounds for
*vertical* segments `{x} × [a,b]`.

Rather than duplicating the Tonelli/Cauchy-Schwarz computation and the simple-path
oscillation argument, this module transports them along the coordinate swap
`ReflectedGMS.planeSwap`, the linear isometry of the plane exchanging the two
coordinates.  Pushing an indexed cell family forward by `planeSwap` gives
`ReflectedGMS.swapIndexedCells`, whose *horizontal* data is exactly the *vertical* data of
the original family: `planeSwap ⁻¹' (horizontal a b y) = vertical y a b`, and the
conductance graph is literally unchanged.  Because `planeSwap` is an isometry the
geometric mass `∑_H d_H ^ 2 π*(H)` is preserved, so the transported estimates have the
*same* constants and refer to the *original* geometry and energy.

All statements live in `ℝ≥0∞`; no summability, finiteness or integrability hypothesis is
used, and the almost-everywhere statements quantify over *all* endpoint pairs `a < b`
simultaneously at a fixed good offset, as the manuscript's `x ∉ N_v` formulation
requires.
-/

set_option autoImplicit false

open MeasureTheory Set
open scoped ENNReal NNReal

namespace ReflectedGMS

variable {V : Type*}

/-! ### The coordinate swap of the plane -/

/-- The linear isometry of the plane exchanging the two coordinates. -/
noncomputable def planeSwap : Plane ≃ₗᵢ[ℝ] Plane :=
  LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ (Equiv.swap (0 : Fin 2) 1)

theorem planeSwap_apply (z : Plane) (i : Fin 2) :
    planeSwap z i = z (Equiv.swap (0 : Fin 2) 1 i) := by
  simp [planeSwap, Equiv.piCongrLeft']

theorem planeSwap_apply_zero (z : Plane) : planeSwap z 0 = z 1 := by
  rw [planeSwap_apply]; simp

theorem planeSwap_apply_one (z : Plane) : planeSwap z 1 = z 0 := by
  rw [planeSwap_apply]; simp

/-- The swap turns a horizontal segment into a vertical one: this is the whole geometric
content of the transfer. -/
theorem planeSwap_preimage_horizontal (a b y : ℝ) :
    planeSwap ⁻¹' (horizontal a b y) = vertical y a b := by
  ext z
  simp only [Set.mem_preimage, horizontal, vertical, Set.mem_setOf_eq,
    planeSwap_apply_zero, planeSwap_apply_one]
  tauto

/-! ### The swapped cell family -/

/-- The indexed cell family obtained by pushing every cell forward along the coordinate
swap.  The conductance graph is unchanged. -/
noncomputable def swapIndexedCells (F : IndexedCells V) : IndexedCells V where
  cell v := (F.cell v).map planeSwap planeSwap.continuous
  graph := F.graph

@[simp]
theorem swapIndexedCells_graph (F : IndexedCells V) :
    (swapIndexedCells F).graph = F.graph := rfl

theorem coe_cell_swapIndexedCells (F : IndexedCells V) (v : V) :
    ((swapIndexedCells F).cell v : Set Plane) = planeSwap '' (F.cell v : Set Plane) := rfl

/-- A swapped cell meets a set exactly when the original cell meets the swapped-back set. -/
theorem hits_swapIndexedCells (F : IndexedCells V) (A : Set Plane) (v : V) :
    Hits (swapIndexedCells F) A v ↔ Hits F (planeSwap ⁻¹' A) v := by
  constructor
  · rintro ⟨z, hz, hzA⟩
    rw [coe_cell_swapIndexedCells] at hz
    obtain ⟨w, hw, rfl⟩ := hz
    exact ⟨w, hw, hzA⟩
  · rintro ⟨w, hw, hwA⟩
    refine ⟨planeSwap w, ?_, hwA⟩
    rw [coe_cell_swapIndexedCells]
    exact ⟨w, hw, rfl⟩

/-- Horizontal hits of the swapped family are vertical hits of the original family. -/
theorem hits_swapIndexedCells_horizontal (F : IndexedCells V) (a b x : ℝ) (v : V) :
    Hits (swapIndexedCells F) (horizontal a b x) v ↔ Hits F (vertical x a b) v := by
  rw [hits_swapIndexedCells, planeSwap_preimage_horizontal]

/-- The swap preserves cell diameters, because it is an isometry. -/
theorem cellDiameter_swapIndexedCells (F : IndexedCells V) (v : V) :
    cellDiameter (swapIndexedCells F) v = cellDiameter F v := by
  simp only [cellDiameter, coe_cell_swapIndexedCells]
  exact planeSwap.isometry.ediam_image _

/-! ### Transport of the connectivity hypothesis -/

/-- Horizontal reachability for the swapped family is vertical reachability for the
original family.  The two conductance graphs are literally the same, so the finite walks
are the same objects and only the `Hits` predicate has to be translated. -/
theorem segmentReachable_swapIndexedCells_horizontal (F : IndexedCells V) (a b x : ℝ) :
    SegmentReachable (swapIndexedCells F) (horizontal a b x)
      ↔ SegmentReachable F (vertical x a b) := by
  rw [segmentReachable_iff_finiteWalk, segmentReachable_iff_finiteWalk]
  constructor
  · intro h v w hv hw
    obtain ⟨p, hp⟩ := h v w
      ((hits_swapIndexedCells_horizontal F a b x v).mpr hv)
      ((hits_swapIndexedCells_horizontal F a b x w).mpr hw)
    exact ⟨p, fun z hz => (hits_swapIndexedCells_horizontal F a b x z).mp (hp z hz)⟩
  · intro h v w hv hw
    obtain ⟨p, hp⟩ := h v w
      ((hits_swapIndexedCells_horizontal F a b x v).mp hv)
      ((hits_swapIndexedCells_horizontal F a b x w).mp hw)
    exact ⟨p, fun z hz => (hits_swapIndexedCells_horizontal F a b x z).mpr (hp z hz)⟩

/-- A good *vertical* offset of `F` is a good *horizontal* offset of `swapIndexedCells F`,
simultaneously for every endpoint pair. -/
theorem horizontalGood_swapIndexedCells (F : IndexedCells V) (x : ℝ) :
    HorizontalGood (swapIndexedCells F) x ↔ VerticalGood F x := by
  constructor
  · intro h a b hab
    exact (segmentReachable_swapIndexedCells_horizontal F a b x).mp (h a b hab)
  · intro h a b hab
    exact (segmentReachable_swapIndexedCells_horizontal F a b x).mpr (h a b hab)

/-! ### Vertical offsets met by a cell -/

/-- The set of offsets `x` whose vertical segment `{x} × [a,b]` meets the cell of `v`. -/
def verticalHitOffsets (F : IndexedCells V) (a b : ℝ) (v : V) : Set ℝ :=
  {x | Hits F (vertical x a b) v}

theorem mem_verticalHitOffsets {F : IndexedCells V} {a b x : ℝ} {v : V} :
    x ∈ verticalHitOffsets F a b v ↔ Hits F (vertical x a b) v := Iff.rfl

theorem verticalHitOffsets_eq_horizontal (F : IndexedCells V) (a b : ℝ) (v : V) :
    verticalHitOffsets F a b v = horizontalHitOffsets (swapIndexedCells F) a b v := by
  ext x
  rw [mem_verticalHitOffsets, mem_horizontalHitOffsets,
    hits_swapIndexedCells_horizontal]

theorem verticalHitOffsets_isCompact (F : IndexedCells V) (a b : ℝ) (v : V) :
    IsCompact (verticalHitOffsets F a b v) := by
  rw [verticalHitOffsets_eq_horizontal]
  exact horizontalHitOffsets_isCompact (swapIndexedCells F) a b v

theorem verticalHitOffsets_measurableSet (F : IndexedCells V) (a b : ℝ) (v : V) :
    MeasurableSet (verticalHitOffsets F a b v) :=
  (verticalHitOffsets_isCompact F a b v).measurableSet

/-! ### The vertical line variation -/

/-- The contribution of an ordered pair of cells to the variation along the vertical
segment `{x} × [a,b]`. -/
noncomputable def verticalLineEdgeTerm (F : IndexedCells V) (f : V → ℝ) (a b : ℝ)
    (p : V × V) (x : ℝ) : ℝ≥0∞ :=
  (verticalHitOffsets F a b p.1 ∩ verticalHitOffsets F a b p.2).indicator
    (fun _ => edgeGradAbs F.graph f p) x

theorem verticalLineEdgeTerm_eq_horizontal (F : IndexedCells V) (f : V → ℝ) (a b : ℝ)
    (p : V × V) (x : ℝ) :
    verticalLineEdgeTerm F f a b p x
      = horizontalLineEdgeTerm (swapIndexedCells F) f a b p x := by
  simp only [verticalLineEdgeTerm, horizontalLineEdgeTerm,
    verticalHitOffsets_eq_horizontal, swapIndexedCells_graph]

/-- `V_f(x)`: the total variation of `f` along the edges of the cell graph meeting the
vertical segment `{x} × [a,b]`.  As in the horizontal case the ordered-pair sum is
divided by two, so each unordered edge is counted once. -/
noncomputable def verticalLineVariation (F : IndexedCells V) (f : V → ℝ)
    (a b x : ℝ) : ℝ≥0∞ :=
  (∑' p : V × V, verticalLineEdgeTerm F f a b p x) / 2

theorem verticalLineVariation_eq_horizontal (F : IndexedCells V) (f : V → ℝ)
    (a b x : ℝ) :
    verticalLineVariation F f a b x
      = horizontalLineVariation (swapIndexedCells F) f a b x := by
  simp only [verticalLineVariation, horizontalLineVariation,
    verticalLineEdgeTerm_eq_horizontal]

theorem measurable_verticalLineEdgeTerm (F : IndexedCells V) (f : V → ℝ) (a b : ℝ)
    (p : V × V) : Measurable (verticalLineEdgeTerm F f a b p) :=
  measurable_const.indicator
    ((verticalHitOffsets_measurableSet F a b p.1).inter
      (verticalHitOffsets_measurableSet F a b p.2))

/-! ### The vertical integral estimate -/

/-! ### The vertical oscillation estimate -/

/-- At a good vertical offset, any two cells meeting the segment `{x} × [a,b]` have
`|f H' - f H| ≤ V_f(x)`, with the `/2` normalization intact. -/
theorem ofReal_abs_sub_le_verticalLineVariation (F : IndexedCells V) (f : V → ℝ)
    {a b x : ℝ} (hab : a < b) (hx : VerticalGood F x) {v w : V}
    (hv : Hits F (vertical x a b) v) (hw : Hits F (vertical x a b) w) :
    ENNReal.ofReal |f w - f v| ≤ verticalLineVariation F f a b x := by
  rw [verticalLineVariation_eq_horizontal]
  exact ofReal_abs_sub_le_horizontalLineVariation (swapIndexedCells F) f hab
    ((horizontalGood_swapIndexedCells F x).mpr hx)
    ((hits_swapIndexedCells_horizontal F a b x v).mpr hv)
    ((hits_swapIndexedCells_horizontal F a b x w).mpr hw)

/-- `osc_{ℍ(L_x)} f`: the oscillation of `f` over the cells meeting the vertical segment
`{x} × [a,b]`. -/
noncomputable def verticalLineOscillation (F : IndexedCells V) (f : V → ℝ)
    (a b x : ℝ) : ℝ≥0∞ :=
  ⨆ v : {v : V // Hits F (vertical x a b) v},
    ⨆ w : {w : V // Hits F (vertical x a b) w}, ENNReal.ofReal |f w.1 - f v.1|

/-- **The oscillation half of the vertical line lemma** (manuscript `s:lem:lines`, second
assertion, vertical case).  At a good offset the oscillation over the vertical segment
subgraph is at most the vertical line variation. -/
theorem verticalLineOscillation_le_verticalLineVariation (F : IndexedCells V)
    (f : V → ℝ) {a b x : ℝ} (hab : a < b) (hx : VerticalGood F x) :
    verticalLineOscillation F f a b x ≤ verticalLineVariation F f a b x :=
  iSup_le fun v => iSup_le fun w =>
    ofReal_abs_sub_le_verticalLineVariation F f hab hx v.2 w.2

/-! ### Both directions at once -/

end ReflectedGMS
