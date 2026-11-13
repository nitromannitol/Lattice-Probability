/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module ReflectedGMS.Limit.InteriorRepresentative at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.ReflectedGMS.Limit.CellRootedEncodingRepair
import LatticeProb.Bonanno.ReflectedGMS.Environment.UncoveredFacts
import LatticeProb.Bonanno.ReflectedGMS.InvarianceAssembly
import LatticeProb.Bonanno.ReflectedGMS.Spatial.RootedMassBounds
import LatticeProb.Bonanno.ReflectedGMS.Spatial.ActualSpatialDensityBridge
import LatticeProb.Bonanno.ReflectedGMS.Spatial.RootedFiniteEnergyDensityMeasurable
import LatticeProb.Bonanno.ReflectedGMS.Temporal.FlowSpaceTimeScale

/-!
# A measurable, similarity-covariant interior representative off the boundary mask (packet P5)

The cell-rooted repair (`Limit/CellRootedEncodingRepair`) needs a representative field whose
values are interior points of their cells lying on NO cell's frontier (`InteriorOffMask`), and the
cell-rooted transport needs it measurable and covariant along the canonical relabelling
(`RepTranslationCovariant`, `RepDilationCovariant`).  Only a non-measurable choice existed
(`CellRootedEncodingRepair.exists_interiorOffMask`).

## Why no incenter

Cells are compact, connected, with nonempty interior and null frontier, but NOT regular closed: a
valid environment may have a neighbouring cell `H'` whose frontier contains a "hair" through the
interior of `H`.  The incenter of `H` (or any point chosen from `H` alone) can lie on such a hair,
i.e. on the boundary mask.  The fix is to measure the distance to the OTHER cells, not to `Hᶜ`.

## The geometric input: interior points avoided by every other cell exist (AE-LC)

`freeSet F v := interior (cell v) \ ⋃ (neighbour cells)` is open (finitely many neighbours) and
nonempty (the neighbours meet `interior (cell v)` only on their null frontiers).  Every point of it
lies in no other cell (`eq_of_mem_freeSet`): if `p ∈ freeSet ∩ cell w`, `w ≠ v`, the connected cell
`w` leaves a small square around `p`, so (`rectangle_projection`, a clopen-rectangle argument) its
trace in the square projects onto a positive-measure set of horizontal or vertical offsets; a good
offset (AE-LC) gives a short segment inside `freeSet` hitting `v` and `w`, whose walk from `v` must
pass through a neighbour of `v` hitting the segment — impossible inside `freeSet`.  Hence
`exists_clear_point`: some point has positive distance to every other cell.

## The field

`Clear F v x` := `x` has a uniform positive distance to every other cell; it implies
`x ∈ interior (cell v)` and `x ∉ boundaryMask F`, and it is similarity covariant
(`clear_relabel_iff`).  The candidates `lexMin H + diam H • q_k` (`q_k = rationalPoint k`) form a
covariant dense family; `interiorField` takes the first clear candidate (`Nat.find`), which is
measurable (`measurable_find`, joint continuity of `infDist` on `Plane × CompactCell`).

## Results

* `interiorField : CellField` (measurable by construction);
* `isCellRepresentative_interiorField`, **`interiorOffMask_interiorField`** — everywhere, every
  valid environment, no gate;
* `representativeCovariant_interiorField` (every similarity relabelling), hence
  **`repTranslationCovariant_interiorField`**, **`repDilationCovariant_interiorField`**;
* `exists_interiorOffMask_covariant` (the packaged producer) and the flow/scale invariance of
  `Coupled interiorField.value`.

Nothing here certifies the transport at the cell-rooted law, `hregen`, or either main theorem.
-/

set_option autoImplicit false

open MeasureTheory Set Filter Topology

namespace ReflectedGMS.InteriorRepresentative

open Code EnvironmentFields EnvironmentLaws RootDensities InvarianceMainStatement
open ReflectedGMS.TwoSidedRegenerationFlow ReflectedGMS.CellRootedEncodingRepair
open ReflectedGMS.RootedFiniteEnergyDensityMeasurable ReflectedGMS.ActualMarkedBlockTransport

/-! ### 1. Squares, segments and rational points in the plane -/

/-- A point in the open square of half-side `r` around `p` is within `2 r` of `p`. -/
theorem dist_lt_of_abs_lt {p z : Plane} {r : ℝ} (hr : 0 < r) (h0 : |z 0 - p 0| < r)
    (h1 : |z 1 - p 1| < r) : dist z p < 2 * r := by
  rw [EuclideanSpace.dist_eq, Fin.sum_univ_two, Real.dist_eq, Real.dist_eq,
    Real.sqrt_lt' (by linarith), sq_abs, sq_abs]
  obtain ⟨h0a, h0b⟩ := abs_lt.1 h0
  obtain ⟨h1a, h1b⟩ := abs_lt.1 h1
  nlinarith

/-- The fixed rational points are dense in the plane. -/
theorem exists_rationalPoint_dist_lt (y : Plane) {ε : ℝ} (hε : 0 < ε) :
    ∃ k : ℕ, dist (rationalPoint k) y < ε := by
  obtain ⟨a, ha1, ha2⟩ := exists_rat_btwn (show y 0 - ε / 2 < y 0 + ε / 2 by linarith)
  obtain ⟨b, hb1, hb2⟩ := exists_rat_btwn (show y 1 - ε / 2 < y 1 + ε / 2 by linarith)
  obtain ⟨k, hk⟩ := rationalPoint_exhausts a b
  refine ⟨k, ?_⟩
  have h0 : rationalPoint k 0 = a := by rw [hk]; simp
  have h1 : rationalPoint k 1 = b := by rw [hk]; simp
  have h := dist_lt_of_abs_lt (p := y) (z := rationalPoint k) (r := ε / 2) (by linarith)
    (by rw [h0]; exact abs_lt.2 ⟨by linarith, by linarith⟩)
    (by rw [h1]; exact abs_lt.2 ⟨by linarith, by linarith⟩)
  linarith

/-- **Clopen-rectangle argument.**  A preconnected set through the centre of an open square that
leaves the square meets it along a positive-measure set of horizontal offsets or of vertical
offsets. -/
theorem rectangle_projection (D : Set Plane) (hD : IsPreconnected D) {y : Plane} (hy : y ∈ D)
    {r : ℝ} (hr : 0 < r) (hout : ∃ z ∈ D, ¬ (|z 0 - y 0| < r ∧ |z 1 - y 1| < r)) :
    volume {t : ℝ | ∃ z ∈ D, |z 0 - y 0| < r ∧ |z 1 - y 1| < r ∧ z 1 = t} ≠ 0 ∨
      volume {t : ℝ | ∃ z ∈ D, |z 0 - y 0| < r ∧ |z 1 - y 1| < r ∧ z 0 = t} ≠ 0 := by
  by_contra hcon
  push_neg at hcon
  obtain ⟨hA, hB⟩ := hcon
  have pick : ∀ {N : Set ℝ}, volume N = 0 → ∀ {α β : ℝ}, α < β → ∃ t ∈ Ioo α β, t ∉ N := by
    intro N hN α β hαβ
    by_contra h
    push_neg at h
    have h0 : volume (Ioo α β) = 0 := measure_mono_null h hN
    rw [Real.volume_Ioo, ENNReal.ofReal_eq_zero] at h0
    linarith
  obtain ⟨a, ha, haB⟩ := pick hB (show y 0 - r < y 0 by linarith)
  obtain ⟨b, hb, hbB⟩ := pick hB (show y 0 < y 0 + r by linarith)
  obtain ⟨c, hc, hcA⟩ := pick hA (show y 1 - r < y 1 by linarith)
  obtain ⟨d, hd, hdA⟩ := pick hA (show y 1 < y 1 + r by linarith)
  have hc0 : Continuous fun z : Plane => z 0 := by fun_prop
  have hc1 : Continuous fun z : Plane => z 1 := by fun_prop
  let U₁ : Set Plane := {z | a < z 0 ∧ z 0 < b ∧ c < z 1 ∧ z 1 < d}
  let U₂ : Set Plane := {z | z 0 < a ∨ b < z 0 ∨ z 1 < c ∨ d < z 1}
  have hU₁ : IsOpen U₁ :=
    (isOpen_lt continuous_const hc0).inter ((isOpen_lt hc0 continuous_const).inter
      ((isOpen_lt continuous_const hc1).inter (isOpen_lt hc1 continuous_const)))
  have hU₂ : IsOpen U₂ :=
    (isOpen_lt hc0 continuous_const).union ((isOpen_lt continuous_const hc0).union
      ((isOpen_lt hc1 continuous_const).union (isOpen_lt continuous_const hc1)))
  have hin : ∀ z : Plane, a ≤ z 0 → z 0 ≤ b → c ≤ z 1 → z 1 ≤ d →
      |z 0 - y 0| < r ∧ |z 1 - y 1| < r := fun z h1 h2 h3 h4 =>
    ⟨abs_lt.2 ⟨by linarith [ha.1], by linarith [hb.2]⟩,
      abs_lt.2 ⟨by linarith [hc.1], by linarith [hd.2]⟩⟩
  have hcover : D ⊆ U₁ ∪ U₂ := by
    intro z hz
    by_cases h2 : z ∈ U₂
    · exact Or.inr h2
    · left
      simp only [U₂, Set.mem_setOf_eq, not_or, not_lt] at h2
      obtain ⟨h1, h2, h3, h4⟩ := h2
      obtain ⟨hQ0, hQ1⟩ := hin z h1 h2 h3 h4
      show a < z 0 ∧ z 0 < b ∧ c < z 1 ∧ z 1 < d
      refine ⟨lt_of_le_of_ne h1 ?_, lt_of_le_of_ne h2 ?_, lt_of_le_of_ne h3 ?_,
        lt_of_le_of_ne h4 ?_⟩
      · intro heq; exact haB ⟨z, hz, hQ0, hQ1, heq.symm⟩
      · intro heq; exact hbB ⟨z, hz, hQ0, hQ1, heq⟩
      · intro heq; exact hcA ⟨z, hz, hQ0, hQ1, heq.symm⟩
      · intro heq; exact hdA ⟨z, hz, hQ0, hQ1, heq⟩
  have hne1 : (D ∩ U₁).Nonempty := ⟨y, hy, ha.2, hb.1, hc.2, hd.1⟩
  have hne2 : (D ∩ U₂).Nonempty := by
    obtain ⟨z, hz, hzQ⟩ := hout
    refine ⟨z, hz, ?_⟩
    by_contra h2
    simp only [U₂, Set.mem_setOf_eq, not_or, not_lt] at h2
    obtain ⟨h1, h2, h3, h4⟩ := h2
    exact hzQ (hin z h1 h2 h3 h4)
  obtain ⟨z, -, hz1, hz2⟩ := hD U₁ U₂ hU₁ hU₂ hcover hne1 hne2
  obtain ⟨h1, h2, h3, h4⟩ := hz1
  rcases hz2 with h | h | h | h <;> linarith

/-! ### 2. The free part of a cell: avoided by every other cell -/

section Geometry

variable {V : Type*} [Countable V] (F : IndexedCells V)

/-- The union of the neighbour cells of `v` (finitely many under `Geometry`). -/
def nbrUnion (v : V) : Set Plane :=
  ⋃ w ∈ F.graph.toSimpleGraph.neighborSet v, (F.cell w : Set Plane)

/-- **The free part of a cell**: its interior minus the neighbour cells. -/
def freeSet (v : V) : Set Plane :=
  interior (F.cell v : Set Plane) \ nbrUnion F v

theorem isClosed_nbrUnion (hF : Geometry F) (v : V) : IsClosed (nbrUnion F v) :=
  Set.Finite.isClosed_biUnion (hF.2.2.2.2.2.2.1 v) fun w _ => (F.cell w).isCompact.isClosed

theorem isOpen_freeSet (hF : Geometry F) (v : V) : IsOpen (freeSet F v) :=
  isOpen_interior.sdiff (isClosed_nbrUnion F hF v)

/-- The neighbour cells meet the interior of `v` only on the boundary mask. -/
theorem interior_inter_nbrUnion_subset (hF : Geometry F) (v : V) :
    interior (F.cell v : Set Plane) ∩ nbrUnion F v ⊆ boundaryMask F := by
  rintro x ⟨hxi, hxn⟩
  simp only [nbrUnion, Set.mem_iUnion] at hxn
  obtain ⟨w, hw, hxw⟩ := hxn
  have hwv : w ≠ v := ((F.graph.toSimpleGraph.mem_neighborSet v w).1 hw).ne'
  refine Set.mem_union_left _ (Set.mem_iUnion.2 ⟨w, ?_⟩)
  have hclosed : IsClosed (F.cell w : Set Plane) := (F.cell w).isCompact.isClosed
  rw [frontier, hclosed.closure_eq]
  exact ⟨hxw, fun hxw' => Set.disjoint_left.1 (hF.2.2.2.1 hwv) hxw' hxi⟩

/-- **The free part is nonempty**: otherwise the interior of `v` would sit in the null mask. -/
theorem freeSet_nonempty (hF : Geometry F) (v : V) : (freeSet F v).Nonempty := by
  by_contra hne
  have hsub : interior (F.cell v : Set Plane) ⊆ boundaryMask F := by
    intro x hx
    by_cases hxn : x ∈ nbrUnion F v
    · exact interior_inter_nbrUnion_subset F hF v ⟨hx, hxn⟩
    · exact (hne ⟨x, hx, hxn⟩).elim
  have hnull : volume (interior (F.cell v : Set Plane)) = 0 :=
    measure_mono_null hsub
      (measure_union_null (measure_iUnion_null fun w => hF.2.2.1 w) (volume_uncoveredSet hF))
  have hempty := MeasureTheory.Measure.interior_eq_empty_of_null hnull
  rw [interior_interior] at hempty
  exact (hF.2.1 v).ne_empty hempty

/-- Along a good horizontal offset, a point of the free part of `v` lies in no other cell. -/
theorem eq_of_mem_freeSet_horizontalGood (hF : Geometry F) {v w : V} {p : Plane}
    (hp : p ∈ freeSet F v) (hpw : p ∈ (F.cell w : Set Plane)) (hgood : HorizontalGood F (p 1)) :
    w = v := by
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 (isOpen_freeSet F hF v) p hp
  have hSsub : horizontal (p 0 - ε / 4) (p 0 + ε / 4) (p 1) ⊆ freeSet F v := by
    rintro z ⟨h1, h2, h3⟩
    apply hball
    rw [Metric.mem_ball]
    have h := dist_lt_of_abs_lt (p := p) (z := z) (r := ε / 2) (by linarith)
      (abs_lt.2 ⟨by linarith, by linarith⟩) (by rw [h3, sub_self, abs_zero]; linarith)
    linarith
  have hpS : p ∈ horizontal (p 0 - ε / 4) (p 0 + ε / 4) (p 1) :=
    ⟨by linarith, by linarith, rfl⟩
  have hv : Hits F (horizontal (p 0 - ε / 4) (p 0 + ε / 4) (p 1)) v :=
    ⟨p, interior_subset hp.1, hpS⟩
  have hw : Hits F (horizontal (p 0 - ε / 4) (p 0 + ε / 4) (p 1)) w := ⟨p, hpw, hpS⟩
  obtain ⟨q, hq⟩ := (horizontalGood_iff_finiteWalk F (p 1)).1 hgood _ _ (by linarith) v w hv hw
  by_contra hwv
  cases q with
  | nil => exact hwv rfl
  | cons hadj q' =>
      have hmem := List.mem_cons_of_mem v (SimpleGraph.Walk.start_mem_support q')
      rw [← SimpleGraph.Walk.support_cons hadj q'] at hmem
      obtain ⟨x, hxu, hxS⟩ := hq _ hmem
      exact (hSsub hxS).2 (Set.mem_biUnion hadj hxu)

/-- Along a good vertical offset, a point of the free part of `v` lies in no other cell. -/
theorem eq_of_mem_freeSet_verticalGood (hF : Geometry F) {v w : V} {p : Plane}
    (hp : p ∈ freeSet F v) (hpw : p ∈ (F.cell w : Set Plane)) (hgood : VerticalGood F (p 0)) :
    w = v := by
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 (isOpen_freeSet F hF v) p hp
  have hSsub : vertical (p 0) (p 1 - ε / 4) (p 1 + ε / 4) ⊆ freeSet F v := by
    rintro z ⟨h1, h2, h3⟩
    apply hball
    rw [Metric.mem_ball]
    have h := dist_lt_of_abs_lt (p := p) (z := z) (r := ε / 2) (by linarith)
      (by rw [h1, sub_self, abs_zero]; linarith) (abs_lt.2 ⟨by linarith, by linarith⟩)
    linarith
  have hpS : p ∈ vertical (p 0) (p 1 - ε / 4) (p 1 + ε / 4) :=
    ⟨rfl, by linarith, by linarith⟩
  have hv : Hits F (vertical (p 0) (p 1 - ε / 4) (p 1 + ε / 4)) v :=
    ⟨p, interior_subset hp.1, hpS⟩
  have hw : Hits F (vertical (p 0) (p 1 - ε / 4) (p 1 + ε / 4)) w := ⟨p, hpw, hpS⟩
  obtain ⟨q, hq⟩ := (verticalGood_iff_finiteWalk F (p 0)).1 hgood _ _ (by linarith) v w hv hw
  by_contra hwv
  cases q with
  | nil => exact hwv rfl
  | cons hadj q' =>
      have hmem := List.mem_cons_of_mem v (SimpleGraph.Walk.start_mem_support q')
      rw [← SimpleGraph.Walk.support_cons hadj q'] at hmem
      obtain ⟨x, hxu, hxS⟩ := hq _ hmem
      exact (hSsub hxS).2 (Set.mem_biUnion hadj hxu)

/-- **Every point of the free part of `v` lies in no other cell** (AE-LC + connected cells). -/
theorem eq_of_mem_freeSet (hF : Geometry F) (hL : AELineConnected F) {v w : V} {p : Plane}
    (hp : p ∈ freeSet F v) (hpw : p ∈ (F.cell w : Set Plane)) : w = v := by
  by_contra hwv
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 (isOpen_freeSet F hF v) p hp
  have hQ : ∀ z : Plane, |z 0 - p 0| < ε / 2 → |z 1 - p 1| < ε / 2 → z ∈ freeSet F v := by
    intro z h0 h1
    apply hball
    rw [Metric.mem_ball]
    have h := dist_lt_of_abs_lt (by linarith : (0 : ℝ) < ε / 2) h0 h1
    linarith
  have hout : ∃ z ∈ (F.cell w : Set Plane), ¬ (|z 0 - p 0| < ε / 2 ∧ |z 1 - p 1| < ε / 2) := by
    by_contra h
    push_neg at h
    obtain ⟨x, hx⟩ := hF.2.1 w
    have hxc := h x (interior_subset hx)
    exact Set.disjoint_left.1 (hF.2.2.2.1 hwv) hx (hQ x hxc.1 hxc.2).1
  rcases rectangle_projection _ (hF.1 w).isPreconnected hpw (by linarith : (0 : ℝ) < ε / 2)
      hout with hA | hB
  · have hex : ∃ t, t ∈ {t : ℝ | ∃ z ∈ (F.cell w : Set Plane), |z 0 - p 0| < ε / 2 ∧
        |z 1 - p 1| < ε / 2 ∧ z 1 = t} ∧ HorizontalGood F t := by
      by_contra h
      push_neg at h
      exact hA (measure_mono_null (fun t ht => h t ht) (ae_iff.1 hL.1))
    obtain ⟨t, ⟨z, hzw, h0, h1, rfl⟩, hgood⟩ := hex
    exact hwv (eq_of_mem_freeSet_horizontalGood F hF (hQ z h0 h1) hzw hgood)
  · have hex : ∃ t, t ∈ {t : ℝ | ∃ z ∈ (F.cell w : Set Plane), |z 0 - p 0| < ε / 2 ∧
        |z 1 - p 1| < ε / 2 ∧ z 0 = t} ∧ VerticalGood F t := by
      by_contra h
      push_neg at h
      exact hB (measure_mono_null (fun t ht => h t ht) (ae_iff.1 hL.2))
    obtain ⟨t, ⟨z, hzw, h0, h1, rfl⟩, hgood⟩ := hex
    exact hwv (eq_of_mem_freeSet_verticalGood F hF (hQ z h0 h1) hzw hgood)

/-- **A clear point exists**: some point has a uniform positive distance to every other cell. -/
theorem exists_clear_point (hF : Geometry F) (hL : AELineConnected F) (v : V) :
    ∃ p : Plane, ∃ δ > 0, ∀ w : V, w ≠ v → δ ≤ Metric.infDist p (F.cell w : Set Plane) := by
  obtain ⟨p, hp⟩ := freeSet_nonempty F hF v
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 (isOpen_freeSet F hF v) p hp
  refine ⟨p, ε, hε, fun w hwv => ?_⟩
  rw [Metric.le_infDist (F.cell w).nonempty]
  intro y hy
  by_contra hlt
  push_neg at hlt
  exact hwv (eq_of_mem_freeSet F hF hL (hball (Metric.mem_ball.2 (by rwa [dist_comm]))) hy)

/-! ### 3. Clear points -/

/-- **Clear point of `v`**: a uniform positive distance to every other cell. -/
def Clear (v : V) (x : Plane) : Prop :=
  ∃ δ > 0, ∀ w : V, w ≠ v → δ ≤ Metric.infDist x (F.cell w : Set Plane)

/-- The ball is contained in the cell.  Only the *covered* points of the ball are seen
directly; the cell is compact, hence closed, and the covered points are dense because the
uncovered set is `H¹`-null, so the inclusion extends to the whole ball. -/
theorem ball_subset_cell_of_forall (hF : Geometry F) {v : V} {x : Plane} {δ : ℝ}
    (h : ∀ w : V, w ≠ v → δ ≤ Metric.infDist x (F.cell w : Set Plane)) :
    Metric.ball x δ ⊆ (F.cell v : Set Plane) := by
  refine subset_of_isClosed_of_inter_compl_subset hF Metric.isOpen_ball
    (F.cell v).isCompact.isClosed ?_
  rintro y ⟨hy, hyc⟩
  obtain ⟨w, hw⟩ := exists_mem_cell_of_notMem_uncoveredSet hyc
  by_cases hwv : w = v
  · rw [← hwv]
    exact hw
  · exfalso
    have h1 := h w hwv
    have h2 : Metric.infDist x (F.cell w : Set Plane) ≤ dist x y :=
      Metric.infDist_le_dist_of_mem hw
    rw [Metric.mem_ball, dist_comm] at hy
    linarith

/-- A clear point is an interior point of its cell. -/
theorem mem_interior_of_clear (hF : Geometry F) {v : V} {x : Plane} (h : Clear F v x) :
    x ∈ interior (F.cell v : Set Plane) := by
  obtain ⟨δ, hδ, h⟩ := h
  exact interior_mono (ball_subset_cell_of_forall F hF h)
    (by rw [Metric.isOpen_ball.interior_eq]; exact Metric.mem_ball_self hδ)

/-- **A clear point is off the boundary mask.** -/
theorem notMem_boundaryMask_of_clear (hF : Geometry F) {v : V} {x : Plane} (h : Clear F v x) :
    x ∉ boundaryMask F := by
  -- a clear point lies in the interior of its own cell, so it is covered; only the frontier part
  -- of the mask can apply
  have hxcell : x ∈ ⋃ u, (F.cell u : Set Plane) :=
    Set.mem_iUnion.mpr ⟨v, interior_subset (mem_interior_of_clear F hF h)⟩
  intro hm
  have hmfr : x ∈ ⋃ w, frontier ((F.cell w : Set Plane)) := by
    rcases hm with hfr | hunc
    · exact hfr
    · exact absurd hxcell hunc
  obtain ⟨w, hw⟩ := Set.mem_iUnion.1 hmfr
  by_cases hwv : w = v
  · rw [hwv] at hw
    exact hw.2 (mem_interior_of_clear F hF h)
  · obtain ⟨δ, hδ, hδw⟩ := h
    have hxw : x ∈ (F.cell w : Set Plane) := (F.cell w).isCompact.isClosed.frontier_subset hw
    have h1 := hδw w hwv
    rw [Metric.infDist_zero_of_mem hxw] at h1
    linarith

/-- Points near a clear point with margin `δ` are clear. -/
theorem clear_of_dist_lt {v : V} {p x : Plane} {δ : ℝ} (hδ : 0 < δ)
    (hp : ∀ w : V, w ≠ v → δ ≤ Metric.infDist p (F.cell w : Set Plane)) (hx : dist x p < δ / 2) :
    Clear F v x := by
  refine ⟨δ / 2, by linarith, fun w hw => ?_⟩
  have h1 := Metric.infDist_le_infDist_add_dist (x := p) (y := x) (s := (F.cell w : Set Plane))
  have h2 := hp w hw
  rw [dist_comm] at h1
  linarith

end Geometry

/-! ### 4. Covariance of clear points -/

/-- **Clear points are similarity covariant.** -/
theorem clear_relabel_iff {s : ℝ} {u : Plane} {hs : 0 < s} {e e' : Env}
    {relabel : Vertex e.val ≃ Vertex e'.val} (hrel : IsSimilarityRelabel s u hs e e' relabel)
    (v : Vertex e.val) (x : Plane) :
    Clear (decode e') (relabel v) (positiveSimilarity s u x) ↔ Clear (decode e) v x := by
  have hdist : ∀ w : Vertex e.val, Metric.infDist (positiveSimilarity s u x)
      ((decode e').cell (relabel w) : Set Plane) =
        s * Metric.infDist x ((decode e).cell w : Set Plane) := fun w => by
    rw [hrel.1 w, coe_transformCell, Spatial.infDist_image_positiveSimilarity s u hs]
  constructor
  · rintro ⟨δ, hδ, h⟩
    refine ⟨δ / s, div_pos hδ hs, fun w hw => ?_⟩
    have h1 := h (relabel w) (fun heq => hw (relabel.injective heq))
    rw [hdist w] at h1
    rw [div_le_iff₀ hs, mul_comm]
    exact h1
  · rintro ⟨δ, hδ, h⟩
    refine ⟨s * δ, mul_pos hs hδ, fun w' hw' => ?_⟩
    obtain ⟨w, rfl⟩ := relabel.surjective w'
    have hwv : w ≠ v := fun heq => hw' (by rw [heq])
    rw [hdist w]
    exact mul_le_mul_of_nonneg_left (h w hwv) hs.le

/-! ### 5. Covariant candidates -/

/-- **The covariant candidates of a cell**: `lexMin H + diam H • q_k`. -/
noncomputable def candidate (K : CompactCell) (k : ℕ) : Plane :=
  InvarianceAssembly.lexMin K + Metric.diam (K : Set Plane) • rationalPoint k

theorem candidate_transformCell (s : ℝ) (u : Plane) (hs : 0 < s) (K : CompactCell) (k : ℕ) :
    candidate (transformCell s u hs K) k = positiveSimilarity s u (candidate K k) := by
  rw [candidate, candidate, InvarianceAssembly.lexMin_transformCell, coe_transformCell,
    Spatial.diam_image_positiveSimilarity s u hs, positiveSimilarity_apply,
    positiveSimilarity_apply, mul_smul, smul_sub, smul_sub, smul_add]
  abel

/-- **Some candidate is clear** at every active vertex of every valid environment. -/
theorem exists_candidate_clear (e : Env) (v : Vertex e.val) :
    ∃ k : ℕ, Clear (decode e) v (candidate ((decode e).cell v) k) := by
  obtain ⟨p, δ, hδ, hp⟩ :=
    exists_clear_point (decode e) (decode_geometry e) (decode_aeLineConnected e) v
  have hd : 0 < Metric.diam ((decode e).cell v : Set Plane) := FlowSpaceTimeScale.diam_cell_pos e v
  obtain ⟨k, hk⟩ := exists_rationalPoint_dist_lt
    ((Metric.diam ((decode e).cell v : Set Plane))⁻¹ •
      (p - InvarianceAssembly.lexMin ((decode e).cell v)))
    (div_pos hδ (mul_pos two_pos hd))
  refine ⟨k, clear_of_dist_lt (decode e) hδ hp ?_⟩
  have hp' : p = InvarianceAssembly.lexMin ((decode e).cell v) +
      Metric.diam ((decode e).cell v : Set Plane) •
        ((Metric.diam ((decode e).cell v : Set Plane))⁻¹ •
          (p - InvarianceAssembly.lexMin ((decode e).cell v))) := by
    rw [smul_smul, mul_inv_cancel₀ hd.ne', one_smul]
    abel
  rw [candidate]
  conv_lhs => rw [hp']
  rw [dist_add_left, dist_smul₀, Real.norm_eq_abs, abs_of_pos hd]
  calc Metric.diam ((decode e).cell v : Set Plane) * dist (rationalPoint k)
        ((Metric.diam ((decode e).cell v : Set Plane))⁻¹ •
          (p - InvarianceAssembly.lexMin ((decode e).cell v)))
      < Metric.diam ((decode e).cell v : Set Plane) *
          (δ / (2 * Metric.diam ((decode e).cell v : Set Plane))) :=
        mul_lt_mul_of_pos_left hk hd
    _ = δ / 2 := by
      have hd' := hd.ne'
      field_simp

/-! ### 6. The label-level selection and its measurability -/

/-- The clear predicate at a code label, with countably many thresholds. -/
def ClearSlot (e : Env) (n : ℕ) (x : Plane) : Prop :=
  ∃ j : ℕ, ∀ m : ℕ, (e.val.1 m).isSome → m ≠ n →
    1 / ((j : ℝ) + 1) ≤ Metric.infDist x (slotCell e m : Set Plane)

theorem clearSlot_iff (e : Env) (v : Vertex e.val) (x : Plane) :
    ClearSlot e v.val x ↔ Clear (decode e) v x := by
  constructor
  · rintro ⟨j, h⟩
    refine ⟨1 / ((j : ℝ) + 1), by positivity, fun w hw => ?_⟩
    have h1 := h w.val w.property (fun heq => hw (Subtype.ext heq))
    rwa [slotCell_eq_cell] at h1
  · rintro ⟨δ, hδ, h⟩
    obtain ⟨j, hj⟩ := exists_nat_one_div_lt hδ
    refine ⟨j, fun m hm hmn => ?_⟩
    have h1 := h ⟨m, hm⟩ (fun heq => hmn (congrArg Subtype.val heq))
    rw [slotCell_eq_cell e ⟨m, hm⟩]
    linarith

/-- The selection predicate at label `n`: vacuous at an absent label. -/
def SelPred (e : Env) (n k : ℕ) : Prop :=
  (e.val.1 n).isSome → ClearSlot e n (candidate (slotCell e n) k)

theorem selPred_iff (e : Env) (v : Vertex e.val) (k : ℕ) :
    SelPred e v.val k ↔ Clear (decode e) v (candidate ((decode e).cell v) k) := by
  unfold SelPred
  rw [← clearSlot_iff, ← slotCell_eq_cell]
  exact ⟨fun h => h v.property, fun h _ => h⟩

theorem exists_selPred (e : Env) (n : ℕ) : ∃ k, SelPred e n k := by
  by_cases hn : (e.val.1 n).isSome
  · obtain ⟨k, hk⟩ := exists_candidate_clear e ⟨n, hn⟩
    exact ⟨k, (selPred_iff e ⟨n, hn⟩ k).2 hk⟩
  · exact ⟨0, fun h => absurd h hn⟩

/-- The index of the first clear candidate. -/
noncomputable def selIndex (e : Env) (n : ℕ) : ℕ :=
  @Nat.find (SelPred e n) (Classical.decPred _) (exists_selPred e n)

theorem selPred_selIndex (e : Env) (n : ℕ) : SelPred e n (selIndex e n) :=
  @Nat.find_spec (SelPred e n) (Classical.decPred _) (exists_selPred e n)

theorem measurableSet_isSome (m : ℕ) : MeasurableSet {e : Env | (e.val.1 m).isSome} :=
  ((measurable_pi_apply m).comp (measurable_fst.comp measurable_inclusion))
    Spatial.measurableSet_slotIsSome

theorem measurable_candidate_slot (n k : ℕ) :
    Measurable fun e : Env => candidate (slotCell e n) k := by
  have hK := measurable_slotCell_env n
  exact (InvarianceAssembly.measurable_lexMin.comp hK).add
    ((Spatial.measurable_cellDiam.comp hK).smul_const _)

theorem measurable_clearSlot {X : Env → Plane} (hX : Measurable X) (n : ℕ) :
    Measurable fun e : Env => ClearSlot e n (X e) := by
  unfold ClearSlot
  refine Measurable.exists fun j => Measurable.forall fun m => ?_
  have hsome : Measurable fun e : Env => (e.val.1 m).isSome = true :=
    measurableSet_setOfPred.1 (measurableSet_isSome m)
  have hdist0 : Measurable ((fun q : Plane × CompactCell => Metric.infDist q.1 (q.2 : Set Plane)) ∘
      fun e : Env => (X e, slotCell e m)) :=
    FlowSpaceTimeScale.measurable_infDist_joint.comp (hX.prodMk (measurable_slotCell_env m))
  have hdist : Measurable fun e : Env => Metric.infDist (X e) (slotCell e m : Set Plane) := by
    simpa only [Function.comp_def] using hdist0
  have hle : Measurable fun e : Env =>
      1 / ((j : ℝ) + 1) ≤ Metric.infDist (X e) (slotCell e m : Set Plane) :=
    measurableSet_setOfPred.1 (measurableSet_le measurable_const hdist)
  exact hsome.imp (measurable_const.imp hle)

theorem measurable_selIndex (n : ℕ) : Measurable fun e : Env => selIndex e n := by
  refine @measurable_find Env _ (fun e k => SelPred e n k) (fun e => Classical.decPred _)
    (fun e => exists_selPred e n) fun k => ?_
  exact measurableSet_setOfPred.2
    ((measurableSet_setOfPred.1 (measurableSet_isSome n)).imp
      (measurable_clearSlot (measurable_candidate_slot n k) n))

/-! ### 7. The field -/

/-- The value at a label: the first clear candidate of a present cell, `0` at an absent label. -/
noncomputable def interiorValue (e : Env) (n : ℕ) : Plane :=
  if (e.val.1 n).isSome then candidate (slotCell e n) (selIndex e n) else 0

theorem measurable_interiorValue (n : ℕ) : Measurable fun e : Env => interiorValue e n := by
  unfold interiorValue
  have hjoint : Measurable fun p : Env × ℕ => candidate (slotCell p.1 n) p.2 :=
    measurable_from_prod_countable_left fun k => measurable_candidate_slot n k
  have h0 : Measurable ((fun p : Env × ℕ => candidate (slotCell p.1 n) p.2) ∘
      fun e : Env => (e, selIndex e n)) :=
    hjoint.comp (measurable_id.prodMk (measurable_selIndex n))
  have h1 : Measurable fun e : Env => candidate (slotCell e n) (selIndex e n) := by
    simpa only [Function.comp_def] using h0
  exact Measurable.ite (measurableSet_isSome n) h1 measurable_const

/-- **The measurable interior representative field.** -/
noncomputable def interiorField : CellField where
  value := interiorValue
  measurable_value := Measurable.of_eval fun n => measurable_interiorValue n
  absent_zero := fun e n hn => by
    show interiorValue e n = 0
    simp [interiorValue, hn]

theorem interiorField_at (e : Env) (v : Vertex e.val) :
    interiorField.at e v = candidate ((decode e).cell v) (selIndex e v.val) := by
  show interiorValue e v.val = _
  rw [interiorValue, if_pos v.property, slotCell_eq_cell]

/-- **The value at every active vertex is a clear point of its cell.** -/
theorem clear_interiorField (e : Env) (v : Vertex e.val) :
    Clear (decode e) v (interiorField.at e v) := by
  rw [interiorField_at, ← selPred_iff]
  exact selPred_selIndex e v.val

/-- The value is an interior point of its cell. -/
theorem mem_interior_interiorField (e : Env) (v : Vertex e.val) :
    interiorField.at e v ∈ interior ((decode e).cell v : Set Plane) :=
  mem_interior_of_clear (decode e) (decode_geometry e) (clear_interiorField e v)

/-- **(i) Cell representative.** -/
theorem isCellRepresentative_interiorField : IsCellRepresentative interiorField := fun e v =>
  interior_subset (mem_interior_interiorField e v)

/-- **(ii) Interior, off the boundary mask — at EVERY valid environment.** -/
theorem interiorOffMask_interiorField : InteriorOffMask interiorField.value := by
  intro e n hn
  have h := clear_interiorField e ⟨n, hn⟩
  exact ⟨notMem_boundaryMask_of_clear (decode e) (decode_geometry e) h,
    interior_subset (mem_interior_of_clear (decode e) (decode_geometry e) h)⟩

/-! ### 8. Covariance -/

/-- The selected index is invariant under every similarity relabelling. -/
theorem selIndex_relabel {s : ℝ} {u : Plane} {hs : 0 < s} {e e' : Env}
    {relabel : Vertex e.val ≃ Vertex e'.val} (hrel : IsSimilarityRelabel s u hs e e' relabel)
    (v : Vertex e.val) : selIndex e' (relabel v).val = selIndex e v.val := by
  unfold selIndex
  classical
  refine Nat.find_congr' ?_
  intro k
  rw [selPred_iff, selPred_iff, hrel.1 v, candidate_transformCell, clear_relabel_iff hrel]

/-- **(iv) Full physical covariance** along every similarity relabelling. -/
theorem representativeCovariant_interiorField : RepresentativeCovariant interiorField := by
  intro s u hs e e' relabel hrel v
  rw [interiorField_at, interiorField_at, selIndex_relabel hrel v, hrel.1 v,
    candidate_transformCell]

/-- Covariance along the canonical label map. -/
theorem interiorValue_simLabel {s : ℝ} {u : Plane} {hs : 0 < s} {e : Env} {n : ℕ}
    (h : (e.val.1 n).isSome) :
    interiorField.value (similarityTargetEnv s u hs e) (simLabel s u hs e n)
      = positiveSimilarity s u (interiorField.value e n) := by
  rw [simLabel_of_isSome h]
  exact representativeCovariant_interiorField s u hs e _
    (LabelBijectionProducer.similarityRelabel s u hs e)
    (LabelBijectionProducer.isSimilarityRelabel_similarityRelabel s u hs e) ⟨n, h⟩

/-- **(iv) Translation covariance along the canonical relabelling.** -/
theorem repTranslationCovariant_interiorField : RepTranslationCovariant interiorField.value := by
  intro u e n h
  have h1 : interiorField.value (translateEnv u e) (simLabel 1 u one_pos e n)
      = positiveSimilarity 1 u (interiorField.value e n) := interiorValue_simLabel h
  rw [h1, positiveSimilarity_apply, one_smul]

/-- **(iv) Dilation covariance along the canonical relabelling.** -/
theorem repDilationCovariant_interiorField : RepDilationCovariant interiorField.value := by
  intro C hC e n h
  rw [interiorValue_simLabel h, positiveSimilarity_apply, sub_zero]

section CellRootedLaw

open ProbabilityTheory ReflectedGMS.EnvironmentWalkDataProducer ReflectedGMS.FlowCodingKernel
  ReflectedGMS.OriginRootedTransportObstruction

end CellRootedLaw

end ReflectedGMS.InteriorRepresentative
