/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module ReflectedGMS.Environment.CanonicalRelabel at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.ReflectedGMS.Environment.CanonicalUniqueness
import LatticeProb.Bonanno.ReflectedGMS.Environment.SingularWitnessFacts
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar

/-! # The canonical similarity action on encoded environments

`Similarity.lean` transforms geometric cells, and `CanonicalUniqueness.lean`
shows a physical similarity determines at most one canonically labelled target
environment. This file constructs that target: transformed actual cells are
relabelled by their own least rational interior-hit index, conductances are
transported through the inverse label lookup, and absent labels keep the zero
slot. The result is an actual valid `Env` together with `IsSimilarity`.

Nothing here asserts measurability of the least-label events or of the joint
action; the environment encoding of `Code.lean` is reused verbatim. -/

set_option autoImplicit false

open MeasureTheory Set TopologicalSpace

namespace ReflectedGMS

/-! ## Elementary accessors for the geometry clauses -/

theorem Geometry.cell_isConnected {V : Type*} [Countable V] {F : IndexedCells V}
    (h : Geometry F) (v : V) : IsConnected (F.cell v : Set Plane) :=
  h.1 v

theorem Geometry.interior_cell_nonempty {V : Type*} [Countable V] {F : IndexedCells V}
    (h : Geometry F) (v : V) : (interior (F.cell v : Set Plane)).Nonempty :=
  h.2.1 v

theorem Geometry.volume_frontier_cell {V : Type*} [Countable V] {F : IndexedCells V}
    (h : Geometry F) (v : V) : volume (frontier (F.cell v : Set Plane)) = 0 :=
  h.2.2.1 v

theorem Geometry.disjoint_interior_cell {V : Type*} [Countable V] {F : IndexedCells V}
    (h : Geometry F) {v w : V} (hvw : v ≠ w) :
    Disjoint (interior (F.cell v : Set Plane)) (interior (F.cell w : Set Plane)) :=
  h.2.2.2.1 hvw

/-- The covering clause of `Geometry`: the uncovered set is `H¹`-null.

This replaces the earlier accessor `Geometry.iUnion_cell`, which returned
`(⋃ v, cell v) = Set.univ`.  That statement is no longer available: the covering clause was weakened
so that the singular-set manuscript's Definition 1.1 satisfies it (cells there cover only the
complement of an `H¹`-null closed set).  Consumers that need a covered point should use the
primitives in `Environment/UncoveredFacts.lean`, which supply a covered point in every nonempty open
set and covered points along almost every axis-parallel line. -/
theorem Geometry.hausdorffMeasure_uncoveredSet {V : Type*} [Countable V] {F : IndexedCells V}
    (h : Geometry F) : μH[1] (uncoveredSet F) = 0 :=
  h.2.2.2.2.1

theorem Geometry.graph_connected {V : Type*} [Countable V] {F : IndexedCells V}
    (h : Geometry F) : F.graph.toSimpleGraph.Connected :=
  h.2.2.2.2.2.1

theorem Geometry.neighborSet_finite {V : Type*} [Countable V] {F : IndexedCells V}
    (h : Geometry F) (v : V) : (F.graph.toSimpleGraph.neighborSet v).Finite :=
  h.2.2.2.2.2.2.1 v

theorem Geometry.cell_inter_nonempty {V : Type*} [Countable V] {F : IndexedCells V}
    (h : Geometry F) {v w : V} (hvw : F.graph.toSimpleGraph.Adj v w) :
    ((F.cell v : Set Plane) ∩ (F.cell w : Set Plane)).Nonempty :=
  h.2.2.2.2.2.2.2 hvw

theorem Geometry.nonempty_vertex {V : Type*} [Countable V] {F : IndexedCells V}
    (h : Geometry F) : Nonempty V :=
  h.graph_connected.nonempty

/-! ## Transport of the environment clauses along a weighted relabelling -/

/-- A conductance-preserving relabelling is an isomorphism of the cell graphs. -/
def conductanceGraphIso {V W : Type*} {F : IndexedCells V} {G : IndexedCells W} (q : V ≃ W)
    (hg : ∀ v w, G.graph.c (q v) (q w) = F.graph.c v w) :
    F.graph.toSimpleGraph ≃g G.graph.toSimpleGraph where
  toEquiv := q
  map_rel_iff' := by
    intro v w
    show G.graph.toSimpleGraph.Adj (q v) (q w) ↔ F.graph.toSimpleGraph.Adj v w
    simp only [ReflectedWalk.ConductanceGraph.toSimpleGraph_adj, hg]

theorem hits_relabel {V W : Type*} {F : IndexedCells V} {G : IndexedCells W} (q : V ≃ W)
    (hc : ∀ v, G.cell (q v) = F.cell v) (A : Set Plane) (v : V) :
    Hits G A (q v) ↔ Hits F A v := by
  unfold Hits
  rw [hc v]

theorem segmentReachable_relabel {V W : Type*} {F : IndexedCells V} {G : IndexedCells W}
    (q : V ≃ W) (hc : ∀ v, G.cell (q v) = F.cell v)
    (hg : ∀ v w, G.graph.c (q v) (q w) = F.graph.c v w) {A : Set Plane}
    (h : SegmentReachable F A) : SegmentReachable G A := by
  rw [segmentReachable_iff_finiteWalk] at h ⊢
  intro x y hx hy
  obtain ⟨v, rfl⟩ := q.surjective x
  obtain ⟨w, rfl⟩ := q.surjective y
  obtain ⟨p, hp⟩ := h v w ((hits_relabel q hc A v).mp hx) ((hits_relabel q hc A w).mp hy)
  have hmap : ∀ z ∈ (p.map (conductanceGraphIso q hg).toHom).support, Hits G A z := by
    intro z hz
    rw [SimpleGraph.Walk.support_map] at hz
    obtain ⟨x', hx', rfl⟩ := List.mem_map.mp hz
    exact (hits_relabel q hc A x').mpr (hp x' hx')
  exact ⟨p.map (conductanceGraphIso q hg).toHom, hmap⟩

theorem aeLineConnected_relabel {V W : Type*} {F : IndexedCells V} {G : IndexedCells W}
    (q : V ≃ W) (hc : ∀ v, G.cell (q v) = F.cell v)
    (hg : ∀ v w, G.graph.c (q v) (q w) = F.graph.c v w)
    (h : AELineConnected F) : AELineConnected G := by
  refine ⟨?_, ?_⟩
  · filter_upwards [h.1] with y hy
    intro a b hab
    exact segmentReachable_relabel q hc hg (hy a b hab)
  · filter_upwards [h.2] with x hx
    intro a b hab
    exact segmentReachable_relabel q hc hg (hx a b hab)

theorem geometry_relabel {V W : Type*} [Countable V] [Countable W]
    {F : IndexedCells V} {G : IndexedCells W} (q : V ≃ W)
    (hc : ∀ v, G.cell (q v) = F.cell v)
    (hg : ∀ v w, G.graph.c (q v) (q w) = F.graph.c v w)
    (h : Geometry F) : Geometry G := by
  have hadj : ∀ v w : V,
      G.graph.toSimpleGraph.Adj (q v) (q w) ↔ F.graph.toSimpleGraph.Adj v w := by
    intro v w
    simp only [ReflectedWalk.ConductanceGraph.toSimpleGraph_adj, hg]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro x
    obtain ⟨v, rfl⟩ := q.surjective x
    rw [hc v]
    exact h.cell_isConnected v
  · intro x
    obtain ⟨v, rfl⟩ := q.surjective x
    rw [hc v]
    exact h.interior_cell_nonempty v
  · intro x
    obtain ⟨v, rfl⟩ := q.surjective x
    rw [hc v]
    exact h.volume_frontier_cell v
  · intro x y hxy
    obtain ⟨v, rfl⟩ := q.surjective x
    obtain ⟨w, rfl⟩ := q.surjective y
    rw [hc v, hc w]
    exact h.disjoint_interior_cell (fun hvw => hxy (congrArg q hvw))
  · exact hausdorffMeasure_one_compl_iUnion_cell_relabel q hc h.hausdorffMeasure_uncoveredSet
  · exact (conductanceGraphIso q hg).connected_iff.mp h.graph_connected
  · intro x
    obtain ⟨v, rfl⟩ := q.surjective x
    have himg : G.graph.toSimpleGraph.neighborSet (q v)
        = q '' F.graph.toSimpleGraph.neighborSet v := by
      ext y
      obtain ⟨w, rfl⟩ := q.surjective y
      simp only [SimpleGraph.mem_neighborSet, hadj, Set.mem_image]
      constructor
      · intro hw
        exact ⟨w, hw, rfl⟩
      · rintro ⟨w', hw', hww⟩
        rwa [q.injective hww] at hw'
    rw [himg]
    exact (h.neighborSet_finite v).image q
  · intro x y hxy
    obtain ⟨v, rfl⟩ := q.surjective x
    obtain ⟨w, rfl⟩ := q.surjective y
    rw [hc v, hc w]
    exact h.cell_inter_nonempty ((hadj v w).mp hxy)

/-! ## The geometric similarity transport -/

theorem coe_positiveSimilarityHomeomorph (s : ℝ) (u : Plane) (hs : 0 < s) :
    ⇑(positiveSimilarityHomeomorph s u hs) = positiveSimilarity s u := rfl

theorem interior_coe_transformCell (s : ℝ) (u : Plane) (hs : 0 < s) (K : Code.CompactCell) :
    interior (transformCell s u hs K : Set Plane)
      = positiveSimilarity s u '' interior (K : Set Plane) := by
  rw [coe_transformCell, ← coe_positiveSimilarityHomeomorph s u hs,
    Homeomorph.image_interior]

theorem frontier_coe_transformCell (s : ℝ) (u : Plane) (hs : 0 < s) (K : Code.CompactCell) :
    frontier (transformCell s u hs K : Set Plane)
      = positiveSimilarity s u '' frontier (K : Set Plane) := by
  rw [coe_transformCell, ← coe_positiveSimilarityHomeomorph s u hs,
    Homeomorph.image_frontier]

theorem image_positiveSimilarity_eq_preimage (s : ℝ) (u : Plane) (hs : 0 < s) (A : Set Plane) :
    positiveSimilarity s u '' A = positiveSimilarity s⁻¹ (-s • u) ⁻¹' A := by
  ext w
  constructor
  · rintro ⟨z, hz, rfl⟩
    show positiveSimilarity s⁻¹ (-s • u) (positiveSimilarity s u z) ∈ A
    rw [positiveSimilarity_inverse_left s u z hs]
    exact hz
  · intro hw
    exact ⟨positiveSimilarity s⁻¹ (-s • u) w, hw, positiveSimilarity_inverse_right s u w hs⟩

theorem volume_positiveSimilarity_preimage_eq_zero (t : ℝ) (ht : t ≠ 0) (w : Plane)
    {A : Set Plane} (hA : volume A = 0) : volume (positiveSimilarity t w ⁻¹' A) = 0 := by
  have hcomp : positiveSimilarity t w ⁻¹' A
      = (fun z : Plane => z + -w) ⁻¹' ((fun z : Plane => t • z) ⁻¹' A) := by
    ext z
    simp [positiveSimilarity, sub_eq_add_neg]
  rw [hcomp, measure_preimage_add_right, Measure.addHaar_preimage_smul volume ht, hA, mul_zero]

theorem volume_positiveSimilarity_image_eq_zero (s : ℝ) (u : Plane) (hs : 0 < s)
    {A : Set Plane} (hA : volume A = 0) : volume (positiveSimilarity s u '' A) = 0 := by
  rw [image_positiveSimilarity_eq_preimage s u hs]
  exact volume_positiveSimilarity_preimage_eq_zero s⁻¹ (inv_ne_zero hs.ne') _ hA

theorem geometry_transformIndexedCells {V : Type*} [Countable V] (s : ℝ) (u : Plane) (hs : 0 < s)
    {F : IndexedCells V} (h : Geometry F) : Geometry (transformIndexedCells s u hs F) := by
  have hcont : Continuous (positiveSimilarity s u) :=
    (positiveSimilarityHomeomorph s u hs).continuous
  have hinj : Function.Injective (positiveSimilarity s u) :=
    (positiveSimilarityHomeomorph s u hs).injective
  have hsurj : Function.Surjective (positiveSimilarity s u) :=
    (positiveSimilarityHomeomorph s u hs).surjective
  refine ⟨?_, ?_, ?_, ?_, ?_, h.graph_connected, h.neighborSet_finite, ?_⟩
  · intro v
    rw [transformIndexedCells_cell, coe_transformCell]
    exact (h.cell_isConnected v).image _ hcont.continuousOn
  · intro v
    rw [transformIndexedCells_cell, interior_coe_transformCell]
    exact (h.interior_cell_nonempty v).image _
  · intro v
    rw [transformIndexedCells_cell, frontier_coe_transformCell]
    exact volume_positiveSimilarity_image_eq_zero s u hs (h.volume_frontier_cell v)
  · intro v w hvw
    rw [transformIndexedCells_cell, transformIndexedCells_cell,
      interior_coe_transformCell, interior_coe_transformCell]
    exact Set.disjoint_image_of_injective hinj (h.disjoint_interior_cell hvw)
  · exact hausdorffMeasure_one_compl_iUnion_cell_transform s u hs h.hausdorffMeasure_uncoveredSet
  · intro v w hvw
    rw [transformIndexedCells_cell, transformIndexedCells_cell, coe_transformCell,
      coe_transformCell, ← Set.image_inter hinj]
    exact (h.cell_inter_nonempty hvw).image _

/-! ## Almost-sure line connectivity of the transformed environment -/

theorem le_positiveScale_iff {s : ℝ} (hs : 0 < s) (c t w : ℝ) :
    c ≤ s * (t - w) ↔ s⁻¹ * c + w ≤ t := by
  constructor
  · intro h
    have h' : s⁻¹ * c ≤ t - w := (inv_mul_le_iff₀ hs).mpr h
    linarith
  · intro h
    have h' : s⁻¹ * c ≤ t - w := by linarith
    exact (inv_mul_le_iff₀ hs).mp h'

theorem positiveScale_le_iff {s : ℝ} (hs : 0 < s) (c t w : ℝ) :
    s * (t - w) ≤ c ↔ t ≤ s⁻¹ * c + w := by
  constructor
  · intro h
    have h' : t - w ≤ s⁻¹ * c := (le_inv_mul_iff₀ hs).mpr h
    linarith
  · intro h
    have h' : t - w ≤ s⁻¹ * c := by linarith
    exact (le_inv_mul_iff₀ hs).mp h'

theorem positiveScale_eq_iff {s : ℝ} (hs : 0 < s) (c t w : ℝ) :
    s * (t - w) = c ↔ t = s⁻¹ * c + w := by
  constructor
  · intro h
    have h2 : t - w = s⁻¹ * c := by rw [← h, inv_mul_cancel_left₀ hs.ne']
    linarith
  · intro h
    have h2 : t - w = s⁻¹ * c := by linarith
    rw [h2, mul_inv_cancel_left₀ hs.ne']

theorem preimage_positiveSimilarity_horizontal (s : ℝ) (u : Plane) (hs : 0 < s) (a b y : ℝ) :
    positiveSimilarity s u ⁻¹' horizontal a b y
      = horizontal (s⁻¹ * a + u 0) (s⁻¹ * b + u 0) (s⁻¹ * y + u 1) := by
  ext z
  have hz0 : positiveSimilarity s u z 0 = s * (z 0 - u 0) := by simp [positiveSimilarity]
  have hz1 : positiveSimilarity s u z 1 = s * (z 1 - u 1) := by simp [positiveSimilarity]
  simp only [Set.mem_preimage, horizontal, Set.mem_setOf_eq, hz0, hz1,
    le_positiveScale_iff hs, positiveScale_le_iff hs, positiveScale_eq_iff hs]

theorem preimage_positiveSimilarity_vertical (s : ℝ) (u : Plane) (hs : 0 < s) (x a b : ℝ) :
    positiveSimilarity s u ⁻¹' vertical x a b
      = vertical (s⁻¹ * x + u 0) (s⁻¹ * a + u 1) (s⁻¹ * b + u 1) := by
  ext z
  have hz0 : positiveSimilarity s u z 0 = s * (z 0 - u 0) := by simp [positiveSimilarity]
  have hz1 : positiveSimilarity s u z 1 = s * (z 1 - u 1) := by simp [positiveSimilarity]
  simp only [Set.mem_preimage, vertical, Set.mem_setOf_eq, hz0, hz1,
    le_positiveScale_iff hs, positiveScale_le_iff hs, positiveScale_eq_iff hs]

theorem hits_transformIndexedCells {V : Type*} (s : ℝ) (u : Plane) (hs : 0 < s)
    (F : IndexedCells V) (A : Set Plane) (v : V) :
    Hits (transformIndexedCells s u hs F) A v ↔ Hits F (positiveSimilarity s u ⁻¹' A) v := by
  unfold Hits
  rw [transformIndexedCells_cell, coe_transformCell, ← Set.image_inter_preimage,
    Set.image_nonempty]

theorem segmentReachable_transformIndexedCells {V : Type*} (s : ℝ) (u : Plane) (hs : 0 < s)
    (F : IndexedCells V) (A : Set Plane)
    (h : SegmentReachable F (positiveSimilarity s u ⁻¹' A)) :
    SegmentReachable (transformIndexedCells s u hs F) A := by
  rw [segmentReachable_iff_finiteWalk] at h ⊢
  intro v w hv hw
  obtain ⟨p, hp⟩ := h v w ((hits_transformIndexedCells s u hs F A v).mp hv)
    ((hits_transformIndexedCells s u hs F A w).mp hw)
  exact ⟨p, fun z hz => (hits_transformIndexedCells s u hs F A z).mpr (hp z hz)⟩

theorem volume_preimage_affine_eq_zero {a c : ℝ} (ha : a ≠ 0) {N : Set ℝ}
    (hN : volume N = 0) : volume ((fun y : ℝ => a * y + c) ⁻¹' N) = 0 := by
  have hcomp : (fun y : ℝ => a * y + c) ⁻¹' N
      = (fun y : ℝ => a * y) ⁻¹' ((fun y : ℝ => y + c) ⁻¹' N) := rfl
  rw [hcomp, Real.volume_preimage_mul_left ha, measure_preimage_add_right, hN, mul_zero]

theorem aeLineConnected_transformIndexedCells {V : Type*} (s : ℝ) (u : Plane) (hs : 0 < s)
    {F : IndexedCells V} (h : AELineConnected F) :
    AELineConnected (transformIndexedCells s u hs F) := by
  obtain ⟨Nh, Nv, hNhm, hNh0, hNvm, hNv0, hNh, hNv⟩ :=
    (aeLineConnected_iff_exists_measurable_null_sets F).mp h
  have hinv : (0 : ℝ) < s⁻¹ := inv_pos.mpr hs
  refine (aeLineConnected_iff_exists_measurable_null_sets _).mpr
    ⟨(fun y : ℝ => s⁻¹ * y + u 1) ⁻¹' Nh, (fun x : ℝ => s⁻¹ * x + u 0) ⁻¹' Nv,
      hNhm.preimage ((measurable_const_mul _).add_const _),
      volume_preimage_affine_eq_zero (ne_of_gt hinv) hNh0,
      hNvm.preimage ((measurable_const_mul _).add_const _),
      volume_preimage_affine_eq_zero (ne_of_gt hinv) hNv0, ?_, ?_⟩
  · intro y hy a b hab
    have hgood : HorizontalGood F (s⁻¹ * y + u 1) := hNh _ hy
    refine segmentReachable_transformIndexedCells s u hs F (horizontal a b y) ?_
    rw [preimage_positiveSimilarity_horizontal s u hs a b y]
    refine hgood _ _ ?_
    have := mul_lt_mul_of_pos_left hab hinv
    linarith
  · intro x hx a b hab
    have hgood : VerticalGood F (s⁻¹ * x + u 0) := hNv _ hx
    refine segmentReachable_transformIndexedCells s u hs F (vertical x a b) ?_
    rw [preimage_positiveSimilarity_vertical s u hs x a b]
    refine hgood _ _ ?_
    have := mul_lt_mul_of_pos_left hab hinv
    linarith

/-! ## Least rational interior labels exist -/

namespace Code

theorem exists_rationalPoint_mem {U : Set Plane} (hU : IsOpen U) (hne : U.Nonempty) :
    ∃ n : ℕ, rationalPoint n ∈ U := by
  obtain ⟨z, hz⟩ := hne
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hU z hz
  obtain ⟨a, ha⟩ := exists_rat_near (z 0) (half_pos hε)
  obtain ⟨b, hb⟩ := exists_rat_near (z 1) (half_pos hε)
  obtain ⟨n, hn⟩ := rationalPoint_exhausts a b
  refine ⟨n, hball ?_⟩
  have h0 : (WithLp.toLp 2 ![(a : ℝ), (b : ℝ)] : Plane) 0 = (a : ℝ) := by simp
  have h1 : (WithLp.toLp 2 ![(a : ℝ), (b : ℝ)] : Plane) 1 = (b : ℝ) := by simp
  have ha' : |(a : ℝ) - z 0| < ε / 2 := by rw [abs_sub_comm]; exact ha
  have hb' : |(b : ℝ) - z 1| < ε / 2 := by rw [abs_sub_comm]; exact hb
  have ha0 : (0 : ℝ) ≤ |(a : ℝ) - z 0| := abs_nonneg _
  have hb0 : (0 : ℝ) ≤ |(b : ℝ) - z 1| := abs_nonneg _
  rw [hn, Metric.mem_ball, EuclideanSpace.dist_eq]
  refine (Real.sqrt_lt' hε).mpr ?_
  rw [Fin.sum_univ_two, h0, h1, Real.dist_eq, Real.dist_eq]
  nlinarith

theorem exists_leastInteriorLabel {K : CompactCell}
    (hK : (interior (K : Set Plane)).Nonempty) : ∃ n : ℕ, LeastInteriorLabel K n := by
  classical
  obtain ⟨n, hn⟩ := exists_rationalPoint_mem isOpen_interior hK
  have hex : ∃ m : ℕ, rationalPoint m ∈ interior (K : Set Plane) := ⟨n, hn⟩
  exact ⟨Nat.find hex, Nat.find_spec hex, fun m hm => Nat.find_min hex hm⟩

/-- The least rational interior-hit index of a cell with nonempty interior. -/
noncomputable def leastInteriorLabel (K : CompactCell)
    (hK : (interior (K : Set Plane)).Nonempty) : ℕ :=
  (exists_leastInteriorLabel hK).choose

theorem leastInteriorLabel_spec (K : CompactCell)
    (hK : (interior (K : Set Plane)).Nonempty) :
    LeastInteriorLabel K (leastInteriorLabel K hK) :=
  (exists_leastInteriorLabel hK).choose_spec

/-! ## The canonical code of an indexed cell family -/

variable {V : Type*} [Countable V]

/-- The canonical label of a vertex: the least rational interior hit of its cell. -/
noncomputable def canonicalLabel (F : IndexedCells V) (hG : Geometry F) (v : V) : ℕ :=
  leastInteriorLabel (F.cell v) (hG.interior_cell_nonempty v)

theorem leastInteriorLabel_canonicalLabel (F : IndexedCells V) (hG : Geometry F) (v : V) :
    LeastInteriorLabel (F.cell v) (canonicalLabel F hG v) :=
  leastInteriorLabel_spec _ _

theorem canonicalLabel_injective (F : IndexedCells V) (hG : Geometry F) :
    Function.Injective (canonicalLabel F hG) := by
  intro v w hvw
  by_contra hne
  have h1 := (leastInteriorLabel_canonicalLabel F hG v).1
  have h2 := (leastInteriorLabel_canonicalLabel F hG w).1
  rw [hvw] at h1
  exact Set.disjoint_left.mp (hG.disjoint_interior_cell hne) h1 h2

/-- Inverse label lookup; junk values at labels that are not used. -/
noncomputable def canonicalVertex (F : IndexedCells V) (hG : Geometry F) (n : ℕ) : V :=
  haveI := hG.nonempty_vertex
  Function.invFun (canonicalLabel F hG) n

theorem canonicalVertex_canonicalLabel (F : IndexedCells V) (hG : Geometry F) (v : V) :
    canonicalVertex F hG (canonicalLabel F hG v) = v := by
  haveI := hG.nonempty_vertex
  exact Function.leftInverse_invFun (canonicalLabel_injective F hG) v

/-- Transformed cells placed at their own canonical labels; other slots absent. -/
noncomputable def canonicalSlots (F : IndexedCells V) (hG : Geometry F) (n : ℕ) :
    Option CompactCell :=
  if canonicalLabel F hG (canonicalVertex F hG n) = n then
    some (F.cell (canonicalVertex F hG n))
  else none

/-- Conductances read off through the inverse label lookup; zero at absent slots. -/
noncomputable def canonicalConductance (F : IndexedCells V) (hG : Geometry F) (n m : ℕ) : ℝ :=
  if canonicalLabel F hG (canonicalVertex F hG n) = n ∧
      canonicalLabel F hG (canonicalVertex F hG m) = m then
    F.graph.c (canonicalVertex F hG n) (canonicalVertex F hG m)
  else 0

/-- The canonically labelled raw code of an indexed cell family. -/
noncomputable def canonicalCode (F : IndexedCells V) (hG : Geometry F) : RawCode :=
  (canonicalSlots F hG, canonicalConductance F hG)

theorem canonicalSlots_canonicalLabel (F : IndexedCells V) (hG : Geometry F) (v : V) :
    canonicalSlots F hG (canonicalLabel F hG v) = some (F.cell v) := by
  unfold canonicalSlots
  rw [canonicalVertex_canonicalLabel]
  simp

theorem isSome_canonicalSlots_iff (F : IndexedCells V) (hG : Geometry F) (n : ℕ) :
    (canonicalSlots F hG n).isSome ↔ canonicalLabel F hG (canonicalVertex F hG n) = n := by
  unfold canonicalSlots
  split_ifs with h <;> simp [h]

theorem canonicalConductance_canonicalLabel (F : IndexedCells V) (hG : Geometry F) (v w : V) :
    canonicalConductance F hG (canonicalLabel F hG v) (canonicalLabel F hG w)
      = F.graph.c v w := by
  unfold canonicalConductance
  rw [canonicalVertex_canonicalLabel, canonicalVertex_canonicalLabel]
  simp

theorem canonicalConductance_eq_zero_left (F : IndexedCells V) (hG : Geometry F) {n : ℕ}
    (hn : ¬ canonicalLabel F hG (canonicalVertex F hG n) = n) (m : ℕ) :
    canonicalConductance F hG n m = 0 := by
  unfold canonicalConductance
  rw [if_neg (fun h => hn h.1)]

theorem canonicalConductance_eq_zero_right (F : IndexedCells V) (hG : Geometry F) (n : ℕ)
    {m : ℕ} (hm : ¬ canonicalLabel F hG (canonicalVertex F hG m) = m) :
    canonicalConductance F hG n m = 0 := by
  unfold canonicalConductance
  rw [if_neg (fun h => hm h.2)]

theorem not_canonicalLabel_of_canonicalSlots_none (F : IndexedCells V) (hG : Geometry F)
    {n : ℕ} (h : canonicalSlots F hG n = none) :
    ¬ canonicalLabel F hG (canonicalVertex F hG n) = n := by
  intro hc
  have hsome := (isSome_canonicalSlots_iff F hG n).mpr hc
  rw [h] at hsome
  exact Bool.noConfusion hsome

theorem admissible_canonicalCode (F : IndexedCells V) (hG : Geometry F) :
    AdmissibleConductance (canonicalCode F hG) where
  symm n m := by
    show canonicalConductance F hG n m = canonicalConductance F hG m n
    unfold canonicalConductance
    split_ifs with h1 h2 h3
    · exact F.graph.c_symm _ _
    · exact absurd ⟨h1.2, h1.1⟩ h2
    · exact absurd ⟨h3.2, h3.1⟩ h1
    · rfl
  nonneg n m := by
    show 0 ≤ canonicalConductance F hG n m
    unfold canonicalConductance
    split_ifs with h
    · exact F.graph.c_nonneg _ _
    · exact le_refl 0
  self n := by
    show canonicalConductance F hG n n = 0
    unfold canonicalConductance
    split_ifs with h
    · exact F.graph.c_self _
    · rfl
  absent n m h := by
    show canonicalConductance F hG n m = 0
    rcases h with h | h
    · exact canonicalConductance_eq_zero_left F hG
        (not_canonicalLabel_of_canonicalSlots_none F hG h) m
    · exact canonicalConductance_eq_zero_right F hG n
        (not_canonicalLabel_of_canonicalSlots_none F hG h)
  finiteRow n := by
    by_cases hn : canonicalLabel F hG (canonicalVertex F hG n) = n
    · have hsupp : (Function.support (F.graph.c (canonicalVertex F hG n))).Finite := by
        refine (hG.neighborSet_finite (canonicalVertex F hG n)).subset ?_
        intro w hw
        have hne : F.graph.c (canonicalVertex F hG n) w ≠ 0 := hw
        exact lt_of_le_of_ne (F.graph.c_nonneg _ _) (Ne.symm hne)
      refine (hsupp.image (canonicalLabel F hG)).subset ?_
      intro m hm
      have hval : canonicalConductance F hG n m ≠ 0 := hm
      have hcond : canonicalLabel F hG (canonicalVertex F hG m) = m := by
        by_contra hc
        exact hval (canonicalConductance_eq_zero_right F hG n hc)
      refine ⟨canonicalVertex F hG m, ?_, hcond⟩
      intro hzero
      apply hval
      unfold canonicalConductance
      rw [if_pos ⟨hn, hcond⟩]
      exact hzero
    · have hzero : ∀ m : ℕ, canonicalConductance F hG n m = 0 :=
        fun m => canonicalConductance_eq_zero_left F hG hn m
      have : Function.support ((canonicalCode F hG).2 n) = (∅ : Set ℕ) := by
        ext m
        simp [Function.mem_support, canonicalCode, hzero m]
      rw [this]
      exact Set.finite_empty

/-- The canonical relabelling bijection onto the active slots of the code. -/
noncomputable def canonicalVertexEquiv (F : IndexedCells V) (hG : Geometry F) :
    V ≃ Vertex (canonicalCode F hG) where
  toFun v := ⟨canonicalLabel F hG v, by
    show (canonicalSlots F hG (canonicalLabel F hG v)).isSome
    rw [canonicalSlots_canonicalLabel]
    rfl⟩
  invFun n := canonicalVertex F hG n.val
  left_inv v := canonicalVertex_canonicalLabel F hG v
  right_inv n := Subtype.ext ((isSome_canonicalSlots_iff F hG n.val).mp n.property)

theorem cell_canonicalVertexEquiv (F : IndexedCells V) (hG : Geometry F) (v : V) :
    cell (canonicalCode F hG) (canonicalVertexEquiv F hG v) = F.cell v := by
  refine Option.some_injective _ ?_
  show some (((canonicalCode F hG).1 (canonicalVertexEquiv F hG v).val).get
    (canonicalVertexEquiv F hG v).property) = some (F.cell v)
  rw [Option.some_get]
  exact canonicalSlots_canonicalLabel F hG v

theorem canonicalLabels_canonicalCode (F : IndexedCells V) (hG : Geometry F) :
    CanonicalLabels (canonicalCode F hG) := by
  intro v'
  have hval : canonicalLabel F hG (canonicalVertex F hG v'.val) = v'.val :=
    (isSome_canonicalSlots_iff F hG v'.val).mp v'.property
  have hv' : v' = canonicalVertexEquiv F hG (canonicalVertex F hG v'.val) :=
    Subtype.ext hval.symm
  rw [hv', cell_canonicalVertexEquiv]
  exact leastInteriorLabel_canonicalLabel F hG (canonicalVertex F hG v'.val)

theorem valid_canonicalCode (F : IndexedCells V) (hG : Geometry F)
    (hAE : AELineConnected F) : Valid (canonicalCode F hG) := by
  refine ⟨admissible_canonicalCode F hG, ?_, ?_, canonicalLabels_canonicalCode F hG⟩
  · exact geometry_relabel (canonicalVertexEquiv F hG)
      (fun v => cell_canonicalVertexEquiv F hG v)
      (fun v w => canonicalConductance_canonicalLabel F hG v w) hG
  · exact aeLineConnected_relabel (canonicalVertexEquiv F hG)
      (fun v => cell_canonicalVertexEquiv F hG v)
      (fun v w => canonicalConductance_canonicalLabel F hG v w) hAE

end Code

/-! ## The canonical similarity action -/

namespace EnvironmentLaws
open Code

/-- The actual canonically relabelled image of an environment under the
positive similarity `z ↦ s • (z - u)`. -/
noncomputable def similarityTargetEnv (s : ℝ) (u : Plane) (hs : 0 < s) (e : Env) : Env :=
  ⟨canonicalCode (transformIndexedCells s u hs (decode e))
      (geometry_transformIndexedCells s u hs (decode_geometry e)),
    valid_canonicalCode _ _
      (aeLineConnected_transformIndexedCells s u hs (decode_aeLineConnected e))⟩

/-- The canonical target really is a physical similarity image of `e`. -/
theorem isSimilarity_similarityTargetEnv (s : ℝ) (u : Plane) (hs : 0 < s) (e : Env) :
    IsSimilarity s u hs e (similarityTargetEnv s u hs e) := by
  refine ⟨canonicalVertexEquiv _ _, ?_, ?_⟩
  · intro v
    exact cell_canonicalVertexEquiv _ _ v
  · intro v w
    exact canonicalConductance_canonicalLabel _ _ v w

/-- With the existing uniqueness, the construction is the similarity action. -/
theorem eq_similarityTargetEnv_of_isSimilarity {s : ℝ} {u : Plane} {hs : 0 < s} {e e' : Env}
    (h : IsSimilarity s u hs e e') : e' = similarityTargetEnv s u hs e :=
  IsSimilarity.target_unique h (isSimilarity_similarityTargetEnv s u hs e)

end EnvironmentLaws

end ReflectedGMS
