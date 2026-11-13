/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module ReflectedGMS.Environment.CanonicalSimilarityMeasurable at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.ReflectedGMS.Environment.CanonicalRelabel
import LatticeProb.Bonanno.ReflectedGMS.Spatial.NullBoundaryRoots

/-! # Joint measurability of the canonical similarity action on environments

`Environment/CanonicalRelabel.lean` constructs the canonically relabelled target
`EnvironmentLaws.similarityTargetEnv s u hs e` of a positive similarity and proves
that it is the unique environment related to `e` by `EnvironmentLaws.IsSimilarity`.
It asserts nothing about measurability.  This file supplies the missing analytic
input: the action

`({s // 0 < s} × Plane × Env) → Env,  (s, u, e) ↦ similarityTargetEnv s u hs e`

is measurable for the actual trace sigma algebra of `Code.Env`, jointly in the
scale, the centre and the environment.

The route is exactly the structure of the construction.

* The image of one cell under `z ↦ s • (z - u)` is *jointly continuous* in
  `(s, u, K)` for the Hausdorff metric on nonempty compact cells: the similarity
  is `|s|`-Lipschitz, so the Hausdorff distance of two images is at most
  `|s|` times the Hausdorff distance of the cells, while two similarities applied
  to one cell differ by at most `|s - t| * R + ‖s • u - t • v‖` on the ball of
  radius `R` containing the cell.
* The canonical label events are therefore measurable: the least rational
  interior-hit condition is a countable Boolean combination of the *already
  checked* interior-hit sets `Spatial.measurableSet_cellInterior` evaluated at the
  transformed cell.
* On the event that source slot `m` carries target label `n`, the target slot `n`
  of the code is the transformed cell of slot `m`, and the target conductance is a
  fixed entry of the source conductance matrix; off all these events the target
  slot is absent and the conductance is zero.  A countable-pieces measurability
  criterion assembles the slot and conductance components, which determine the
  action because `Env` carries the trace sigma algebra.

No measurable choice is assumed, the valid-environment subtype is preserved and
the interior-hit measurability of the spatial producer is reused verbatim.
-/

set_option autoImplicit false
set_option maxHeartbeats 1600000

open MeasureTheory Set TopologicalSpace Metric
open scoped ENNReal

namespace ReflectedGMS.CanonicalSimilarity

open Code EnvironmentLaws Spatial

/-! ### A countable-pieces measurability criterion -/

/-- A function that agrees with a measurable function on each of countably many
measurable pieces, and is constant off their union, is measurable. -/
theorem measurable_of_countable_pieces {X Y ι : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    [Countable ι] {S : ι → Set X} (hS : ∀ i, MeasurableSet (S i)) {f : X → Y} {g : ι → X → Y}
    (hg : ∀ i, Measurable (g i)) {c : Y} (hfS : ∀ i, ∀ x ∈ S i, f x = g i x)
    (hfc : ∀ x, (∀ i, x ∉ S i) → f x = c) : Measurable f := by
  intro B hB
  have hpieces : MeasurableSet (⋃ i, S i ∩ g i ⁻¹' B) :=
    MeasurableSet.iUnion fun i => (hS i).inter (hg i hB)
  by_cases hc : c ∈ B
  · have hEq : f ⁻¹' B = (⋃ i, S i ∩ g i ⁻¹' B) ∪ (⋃ i, S i)ᶜ := by
      ext x
      simp only [mem_preimage, mem_union, mem_iUnion, mem_inter_iff, mem_compl_iff, not_exists]
      constructor
      · intro hx
        by_cases hmem : ∃ i, x ∈ S i
        · obtain ⟨i, hi⟩ := hmem
          exact Or.inl ⟨i, hi, by rw [← hfS i x hi]; exact hx⟩
        · exact Or.inr (not_exists.mp hmem)
      · rintro (⟨i, hi, hgi⟩ | hout)
        · rw [hfS i x hi]
          exact hgi
        · rw [hfc x hout]
          exact hc
    rw [hEq]
    exact hpieces.union (MeasurableSet.iUnion hS).compl
  · have hEq : f ⁻¹' B = ⋃ i, S i ∩ g i ⁻¹' B := by
      ext x
      simp only [mem_preimage, mem_iUnion, mem_inter_iff]
      constructor
      · intro hx
        by_cases hmem : ∃ i, x ∈ S i
        · obtain ⟨i, hi⟩ := hmem
          exact ⟨i, hi, by rw [← hfS i x hi]; exact hx⟩
        · refine absurd ?_ hc
          rw [← hfc x (not_exists.mp hmem)]
          exact hx
      · rintro ⟨i, hi, hgi⟩
        rw [hfS i x hi]
        exact hgi
    rw [hEq]
    exact hpieces

/-! ### The similarity image of one cell, jointly in scale, centre and cell -/

/-- The image of a nonempty compact cell under `z ↦ s • (z - u)`, for an arbitrary
real scale.  On positive scales this is the existing `transformCell`. -/
noncomputable def similarityCell (s : ℝ) (u : Plane) (K : CompactCell) : CompactCell :=
  K.map (positiveSimilarity s u) (by
    unfold positiveSimilarity
    fun_prop)

@[simp]
theorem coe_similarityCell (s : ℝ) (u : Plane) (K : CompactCell) :
    (similarityCell s u K : Set Plane) = positiveSimilarity s u '' (K : Set Plane) := rfl

theorem similarityCell_eq_transformCell (s : ℝ) (u : Plane) (hs : 0 < s) (K : CompactCell) :
    similarityCell s u K = transformCell s u hs K := by
  apply SetLike.coe_injective
  rw [coe_similarityCell, coe_transformCell]

/-- The metric on nonempty compact cells is the Hausdorff edistance. -/
theorem edist_compactCell (K L : CompactCell) :
    edist K L = hausdorffEDist (K : Set Plane) (L : Set Plane) := rfl

/-- A Lipschitz map contracts Hausdorff edistances of compact sets by its constant. -/
theorem hausdorffEDist_image_le_mul {C : ℝ≥0∞} {f : Plane → Plane}
    (hf : ∀ x y, edist (f x) (f y) ≤ C * edist x y) {A B : Set Plane}
    (hA : IsCompact A) (hB : IsCompact B) (hAne : A.Nonempty) (hBne : B.Nonempty) :
    hausdorffEDist (f '' A) (f '' B) ≤ C * hausdorffEDist A B := by
  refine hausdorffEDist_le_of_mem_edist ?_ ?_
  · rintro x ⟨a, ha, rfl⟩
    obtain ⟨b, hb, hab⟩ := hB.exists_infEDist_eq_edist hBne a
    refine ⟨f b, mem_image_of_mem f hb, ?_⟩
    calc edist (f a) (f b) ≤ C * edist a b := hf a b
      _ = C * infEDist a B := by rw [hab]
      _ ≤ C * hausdorffEDist A B := by
          gcongr
          exact infEDist_le_hausdorffEDist_of_mem ha
  · rintro y ⟨b, hb, rfl⟩
    obtain ⟨a, ha, hba⟩ := hA.exists_infEDist_eq_edist hAne b
    refine ⟨f a, mem_image_of_mem f ha, ?_⟩
    calc edist (f b) (f a) ≤ C * edist b a := hf b a
      _ = C * infEDist b A := by rw [hba]
      _ ≤ C * hausdorffEDist A B := by
          rw [hausdorffEDist_comm]
          gcongr
          exact infEDist_le_hausdorffEDist_of_mem hb

/-- A positive similarity is `|s|`-Lipschitz. -/
theorem edist_positiveSimilarity_le (s : ℝ) (u : Plane) (x y : Plane) :
    edist (positiveSimilarity s u x) (positiveSimilarity s u y)
      ≤ ENNReal.ofReal |s| * edist x y := by
  rw [edist_dist, edist_dist, ← ENNReal.ofReal_mul (abs_nonneg s)]
  refine ENNReal.ofReal_le_ofReal ?_
  rw [dist_eq_norm, dist_eq_norm]
  have hsub : positiveSimilarity s u x - positiveSimilarity s u y = s • (x - y) := by
    show s • (x - u) - s • (y - u) = s • (x - y)
    rw [← smul_sub]
    congr 1
    abel
  rw [hsub, norm_smul, Real.norm_eq_abs]

/-- Two cells with the same similarity: the Hausdorff distance contracts by `|s|`. -/
theorem edist_similarityCell_cell_le (s : ℝ) (u : Plane) (K L : CompactCell) :
    edist (similarityCell s u K) (similarityCell s u L) ≤ ENNReal.ofReal |s| * edist K L := by
  rw [edist_compactCell, edist_compactCell, coe_similarityCell, coe_similarityCell]
  exact hausdorffEDist_image_le_mul (edist_positiveSimilarity_le s u) K.isCompact L.isCompact
    K.nonempty L.nonempty

/-- One cell with two similarities: the images differ by the pointwise parameter
error on a ball containing the cell. -/
theorem edist_similarityCell_param_le {R : ℝ} (s t : ℝ) (u v : Plane) (K : CompactCell)
    (hR : ∀ x ∈ (K : Set Plane), ‖x‖ ≤ R) :
    edist (similarityCell s u K) (similarityCell t v K)
      ≤ ENNReal.ofReal (|s - t| * R + ‖s • u - t • v‖) := by
  have key : ∀ x ∈ (K : Set Plane),
      edist (positiveSimilarity s u x) (positiveSimilarity t v x)
        ≤ ENNReal.ofReal (|s - t| * R + ‖s • u - t • v‖) := by
    intro x hx
    rw [edist_dist]
    refine ENNReal.ofReal_le_ofReal ?_
    rw [dist_eq_norm]
    have hsub : positiveSimilarity s u x - positiveSimilarity t v x
        = (s - t) • x - (s • u - t • v) := by
      show s • (x - u) - t • (x - v) = (s - t) • x - (s • u - t • v)
      rw [smul_sub, smul_sub, sub_smul]
      abel
    have hmul : |s - t| * ‖x‖ ≤ |s - t| * R :=
      mul_le_mul_of_nonneg_left (hR x hx) (abs_nonneg _)
    rw [hsub]
    calc ‖(s - t) • x - (s • u - t • v)‖ ≤ ‖(s - t) • x‖ + ‖s • u - t • v‖ := norm_sub_le _ _
      _ = |s - t| * ‖x‖ + ‖s • u - t • v‖ := by rw [norm_smul, Real.norm_eq_abs]
      _ ≤ |s - t| * R + ‖s • u - t • v‖ := by linarith
  rw [edist_compactCell, coe_similarityCell, coe_similarityCell]
  refine hausdorffEDist_le_of_mem_edist ?_ ?_
  · rintro w ⟨x, hx, rfl⟩
    exact ⟨positiveSimilarity t v x, mem_image_of_mem _ hx, key x hx⟩
  · rintro w ⟨x, hx, rfl⟩
    refine ⟨positiveSimilarity s u x, mem_image_of_mem _ hx, ?_⟩
    rw [edist_comm]
    exact key x hx

/-- The combined real-distance estimate for the cell similarity map. -/
theorem dist_similarityCell_le {R : ℝ} (s t : ℝ) (u v : Plane) (K L : CompactCell)
    (hR : ∀ x ∈ (L : Set Plane), ‖x‖ ≤ R) (hR0 : 0 ≤ R) :
    dist (similarityCell s u K) (similarityCell t v L)
      ≤ |s| * dist K L + (|s - t| * R + ‖s • u - t • v‖) := by
  have h1 : dist (similarityCell s u K) (similarityCell s u L) ≤ |s| * dist K L := by
    have h := edist_similarityCell_cell_le s u K L
    rw [edist_dist, edist_dist, ← ENNReal.ofReal_mul (abs_nonneg s)] at h
    exact (ENNReal.ofReal_le_ofReal_iff (mul_nonneg (abs_nonneg s) dist_nonneg)).mp h
  have h2 : dist (similarityCell s u L) (similarityCell t v L)
      ≤ |s - t| * R + ‖s • u - t • v‖ := by
    have h := edist_similarityCell_param_le s t u v L hR
    rw [edist_dist] at h
    exact (ENNReal.ofReal_le_ofReal_iff
      (add_nonneg (mul_nonneg (abs_nonneg _) hR0) (norm_nonneg _))).mp h
  calc dist (similarityCell s u K) (similarityCell t v L)
      ≤ dist (similarityCell s u K) (similarityCell s u L)
          + dist (similarityCell s u L) (similarityCell t v L) := dist_triangle _ _ _
    _ ≤ |s| * dist K L + (|s - t| * R + ‖s • u - t • v‖) := add_le_add h1 h2

theorem exists_norm_bound (K : CompactCell) : ∃ R : ℝ, 0 ≤ R ∧ ∀ x ∈ (K : Set Plane), ‖x‖ ≤ R := by
  obtain ⟨R, hR⟩ := K.isCompact.isBounded.subset_closedBall (0 : Plane)
  obtain ⟨x₀, hx₀⟩ := K.nonempty
  exact ⟨R, le_trans (norm_nonneg x₀) (mem_closedBall_zero_iff.mp (hR hx₀)),
    fun x hx => mem_closedBall_zero_iff.mp (hR hx)⟩

/-- The cell similarity map is jointly continuous in scale, centre and cell. -/
theorem continuous_similarityCell :
    Continuous fun p : ℝ × Plane × CompactCell => similarityCell p.1 p.2.1 p.2.2 := by
  rw [continuous_iff_continuousAt]
  rintro ⟨s₀, u₀, K₀⟩
  obtain ⟨R, hR0, hR⟩ := exists_norm_bound K₀
  have hbound : ∀ p : ℝ × Plane × CompactCell,
      dist (similarityCell p.1 p.2.1 p.2.2) (similarityCell s₀ u₀ K₀)
        ≤ |p.1| * dist p.2.2 K₀ + (|p.1 - s₀| * R + ‖p.1 • p.2.1 - s₀ • u₀‖) :=
    fun p => dist_similarityCell_le p.1 s₀ p.2.1 u₀ p.2.2 K₀ hR hR0
  have hs1 : Continuous fun p : ℝ × Plane × CompactCell => p.1 := continuous_fst
  have hu : Continuous fun p : ℝ × Plane × CompactCell => p.2.1 :=
    continuous_fst.comp continuous_snd
  have hK : Continuous fun p : ℝ × Plane × CompactCell => p.2.2 :=
    continuous_snd.comp continuous_snd
  have hcont : Continuous fun p : ℝ × Plane × CompactCell =>
      |p.1| * dist p.2.2 K₀ + (|p.1 - s₀| * R + ‖p.1 • p.2.1 - s₀ • u₀‖) :=
    (hs1.abs.mul (hK.dist continuous_const)).add
      (((hs1.sub continuous_const).abs.mul continuous_const).add
        ((hs1.smul hu).sub continuous_const).norm)
  have hzero : |s₀| * dist K₀ K₀ + (|s₀ - s₀| * R + ‖s₀ • u₀ - s₀ • u₀‖) = 0 := by
    simp
  have htend : Filter.Tendsto (fun p : ℝ × Plane × CompactCell =>
      |p.1| * dist p.2.2 K₀ + (|p.1 - s₀| * R + ‖p.1 • p.2.1 - s₀ • u₀‖))
      (nhds (s₀, u₀, K₀)) (nhds 0) := by
    have h := hcont.tendsto (s₀, u₀, K₀)
    rwa [hzero] at h
  exact tendsto_iff_dist_tendsto_zero.mpr
    (squeeze_zero (fun p => dist_nonneg) hbound htend)

theorem measurable_similarityCell :
    Measurable fun p : ℝ × Plane × CompactCell => similarityCell p.1 p.2.1 p.2.2 :=
  continuous_similarityCell.measurable

/-! ### Present slots of the code -/

/-- Placing a cell in a slot is continuous, hence measurable. -/
theorem continuous_someCell : Continuous (some : CompactCell → Option CompactCell) := by
  have hEq : ⇑slotEquiv ∘ (some : CompactCell → Option CompactCell) = Sum.inl := by
    funext K
    rfl
  refine continuous_induced_rng.mpr ?_
  rw [hEq]
  exact continuous_inl

theorem measurable_someCell : Measurable (some : CompactCell → Option CompactCell) :=
  continuous_someCell.measurable

/-! ### The action and its slot events -/

/-- Positive scales, with the trace sigma algebra of the reals. -/
abbrev PositiveScale := {s : ℝ // 0 < s}

/-- The domain of the joint similarity action. -/
abbrev ActionDomain := PositiveScale × Plane × Env

/-- The canonical similarity action, as a single map of scale, centre and
environment. -/
noncomputable def similarityActionEnv (p : ActionDomain) : Env :=
  similarityTargetEnv p.1.val p.2.1 p.1.property p.2.2

/-- The source cell in slot `m`, read off measurably (`referenceCell` if absent). -/
noncomputable def sourceCell (m : ℕ) (p : ActionDomain) : CompactCell :=
  (p.2.2.val.1 m).getD referenceCell

/-- The similarity image of the slot-`m` source cell. -/
noncomputable def imageCell (m : ℕ) (p : ActionDomain) : CompactCell :=
  similarityCell p.1.val p.2.1 (sourceCell m p)

theorem measurable_slotValue (m : ℕ) :
    Measurable fun p : ActionDomain => p.2.2.val.1 m :=
  ((measurable_pi_apply m).comp (measurable_fst.comp measurable_inclusion)).comp
    (measurable_snd.comp measurable_snd)

theorem measurable_sourceCell (m : ℕ) : Measurable (sourceCell m) :=
  measurable_slotCell.comp (measurable_slotValue m)

theorem measurable_imageCell (m : ℕ) : Measurable (imageCell m) := by
  have hs : Measurable fun p : ActionDomain => (p.1 : ℝ) :=
    measurable_subtype_coe.comp measurable_fst
  have hu : Measurable fun p : ActionDomain => p.2.1 := measurable_fst.comp measurable_snd
  exact measurable_similarityCell.comp (hs.prodMk (hu.prodMk (measurable_sourceCell m)))

/-- A fixed point lies in the interior of a varying cell measurably; this reuses
the checked interior-hit measurability of the spatial producer. -/
theorem measurableSet_interiorPoint (y : Plane) :
    MeasurableSet {K : CompactCell | y ∈ interior (K : Set Plane)} :=
  (measurable_id.prodMk measurable_const) measurableSet_cellInterior

/-- The event that source slot `m` is present and its similarity image carries the
canonical label `n`. -/
def SlotLabelEvent (n m : ℕ) : Set ActionDomain :=
  {p | (p.2.2.val.1 m).isSome ∧ LeastInteriorLabel (imageCell m p) n}

theorem measurableSet_slotLabelEvent (n m : ℕ) : MeasurableSet (SlotLabelEvent n m) := by
  have hpresent : MeasurableSet {p : ActionDomain | (p.2.2.val.1 m).isSome} :=
    (measurable_slotValue m) measurableSet_slotIsSome
  have hhit : ∀ j : ℕ, MeasurableSet
      {p : ActionDomain | rationalPoint j ∈ interior (imageCell m p : Set Plane)} :=
    fun j => (measurable_imageCell m) (measurableSet_interiorPoint (rationalPoint j))
  have hEq : SlotLabelEvent n m =
      ({p : ActionDomain | (p.2.2.val.1 m).isSome} ∩
          {p : ActionDomain | rationalPoint n ∈ interior (imageCell m p : Set Plane)}) ∩
        ⋂ j : ℕ, {p : ActionDomain |
          j < n → rationalPoint j ∉ interior (imageCell m p : Set Plane)} := by
    ext p
    simp only [SlotLabelEvent, mem_setOf_eq, mem_inter_iff, mem_iInter]
    constructor
    · rintro ⟨hsome, hhitn, hlt⟩
      exact ⟨⟨hsome, hhitn⟩, fun j hj => hlt j hj⟩
    · rintro ⟨⟨hsome, hhitn⟩, hlt⟩
      exact ⟨hsome, hhitn, fun j hj => hlt j hj⟩
  rw [hEq]
  refine (hpresent.inter (hhit n)).inter (MeasurableSet.iInter fun j => ?_)
  by_cases hj : j < n
  · have hset : {p : ActionDomain |
        j < n → rationalPoint j ∉ interior (imageCell m p : Set Plane)}
        = {p : ActionDomain | rationalPoint j ∈ interior (imageCell m p : Set Plane)}ᶜ := by
      ext p
      simp only [mem_setOf_eq, mem_compl_iff]
      exact ⟨fun h => h hj, fun h _ => h⟩
    rw [hset]
    exact (hhit j).compl
  · have hset : {p : ActionDomain |
        j < n → rationalPoint j ∉ interior (imageCell m p : Set Plane)} = univ := by
      ext p
      simp only [mem_setOf_eq, mem_univ, iff_true]
      exact fun h => absurd h hj
    rw [hset]
    exact MeasurableSet.univ

/-! ### The canonical code of the transformed family, slot by slot -/

theorem canonicalSlots_eq_some_of_leastInteriorLabel {V : Type*} [Countable V]
    (F : IndexedCells V) (hG : Geometry F) (v : V) {n : ℕ}
    (h : LeastInteriorLabel (F.cell v) n) : canonicalSlots F hG n = some (F.cell v) := by
  have hlab : canonicalLabel F hG v = n :=
    (leastInteriorLabel_canonicalLabel F hG v).unique h
  rw [← hlab]
  exact canonicalSlots_canonicalLabel F hG v

theorem exists_leastInteriorLabel_of_canonicalSlots_isSome {V : Type*} [Countable V]
    (F : IndexedCells V) (hG : Geometry F) {n : ℕ} (h : (canonicalSlots F hG n).isSome) :
    ∃ v : V, LeastInteriorLabel (F.cell v) n := by
  have hval : canonicalLabel F hG (canonicalVertex F hG n) = n :=
    (isSome_canonicalSlots_iff F hG n).mp h
  refine ⟨canonicalVertex F hG n, ?_⟩
  have h2 := leastInteriorLabel_canonicalLabel F hG (canonicalVertex F hG n)
  rwa [hval] at h2

theorem canonicalSlots_eq_none_of_no_label {V : Type*} [Countable V]
    (F : IndexedCells V) (hG : Geometry F) {n : ℕ}
    (h : ∀ v : V, ¬ LeastInteriorLabel (F.cell v) n) : canonicalSlots F hG n = none := by
  refine Option.not_isSome_iff_eq_none.mp fun hsome => ?_
  obtain ⟨v, hv⟩ := exists_leastInteriorLabel_of_canonicalSlots_isSome F hG hsome
  exact h v hv

theorem canonicalConductance_eq_of_leastInteriorLabel {V : Type*} [Countable V]
    (F : IndexedCells V) (hG : Geometry F) (v w : V) {n m : ℕ}
    (hv : LeastInteriorLabel (F.cell v) n) (hw : LeastInteriorLabel (F.cell w) m) :
    canonicalConductance F hG n m = F.graph.c v w := by
  have hlv : canonicalLabel F hG v = n := (leastInteriorLabel_canonicalLabel F hG v).unique hv
  have hlw : canonicalLabel F hG w = m := (leastInteriorLabel_canonicalLabel F hG w).unique hw
  rw [← hlv, ← hlw]
  exact canonicalConductance_canonicalLabel F hG v w

theorem canonicalConductance_eq_zero_of_no_label_left {V : Type*} [Countable V]
    (F : IndexedCells V) (hG : Geometry F) {n : ℕ}
    (h : ∀ v : V, ¬ LeastInteriorLabel (F.cell v) n) (m : ℕ) :
    canonicalConductance F hG n m = 0 := by
  refine canonicalConductance_eq_zero_left F hG (fun hc => ?_) m
  refine h (canonicalVertex F hG n) ?_
  have h2 := leastInteriorLabel_canonicalLabel F hG (canonicalVertex F hG n)
  rwa [hc] at h2

theorem canonicalConductance_eq_zero_of_no_label_right {V : Type*} [Countable V]
    (F : IndexedCells V) (hG : Geometry F) (n : ℕ) {m : ℕ}
    (h : ∀ v : V, ¬ LeastInteriorLabel (F.cell v) m) :
    canonicalConductance F hG n m = 0 := by
  refine canonicalConductance_eq_zero_right F hG n (fun hc => ?_)
  refine h (canonicalVertex F hG m) ?_
  have h2 := leastInteriorLabel_canonicalLabel F hG (canonicalVertex F hG m)
  rwa [hc] at h2

/-! ### The raw target code of the action -/

theorem val_similarityTargetEnv_fst (s : ℝ) (u : Plane) (hs : 0 < s) (e : Env) (n : ℕ) :
    (similarityTargetEnv s u hs e).val.1 n
      = canonicalSlots (transformIndexedCells s u hs (decode e))
          (geometry_transformIndexedCells s u hs (decode_geometry e)) n := rfl

theorem val_similarityTargetEnv_snd (s : ℝ) (u : Plane) (hs : 0 < s) (e : Env) (n m : ℕ) :
    (similarityTargetEnv s u hs e).val.2 n m
      = canonicalConductance (transformIndexedCells s u hs (decode e))
          (geometry_transformIndexedCells s u hs (decode_geometry e)) n m := rfl

theorem decode_cell_eq_getD (e : Env) (v : Vertex e.val) :
    (decode e).cell v = (e.val.1 v.val).getD referenceCell := by
  have h : e.val.1 v.val = some ((decode e).cell v) := (Option.some_get v.property).symm
  rw [h]
  rfl

theorem cell_transformedCells (s : ℝ) (u : Plane) (hs : 0 < s) (e : Env) (v : Vertex e.val) :
    (transformIndexedCells s u hs (decode e)).cell v
      = similarityCell s u ((e.val.1 v.val).getD referenceCell) := by
  rw [transformIndexedCells_cell, similarityCell_eq_transformCell, decode_cell_eq_getD]

theorem targetSlot_eq_some {s : ℝ} {u : Plane} (hs : 0 < s) {e : Env} (v : Vertex e.val) {n : ℕ}
    (h : LeastInteriorLabel (similarityCell s u ((e.val.1 v.val).getD referenceCell)) n) :
    (similarityTargetEnv s u hs e).val.1 n
      = some (similarityCell s u ((e.val.1 v.val).getD referenceCell)) := by
  have h' : LeastInteriorLabel ((transformIndexedCells s u hs (decode e)).cell v) n := by
    rw [cell_transformedCells]
    exact h
  have hslot := canonicalSlots_eq_some_of_leastInteriorLabel
    (transformIndexedCells s u hs (decode e))
    (geometry_transformIndexedCells s u hs (decode_geometry e)) v h'
  rw [val_similarityTargetEnv_fst, hslot, cell_transformedCells]

theorem targetSlot_eq_none {s : ℝ} {u : Plane} (hs : 0 < s) {e : Env} {n : ℕ}
    (h : ∀ v : Vertex e.val,
      ¬ LeastInteriorLabel (similarityCell s u ((e.val.1 v.val).getD referenceCell)) n) :
    (similarityTargetEnv s u hs e).val.1 n = none := by
  rw [val_similarityTargetEnv_fst]
  refine canonicalSlots_eq_none_of_no_label _ _ (fun v hv => h v ?_)
  rwa [cell_transformedCells] at hv

theorem targetConductance_eq {s : ℝ} {u : Plane} (hs : 0 < s) {e : Env}
    (v w : Vertex e.val) {n m : ℕ}
    (hv : LeastInteriorLabel (similarityCell s u ((e.val.1 v.val).getD referenceCell)) n)
    (hw : LeastInteriorLabel (similarityCell s u ((e.val.1 w.val).getD referenceCell)) m) :
    (similarityTargetEnv s u hs e).val.2 n m = e.val.2 v.val w.val := by
  have hv' : LeastInteriorLabel ((transformIndexedCells s u hs (decode e)).cell v) n := by
    rw [cell_transformedCells]
    exact hv
  have hw' : LeastInteriorLabel ((transformIndexedCells s u hs (decode e)).cell w) m := by
    rw [cell_transformedCells]
    exact hw
  rw [val_similarityTargetEnv_snd, canonicalConductance_eq_of_leastInteriorLabel
    (transformIndexedCells s u hs (decode e))
    (geometry_transformIndexedCells s u hs (decode_geometry e)) v w hv' hw']
  rfl

theorem targetConductance_eq_zero_left {s : ℝ} {u : Plane} (hs : 0 < s) {e : Env} {n : ℕ}
    (h : ∀ v : Vertex e.val,
      ¬ LeastInteriorLabel (similarityCell s u ((e.val.1 v.val).getD referenceCell)) n)
    (m : ℕ) : (similarityTargetEnv s u hs e).val.2 n m = 0 := by
  rw [val_similarityTargetEnv_snd]
  refine canonicalConductance_eq_zero_of_no_label_left _ _ (fun v hv => h v ?_) m
  rwa [cell_transformedCells] at hv

theorem targetConductance_eq_zero_right {s : ℝ} {u : Plane} (hs : 0 < s) {e : Env} (n : ℕ)
    {m : ℕ} (h : ∀ v : Vertex e.val,
      ¬ LeastInteriorLabel (similarityCell s u ((e.val.1 v.val).getD referenceCell)) m) :
    (similarityTargetEnv s u hs e).val.2 n m = 0 := by
  rw [val_similarityTargetEnv_snd]
  refine canonicalConductance_eq_zero_of_no_label_right _ _ n (fun v hv => h v ?_)
  rwa [cell_transformedCells] at hv

/-! ### Joint measurability of the action -/

theorem measurable_targetSlot (n : ℕ) :
    Measurable fun p : ActionDomain => (similarityActionEnv p).val.1 n := by
  refine measurable_of_countable_pieces (S := fun m => SlotLabelEvent n m)
    (fun m => measurableSet_slotLabelEvent n m)
    (g := fun m p => some (imageCell m p))
    (fun m => measurable_someCell.comp (measurable_imageCell m)) (c := none) ?_ ?_
  · intro m p hp
    obtain ⟨hsome, hlab⟩ := hp
    exact targetSlot_eq_some p.1.property ⟨m, hsome⟩ hlab
  · intro p hp
    refine targetSlot_eq_none p.1.property (fun v hv => ?_)
    exact hp v.val ⟨v.property, hv⟩

theorem measurable_targetConductance (n m : ℕ) :
    Measurable fun p : ActionDomain => (similarityActionEnv p).val.2 n m := by
  have hrow : Measurable fun p : ActionDomain => p.2.2.val.2 :=
    (measurable_snd.comp measurable_inclusion).comp (measurable_snd.comp measurable_snd)
  refine measurable_of_countable_pieces (ι := ℕ × ℕ)
    (S := fun jk => SlotLabelEvent n jk.1 ∩ SlotLabelEvent m jk.2)
    (fun jk => (measurableSet_slotLabelEvent n jk.1).inter (measurableSet_slotLabelEvent m jk.2))
    (g := fun jk p => p.2.2.val.2 jk.1 jk.2)
    (fun jk => (measurable_pi_apply jk.2).comp ((measurable_pi_apply jk.1).comp hrow))
    (c := 0) ?_ ?_
  · intro jk p hp
    obtain ⟨⟨hj, hjlab⟩, ⟨hk, hklab⟩⟩ := hp
    exact targetConductance_eq p.1.property ⟨jk.1, hj⟩ ⟨jk.2, hk⟩ hjlab hklab
  · intro p hp
    by_cases hex : ∃ j : ℕ, p ∈ SlotLabelEvent n j
    · obtain ⟨j, hjmem⟩ := hex
      refine targetConductance_eq_zero_right p.1.property n (fun w hw => ?_)
      exact hp (j, w.val) ⟨hjmem, ⟨w.property, hw⟩⟩
    · push_neg at hex
      refine targetConductance_eq_zero_left p.1.property (fun v hv => ?_) m
      exact hex v.val ⟨v.property, hv⟩

/-- **The canonical similarity action is jointly measurable** in the positive
scale, the centre and the environment, for the trace sigma algebra of `Env`. -/
theorem measurable_similarityActionEnv : Measurable similarityActionEnv := by
  have hslots : Measurable fun p : ActionDomain => (similarityActionEnv p).val.1 :=
    Measurable.of_eval fun n => measurable_targetSlot n
  have hcond : Measurable fun p : ActionDomain => (similarityActionEnv p).val.2 :=
    Measurable.of_eval fun n => Measurable.of_eval fun m => measurable_targetConductance n m
  have hval : Measurable fun p : ActionDomain => (similarityActionEnv p).val := hslots.prodMk hcond
  exact hval.subtype_mk

end ReflectedGMS.CanonicalSimilarity
