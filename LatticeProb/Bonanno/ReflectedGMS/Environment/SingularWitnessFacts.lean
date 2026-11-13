/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module ReflectedGMS.Environment.SingularWitnessFacts at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.ReflectedGMS.Environment.SingularGeometry
import LatticeProb.Bonanno.ReflectedGMS.Environment.Similarity
import LatticeProb.Bonanno.ReflectedGMS.MeasureTheory.HausdorffPlane
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar

/-!
# Facts about a singular witness, and transport of the covering clause

This file supplies the reusable inputs that the coverage-weakening repairs consume.  Everything is
stated for an explicit hypothesis; nothing here assumes full coverage.

## The covering clause

The weakened covering clause of `ReflectedGMS.Geometry` is one-dimensional Hausdorff nullity of the
**uncovered set** `(⋃ v, (F.cell v : Set Plane))ᶜ`.  All statements below spell that set out rather
than naming it, so that they apply verbatim to `ReflectedGMS.uncoveredSet F`, which unfolds to it.

## What is here

* **The bridge** `ReflectedGMS.SingularWitness.hausdorffMeasure_one_compl_iUnion_cell_eq_zero`:
  a `SingularWitness` (Definition 1.1(ii) of the singular-set manuscript) implies the weakened
  covering clause, because the uncovered set is contained in `Ssing` by `SingularWitness.cover` and
  `μH[1]` is monotone.  Together with
  `ReflectedGMS.GeometrySingular.hausdorffMeasure_one_compl_iUnion_cell_eq_zero` this is what makes
  Definition 1.1 an instance of the weakened `Geometry`.
* **Transport of the covering clause** along a conductance-preserving vertex relabelling
  (`hausdorffMeasure_one_compl_iUnion_cell_relabel`, audit site S3) and along a positive similarity
  (`hausdorffMeasure_one_compl_iUnion_cell_transform`, audit site S4).  These are the drop-in
  replacements for the coverage bullets of `ReflectedGMS.geometry_relabel` and
  `ReflectedGMS.geometry_transformIndexedCells`.
* **Transport of the witness itself** (`SingularWitness.relabel`, `SingularWitness.transform`, and
  their `Nonempty` corollaries), which is what a `Nonempty (SingularWitness F)`-style clause needs.

## What is deliberately *not* here

The general facts about an `H¹`-null planar set — Lebesgue nullity, empty interior, density of the
complement, the closed-set/density step of audit site S9, and the Lebesgue nullity of the coordinate
projections — are **not** restated here.  They are proved once elsewhere and are reused:

* `ReflectedGMS.volume_eq_zero_of_hausdorffMeasure_one` (`MeasureTheory/HausdorffPlane.lean`);
* `ReflectedGMS.coordProj`, `ReflectedGMS.lipschitzWith_coordProj`,
  `ReflectedGMS.volume_image_coordProj_eq_zero` (`Environment/GenericLines.lean`);
* the `uncoveredSet`-level corollaries in `Environment/UncoveredFacts.lean`.

The only general lemmas duplicated below are the two-line `sing`-level corollaries
(`SingularWitness.volume_sing_eq_zero`, `SingularWitness.interior_sing_eq_empty`,
`SingularWitness.dense_compl_sing`), which are facts about a witness rather than about the canonical
uncovered set and which live in the `SingularWitness` namespace, so they collide with nothing.
-/

set_option autoImplicit false

open MeasureTheory Set
open scoped Topology ENNReal NNReal

namespace ReflectedGMS

/-! ## Facts about a singular witness -/

namespace SingularWitness

variable {V : Type*} {F : IndexedCells V}

/-- The uncovered set is contained in the singular set: this is `SingularWitness.cover` contraposed.
Unlike `w.sing`, the uncovered set is a function of `F` alone. -/
theorem compl_iUnion_cell_subset_sing (w : SingularWitness F) :
    (⋃ v, (F.cell v : Set Plane))ᶜ ⊆ w.sing := by
  intro z hz
  rw [Set.mem_compl_iff] at hz
  by_contra hzs
  exact hz (w.cover ((Set.mem_compl_iff _ _).mpr hzs))

/-- **The bridge.**  A singular witness implies the weakened covering clause of `Geometry`:
one-dimensional Hausdorff nullity of the uncovered set.  The right-hand side is definitionally
`ReflectedGMS.uncoveredSet F`. -/
theorem hausdorffMeasure_one_compl_iUnion_cell_eq_zero (w : SingularWitness F) :
    μH[1] ((⋃ v, (F.cell v : Set Plane))ᶜ) = 0 :=
  measure_mono_null w.compl_iUnion_cell_subset_sing w.hausdorff_sing

/-- The singular set is Lebesgue-null. -/
theorem volume_sing_eq_zero (w : SingularWitness F) : volume w.sing = 0 :=
  volume_eq_zero_of_hausdorffMeasure_one w.hausdorff_sing

/-- The uncovered set is Lebesgue-null. -/
theorem volume_compl_iUnion_cell_eq_zero (w : SingularWitness F) :
    volume ((⋃ v, (F.cell v : Set Plane))ᶜ) = 0 :=
  measure_mono_null w.compl_iUnion_cell_subset_sing w.volume_sing_eq_zero

/-- The singular set has empty interior.  Only Lebesgue nullity is used; closedness is not needed. -/
theorem interior_sing_eq_empty (w : SingularWitness F) : interior w.sing = ∅ := by
  by_contra hne
  have hpos : (0 : ℝ≥0∞) < volume w.sing :=
    Measure.measure_pos_of_nonempty_interior (μ := (volume : Measure Plane))
      (Set.nonempty_iff_ne_empty.mpr hne)
  rw [w.volume_sing_eq_zero] at hpos
  exact lt_irrefl _ hpos

/-- The complement of the singular set is dense. -/
theorem dense_compl_sing (w : SingularWitness F) : Dense w.singᶜ :=
  interior_eq_empty_iff_dense_compl.mp w.interior_sing_eq_empty

end SingularWitness

/-- **Definition 1.1 implies the weakened covering clause.** -/
theorem GeometrySingular.hausdorffMeasure_one_compl_iUnion_cell_eq_zero {V : Type*} [Countable V]
    {F : IndexedCells V} (h : GeometrySingular F) :
    μH[1] ((⋃ v, (F.cell v : Set Plane))ᶜ) = 0 :=
  h.nonempty_witness.elim fun w => w.hausdorffMeasure_one_compl_iUnion_cell_eq_zero

/-! ## Elementary properties of a positive similarity -/

theorem injective_positiveSimilarity (s : ℝ) (u : Plane) (hs : 0 < s) :
    Function.Injective (positiveSimilarity s u) := by
  intro a b hab
  have h := congrArg (positiveSimilarity s⁻¹ (-s • u)) hab
  rwa [positiveSimilarity_inverse_left s u a hs, positiveSimilarity_inverse_left s u b hs] at h

/-- Membership in the image of a positive similarity, read through the inverse similarity. -/
theorem mem_image_positiveSimilarity_iff (s : ℝ) (u : Plane) (hs : 0 < s) (A : Set Plane)
    (z : Plane) :
    z ∈ positiveSimilarity s u '' A ↔ positiveSimilarity s⁻¹ (-s • u) z ∈ A := by
  constructor
  · rintro ⟨a, ha, rfl⟩
    rwa [positiveSimilarity_inverse_left s u a hs]
  · intro h
    exact ⟨positiveSimilarity s⁻¹ (-s • u) z, h, positiveSimilarity_inverse_right s u z hs⟩

/-- A positive similarity is a bijection, so it commutes with complementation. -/
theorem compl_image_positiveSimilarity (s : ℝ) (u : Plane) (hs : 0 < s) (A : Set Plane) :
    (positiveSimilarity s u '' A)ᶜ = positiveSimilarity s u '' Aᶜ := by
  ext z
  constructor
  · intro hz
    refine (mem_image_positiveSimilarity_iff s u hs Aᶜ z).mpr ?_
    intro hc
    exact hz ((mem_image_positiveSimilarity_iff s u hs A z).mpr hc)
  · intro hz hc
    exact (mem_image_positiveSimilarity_iff s u hs Aᶜ z).mp hz
      ((mem_image_positiveSimilarity_iff s u hs A z).mp hc)

theorem lipschitzWith_positiveSimilarity (s : ℝ) (u : Plane) (hs : 0 < s) :
    LipschitzWith (Real.toNNReal s) (positiveSimilarity s u) := by
  refine LipschitzWith.of_dist_le_mul fun z w => ?_
  have hcancel : (z - u) - (w - u) = z - w := by abel
  have hsub : positiveSimilarity s u z - positiveSimilarity s u w = s • (z - w) :=
    calc positiveSimilarity s u z - positiveSimilarity s u w
        = s • (z - u) - s • (w - u) := rfl
      _ = s • ((z - u) - (w - u)) := by rw [← smul_sub]
      _ = s • (z - w) := by rw [hcancel]
  have hdist : dist (positiveSimilarity s u z) (positiveSimilarity s u w) = s * dist z w := by
    rw [dist_eq_norm, dist_eq_norm, hsub, norm_smul, Real.norm_eq_abs, abs_of_pos hs]
  exact le_of_eq (by rw [hdist, Real.coe_toNNReal s hs.le])

/-- A positive similarity is Lipschitz, so it preserves `H¹`-nullity. -/
theorem hausdorffMeasure_one_image_positiveSimilarity_eq_zero (s : ℝ) (u : Plane) (hs : 0 < s)
    {A : Set Plane} (hA : μH[1] A = 0) : μH[1] (positiveSimilarity s u '' A) = 0 := by
  have h := (lipschitzWith_positiveSimilarity s u hs).hausdorffMeasure_image_le
    (d := (1 : ℝ)) zero_le_one A
  rw [hA, mul_zero] at h
  exact le_antisymm h (by simp)

/-! ## Transport of the covering clause -/

/-- A conductance-preserving relabelling does not move cells, so the cell union is literally the
same set. -/
theorem iUnion_cell_relabel {V W : Type*} {F : IndexedCells V} {G : IndexedCells W} (q : V ≃ W)
    (hc : ∀ v, G.cell (q v) = F.cell v) :
    (⋃ x, (G.cell x : Set Plane)) = ⋃ v, (F.cell v : Set Plane) := by
  ext z
  simp only [Set.mem_iUnion]
  constructor
  · rintro ⟨x, hx⟩
    obtain ⟨v, rfl⟩ := q.surjective x
    exact ⟨v, by rwa [hc v] at hx⟩
  · rintro ⟨v, hv⟩
    exact ⟨q v, by rw [hc v]; exact hv⟩

/-- **Audit site S3.**  The weakened covering clause transports along a vertex relabelling. -/
theorem hausdorffMeasure_one_compl_iUnion_cell_relabel {V W : Type*} {F : IndexedCells V}
    {G : IndexedCells W} (q : V ≃ W) (hc : ∀ v, G.cell (q v) = F.cell v)
    (h : μH[1] ((⋃ v, (F.cell v : Set Plane))ᶜ) = 0) :
    μH[1] ((⋃ x, (G.cell x : Set Plane))ᶜ) = 0 := by
  rw [iUnion_cell_relabel q hc]
  exact h

/-- The cell union of the transformed family is the image of the cell union. -/
theorem iUnion_cell_transformIndexedCells {V : Type*} (s : ℝ) (u : Plane) (hs : 0 < s)
    (F : IndexedCells V) :
    (⋃ v, ((transformIndexedCells s u hs F).cell v : Set Plane))
      = positiveSimilarity s u '' (⋃ v, (F.cell v : Set Plane)) := by
  rw [Set.image_iUnion]
  exact Set.iUnion_congr fun v => by rw [transformIndexedCells_cell, coe_transformCell]

/-- **Audit site S4.**  The weakened covering clause transports along a positive similarity: the
uncovered set of the transformed family is the image of the uncovered set, and a Lipschitz map
preserves `H¹`-nullity. -/
theorem hausdorffMeasure_one_compl_iUnion_cell_transform {V : Type*} (s : ℝ) (u : Plane)
    (hs : 0 < s) {F : IndexedCells V} (h : μH[1] ((⋃ v, (F.cell v : Set Plane))ᶜ) = 0) :
    μH[1] ((⋃ v, ((transformIndexedCells s u hs F).cell v : Set Plane))ᶜ) = 0 := by
  rw [iUnion_cell_transformIndexedCells s u hs F, compl_image_positiveSimilarity s u hs]
  exact hausdorffMeasure_one_image_positiveSimilarity_eq_zero s u hs h

/-! ## Transport of a singular witness -/

namespace SingularWitness

/-- **Audit site S3, witness form.**  A conductance-preserving relabelling does not move cells, so
the *same* singular set and exceptional set witness Definition 1.1 for the relabelled family. -/
def relabel {V W : Type*} {F : IndexedCells V} {G : IndexedCells W} (w : SingularWitness F)
    (q : V ≃ W) (hc : ∀ v, G.cell (q v) = F.cell v)
    (hg : ∀ v v', G.graph.c (q v) (q v') = F.graph.c v v') : SingularWitness G where
  sing := w.sing
  vstar := w.vstar
  isClosed_sing := w.isClosed_sing
  hausdorff_sing := w.hausdorff_sing
  countable_vstar := w.countable_vstar
  cover := by
    rw [iUnion_cell_relabel q hc]
    exact w.cover
  locallyFinite := by
    intro z hz
    obtain ⟨U, hU, hfin⟩ := w.locallyFinite z hz
    refine ⟨U, hU, Set.Finite.subset (hfin.image q) ?_⟩
    intro x hx
    obtain ⟨v, rfl⟩ := q.surjective x
    have hx' : ((G.cell (q v) : Set Plane) ∩ U).Nonempty := hx
    have hv : ((F.cell v : Set Plane) ∩ U).Nonempty := by rwa [hc v] at hx'
    exact ⟨v, hv, rfl⟩
  face := by
    intro z hz x y hxy hzx hzy
    obtain ⟨v, rfl⟩ := q.surjective x
    obtain ⟨v', rfl⟩ := q.surjective y
    have hzv : z ∈ (F.cell v : Set Plane) := by rwa [hc v] at hzx
    have hzv' : z ∈ (F.cell v' : Set Plane) := by rwa [hc v'] at hzy
    have hvv' : v ≠ v' := fun hEq => hxy (congrArg q hEq)
    have hadj : 0 < F.graph.c v v' := w.face z hz v v' hvv' hzv hzv'
    have hadj' : 0 < G.graph.c (q v) (q v') := by rw [hg v v']; exact hadj
    exact hadj'

/-- **Audit site S4, witness form.**  A positive similarity carries a singular witness to a singular
witness of the transformed family, with `Ssing` and `V*` moved by the similarity. -/
def transform {V : Type*} {F : IndexedCells V} (w : SingularWitness F) (s : ℝ) (u : Plane)
    (hs : 0 < s) : SingularWitness (transformIndexedCells s u hs F) where
  sing := positiveSimilarity s u '' w.sing
  vstar := positiveSimilarity s u '' w.vstar
  isClosed_sing := by
    have h : IsClosed (positiveSimilarity s u '' w.sing) :=
      (positiveSimilarityHomeomorph s u hs).isClosedMap _ w.isClosed_sing
    exact h
  hausdorff_sing := hausdorffMeasure_one_image_positiveSimilarity_eq_zero s u hs w.hausdorff_sing
  countable_vstar := w.countable_vstar.image (positiveSimilarity s u)
  cover := by
    intro z hz
    rw [Set.mem_compl_iff] at hz
    have hz' : positiveSimilarity s⁻¹ (-s • u) z ∉ w.sing := fun hc =>
      hz ((mem_image_positiveSimilarity_iff s u hs w.sing z).mpr hc)
    obtain ⟨v, hv⟩ := Set.mem_iUnion.mp (w.cover ((Set.mem_compl_iff _ _).mpr hz'))
    refine Set.mem_iUnion.mpr ⟨v, ?_⟩
    have hmem : z ∈ positiveSimilarity s u '' ((F.cell v : Set Plane)) :=
      (mem_image_positiveSimilarity_iff s u hs _ z).mpr hv
    exact hmem
  locallyFinite := by
    intro z hz
    have hz' : positiveSimilarity s⁻¹ (-s • u) z ∉ w.sing := fun hc =>
      hz ((mem_image_positiveSimilarity_iff s u hs w.sing z).mpr hc)
    obtain ⟨U, hU, hfin⟩ := w.locallyFinite _ hz'
    have himg : positiveSimilarity s u '' U = positiveSimilarity s⁻¹ (-s • u) ⁻¹' U :=
      Set.ext fun p => mem_image_positiveSimilarity_iff s u hs U p
    refine ⟨positiveSimilarity s u '' U, ?_, ?_⟩
    · rw [himg]
      have hcont : Continuous (positiveSimilarity s⁻¹ (-s • u)) := by
        unfold positiveSimilarity
        fun_prop
      exact hcont.continuousAt.preimage_mem_nhds hU
    · refine Set.Finite.subset hfin ?_
      intro v hv
      have hv' : ((positiveSimilarity s u '' ((F.cell v : Set Plane)))
          ∩ (positiveSimilarity s u '' U)).Nonempty := hv
      rw [← Set.image_inter (injective_positiveSimilarity s u hs), Set.image_nonempty] at hv'
      exact hv'
  face := by
    intro z hz v v' hvv' hzv hzv'
    have hz' : positiveSimilarity s⁻¹ (-s • u) z ∉ w.sing ∪ w.vstar := by
      rintro (hc | hc)
      · exact hz (Or.inl ((mem_image_positiveSimilarity_iff s u hs w.sing z).mpr hc))
      · exact hz (Or.inr ((mem_image_positiveSimilarity_iff s u hs w.vstar z).mpr hc))
    have h1 : z ∈ positiveSimilarity s u '' ((F.cell v : Set Plane)) := hzv
    have h2 : z ∈ positiveSimilarity s u '' ((F.cell v' : Set Plane)) := hzv'
    have hadj : F.graph.toSimpleGraph.Adj v v' :=
      w.face _ hz' v v' hvv' ((mem_image_positiveSimilarity_iff s u hs _ z).mp h1)
        ((mem_image_positiveSimilarity_iff s u hs _ z).mp h2)
    exact hadj

end SingularWitness

/-- The `Nonempty (SingularWitness ·)` form of `SingularWitness.relabel`. -/
theorem nonempty_singularWitness_relabel {V W : Type*} {F : IndexedCells V} {G : IndexedCells W}
    (q : V ≃ W) (hc : ∀ v, G.cell (q v) = F.cell v)
    (hg : ∀ v v', G.graph.c (q v) (q v') = F.graph.c v v')
    (h : Nonempty (SingularWitness F)) : Nonempty (SingularWitness G) :=
  h.elim fun w => ⟨w.relabel q hc hg⟩

/-- The `Nonempty (SingularWitness ·)` form of `SingularWitness.transform`. -/
theorem nonempty_singularWitness_transform {V : Type*} (s : ℝ) (u : Plane) (hs : 0 < s)
    {F : IndexedCells V} (h : Nonempty (SingularWitness F)) :
    Nonempty (SingularWitness (transformIndexedCells s u hs F)) :=
  h.elim fun w => ⟨w.transform s u hs⟩

end ReflectedGMS

#print axioms ReflectedGMS.SingularWitness.hausdorffMeasure_one_compl_iUnion_cell_eq_zero
#print axioms ReflectedGMS.GeometrySingular.hausdorffMeasure_one_compl_iUnion_cell_eq_zero
#print axioms ReflectedGMS.hausdorffMeasure_one_compl_iUnion_cell_relabel
#print axioms ReflectedGMS.hausdorffMeasure_one_compl_iUnion_cell_transform
#print axioms ReflectedGMS.SingularWitness.relabel
#print axioms ReflectedGMS.SingularWitness.transform
#print axioms ReflectedGMS.nonempty_singularWitness_relabel
#print axioms ReflectedGMS.nonempty_singularWitness_transform
