/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module ReflectedGMS.Spatial.GeneralGraphLocalFiniteness at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.ReflectedGMS.Environment.GeneralLaws
import LatticeProb.Bonanno.ReflectedGMS.Environment.GeneralNullBoundaries
import LatticeProb.Bonanno.ReflectedGMS.Spatial.NullBoundaryRoots
import Mathlib.MeasureTheory.Measure.OpenPos
import Mathlib.Util.AssertNoSorry

/-!
# Lemma 2.5: graph local finiteness follows from the moment

Manuscript: "Reflected scale-free invariance principle — cell configurations with singularities"
(`work/general/manuscript-text.txt`, lines 104–126 and 316–358).

**Lemma 2.5.** Under the main geometric hypotheses, mass transport and (FE), every cell has
finitely many neighbours almost surely.

This file proves it for general environments (`Code.EnvGeneral`), as the statement
`GeneralLaws.ae_finiteRows`: almost surely every conductance row of the code has finite support.

## The argument

It is the manuscript's, arranged so that the covering half of Lemma 2.4 is not needed.  Let

  `Z(𝓗) = {u ∉ ∂𝓗 | u lies in a cell with infinitely many neighbours}`,

where `∂𝓗 = RootDensities.boundaryMask` is the rooted-functional exception mask (all cell
frontiers together with the uncovered set).

1. **The density is infinite on `Z`.**  At a point of `Z` the boundary-masked root is the cell
   containing it (`rootAt_cellsOnly_eq_some`, from disjoint interiors), and the (FE) integrand
   of an infinite-degree cell is `∞`: its geometric factor `d²/a` is nonzero because a cell with
   nonempty interior has positive diameter, and every neighbour contributes
   `c + c⁻¹ ≥ 1` to the **extended** conductance sums
   (`finiteEnergyDensity_eq_top_of_infinite_support`).  Hence (FE) forces `P[0 ∈ Z] = 0`
   (`measure_zero_mem_infiniteDegreeSet_eq_zero`).
2. **Mass transport.**  The kernel `T(𝓗, u, v) = 1_{u ∈ Z(𝓗)} |u − v|⁻²` is jointly measurable
   (`Z` is a countable slot condition: `mem_infiniteDegreeSet_iff`) and has scaling degree `−2`
   (`Z` is similarity covariant: `mem_infiniteDegreeSet_similarity_iff`).  Its outgoing integral
   at the origin vanishes almost surely by step 1, so its incoming integral
   `∫_{Z(𝓗)} |u|⁻² du` vanishes almost surely, and `|u|⁻² > 0` everywhere gives
   `area Z(𝓗) = 0` almost surely (`ae_volume_infiniteDegreeSet_eq_zero`).
3. **Conclusion.**  An active label with an infinite row would give
   `int H \ ∂𝓗 ⊆ Z(𝓗)`, of positive area because the mask is Lebesgue-null
   (`GeneralGeometry.volume_boundaryMask`, the deterministic Lemma 2.1).  Inactive labels have
   zero rows (`Code.RawAdmissible.absent`).

The kernel construction follows `ReflectedGMS.Spatial.UncoveredRootTransport` (Lemma 2.4 for the
earlier environment type), whose scaling lemma `Spatial.invEdist_mul_invEdist_positiveSimilarity`
is reused verbatim; the joint measurability follows
`RootedFiniteEnergyDensityMeasurable.maskSet_eq_iUnion`, transcribed from `Env` to `EnvGeneral`.
-/

set_option autoImplicit false

open MeasureTheory Set
open scoped ENNReal

namespace ReflectedGMS.GeneralLaws

open Code Spatial

/-! ### Step 1: the (FE) integrand of an infinite-degree cell is infinite -/

/-- A plane set with nonempty interior has at least two points: a subsingleton is Lebesgue-null,
while a nonempty open set is not. -/
theorem nontrivial_of_interior_nonempty {s : Set Plane} (h : (interior s).Nonempty) :
    s.Nontrivial := by
  by_contra hnt
  have hsub : s.Subsingleton := Set.not_nontrivial_iff.mp hnt
  have hzero : volume s = 0 := hsub.measure_zero volume
  have hpos : 0 < volume (interior s) := isOpen_interior.measure_pos volume h
  have hle : volume (interior s) ≤ volume s := measure_mono interior_subset
  rw [hzero] at hle
  exact absurd (le_antisymm hle zero_le) hpos.ne'

/-- A compact cell with nonempty interior has positive diameter. -/
theorem diam_pos_of_interior_nonempty (K : CompactCell)
    (h : (interior (K : Set Plane)).Nonempty) : 0 < Metric.diam (K : Set Plane) :=
  Metric.diam_pos (nontrivial_of_interior_nonempty h) K.isCompact.isBounded

/-- A neighbour contributes at least one to `c + c⁻¹` (one of the two factors is at least one). -/
theorem one_le_ofReal_add_ofReal_inv {c : ℝ} (hc : 0 < c) :
    (1 : ℝ≥0∞) ≤ ENNReal.ofReal c + ENNReal.ofReal c⁻¹ := by
  rcases le_total 1 c with h1 | h1
  · calc (1 : ℝ≥0∞) = ENNReal.ofReal 1 := ENNReal.ofReal_one.symm
      _ ≤ ENNReal.ofReal c := ENNReal.ofReal_le_ofReal h1
      _ ≤ ENNReal.ofReal c + ENNReal.ofReal c⁻¹ := le_self_add
  · have h1' : 1 ≤ c⁻¹ := (one_le_inv₀ hc).mpr h1
    calc (1 : ℝ≥0∞) = ENNReal.ofReal 1 := ENNReal.ofReal_one.symm
      _ ≤ ENNReal.ofReal c⁻¹ := ENNReal.ofReal_le_ofReal h1'
      _ ≤ ENNReal.ofReal c + ENNReal.ofReal c⁻¹ := le_add_self

/-- With infinitely many neighbours the extended sum `π(H) + π*(H)` is infinite. -/
theorem tsum_ofReal_add_tsum_ofReal_inv_eq_top {V : Type*} (C : CellConfiguration V) (v : V)
    (hinf : (Function.support (C.c v)).Infinite) :
    (∑' w, ENNReal.ofReal (C.c v w)) + ∑' w, ENNReal.ofReal (C.c v w)⁻¹ = ∞ := by
  rw [← ENNReal.tsum_add]
  have : Infinite (Function.support (C.c v)) := hinf.to_subtype
  have hconst : ∑' _ : Function.support (C.c v), (1 : ℝ≥0∞) = ∞ :=
    ENNReal.tsum_const_eq_top_of_ne_zero one_ne_zero
  have hle : ∑' _ : Function.support (C.c v), (1 : ℝ≥0∞)
      ≤ ∑' w, (ENNReal.ofReal (C.c v w) + ENNReal.ofReal (C.c v w)⁻¹) := by
    calc ∑' _ : Function.support (C.c v), (1 : ℝ≥0∞)
        ≤ ∑' w : Function.support (C.c v),
            (ENNReal.ofReal (C.c v w) + ENNReal.ofReal (C.c v w)⁻¹) := by
          refine ENNReal.tsum_le_tsum fun w => ?_
          have hne : C.c v w ≠ 0 := Function.mem_support.mp w.property
          exact one_le_ofReal_add_ofReal_inv (lt_of_le_of_ne (C.c_nonneg v w) (Ne.symm hne))
      _ ≤ ∑' w, (ENNReal.ofReal (C.c v w) + ENNReal.ofReal (C.c v w)⁻¹) :=
          ENNReal.tsum_comp_le_tsum_of_injective Subtype.val_injective
            (fun w => ENNReal.ofReal (C.c v w) + ENNReal.ofReal (C.c v w)⁻¹)
  rw [hconst] at hle
  exact top_le_iff.mp hle

/-- **The (FE) integrand of an infinite-degree cell is infinite.**  The geometric factor
`d²/a` is nonzero (positive diameter; the area is finite), and the extended conductance sums are
infinite. -/
theorem finiteEnergyDensity_eq_top_of_infinite_support {V : Type*} (C : CellConfiguration V)
    (v : V) (hint : (interior (C.cell v : Set Plane)).Nonempty)
    (hinf : (Function.support (C.c v)).Infinite) :
    finiteEnergyDensity C v = ∞ := by
  have hdiam : 0 < Metric.diam (C.cell v : Set Plane) := diam_pos_of_interior_nonempty _ hint
  have hnum : ENNReal.ofReal (Metric.diam (C.cell v : Set Plane) ^ 2) ≠ 0 := by
    rw [Ne, ENNReal.ofReal_eq_zero, not_le]
    exact pow_pos hdiam 2
  have hfac : ENNReal.ofReal (Metric.diam (C.cell v : Set Plane) ^ 2) /
      ENNReal.ofReal (StatementIngredients.cellArea C.cellsOnly v) ≠ 0 := by
    rw [Ne, ENNReal.div_eq_zero_iff, not_or]
    exact ⟨hnum, ENNReal.ofReal_ne_top⟩
  unfold finiteEnergyDensity
  rw [tsum_ofReal_add_tsum_ofReal_inv_eq_top C v hinf, ENNReal.mul_top hfac]

/-- Off the boundary mask, a point of a cell is rooted at that cell (disjoint interiors). -/
theorem rootAt_cellsOnly_eq_some {V : Type*} {C : CellConfiguration V}
    (hC : GeneralGeometry C) {z : Plane} {v : V}
    (hz : z ∉ RootDensities.boundaryMask C.cellsOnly) (hv : z ∈ (C.cell v : Set Plane)) :
    RootDensities.rootAt C.cellsOnly z = some v := by
  have hfr : z ∉ frontier (C.cell v : Set Plane) := fun h =>
    hz (Set.mem_union_left _ (Set.mem_iUnion.mpr ⟨v, h⟩))
  have hint : RootDensities.IsInteriorRoot C.cellsOnly z v := by
    show z ∈ interior (C.cell v : Set Plane)
    have hclosed : IsClosed (C.cell v : Set Plane) := (C.cell v).isCompact.isClosed
    rw [frontier, hclosed.closure_eq] at hfr
    exact Classical.byContradiction fun hn => hfr ⟨hv, hn⟩
  have huniq : ∃! w, RootDensities.IsInteriorRoot C.cellsOnly z w := by
    refine ⟨v, hint, fun w hw => ?_⟩
    by_contra hwv
    exact Set.disjoint_left.mp (hC.disjoint_interior hwv) hw hint
  have hchoose : huniq.exists.choose = v := huniq.unique huniq.exists.choose_spec hint
  simp [RootDensities.rootAt, hz, huniq, hchoose]

/-! ### The infinite-degree set and its joint measurability -/

/-- The manuscript's set `Z(𝓗)`: points off the rooted-functional exception mask lying in a cell
with infinitely many neighbours. -/
def infiniteDegreeSet (e : EnvGeneral) : Set Plane :=
  (RootDensities.boundaryMask (config e).cellsOnly)ᶜ ∩
    ⋃ v : Vertex e.val, {u | u ∈ ((config e).cell v : Set Plane) ∧
      (Function.support ((config e).c v)).Infinite}

/-- The configuration row of an active label is infinite exactly when the raw code row is:
inactive labels carry no conductance. -/
theorem infinite_support_config_iff (e : EnvGeneral) (v : Vertex e.val) :
    (Function.support ((config e).c v)).Infinite ↔
      (Function.support (e.val.2 v.val)).Infinite := by
  have himg : Subtype.val '' Function.support ((config e).c v)
      = Function.support (e.val.2 v.val) := by
    ext m
    constructor
    · rintro ⟨w, hw, rfl⟩
      exact hw
    · intro hm
      have hsome : (e.val.1 m).isSome := by
        cases hcase : e.val.1 m with
        | none => exact absurd (e.property.choose.absent v.val m (Or.inr hcase)) hm
        | some K => rfl
      exact ⟨⟨m, hsome⟩, hm, rfl⟩
  rw [← himg, Set.infinite_image_iff Subtype.val_injective.injOn]

/-- The cell at code slot `n`, with the reference cell at absent slots. -/
noncomputable def generalSlotCell (e : EnvGeneral) (n : ℕ) : CompactCell :=
  (e.val.1 n).getD referenceCell

theorem measurable_generalSlotCell (n : ℕ) :
    Measurable fun e : EnvGeneral => generalSlotCell e n :=
  measurable_slotCell.comp
    ((measurable_pi_apply n).comp (measurable_fst.comp measurable_subtype_coe))

theorem generalSlotCell_eq_cell (e : EnvGeneral) (v : Vertex e.val) :
    generalSlotCell e v.val = (config e).cell v := by
  have hv : e.val.1 v.val = some (Code.cell e.val v) := (Option.some_get v.property).symm
  show (e.val.1 v.val).getD referenceCell = Code.cell e.val v
  rw [hv, Option.getD_some]

/-- Reading code slot `n` is measurable on the product space. -/
theorem measurable_slot_prod (n : ℕ) :
    Measurable fun q : EnvGeneral × Plane => q.1.val.1 n := by
  have h : Measurable fun e : EnvGeneral => e.val.1 n :=
    (measurable_pi_apply n).comp (measurable_fst.comp measurable_subtype_coe)
  exact h.comp measurable_fst

theorem measurable_conductance_general (n m : ℕ) :
    Measurable fun e : EnvGeneral => e.val.2 n m :=
  (measurable_pi_apply m).comp
    ((measurable_pi_apply n).comp (measurable_snd.comp measurable_subtype_coe))

/-- "Row `n` is infinite" is a measurable event of the conductance coordinates. -/
theorem measurableSet_infiniteRow (n : ℕ) :
    MeasurableSet {e : EnvGeneral | (Function.support (e.val.2 n)).Infinite} := by
  have hEq : {e : EnvGeneral | (Function.support (e.val.2 n)).Infinite}
      = ⋂ N : ℕ, ⋃ m : ℕ, {e : EnvGeneral | N < m ∧ e.val.2 n m ≠ 0} := by
    ext e
    simp only [Set.mem_ofPred_eq, Set.mem_iInter, Set.mem_iUnion]
    rw [Set.infinite_iff_exists_gt]
    simp only [Function.mem_support]
    constructor
    · intro h N
      obtain ⟨m, hm, hNm⟩ := h N
      exact ⟨m, hNm, hm⟩
    · intro h N
      obtain ⟨m, hNm, hm⟩ := h N
      exact ⟨m, hm, hNm⟩
  rw [hEq]
  refine MeasurableSet.iInter fun N => MeasurableSet.iUnion fun m => ?_
  by_cases hNm : N < m
  · have hset : {e : EnvGeneral | N < m ∧ e.val.2 n m ≠ 0}
        = (fun e : EnvGeneral => e.val.2 n m) ⁻¹' {(0 : ℝ)}ᶜ := by
      ext e
      simp [hNm]
    rw [hset]
    exact measurable_conductance_general n m (measurableSet_singleton 0).compl
  · have hset : {e : EnvGeneral | N < m ∧ e.val.2 n m ≠ 0} = ∅ := by
      ext e
      simp [hNm]
    rw [hset]
    exact MeasurableSet.empty

/-- The rooted-functional exception mask on the product space. -/
def generalMaskSet : Set (EnvGeneral × Plane) :=
  {q | q.2 ∈ RootDensities.boundaryMask (config q.1).cellsOnly}

/-- The covered part of the product space, as a countable union over code slots. -/
def generalCoveredProdSet : Set (EnvGeneral × Plane) :=
  ⋃ n : ℕ, ({q : EnvGeneral × Plane | (q.1.val.1 n).isSome} ∩
    {q : EnvGeneral × Plane | q.2 ∈ (generalSlotCell q.1 n : Set Plane)})

theorem mem_generalCoveredProdSet_iff (e : EnvGeneral) (z : Plane) :
    ((e, z) ∈ generalCoveredProdSet) ↔ z ∈ ⋃ v, ((config e).cell v : Set Plane) := by
  constructor
  · intro hq
    obtain ⟨n, hn, hz⟩ := mem_iUnion.mp hq
    refine mem_iUnion.mpr ⟨⟨n, hn⟩, ?_⟩
    rw [← generalSlotCell_eq_cell e ⟨n, hn⟩]
    exact hz
  · intro hz
    obtain ⟨v, hv⟩ := mem_iUnion.mp hz
    refine mem_iUnion.mpr ⟨v.val, v.property, ?_⟩
    show z ∈ (generalSlotCell e v.val : Set Plane)
    rw [generalSlotCell_eq_cell e v]
    exact hv

theorem measurableSet_generalCoveredProdSet : MeasurableSet generalCoveredProdSet := by
  refine MeasurableSet.iUnion fun n => MeasurableSet.inter ?_ ?_
  · exact measurable_slot_prod n measurableSet_slotIsSome
  · exact (((measurable_generalSlotCell n).comp measurable_fst).prodMk measurable_snd)
      measurableSet_cellMem

/-- The mask splits into the slotwise frontier part and the uncovered part. -/
theorem generalMaskSet_eq_iUnion :
    generalMaskSet = (⋃ n : ℕ, ({q : EnvGeneral × Plane | (q.1.val.1 n).isSome} ∩
      {q : EnvGeneral × Plane | q.2 ∈ frontier (generalSlotCell q.1 n : Set Plane)})) ∪
        generalCoveredProdSetᶜ := by
  ext ⟨e, z⟩
  show (z ∈ (⋃ v, frontier ((config e).cell v : Set Plane)) ∪
      uncoveredSet (config e).cellsOnly) ↔ _
  constructor
  · rintro (hfr | hunc)
    · obtain ⟨v, hv⟩ := mem_iUnion.mp hfr
      refine Or.inl (mem_iUnion.mpr ⟨v.val, v.property, ?_⟩)
      show z ∈ frontier (generalSlotCell e v.val : Set Plane)
      rw [generalSlotCell_eq_cell e v]
      exact hv
    · exact Or.inr fun hc => hunc ((mem_generalCoveredProdSet_iff e z).mp hc)
  · rintro (hfr | hnc)
    · obtain ⟨n, hn, hz⟩ := mem_iUnion.mp hfr
      refine Or.inl (mem_iUnion.mpr ⟨⟨n, hn⟩, ?_⟩)
      rw [← generalSlotCell_eq_cell e ⟨n, hn⟩]
      exact hz
    · exact Or.inr fun hc => hnc ((mem_generalCoveredProdSet_iff e z).mpr hc)

theorem measurableSet_generalMaskSet : MeasurableSet generalMaskSet := by
  rw [generalMaskSet_eq_iUnion]
  refine MeasurableSet.union (MeasurableSet.iUnion fun n => MeasurableSet.inter ?_ ?_)
    measurableSet_generalCoveredProdSet.compl
  · exact measurable_slot_prod n measurableSet_slotIsSome
  · exact (((measurable_generalSlotCell n).comp measurable_fst).prodMk measurable_snd)
      measurableSet_cellFrontier

/-- The infinite-degree set is a countable slot condition off the mask. -/
theorem mem_infiniteDegreeSet_iff (e : EnvGeneral) (z : Plane) :
    z ∈ infiniteDegreeSet e ↔ z ∉ RootDensities.boundaryMask (config e).cellsOnly ∧
      ∃ n : ℕ, (e.val.1 n).isSome ∧ z ∈ (generalSlotCell e n : Set Plane) ∧
        (Function.support (e.val.2 n)).Infinite := by
  unfold infiniteDegreeSet
  rw [Set.mem_inter_iff, Set.mem_compl_iff, Set.mem_iUnion]
  refine and_congr Iff.rfl ⟨?_, ?_⟩
  · rintro ⟨v, hzv, hinf⟩
    refine ⟨v.val, v.property, ?_, (infinite_support_config_iff e v).mp hinf⟩
    rw [generalSlotCell_eq_cell e v]
    exact hzv
  · rintro ⟨n, hn, hz, hinf⟩
    refine ⟨⟨n, hn⟩, ?_, (infinite_support_config_iff e ⟨n, hn⟩).mpr hinf⟩
    rw [← generalSlotCell_eq_cell e ⟨n, hn⟩]
    exact hz

/-- Joint measurability of the membership relation of `Z`. -/
theorem measurableSet_infiniteDegreeProdSet :
    MeasurableSet {q : EnvGeneral × Plane | q.2 ∈ infiniteDegreeSet q.1} := by
  have hEq : {q : EnvGeneral × Plane | q.2 ∈ infiniteDegreeSet q.1}
      = generalMaskSetᶜ ∩ ⋃ n : ℕ, ({q : EnvGeneral × Plane | (q.1.val.1 n).isSome} ∩
          ({q : EnvGeneral × Plane | q.2 ∈ (generalSlotCell q.1 n : Set Plane)} ∩
            {q : EnvGeneral × Plane | (Function.support (q.1.val.2 n)).Infinite})) := by
    ext q
    show q.2 ∈ infiniteDegreeSet q.1 ↔ _
    rw [mem_infiniteDegreeSet_iff, Set.mem_inter_iff, Set.mem_iUnion]
    exact Iff.rfl
  rw [hEq]
  refine measurableSet_generalMaskSet.compl.inter
    (MeasurableSet.iUnion fun n => MeasurableSet.inter ?_ (MeasurableSet.inter ?_ ?_))
  · exact measurable_slot_prod n measurableSet_slotIsSome
  · exact (((measurable_generalSlotCell n).comp measurable_fst).prodMk measurable_snd)
      measurableSet_cellMem
  · exact measurable_fst (measurableSet_infiniteRow n)

/-! ### Similarity covariance of the infinite-degree set -/

section Covariance

/-- Cell membership is covariant (the similarity is injective).  Same statement as
`ActualSpatialDensityBridge.mem_transformCell_iff`, restated here to avoid that module's large
import closure. -/
theorem mem_transformCell_iff_general (s : ℝ) (u : Plane) (hs : 0 < s) (K : CompactCell)
    (z : Plane) :
    positiveSimilarity s u z ∈ ((transformCell s u hs K : CompactCell) : Set Plane)
      ↔ z ∈ (K : Set Plane) := by
  have himg : ((transformCell s u hs K : CompactCell) : Set Plane)
      = positiveSimilarityHomeomorph s u hs '' (K : Set Plane) := rfl
  rw [himg]
  exact Function.Injective.mem_set_image (positiveSimilarityHomeomorph s u hs).injective

/-- Cell frontiers are covariant (the similarity is a homeomorphism).  Same statement as
`ActualSpatialDensityBridge.mem_frontier_transformCell_iff`. -/
theorem mem_frontier_transformCell_iff_general (s : ℝ) (u : Plane) (hs : 0 < s)
    (K : CompactCell) (z : Plane) :
    positiveSimilarity s u z ∈ frontier ((transformCell s u hs K : CompactCell) : Set Plane)
      ↔ z ∈ frontier (K : Set Plane) := by
  have himg : ((transformCell s u hs K : CompactCell) : Set Plane)
      = positiveSimilarityHomeomorph s u hs '' (K : Set Plane) := rfl
  rw [himg, ← Homeomorph.image_frontier]
  exact Function.Injective.mem_set_image (positiveSimilarityHomeomorph s u hs).injective

/-- The rooted-functional exception mask is covariant under a relabelled similarity of cell
configurations. -/
theorem mem_boundaryMask_cellsOnly_similarity_iff {V V' : Type*} (C : CellConfiguration V)
    (C' : CellConfiguration V') (relabel : V ≃ V') {s : ℝ} {u : Plane} {hs : 0 < s}
    (hcell : ∀ v, C'.cell (relabel v) = transformCell s u hs (C.cell v)) (z : Plane) :
    positiveSimilarity s u z ∈ RootDensities.boundaryMask C'.cellsOnly
      ↔ z ∈ RootDensities.boundaryMask C.cellsOnly := by
  have hcov : positiveSimilarity s u z ∈ (⋃ v', (C'.cell v' : Set Plane))
      ↔ z ∈ ⋃ v, (C.cell v : Set Plane) := by
    constructor
    · intro hz
      obtain ⟨v', hv'⟩ := Set.mem_iUnion.mp hz
      obtain ⟨v, rfl⟩ := relabel.surjective v'
      rw [hcell v] at hv'
      exact Set.mem_iUnion.mpr ⟨v, (mem_transformCell_iff_general s u hs _ z).1 hv'⟩
    · intro hz
      obtain ⟨v, hv⟩ := Set.mem_iUnion.mp hz
      refine Set.mem_iUnion.mpr ⟨relabel v, ?_⟩
      rw [hcell v]
      exact (mem_transformCell_iff_general s u hs _ z).2 hv
  have hfr : positiveSimilarity s u z ∈ (⋃ v', frontier (C'.cell v' : Set Plane))
      ↔ z ∈ ⋃ v, frontier (C.cell v : Set Plane) := by
    constructor
    · intro hz
      obtain ⟨v', hv'⟩ := Set.mem_iUnion.mp hz
      obtain ⟨v, rfl⟩ := relabel.surjective v'
      rw [hcell v] at hv'
      exact Set.mem_iUnion.mpr ⟨v, (mem_frontier_transformCell_iff_general s u hs _ z).1 hv'⟩
    · intro hz
      obtain ⟨v, hv⟩ := Set.mem_iUnion.mp hz
      refine Set.mem_iUnion.mpr ⟨relabel v, ?_⟩
      rw [hcell v]
      exact (mem_frontier_transformCell_iff_general s u hs _ z).2 hv
  show (positiveSimilarity s u z ∈
      (⋃ v', frontier (C'.cell v' : Set Plane)) ∪ (⋃ v', (C'.cell v' : Set Plane))ᶜ)
    ↔ (z ∈ (⋃ v, frontier (C.cell v : Set Plane)) ∪ (⋃ v, (C.cell v : Set Plane))ᶜ)
  rw [Set.mem_union, Set.mem_union, Set.mem_compl_iff, Set.mem_compl_iff, hcov, hfr]

/-- Infinite rows are preserved by a conductance-preserving relabelling. -/
theorem infinite_support_relabel_iff {V V' : Type*} (C : CellConfiguration V)
    (C' : CellConfiguration V') (relabel : V ≃ V')
    (hc : ∀ v w, C'.c (relabel v) (relabel w) = C.c v w) (v : V) :
    (Function.support (C'.c (relabel v))).Infinite ↔ (Function.support (C.c v)).Infinite := by
  have hsupp : Function.support (C'.c (relabel v))
      = relabel '' Function.support (C.c v) := by
    ext w'
    obtain ⟨w, rfl⟩ := relabel.surjective w'
    rw [Function.mem_support, hc v w, relabel.injective.mem_set_image, Function.mem_support]
  rw [hsupp, Set.infinite_image_iff relabel.injective.injOn]

/-- **Similarity covariance of `Z`.** -/
theorem mem_infiniteDegreeSet_similarity_iff {s : ℝ} {u : Plane} {hs : 0 < s}
    {e e' : EnvGeneral} (hsim : IsSimilarity s u hs e e') (z : Plane) :
    positiveSimilarity s u z ∈ infiniteDegreeSet e' ↔ z ∈ infiniteDegreeSet e := by
  obtain ⟨relabel, hcell, hc⟩ := hsim
  unfold infiniteDegreeSet
  rw [Set.mem_inter_iff, Set.mem_inter_iff, Set.mem_compl_iff, Set.mem_compl_iff,
    mem_boundaryMask_cellsOnly_similarity_iff (config e) (config e') relabel hcell z,
    Set.mem_iUnion, Set.mem_iUnion]
  refine and_congr Iff.rfl ⟨?_, ?_⟩
  · rintro ⟨v', hzv, hinf⟩
    obtain ⟨v, rfl⟩ := relabel.surjective v'
    rw [hcell v] at hzv
    exact ⟨v, (mem_transformCell_iff_general s u hs _ z).1 hzv,
      (infinite_support_relabel_iff _ _ relabel hc v).1 hinf⟩
  · rintro ⟨v, hzv, hinf⟩
    refine ⟨relabel v, ?_, (infinite_support_relabel_iff _ _ relabel hc v).2 hinf⟩
    rw [hcell v]
    exact (mem_transformCell_iff_general s u hs _ z).2 hzv

end Covariance

/-! ### Step 2: the manuscript's transport kernel -/

/-- Source points of the transport: those in `Z`. -/
def infiniteDegreeSourceSet : Set (EnvGeneral × Plane × Plane) :=
  {p | p.2.1 ∈ infiniteDegreeSet p.1}

theorem measurableSet_infiniteDegreeSourceSet : MeasurableSet infiniteDegreeSourceSet := by
  have hmap : Measurable fun p : EnvGeneral × Plane × Plane => (p.1, p.2.1) :=
    measurable_fst.prodMk (measurable_fst.comp measurable_snd)
  have hEq : infiniteDegreeSourceSet
      = (fun p : EnvGeneral × Plane × Plane => (p.1, p.2.1)) ⁻¹'
          {q : EnvGeneral × Plane | q.2 ∈ infiniteDegreeSet q.1} :=
    Set.ext fun _ => Iff.rfl
  rw [hEq]
  exact hmap measurableSet_infiniteDegreeProdSet

/-- The manuscript's kernel `T(𝓗, u, v) = 1_{u ∈ Z(𝓗)} |u − v|⁻²`, with the inverse square written
multiplicatively in `ℝ≥0∞` (value `∞` rather than `0` on the Lebesgue-null diagonal, exactly as in
`Spatial.uncoveredRootTransport`). -/
noncomputable def infiniteDegreeTransport (p : EnvGeneral × Plane × Plane) : ℝ≥0∞ :=
  Set.indicator infiniteDegreeSourceSet
    (fun q : EnvGeneral × Plane × Plane => (edist q.2.1 q.2.2)⁻¹ * (edist q.2.1 q.2.2)⁻¹) p

theorem infiniteDegreeTransport_of_notMem (e : EnvGeneral) (w z : Plane)
    (hw : w ∉ infiniteDegreeSet e) : infiniteDegreeTransport (e, w, z) = 0 := by
  unfold infiniteDegreeTransport
  exact Set.indicator_of_notMem (show (e, w, z) ∉ infiniteDegreeSourceSet from hw) _

theorem infiniteDegreeTransport_of_mem (e : EnvGeneral) (w z : Plane)
    (hw : w ∈ infiniteDegreeSet e) :
    infiniteDegreeTransport (e, w, z) = (edist w z)⁻¹ * (edist w z)⁻¹ := by
  unfold infiniteDegreeTransport
  exact Set.indicator_of_mem (show (e, w, z) ∈ infiniteDegreeSourceSet from hw) _

theorem measurable_infiniteDegreeTransport : Measurable infiniteDegreeTransport := by
  have hpair : Measurable fun q : EnvGeneral × Plane × Plane => (q.2.1, q.2.2) :=
    (measurable_fst.comp measurable_snd).prodMk (measurable_snd.comp measurable_snd)
  have hed : Measurable fun q : EnvGeneral × Plane × Plane => edist q.2.1 q.2.2 :=
    measurable_edist.comp hpair
  exact (hed.inv.mul hed.inv).indicator measurableSet_infiniteDegreeSourceSet

theorem infiniteDegreeTransport_covariant (s : ℝ) (u : Plane) (hs : 0 < s) (e e' : EnvGeneral)
    (hsim : IsSimilarity s u hs e e') (w z : Plane) :
    infiniteDegreeTransport (e', positiveSimilarity s u w, positiveSimilarity s u z)
      = ENNReal.ofReal ((s ^ 2)⁻¹) * infiniteDegreeTransport (e, w, z) := by
  by_cases hw : w ∈ infiniteDegreeSet e
  · have hw' : positiveSimilarity s u w ∈ infiniteDegreeSet e' :=
      (mem_infiniteDegreeSet_similarity_iff hsim w).2 hw
    rw [infiniteDegreeTransport_of_mem e' _ _ hw', infiniteDegreeTransport_of_mem e w z hw]
    exact invEdist_mul_invEdist_positiveSimilarity s u hs w z
  · have hw' : positiveSimilarity s u w ∉ infiniteDegreeSet e' := fun h =>
      hw ((mem_infiniteDegreeSet_similarity_iff hsim w).1 h)
    rw [infiniteDegreeTransport_of_notMem e' _ _ hw', infiniteDegreeTransport_of_notMem e w z hw,
      mul_zero]

/-- The kernel as a `GeneralLaws.MassTransportKernel`. -/
noncomputable def infiniteDegreeTransportKernel : MassTransportKernel where
  toFun := infiniteDegreeTransport
  measurable_toFun := measurable_infiniteDegreeTransport
  covariant := fun s u hs e e' hsim w z =>
    infiniteDegreeTransport_covariant s u hs e e' hsim w z

/-! ### Steps 1–2 combined: the root is not in `Z`, and `Z` is null -/

/-- The (FE) integrand is infinite at every point of `Z`. -/
theorem rootedFiniteEnergyDensity_eq_top_of_mem (e : EnvGeneral) {z : Plane}
    (hz : z ∈ infiniteDegreeSet e) : rootedFiniteEnergyDensity (config e) z = ∞ := by
  obtain ⟨hmask, hU⟩ := hz
  obtain ⟨v, hzv, hinf⟩ := Set.mem_iUnion.mp hU
  have hroot : RootDensities.rootAt (config e).cellsOnly z = some v :=
    rootAt_cellsOnly_eq_some (config_generalGeometry e) hmask hzv
  unfold rootedFiniteEnergyDensity
  rw [hroot]
  exact finiteEnergyDensity_eq_top_of_infinite_support (config e) v
    ((config_generalGeometry e).interior_nonempty v) hinf

/-- **(FE) excludes an infinite-degree root cell:** `P[0 ∈ Z] = 0`. -/
theorem measure_zero_mem_infiniteDegreeSet_eq_zero (ν : Measure EnvGeneral)
    (hFE : FiniteEnergyMoment ν) : ν {e | (0 : Plane) ∈ infiniteDegreeSet e} = 0 := by
  have hmap : Measurable fun e : EnvGeneral => ((e, (0 : Plane)) : EnvGeneral × Plane) :=
    measurable_id.prodMk measurable_const
  have hAmeas : MeasurableSet {e : EnvGeneral | (0 : Plane) ∈ infiniteDegreeSet e} :=
    hmap measurableSet_infiniteDegreeProdSet
  have hle : ∀ e : EnvGeneral,
      {e : EnvGeneral | (0 : Plane) ∈ infiniteDegreeSet e}.indicator (fun _ => (∞ : ℝ≥0∞)) e
        ≤ rootedFiniteEnergyDensity (config e) 0 := by
    intro e
    by_cases he : e ∈ {e : EnvGeneral | (0 : Plane) ∈ infiniteDegreeSet e}
    · rw [Set.indicator_of_mem he, rootedFiniteEnergyDensity_eq_top_of_mem e he]
    · rw [Set.indicator_of_notMem he]
      exact zero_le
  have hint : ∞ * ν {e | (0 : Plane) ∈ infiniteDegreeSet e}
      ≤ ∫⁻ e, rootedFiniteEnergyDensity (config e) 0 ∂ν := by
    rw [← lintegral_indicator_const hAmeas]
    exact lintegral_mono hle
  by_contra hne
  rw [ENNReal.top_mul hne] at hint
  exact absurd (lt_of_le_of_lt hint hFE) (lt_irrefl ∞)

/-- **Mass transport makes `Z` Lebesgue-null almost surely.** -/
theorem ae_volume_infiniteDegreeSet_eq_zero (ν : Measure EnvGeneral) (hmt : MassTransport ν)
    (hFE : FiniteEnergyMoment ν) : ∀ᵐ e ∂ν, volume (infiniteDegreeSet e) = 0 := by
  have h0 := measure_zero_mem_infiniteDegreeSet_eq_zero ν hFE
  have hout : (∫⁻ e, ∫⁻ z : Plane, infiniteDegreeTransport (e, 0, z) ∂volume ∂ν) = 0 := by
    have hae : ∀ᵐ e ∂ν, (∫⁻ z : Plane, infiniteDegreeTransport (e, 0, z) ∂volume) = 0 := by
      refine MeasureTheory.ae_iff.mpr (measure_mono_null ?_ h0)
      intro e he
      by_contra hmem
      apply he
      calc (∫⁻ z : Plane, infiniteDegreeTransport (e, 0, z) ∂volume)
          = ∫⁻ _ : Plane, (0 : ℝ≥0∞) ∂volume :=
            lintegral_congr fun z => infiniteDegreeTransport_of_notMem e 0 z hmem
        _ = 0 := lintegral_zero
    calc (∫⁻ e, ∫⁻ z : Plane, infiniteDegreeTransport (e, 0, z) ∂volume ∂ν)
        = ∫⁻ _ : EnvGeneral, (0 : ℝ≥0∞) ∂ν := lintegral_congr_ae hae
      _ = 0 := lintegral_zero
  have hin : (∫⁻ e, ∫⁻ z : Plane, infiniteDegreeTransport (e, z, 0) ∂volume ∂ν) = 0 :=
    (hmt infiniteDegreeTransportKernel).symm.trans hout
  have hf : Measurable ((infiniteDegreeTransport) ∘
      fun p : EnvGeneral × Plane => (p.1, p.2, (0 : Plane))) :=
    measurable_infiniteDegreeTransport.comp
      (measurable_fst.prodMk (measurable_snd.prodMk measurable_const))
  have hmeas : Measurable fun e : EnvGeneral =>
      ∫⁻ z : Plane, infiniteDegreeTransport (e, z, 0) ∂volume := by
    simpa only [Function.comp_def] using hf.lintegral_prod_right'
  have hae := (lintegral_eq_zero_iff hmeas).mp hin
  filter_upwards [hae] with e he
  have he' : (∫⁻ z : Plane, infiniteDegreeTransport (e, z, 0) ∂volume) = 0 := he
  have hgz : Measurable ((infiniteDegreeTransport) ∘
      fun z : Plane => (e, z, (0 : Plane))) :=
    measurable_infiniteDegreeTransport.comp
      (measurable_const.prodMk (measurable_id.prodMk measurable_const))
  have hmz : Measurable fun z : Plane => infiniteDegreeTransport (e, z, 0) := by
    simpa only [Function.comp_def] using hgz
  have hz := (lintegral_eq_zero_iff hmz).mp he'
  refine measure_mono_null (fun z hzZ => ?_) (MeasureTheory.ae_iff.mp hz)
  show ¬ (infiniteDegreeTransport (e, z, 0) = 0)
  rw [infiniteDegreeTransport_of_mem e z 0 hzZ]
  exact mul_ne_zero (ENNReal.inv_ne_zero.mpr (edist_ne_top z 0))
    (ENNReal.inv_ne_zero.mpr (edist_ne_top z 0))

/-! ### Step 3: Lemma 2.5 -/

/-- **Lemma 2.5, with the deterministic Lemma 2.1 as an explicit input.**  Under mass transport
and (FE), if the rooted-functional exception mask of every environment is Lebesgue-null, then
almost surely every conductance row is finitely supported. -/
theorem ae_finiteRows_of_volume_boundaryMask (ν : Measure EnvGeneral) (hmt : MassTransport ν)
    (hFE : FiniteEnergyMoment ν)
    (hmask : ∀ e : EnvGeneral,
      volume (RootDensities.boundaryMask (config e).cellsOnly) = 0) :
    ∀ᵐ e ∂ν, FiniteRows e.val := by
  filter_upwards [ae_volume_infiniteDegreeSet_eq_zero ν hmt hFE] with e he
  intro n
  by_contra hinf
  cases hcase : e.val.1 n with
  | none =>
      apply hinf
      have hzero : e.val.2 n = 0 :=
        funext fun m => e.property.choose.absent n m (Or.inl hcase)
      rw [hzero, Function.support_zero]
      exact Set.finite_empty
  | some K =>
      have hsome : (e.val.1 n).isSome := Option.isSome_iff_exists.mpr ⟨K, hcase⟩
      have hvinf : (Function.support ((config e).c ⟨n, hsome⟩)).Infinite :=
        (infinite_support_config_iff e ⟨n, hsome⟩).mpr hinf
      have hsub : interior ((config e).cell ⟨n, hsome⟩ : Set Plane) \
          RootDensities.boundaryMask (config e).cellsOnly ⊆ infiniteDegreeSet e := by
        intro z hz
        exact ⟨hz.2, Set.mem_iUnion.mpr ⟨⟨n, hsome⟩, interior_subset hz.1, hvinf⟩⟩
      have hpos : 0 < volume (interior ((config e).cell ⟨n, hsome⟩ : Set Plane)) :=
        isOpen_interior.measure_pos volume
          ((config_generalGeometry e).interior_nonempty ⟨n, hsome⟩)
      have hle := measure_mono (μ := volume) hsub
      rw [measure_sdiff_null (hmask e), he] at hle
      exact absurd (le_antisymm hle zero_le) hpos.ne'

/-- **Lemma 2.5 (graph local finiteness follows from the moment).**  Under mass transport
modulo scaling and (FE), almost surely every cell has finitely many neighbours: every conductance
row of the code is finitely supported. -/
theorem ae_finiteRows (ν : Measure EnvGeneral) (hmt : MassTransport ν)
    (hFE : FiniteEnergyMoment ν) : ∀ᵐ e ∂ν, FiniteRows e.val :=
  ae_finiteRows_of_volume_boundaryMask ν hmt hFE fun e =>
    (config_generalGeometry e).volume_boundaryMask

end ReflectedGMS.GeneralLaws

assert_no_sorry ReflectedGMS.GeneralLaws.finiteEnergyDensity_eq_top_of_infinite_support
assert_no_sorry ReflectedGMS.GeneralLaws.rootAt_cellsOnly_eq_some
assert_no_sorry ReflectedGMS.GeneralLaws.measurableSet_infiniteDegreeProdSet
assert_no_sorry ReflectedGMS.GeneralLaws.mem_infiniteDegreeSet_similarity_iff
assert_no_sorry ReflectedGMS.GeneralLaws.infiniteDegreeTransportKernel
assert_no_sorry ReflectedGMS.GeneralLaws.measure_zero_mem_infiniteDegreeSet_eq_zero
assert_no_sorry ReflectedGMS.GeneralLaws.ae_volume_infiniteDegreeSet_eq_zero
assert_no_sorry ReflectedGMS.GeneralLaws.ae_finiteRows_of_volume_boundaryMask
assert_no_sorry ReflectedGMS.GeneralLaws.ae_finiteRows
#print axioms ReflectedGMS.GeneralLaws.finiteEnergyDensity_eq_top_of_infinite_support
#print axioms ReflectedGMS.GeneralLaws.infiniteDegreeTransportKernel
#print axioms ReflectedGMS.GeneralLaws.ae_volume_infiniteDegreeSet_eq_zero
#print axioms ReflectedGMS.GeneralLaws.ae_finiteRows_of_volume_boundaryMask
#print axioms ReflectedGMS.GeneralLaws.ae_finiteRows
