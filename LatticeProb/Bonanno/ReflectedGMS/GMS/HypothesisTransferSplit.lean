/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module ReflectedGMS.GMS.HypothesisTransferSplit at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.ReflectedGMS.Environment.GeneralLaws
import LatticeProb.Bonanno.ReflectedGMS.Environment.GeneralNullBoundaries
import LatticeProb.Bonanno.ReflectedGMS.Spatial.RootedMassBounds
import Mathlib.Util.AssertNoSorry

/-!
# The two halves of the rooted (FE) integrand, and their measurability

The (FE) integrand of the general manuscript is `d_H² / a_H · (π(H) + π*(H))` read at the root cell
(`GeneralLaws.rootedFiniteEnergyDensity`).  GMS's finite-expectation hypothesis (1.4) bounds the
two halves `d²/a · π` and `d²/a · π*` **separately**, at a root cell `H₀` chosen by an arbitrary,
possibly non-measurable, rule.  A lower Lebesgue integral of a non-measurable function is only
superadditive, so the transfer of (FE) needs each half of the general integrand as a
**measurable** function of the environment.  This file provides that.

* `rowEnergyDensity φ C v = d(H_v)² / a(H_v) · ∑_w ofReal (φ (c(v,w)))` — `φ = id` is the `π`
  half, `φ = (·)⁻¹` the `π*` half (`finiteEnergyDensity_eq_add`);
* `rootedRowEnergyDensity φ C z` — the same read at the root of `z` (zero at masked roots), and
  `rootedFiniteEnergyDensity_eq_add` splits the rooted (FE) integrand into the two halves;
* `rawRootedRowDensity φ` — a slot-sum expression on raw codes, measurable for the Borel
  σ-algebra of `RawCode` (`measurable_rawRootedRowDensity`);
* `rootedRowEnergyDensity_config` — at every general environment the rooted half **equals** the
  raw slot sum of its code (Definition 1.1's disjoint interiors single out the root slot), hence
  `measurable_rootedRowEnergyDensity_config` on `EnvGeneral`.

Reused: the slot-sum technique of `RootedFiniteEnergyDensityMeasurable` (there for `Code.Env` and
the whole density), `Spatial.measurable_slotCell`, `Spatial.measurableSet_cellInterior`,
`Spatial.measurableSet_cellFrontier`, `Spatial.measurableSet_cellMem`,
`Spatial.measurable_cellDiam`, `Spatial.measurable_cellVolume`, and
`GeneralGeometry.disjoint_interior`.
-/

set_option autoImplicit false

open MeasureTheory Set
open scoped ENNReal

namespace ReflectedGMS.GMS

open Code GeneralLaws Spatial

/-! ### The two halves of the (FE) integrand -/

/-- The half `d(H_v)² / a(H_v) · ∑_w ofReal (φ (c(v,w)))` of the (FE) integrand at a vertex. -/
noncomputable def rowEnergyDensity (φ : ℝ → ℝ) {V : Type*} (C : CellConfiguration V) (v : V) :
    ℝ≥0∞ :=
  ENNReal.ofReal (Metric.diam (C.cell v : Set Plane) ^ 2) /
      ENNReal.ofReal (StatementIngredients.cellArea C.cellsOnly v) *
    ∑' w, ENNReal.ofReal (φ (C.c v w))

/-- The same half read at the root cell of `z`; zero at uncovered or boundary points. -/
noncomputable def rootedRowEnergyDensity (φ : ℝ → ℝ) {V : Type*} (C : CellConfiguration V)
    (z : Plane) : ℝ≥0∞ :=
  (RootDensities.rootAt C.cellsOnly z).elim 0 (rowEnergyDensity φ C)

theorem finiteEnergyDensity_eq_add {V : Type*} (C : CellConfiguration V) (v : V) :
    finiteEnergyDensity C v =
      rowEnergyDensity id C v + rowEnergyDensity (fun x : ℝ => x⁻¹) C v :=
  mul_add _ _ _

/-- **The rooted (FE) integrand is the sum of its `π` half and its `π*` half.** -/
theorem rootedFiniteEnergyDensity_eq_add {V : Type*} (C : CellConfiguration V) (z : Plane) :
    rootedFiniteEnergyDensity C z =
      rootedRowEnergyDensity id C z + rootedRowEnergyDensity (fun x : ℝ => x⁻¹) C z := by
  unfold rootedFiniteEnergyDensity rootedRowEnergyDensity
  cases RootDensities.rootAt C.cellsOnly z with
  | none => exact (add_zero 0).symm
  | some v => exact finiteEnergyDensity_eq_add C v

/-! ### Slot sums on raw codes -/

/-- The cell read at slot `n` of a raw code, with the reference cell at absent slots. -/
noncomputable def rawSlotCell (r : RawCode) (n : ℕ) : CompactCell :=
  (r.1 n).getD referenceCell

theorem measurable_rawSlotCell (n : ℕ) : Measurable fun r : RawCode => rawSlotCell r n :=
  measurable_slotCell.comp ((measurable_pi_apply n).comp measurable_fst)

theorem rawSlotCell_vertex (r : RawCode) (v : Vertex r) : rawSlotCell r v.val = cell r v := by
  have hv : r.1 v.val = some (cell r v) := (Option.some_get v.property).symm
  rw [rawSlotCell, hv, Option.getD_some]

theorem measurableSet_rawSlotPresent (n : ℕ) :
    MeasurableSet {r : RawCode | (r.1 n).isSome} := by
  have hm : Measurable fun r : RawCode => r.1 n := (measurable_pi_apply n).comp measurable_fst
  exact hm measurableSet_slotIsSome

theorem measurableSet_rawSlotInterior (n : ℕ) :
    MeasurableSet {r : RawCode | (0 : Plane) ∈ interior (rawSlotCell r n : Set Plane)} :=
  ((measurable_rawSlotCell n).prodMk measurable_const) measurableSet_cellInterior

theorem measurableSet_rawSlotFrontier (n : ℕ) :
    MeasurableSet {r : RawCode | (0 : Plane) ∈ frontier (rawSlotCell r n : Set Plane)} :=
  ((measurable_rawSlotCell n).prodMk measurable_const) measurableSet_cellFrontier

theorem measurableSet_rawSlotMem (n : ℕ) :
    MeasurableSet {r : RawCode | (0 : Plane) ∈ (rawSlotCell r n : Set Plane)} :=
  ((measurable_rawSlotCell n).prodMk measurable_const) measurableSet_cellMem

/-- `d(H_n)² / a(H_n)` at slot `n`. -/
noncomputable def rawCellFactor (r : RawCode) (n : ℕ) : ℝ≥0∞ :=
  ENNReal.ofReal (Metric.diam (rawSlotCell r n : Set Plane) ^ 2) /
    volume (rawSlotCell r n : Set Plane)

theorem measurable_rawCellFactor (n : ℕ) : Measurable fun r : RawCode => rawCellFactor r n :=
  (((measurable_cellDiam.comp (measurable_rawSlotCell n)).pow_const 2).ennreal_ofReal).div
    (measurable_cellVolume.comp (measurable_rawSlotCell n))

/-- `∑_m ofReal (φ (c(n,m)))` over all slots. -/
noncomputable def rawRow (φ : ℝ → ℝ) (r : RawCode) (n : ℕ) : ℝ≥0∞ :=
  ∑' m : ℕ, ENNReal.ofReal (φ (r.2 n m))

theorem measurable_rawRow {φ : ℝ → ℝ} (hφ : Measurable φ) (n : ℕ) :
    Measurable fun r : RawCode => rawRow φ r n :=
  Measurable.ennreal_tsum fun m =>
    (hφ.comp ((measurable_pi_apply m).comp ((measurable_pi_apply n).comp measurable_snd))).ennreal_ofReal

/-- Slot `n` is present and its cell has `0` in its interior. -/
def RawRootSlot (r : RawCode) (n : ℕ) : Prop :=
  (r.1 n).isSome ∧ (0 : Plane) ∈ interior (rawSlotCell r n : Set Plane)

theorem measurableSet_rawRootSlot (n : ℕ) : MeasurableSet {r : RawCode | RawRootSlot r n} :=
  (measurableSet_rawSlotPresent n).inter (measurableSet_rawSlotInterior n)

/-- The raw form of the boundary mask at `0`: `0` is on the frontier of a present slot, or in no
present slot. -/
def rawMask : Set RawCode :=
  (⋃ n : ℕ, {r : RawCode | (r.1 n).isSome} ∩
      {r : RawCode | (0 : Plane) ∈ frontier (rawSlotCell r n : Set Plane)}) ∪
    (⋃ n : ℕ, {r : RawCode | (r.1 n).isSome} ∩
      {r : RawCode | (0 : Plane) ∈ (rawSlotCell r n : Set Plane)})ᶜ

theorem measurableSet_rawMask : MeasurableSet rawMask :=
  (MeasurableSet.iUnion fun n =>
      (measurableSet_rawSlotPresent n).inter (measurableSet_rawSlotFrontier n)).union
    (MeasurableSet.iUnion fun n =>
      (measurableSet_rawSlotPresent n).inter (measurableSet_rawSlotMem n)).compl

open Classical in
/-- **The raw slot sum** of a half of the rooted (FE) integrand at `0`. -/
noncomputable def rawRootedRowDensity (φ : ℝ → ℝ) (r : RawCode) : ℝ≥0∞ :=
  if r ∈ rawMask then 0
  else ∑' n : ℕ, if RawRootSlot r n then rawCellFactor r n * rawRow φ r n else 0

theorem measurable_rawRootedRowDensity {φ : ℝ → ℝ} (hφ : Measurable φ) :
    Measurable (rawRootedRowDensity φ) := by
  classical
  refine Measurable.ite measurableSet_rawMask measurable_const ?_
  exact Measurable.ennreal_tsum fun n =>
    Measurable.ite (measurableSet_rawRootSlot n)
      ((measurable_rawCellFactor n).mul (measurable_rawRow hφ n)) measurable_const

/-! ### The rooted halves at a general environment are the raw slot sums -/

theorem exists_vertex_iff (r : RawCode) (P : CompactCell → Prop) :
    (∃ v : Vertex r, P (cell r v)) ↔ ∃ n, (r.1 n).isSome ∧ P (rawSlotCell r n) := by
  constructor
  · rintro ⟨v, hv⟩
    exact ⟨v.val, v.property, by rw [rawSlotCell_vertex]; exact hv⟩
  · rintro ⟨n, hn, hP⟩
    exact ⟨⟨n, hn⟩, by rw [← rawSlotCell_vertex r ⟨n, hn⟩]; exact hP⟩

/-- The boundary mask of a raw configuration contains `0` exactly when the code lies in
`rawMask`. -/
theorem zero_mem_boundaryMask_iff (r : RawCode) (h : RawAdmissible r) :
    (0 : Plane) ∈ RootDensities.boundaryMask (rawConfig r h).cellsOnly ↔ r ∈ rawMask := by
  have hL : (0 : Plane) ∈ RootDensities.boundaryMask (rawConfig r h).cellsOnly ↔
      (∃ v : Vertex r, (0 : Plane) ∈ frontier (cell r v : Set Plane)) ∨
        ¬ ∃ v : Vertex r, (0 : Plane) ∈ (cell r v : Set Plane) := by
    show (0 : Plane) ∈ (⋃ v : Vertex r, frontier (cell r v : Set Plane)) ∪
        (⋃ v : Vertex r, (cell r v : Set Plane))ᶜ ↔ _
    simp only [mem_union, mem_iUnion, mem_compl_iff]
  have hR : r ∈ rawMask ↔
      (∃ n, (r.1 n).isSome ∧ (0 : Plane) ∈ frontier (rawSlotCell r n : Set Plane)) ∨
        ¬ ∃ n, (r.1 n).isSome ∧ (0 : Plane) ∈ (rawSlotCell r n : Set Plane) := by
    simp only [rawMask, mem_union, mem_iUnion, mem_compl_iff, mem_inter_iff, mem_setOf_eq]
  rw [hL, hR]
  exact or_congr (exists_vertex_iff r fun K => (0 : Plane) ∈ frontier (K : Set Plane))
    (not_congr (exists_vertex_iff r fun K => (0 : Plane) ∈ (K : Set Plane)))

/-- The row of a present slot is supported on present slots, for any `φ` with `φ 0 = 0`. -/
theorem support_row_subset {φ : ℝ → ℝ} (hφ0 : φ 0 = 0) (r : RawCode) (h : RawAdmissible r)
    (n : ℕ) :
    Function.support (fun m : ℕ => ENNReal.ofReal (φ (r.2 n m))) ⊆ {m : ℕ | (r.1 m).isSome} := by
  intro m hm
  by_contra hnone
  have hmn : r.1 m = none := Option.not_isSome_iff_eq_none.mp hnone
  apply hm
  show ENNReal.ofReal (φ (r.2 n m)) = 0
  rw [h.absent n m (Or.inr hmn), hφ0, ENNReal.ofReal_zero]

/-- At a vertex of a raw configuration the half of the (FE) integrand is the slot term. -/
theorem rowEnergyDensity_rawConfig {φ : ℝ → ℝ} (hφ0 : φ 0 = 0) (r : RawCode) (h : RawAdmissible r)
    (v : Vertex r) :
    rowEnergyDensity φ (rawConfig r h) v = rawCellFactor r v.val * rawRow φ r v.val := by
  have harea : ENNReal.ofReal (StatementIngredients.cellArea (rawConfig r h).cellsOnly v) =
      volume (cell r v : Set Plane) :=
    ENNReal.ofReal_toReal (cell r v).isCompact.measure_lt_top.ne
  have hrow : (∑' w : Vertex r, ENNReal.ofReal (φ ((rawConfig r h).c v w))) = rawRow φ r v.val := by
    calc (∑' w : Vertex r, ENNReal.ofReal (φ ((rawConfig r h).c v w)))
        = ∑' m : {m : ℕ | (r.1 m).isSome}, ENNReal.ofReal (φ (r.2 v.val m.val)) := rfl
      _ = ∑' m : ℕ, ENNReal.ofReal (φ (r.2 v.val m)) :=
          tsum_subtype_eq_of_support_subset (support_row_subset hφ0 r h v.val)
  rw [rowEnergyDensity, harea, hrow, rawCellFactor, rawSlotCell_vertex]
  rfl

/-- **At every general environment the rooted half of the (FE) integrand is the raw slot sum of
its code.**  Off the mask, `0` lies in the interior of exactly one present slot (Definition 1.1:
distinct cells have disjoint interiors), and that slot is the root. -/
theorem rootedRowEnergyDensity_config {φ : ℝ → ℝ} (hφ0 : φ 0 = 0) (e : EnvGeneral) :
    rootedRowEnergyDensity φ (config e) 0 = rawRootedRowDensity φ e.val := by
  classical
  have hgeom := config_generalGeometry e
  have hmask := zero_mem_boundaryMask_iff e.val e.property.choose
  by_cases hz : (0 : Plane) ∈ RootDensities.boundaryMask (config e).cellsOnly
  · have hr : e.val ∈ rawMask := hmask.1 hz
    rw [rootedRowEnergyDensity, RootDensities.rootAt_eq_none_of_mem_boundaryMask _ hz,
      rawRootedRowDensity, if_pos hr]
    rfl
  · have hr : e.val ∉ rawMask := fun h => hz (hmask.2 h)
    have hz' : (0 : Plane) ∉ (⋃ v : Vertex e.val, frontier (cell e.val v : Set Plane)) ∪
        (⋃ v : Vertex e.val, (cell e.val v : Set Plane))ᶜ := hz
    have hcov : (0 : Plane) ∈ ⋃ v : Vertex e.val, (cell e.val v : Set Plane) := by
      by_contra hc
      exact hz' (Or.inr hc)
    obtain ⟨v, hv0⟩ := mem_iUnion.mp hcov
    have hvint : (0 : Plane) ∈ interior (cell e.val v : Set Plane) := by
      have hfr : (0 : Plane) ∉ frontier (cell e.val v : Set Plane) := fun hf =>
        hz' (Or.inl (mem_iUnion.mpr ⟨v, hf⟩))
      rw [frontier, (cell e.val v).isCompact.isClosed.closure_eq] at hfr
      exact Classical.byContradiction fun hn => hfr ⟨hv0, hn⟩
    have huniq : ∀ w : Vertex e.val, (0 : Plane) ∈ interior (cell e.val w : Set Plane) → w = v := by
      intro w hw
      by_contra hwv
      exact Set.disjoint_left.1 (GeneralGeometry.disjoint_interior hgeom hwv) hw hvint
    have hex : ∃! w, RootDensities.IsInteriorRoot (config e).cellsOnly 0 w :=
      ⟨v, hvint, fun w hw => huniq w hw⟩
    have hroot : RootDensities.rootAt (config e).cellsOnly 0 = some v := by
      unfold RootDensities.rootAt
      rw [dif_neg hz, dif_pos hex]
      exact congrArg some (huniq _ hex.exists.choose_spec)
    have hslot : RawRootSlot e.val v.val :=
      ⟨v.property, by rw [rawSlotCell_vertex]; exact hvint⟩
    have hother : ∀ n : ℕ, n ≠ v.val →
        (if RawRootSlot e.val n then rawCellFactor e.val n * rawRow φ e.val n else 0) = 0 := by
      intro n hn
      rw [if_neg]
      rintro ⟨hs, hi⟩
      have hi' : (0 : Plane) ∈ interior (cell e.val ⟨n, hs⟩ : Set Plane) := by
        rw [← rawSlotCell_vertex]
        exact hi
      exact hn (congrArg Subtype.val (huniq ⟨n, hs⟩ hi'))
    rw [rootedRowEnergyDensity, hroot, rawRootedRowDensity, if_neg hr, tsum_eq_single v.val hother,
      if_pos hslot]
    exact rowEnergyDensity_rawConfig hφ0 e.val e.property.choose v

/-- **Each rooted half of the (FE) integrand is a measurable function of the general
environment.** -/
theorem measurable_rootedRowEnergyDensity_config {φ : ℝ → ℝ} (hφ : Measurable φ)
    (hφ0 : φ 0 = 0) : Measurable fun e : EnvGeneral => rootedRowEnergyDensity φ (config e) 0 := by
  have hEq : (fun e : EnvGeneral => rootedRowEnergyDensity φ (config e) 0) =
      rawRootedRowDensity φ ∘ Subtype.val :=
    funext fun e => rootedRowEnergyDensity_config hφ0 e
  rw [hEq]
  exact (measurable_rawRootedRowDensity hφ).comp measurable_subtype_coe

end ReflectedGMS.GMS

assert_no_sorry ReflectedGMS.GMS.rootedFiniteEnergyDensity_eq_add
assert_no_sorry ReflectedGMS.GMS.measurable_rawRootedRowDensity
assert_no_sorry ReflectedGMS.GMS.zero_mem_boundaryMask_iff
assert_no_sorry ReflectedGMS.GMS.rootedRowEnergyDensity_config
assert_no_sorry ReflectedGMS.GMS.measurable_rootedRowEnergyDensity_config

#print axioms ReflectedGMS.GMS.rootedFiniteEnergyDensity_eq_add
#print axioms ReflectedGMS.GMS.rootedRowEnergyDensity_config
#print axioms ReflectedGMS.GMS.measurable_rootedRowEnergyDensity_config
