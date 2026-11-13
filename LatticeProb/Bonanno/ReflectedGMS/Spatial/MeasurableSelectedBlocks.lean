/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module ReflectedGMS.Spatial.MeasurableSelectedBlocks at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.ReflectedGMS.Spatial.MarkedBlockAveraging
import LatticeProb.Bonanno.ReflectedGMS.Spatial.RootedMassBounds

/-!
# Measurability of the selected origin block

`ReflectedGMS.Spatial.MarkedBlockAveraging` proves the conditional block
averaging lemma `blockAverage_ae_eq_condExp` from three explicit producer
dependencies: the equivariance `BlockEquivariant`, the joint measurability
`MeasurableBlockGraph` of the selected origin block, and the measurability of
its side length `blockSideAt`.  This module supplies the last two for the
*actual* environment–grid observables of a marked configuration; it does not
touch the equivariance input.

The route is the one forced by the concrete objects, in which a patch may
contain infinitely many cells and no maximal or selected index is assumed
measurable:

* a compact cell meets a closed axis-parallel box exactly when, at every
  resolution `1/(n+1)`, some point of a fixed countable dense set of the plane
  is within `1/(n+1)` of the cell and within `1/(n+1)` of the box
  (`cellMeetsBox_iff`).  The backward direction uses compactness of the cell,
  not of the box, so `measurableSet_cellMeetsBoxSet` is a countable
  intersection of countable unions of closed/open conditions;
* consequently `maxCellDiameter` of an actual rectangle patch is the countable
  supremum over *code slots* of the cell diameter masked by the meeting
  condition (`maxCellDiameter_eq_iSup_slotBoxDiam`), so it is jointly
  measurable in the environment and the grid even when the patch is infinite;
* along the origin ancestor chain the dyadic indices are the explicit levels
  `originIndex (k + j)` (`MarkedBlockAveraging.ancestor_originIndex`), so
  `cellRatio`, `ancestorRatio`, `inverseRatio` and `blockIndex` are measurable
  by countable suprema and sums, and every `Selected` event of the origin chain
  is measurable (`measurableSet_originSelected`);
* the selected level itself is a `Classical.epsilon`.  It is measurable exactly
  because the selection is pathwise unique: on `{ω | OriginSelected … k}` it
  equals `k`, and off the (countable) union of those events the epsilon of an
  everywhere false predicate is the *same* junk level
  (`blockLevel_eq_defaultLevel`).  Uniqueness is kept as the explicit
  hypothesis `UniqueOriginSelection`, which the checked
  `MarkedBlockAveraging.originSelected_unique` derives from strict monotonicity
  of `κ` along the origin chain.

The conclusions are `measurableBlockGraph` and `measurable_blockSideAt`, with
the packaged corollary `measurableSelectedBlock_of_strictMono`.  The remaining
producer dependency of the consumer, not addressed here, is
`MarkedReRooting.BlockEquivariant` together with the mark-invariance input of
`MarkedBlockTransport`.
-/

set_option autoImplicit false
set_option maxHeartbeats 1600000

open MeasureTheory Set TopologicalSpace
open scoped ENNReal

namespace ReflectedGMS.MeasurableSelectedBlocks

open StatementIngredients DyadicApproximation DiameterBlockIndex MarkedBlockAveraging Code Spatial

variable {V : Type*}

/-! ### Coordinates of the plane -/

theorem dist_planeCoord_le (z w : Plane) (i : Fin 2) : |z i - w i| ≤ dist z w := by
  simpa [Real.dist_eq] using PiLp.dist_apply_le z w i

theorem continuous_planeCoord (i : Fin 2) : Continuous fun z : Plane => z i :=
  (LipschitzWith.mk_one fun z w => PiLp.dist_apply_le z w i).continuous

theorem measurable_planeCoord (i : Fin 2) : Measurable fun z : Plane => z i :=
  (continuous_planeCoord i).measurable

/-! ### A compact cell meeting a closed box -/

/-- The carrier of the closed axis-parallel box with corner coordinate vectors
`l` and `u`.  For a `Rectangle` this is definitionally `Rectangle.carrier`. -/
def boxCarrier (l u : Fin 2 → ℝ) : Set Plane := {z | ∀ i, l i ≤ z i ∧ z i ≤ u i}

theorem rectangle_carrier_eq_boxCarrier (Q : Rectangle) :
    Q.carrier = boxCarrier Q.lower Q.upper := rfl

/-- A compact cell meets a closed box exactly when, at every resolution, some
point of a fixed dense set is that close to both.  Only the cell is used as a
compact set, so this is available before any local finiteness of the patch. -/
theorem cellMeetsBox_iff {Dn : Set Plane} (hDn : Dense Dn) (K : CompactCell)
    (l u : Fin 2 → ℝ) :
    ((K : Set Plane) ∩ boxCarrier l u).Nonempty ↔
      ∀ n : ℕ, ∃ y ∈ Dn, Metric.infDist y (K : Set Plane) < 1 / ((n : ℝ) + 1) ∧
        ∀ i, l i ≤ y i + 1 / ((n : ℝ) + 1) ∧ y i - 1 / ((n : ℝ) + 1) ≤ u i := by
  constructor
  · rintro ⟨x, hxK, hxbox⟩ n
    have hpos : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
    obtain ⟨y, hyD, hxy⟩ := Metric.mem_closure_iff.mp (hDn x) _ hpos
    refine ⟨y, hyD, ?_, fun i => ?_⟩
    · refine lt_of_le_of_lt (Metric.infDist_le_dist_of_mem hxK) ?_
      rwa [dist_comm]
    · have hcoord := abs_le.mp (dist_planeCoord_le x y i)
      have hb := hxbox i
      constructor
      · linarith [hcoord.1, hcoord.2, hb.1]
      · linarith [hcoord.1, hcoord.2, hb.2]
  · intro h
    choose y hyD hy1 hy2 using h
    choose z hzK hzdist using fun n : ℕ => K.isCompact.exists_infDist_eq_dist K.nonempty (y n)
    obtain ⟨a, haK, φ, hφ, hlim⟩ := K.isCompact.tendsto_subseq hzK
    have hφle : ∀ n : ℕ, n ≤ φ n := fun _ => hφ.le_apply
    have hkey : ∀ ε : ℝ, 0 < ε → ∃ n : ℕ,
        dist (z (φ n)) a < ε ∧ 1 / ((φ n : ℝ) + 1) < ε := by
      intro ε hε
      obtain ⟨N, hN⟩ := exists_nat_one_div_lt hε
      obtain ⟨M, hM⟩ := Metric.tendsto_atTop.mp hlim ε hε
      refine ⟨max M N, hM _ (le_max_left _ _), ?_⟩
      have hle : N ≤ φ (max M N) := le_trans (le_max_right M N) (hφle _)
      have hNle : (N : ℝ) + 1 ≤ ((φ (max M N) : ℕ) : ℝ) + 1 := by
        have hcast : (N : ℝ) ≤ ((φ (max M N) : ℕ) : ℝ) := by exact_mod_cast hle
        linarith
      exact lt_of_le_of_lt (one_div_le_one_div_of_le (by positivity) hNle) hN
    have hdiff : ∀ n : ℕ, dist (z (φ n)) (y (φ n)) < 1 / ((φ n : ℝ) + 1) := by
      intro n
      rw [dist_comm, ← hzdist (φ n)]
      exact hy1 (φ n)
    refine ⟨a, haK, fun i => ?_⟩
    constructor
    · refine _root_.le_of_forall_pos_le_add fun ε hε => ?_
      obtain ⟨n, hn1, hn2⟩ := hkey (ε / 3) (by linarith)
      have hc1 := abs_le.mp (dist_planeCoord_le a (z (φ n)) i)
      have hc2 := abs_le.mp (dist_planeCoord_le (z (φ n)) (y (φ n)) i)
      have hd1 : dist a (z (φ n)) < ε / 3 := by rwa [dist_comm]
      have hd2 : dist (z (φ n)) (y (φ n)) < ε / 3 := lt_trans (hdiff n) hn2
      have hb := (hy2 (φ n) i).1
      linarith [hc1.1, hc1.2, hc2.1, hc2.2]
    · refine _root_.le_of_forall_pos_le_add fun ε hε => ?_
      obtain ⟨n, hn1, hn2⟩ := hkey (ε / 3) (by linarith)
      have hc1 := abs_le.mp (dist_planeCoord_le a (z (φ n)) i)
      have hc2 := abs_le.mp (dist_planeCoord_le (z (φ n)) (y (φ n)) i)
      have hd1 : dist a (z (φ n)) < ε / 3 := by rwa [dist_comm]
      have hd2 : dist (z (φ n)) (y (φ n)) < ε / 3 := lt_trans (hdiff n) hn2
      have hb := (hy2 (φ n) i).2
      linarith [hc1.1, hc1.2, hc2.1, hc2.2]

/-- Pairs of a compact cell and a closed box that actually meet. -/
def CellMeetsBoxSet : Set (CompactCell × ((Fin 2 → ℝ) × (Fin 2 → ℝ))) :=
  {p | ((p.1 : Set Plane) ∩ boxCarrier p.2.1 p.2.2).Nonempty}

/-- A set described by a countable-resolution approximation criterion is
measurable.  Every argument is opaque, so this set algebra never unfolds the
concrete cell, box or environment data. -/
theorem measurableSet_of_forall_exists {α γ : Type*} [MeasurableSpace α] {S : Set α}
    {Dn : Set γ} (hDn : Dn.Countable) {A : ℕ → γ → Set α}
    (hA : ∀ (n : ℕ) (y : γ), MeasurableSet (A n y))
    (hS : ∀ x : α, x ∈ S ↔ ∀ n : ℕ, ∃ y ∈ Dn, x ∈ A n y) :
    MeasurableSet S := by
  have key : S = ⋂ n : ℕ, ⋃ y ∈ Dn, A n y := by
    refine Set.ext fun x => ?_
    rw [hS x]
    constructor
    · intro h
      refine mem_iInter.2 fun n => mem_iUnion₂.2 ?_
      obtain ⟨y, hy, hxy⟩ := h n
      exact ⟨y, hy, hxy⟩
    · intro h n
      obtain ⟨y, hy, hxy⟩ := mem_iUnion₂.1 (mem_iInter.1 h n)
      exact ⟨y, hy, hxy⟩
  rw [key]
  exact MeasurableSet.iInter fun n => MeasurableSet.biUnion hDn fun y _ => hA n y

/-- Distance to a varying compact cell from a fixed point.  The composition is
bridged by `Function.comp_def` rather than by a definitional unfolding of the
Hausdorff metric structure. -/
theorem measurable_infDist_cell (y : Plane) :
    Measurable fun K : CompactCell => Metric.infDist y (K : Set Plane) := by
  have hlip : Continuous fun q : Plane × CompactCell =>
      Metric.infDist q.1 (q.2 : Set Plane) :=
    (NonemptyCompacts.lipschitz_infDist (α := Plane)).continuous
  have hpair : Continuous fun K : CompactCell => ((y : Plane), K) :=
    continuous_const.prodMk continuous_id
  have hcomp : Measurable ((fun q : Plane × CompactCell =>
      Metric.infDist q.1 (q.2 : Set Plane)) ∘ fun K : CompactCell => ((y : Plane), K)) :=
    (hlip.comp hpair).measurable
  simpa only [Function.comp_def] using hcomp

theorem measurableSet_cellMeetsBoxSet : MeasurableSet CellMeetsBoxSet := by
  obtain ⟨Dn, hDcount, hDdense⟩ := exists_countable_dense Plane
  refine measurableSet_of_forall_exists (A := fun (n : ℕ) (y : Plane) =>
      {p : CompactCell × ((Fin 2 → ℝ) × (Fin 2 → ℝ)) |
        Metric.infDist y (p.1 : Set Plane) < 1 / ((n : ℝ) + 1) ∧
        ∀ i, p.2.1 i ≤ y i + 1 / ((n : ℝ) + 1) ∧ y i - 1 / ((n : ℝ) + 1) ≤ p.2.2 i})
    hDcount ?_ fun p => cellMeetsBox_iff hDdense p.1 p.2.1 p.2.2
  intro n y
  have hinf : Measurable fun p : CompactCell × ((Fin 2 → ℝ) × (Fin 2 → ℝ)) =>
      Metric.infDist y (p.1 : Set Plane) := (measurable_infDist_cell y).comp measurable_fst
  have hlow : ∀ i : Fin 2, Measurable fun p : CompactCell × ((Fin 2 → ℝ) × (Fin 2 → ℝ)) =>
      p.2.1 i := fun i => (measurable_pi_apply i).comp (measurable_fst.comp measurable_snd)
  have hupp : ∀ i : Fin 2, Measurable fun p : CompactCell × ((Fin 2 → ℝ) × (Fin 2 → ℝ)) =>
      p.2.2 i := fun i => (measurable_pi_apply i).comp (measurable_snd.comp measurable_snd)
  have hEq : {p : CompactCell × ((Fin 2 → ℝ) × (Fin 2 → ℝ)) |
        Metric.infDist y (p.1 : Set Plane) < 1 / ((n : ℝ) + 1) ∧
        ∀ i, p.2.1 i ≤ y i + 1 / ((n : ℝ) + 1) ∧ y i - 1 / ((n : ℝ) + 1) ≤ p.2.2 i}
      = {p : CompactCell × ((Fin 2 → ℝ) × (Fin 2 → ℝ)) |
          Metric.infDist y (p.1 : Set Plane) < 1 / ((n : ℝ) + 1)} ∩
        ⋂ i : Fin 2,
          ({p : CompactCell × ((Fin 2 → ℝ) × (Fin 2 → ℝ)) |
              p.2.1 i ≤ y i + 1 / ((n : ℝ) + 1)} ∩
            {p : CompactCell × ((Fin 2 → ℝ) × (Fin 2 → ℝ)) |
              y i - 1 / ((n : ℝ) + 1) ≤ p.2.2 i}) :=
    Set.ext fun _ =>
      ⟨fun h => ⟨h.1, mem_iInter.2 fun i => ⟨(h.2 i).1, (h.2 i).2⟩⟩,
       fun h => ⟨h.1, fun i => ⟨(mem_iInter.1 h.2 i).1, (mem_iInter.1 h.2 i).2⟩⟩⟩
  rw [hEq]
  exact (hinf measurableSet_Iio).inter (MeasurableSet.iInter fun i =>
    ((hlow i) measurableSet_Iic).inter ((hupp i) measurableSet_Ici))

/-! ### The maximal cell diameter of a patch as a countable slot supremum -/

/-- Present code slots whose cell meets the box. -/
def SlotMeetsBoxSet : Set (Option CompactCell × ((Fin 2 → ℝ) × (Fin 2 → ℝ))) :=
  {q | q.1.isSome ∧
    (((q.1.getD referenceCell : CompactCell) : Set Plane) ∩ boxCarrier q.2.1 q.2.2).Nonempty}

theorem measurableSet_slotMeetsBoxSet : MeasurableSet SlotMeetsBoxSet := by
  have hmap : Measurable fun q : Option CompactCell × ((Fin 2 → ℝ) × (Fin 2 → ℝ)) =>
      ((q.1.getD referenceCell : CompactCell), q.2) :=
    (measurable_slotCell.comp measurable_fst).prodMk measurable_snd
  have h1 : MeasurableSet {q : Option CompactCell × ((Fin 2 → ℝ) × (Fin 2 → ℝ)) | q.1.isSome} :=
    measurable_fst measurableSet_slotIsSome
  have h2 := hmap measurableSet_cellMeetsBoxSet
  have hEq : SlotMeetsBoxSet
      = {q : Option CompactCell × ((Fin 2 → ℝ) × (Fin 2 → ℝ)) | q.1.isSome} ∩
        ((fun q : Option CompactCell × ((Fin 2 → ℝ) × (Fin 2 → ℝ)) =>
          ((q.1.getD referenceCell : CompactCell), q.2)) ⁻¹' CellMeetsBoxSet) :=
    Set.ext fun _ => Iff.rfl
  rw [hEq]
  exact h1.inter h2

/-- The cell diameter contributed by one code slot to a box: zero for an absent
slot and for a cell missing the box. -/
noncomputable def slotBoxDiam (q : Option CompactCell × ((Fin 2 → ℝ) × (Fin 2 → ℝ))) : ℝ≥0∞ :=
  SlotMeetsBoxSet.indicator
    (fun q => ENNReal.ofReal (Metric.diam ((q.1.getD referenceCell : CompactCell) : Set Plane))) q

theorem measurable_slotBoxDiam : Measurable slotBoxDiam := by
  have hdiam : Measurable fun q : Option CompactCell × ((Fin 2 → ℝ) × (Fin 2 → ℝ)) =>
      ENNReal.ofReal (Metric.diam ((q.1.getD referenceCell : CompactCell) : Set Plane)) :=
    (measurable_cellDiam.comp (measurable_slotCell.comp measurable_fst)).ennreal_ofReal
  exact hdiam.indicator measurableSet_slotMeetsBoxSet

theorem getD_eq_get (o : Option CompactCell) (h : o.isSome) :
    o.getD referenceCell = o.get h := by
  cases o with
  | none => simp at h
  | some K => rfl

/-- The manuscript's `D(S)` for an actual rectangle patch is a supremum over the
countably many code slots, with the meeting condition as a measurable mask.  No
finiteness of the patch is used. -/
theorem maxCellDiameter_eq_iSup_slotBoxDiam (e : Env) (D : Grid) (s : SquareIndex) :
    maxCellDiameter (decode e) D s
      = ⨆ n : ℕ, slotBoxDiam (e.val.1 n, ((square D s).lower, (square D s).upper)) := by
  refine le_antisymm (iSup_le fun v => ?_) (iSup_le fun n => ?_)
  · have hcell : ((e.val.1 v.1.val).getD referenceCell : CompactCell) = (decode e).cell v.1 :=
      getD_eq_get _ v.1.property
    have hmem : (e.val.1 v.1.val, ((square D s).lower, (square D s).upper)) ∈ SlotMeetsBoxSet :=
      ⟨v.1.property, by rw [hcell]; exact v.2⟩
    have hval : slotBoxDiam (e.val.1 v.1.val, ((square D s).lower, (square D s).upper))
        = ENNReal.ofReal (Metric.diam ((decode e).cell v.1 : Set Plane)) := by
      unfold slotBoxDiam
      rw [Set.indicator_of_mem hmem, hcell]
    rw [← hval]
    exact le_iSup
      (fun n : ℕ => slotBoxDiam (e.val.1 n, ((square D s).lower, (square D s).upper))) v.1.val
  · by_cases hmem : (e.val.1 n, ((square D s).lower, (square D s).upper)) ∈ SlotMeetsBoxSet
    · have hsome := hmem.1
      have hcell : ((e.val.1 n).getD referenceCell : CompactCell)
          = (decode e).cell ⟨n, hsome⟩ := getD_eq_get _ hsome
      have hhits : (⟨n, hsome⟩ : Vertex e.val) ∈ patchVertices (decode e) (square D s) := by
        have hne := hmem.2
        rw [hcell] at hne
        exact hne
      have hval : slotBoxDiam (e.val.1 n, ((square D s).lower, (square D s).upper))
          = ENNReal.ofReal (Metric.diam ((decode e).cell ⟨n, hsome⟩ : Set Plane)) := by
        unfold slotBoxDiam
        rw [Set.indicator_of_mem hmem, hcell]
      rw [hval]
      exact le_iSup (fun v : patchVertices (decode e) (square D s) =>
        ENNReal.ofReal (Metric.diam ((decode e).cell v.1 : Set Plane))) ⟨⟨n, hsome⟩, hhits⟩
    · have hval : slotBoxDiam (e.val.1 n, ((square D s).lower, (square D s).upper)) = 0 := by
        unfold slotBoxDiam
        rw [Set.indicator_of_notMem hmem]
      rw [hval]
      exact zero_le

/-! ### Measurability of the dyadic grid data -/

theorem measurable_gridData : Measurable fun D : Grid => (D.phase, D.origin, D.digit) :=
  measurable_iff_comap_le.2 le_rfl

theorem measurable_gridPhase : Measurable fun D : Grid => D.phase :=
  measurable_fst.comp measurable_gridData

theorem measurable_gridOrigin (k : ℤ) (i : Fin 2) : Measurable fun D : Grid => D.origin k i :=
  (measurable_pi_apply i).comp ((measurable_pi_apply k).comp
    (measurable_fst.comp (measurable_snd.comp measurable_gridData)))

theorem measurable_side (k : ℤ) : Measurable fun D : Grid => side D k := by
  show Measurable fun D : Grid => (2 : ℝ) ^ (D.phase + (k : ℝ))
  exact ((Real.continuous_const_rpow (by norm_num : (2 : ℝ) ≠ 0)).measurable).comp
    (measurable_gridPhase.add_const _)

theorem measurable_squareLower (s : SquareIndex) (i : Fin 2) :
    Measurable fun D : Grid => (square D s).lower i := by
  show Measurable fun D : Grid => D.origin s.1 i + side D s.1 * (s.2 i : ℝ)
  exact (measurable_gridOrigin s.1 i).add ((measurable_side s.1).mul_const _)

theorem measurable_squareUpper (s : SquareIndex) (i : Fin 2) :
    Measurable fun D : Grid => (square D s).upper i := by
  show Measurable fun D : Grid =>
    D.origin s.1 i + side D s.1 * (s.2 i : ℝ) + side D s.1
  exact ((measurable_gridOrigin s.1 i).add
    ((measurable_side s.1).mul_const _)).add (measurable_side s.1)

theorem measurable_squareLowerVec (s : SquareIndex) :
    Measurable fun D : Grid => (square D s).lower :=
  Measurable.of_eval fun i => measurable_squareLower s i

theorem measurable_squareUpperVec (s : SquareIndex) :
    Measurable fun D : Grid => (square D s).upper :=
  Measurable.of_eval fun i => measurable_squareUpper s i

/-! ### Joint measurability of the diameter and block indices -/

theorem measurable_envSlot (n : ℕ) : Measurable fun p : Env × Grid => p.1.val.1 n :=
  ((measurable_pi_apply n).comp (measurable_fst.comp measurable_inclusion)).comp measurable_fst

theorem measurable_maxCellDiameter (s : SquareIndex) :
    Measurable fun p : Env × Grid => maxCellDiameter (decode p.1) p.2 s := by
  have hEq : (fun p : Env × Grid => maxCellDiameter (decode p.1) p.2 s)
      = fun p : Env × Grid => ⨆ n : ℕ,
          slotBoxDiam (p.1.val.1 n, ((square p.2 s).lower, (square p.2 s).upper)) :=
    funext fun p => maxCellDiameter_eq_iSup_slotBoxDiam p.1 p.2 s
  rw [hEq]
  refine Measurable.iSup fun n => ?_
  exact measurable_slotBoxDiam.comp ((measurable_envSlot n).prodMk
    (((measurable_squareLowerVec s).comp measurable_snd).prodMk
      ((measurable_squareUpperVec s).comp measurable_snd)))

theorem measurable_cellRatio (s : SquareIndex) :
    Measurable fun p : Env × Grid => cellRatio (decode p.1) p.2 s := by
  have hEq : (fun p : Env × Grid => cellRatio (decode p.1) p.2 s)
      = fun p : Env × Grid => maxCellDiameter (decode p.1) p.2 s *
          (ENNReal.ofReal (side p.2 s.1))⁻¹ :=
    funext fun _ => div_eq_mul_inv _ _
  rw [hEq]
  exact (measurable_maxCellDiameter s).mul
    ((((measurable_side s.1).comp measurable_snd).ennreal_ofReal).inv)

/-- Along the origin chain the ancestor indices are the explicit origin levels,
by the checked `MarkedBlockAveraging.ancestor_originIndex`. -/
theorem ancestorRatio_originIndex_eq (F : IndexedCells V) (D : Grid) (k : ℤ) :
    ancestorRatio F D (originIndex k) = ⨆ j : ℕ, cellRatio F D (originIndex (k + (j : ℤ))) := by
  rw [ancestorRatio_eq_iSup]
  exact iSup_congr fun j => by rw [ancestor_originIndex]

theorem blockIndex_originIndex_eq (F : IndexedCells V) (D : Grid) (k : ℤ) :
    blockIndex F D (originIndex k)
      = ∑' j : ℕ, ((4 : ℝ≥0∞) ^ j)⁻¹ * inverseRatio F D (originIndex (k + (j : ℤ))) := by
  unfold blockIndex
  exact tsum_congr fun j => by rw [ancestor_originIndex]

theorem measurable_ancestorRatio_originIndex (k : ℤ) :
    Measurable fun p : Env × Grid => ancestorRatio (decode p.1) p.2 (originIndex k) := by
  have hEq : (fun p : Env × Grid => ancestorRatio (decode p.1) p.2 (originIndex k))
      = fun p : Env × Grid => ⨆ j : ℕ,
          cellRatio (decode p.1) p.2 (originIndex (k + (j : ℤ))) :=
    funext fun p => ancestorRatio_originIndex_eq _ _ k
  rw [hEq]
  exact Measurable.iSup fun j => measurable_cellRatio (originIndex (k + (j : ℤ)))

theorem measurable_inverseRatio_originIndex (k : ℤ) :
    Measurable fun p : Env × Grid => inverseRatio (decode p.1) p.2 (originIndex k) :=
  (measurable_ancestorRatio_originIndex k).inv

theorem measurable_blockIndex_originIndex (k : ℤ) :
    Measurable fun p : Env × Grid => blockIndex (decode p.1) p.2 (originIndex k) := by
  have hEq : (fun p : Env × Grid => blockIndex (decode p.1) p.2 (originIndex k))
      = fun p : Env × Grid => ∑' j : ℕ,
          ((4 : ℝ≥0∞) ^ j)⁻¹ * inverseRatio (decode p.1) p.2 (originIndex (k + (j : ℤ))) :=
    funext fun p => blockIndex_originIndex_eq _ _ k
  rw [hEq]
  exact Measurable.ennreal_tsum fun j =>
    (measurable_inverseRatio_originIndex (k + (j : ℤ))).const_mul _

/-- Every selection event of the origin chain is measurable in the environment
and the grid. -/
theorem measurableSet_originSelected (m : ℝ) (k : ℤ) :
    MeasurableSet {p : Env × Grid | OriginSelected (decode p.1) p.2 m k} := by
  by_cases hm : (0 : ℝ) < m
  · have hEq : {p : Env × Grid | OriginSelected (decode p.1) p.2 m k}
        = {p : Env × Grid | blockIndex (decode p.1) p.2 (originIndex k) ≤ ENNReal.ofReal m} ∩
          {p : Env × Grid |
            ENNReal.ofReal m < blockIndex (decode p.1) p.2 (originIndex (k + 1))} := by
      ext p
      constructor
      · rintro ⟨-, h1, h2⟩
        rw [parent_originIndex] at h2
        exact ⟨h1, h2⟩
      · rintro ⟨h1, h2⟩
        refine ⟨hm, h1, ?_⟩
        rw [parent_originIndex]
        exact h2
    rw [hEq]
    exact (measurableSet_le (measurable_blockIndex_originIndex k) measurable_const).inter
      (measurableSet_lt measurable_const (measurable_blockIndex_originIndex (k + 1)))
  · have hEq : {p : Env × Grid | OriginSelected (decode p.1) p.2 m k} = ∅ := by
      ext p
      simp only [mem_empty_iff_false, iff_false]
      rintro ⟨h, -, -⟩
      exact hm h
    rw [hEq]
    exact MeasurableSet.empty

/-! ### The selected level -/

/-- The junk level produced by `MarkedBlockAveraging.blockLevel` when no origin
square is selected.  It does not depend on the environment or the grid. -/
noncomputable def defaultLevel : ℤ := Classical.epsilon fun _ : ℤ => False

theorem blockLevel_eq_defaultLevel {F : IndexedCells V} {D : Grid} {m : ℝ}
    (h : ¬ ∃ k : ℤ, OriginSelected F D m k) : blockLevel F D m = defaultLevel := by
  have hpred : (fun k : ℤ => OriginSelected F D m k) = fun _ : ℤ => False :=
    funext fun k => eq_false fun hk => h ⟨k, hk⟩
  show Classical.epsilon (fun k : ℤ => OriginSelected F D m k)
      = Classical.epsilon fun _ : ℤ => False
  rw [hpred]

theorem blockLevel_eq_of_unique {F : IndexedCells V} {D : Grid} {m : ℝ}
    (huniq : ∀ k l : ℤ, OriginSelected F D m k → OriginSelected F D m l → k = l)
    {k : ℤ} (hk : OriginSelected F D m k) : blockLevel F D m = k :=
  huniq _ _ (originSelected_blockLevel ⟨k, hk⟩) hk

/-- A graph selected by a countable measurable index is measurable.  All the
data is opaque here, so the set algebra never unfolds the environment-dependent
block description. -/
theorem measurableSet_graph_of_countable_index {Ω ι β : Type*} [MeasurableSpace Ω]
    [MeasurableSpace β] [Countable ι] [MeasurableSpace ι] [MeasurableSingletonClass ι]
    {f : Ω → ι} (hf : Measurable f) {S : ι → Ω → Set β}
    (hS : ∀ i : ι, MeasurableSet {p : Ω × β | p.2 ∈ S i p.1}) :
    MeasurableSet {p : Ω × β | p.2 ∈ S (f p.1) p.1} := by
  have hEq : {p : Ω × β | p.2 ∈ S (f p.1) p.1}
      = ⋃ i : ι, ({p : Ω × β | f p.1 = i} ∩ {p : Ω × β | p.2 ∈ S i p.1}) := by
    refine Set.ext fun p => ⟨fun hp => mem_iUnion.2 ⟨f p.1, rfl, hp⟩, fun hp => ?_⟩
    obtain ⟨i, hi, hmem⟩ := mem_iUnion.1 hp
    show p.2 ∈ S (f p.1) p.1
    rw [show f p.1 = i from hi]
    exact hmem
  rw [hEq]
  exact MeasurableSet.iUnion fun i =>
    ((hf.comp measurable_fst) (measurableSet_singleton i)).inter (hS i)

/-! ### The measurable selected block of a marked configuration -/

section Marked

variable {Ω : Type*} [MeasurableSpace Ω] (R : MarkedReRooting Ω) (m : ℝ)

/-- At most one origin square is selected, in every marked configuration.  This
is the manuscript's uniqueness of `S_m(0)`; the checked
`MarkedBlockAveraging.originSelected_unique` derives it from strict
monotonicity of `κ` along the origin chain. -/
def UniqueOriginSelection : Prop :=
  ∀ ω : Ω, ∀ k l : ℤ,
    OriginSelected (decode (R.env ω)) (R.grid ω) m k →
    OriginSelected (decode (R.env ω)) (R.grid ω) m l → k = l

variable {R m}

/-- The definitional bridge from the consumer's selected block to the explicit
half-open origin square of the selected level.  Proving it once, on its own,
keeps the environment observable opaque in every later set computation. -/
theorem blockSetAt_eq (ω : Ω) :
    R.blockSetAt m ω = halfOpenSquare (R.grid ω) (originIndex (R.blockLevelAt m ω)) := rfl

theorem measurableSet_originSelectedAt (henv : Measurable R.env) (hgrid : Measurable R.grid)
    (k : ℤ) :
    MeasurableSet {ω : Ω | OriginSelected (decode (R.env ω)) (R.grid ω) m k} :=
  (henv.prodMk hgrid) (measurableSet_originSelected m k)

/-- The selected level is measurable: on each selection event it is the
corresponding level, and off all of them it is the fixed junk level. -/
theorem measurable_blockLevelAt (henv : Measurable R.env) (hgrid : Measurable R.grid)
    (huniq : UniqueOriginSelection R m) : Measurable (R.blockLevelAt m) := by
  have hsel : ∀ l : ℤ,
      MeasurableSet {ω : Ω | OriginSelected (decode (R.env ω)) (R.grid ω) m l} :=
    fun l => measurableSet_originSelectedAt henv hgrid l
  have hlevel : ∀ ω : Ω, ∀ l : ℤ,
      OriginSelected (decode (R.env ω)) (R.grid ω) m l → R.blockLevelAt m ω = l :=
    fun ω l hl => blockLevel_eq_of_unique (huniq ω) hl
  refine measurable_to_countable' fun k => ?_
  by_cases hk : k = defaultLevel
  · have hEq : R.blockLevelAt m ⁻¹' {k}
        = {ω : Ω | OriginSelected (decode (R.env ω)) (R.grid ω) m k} ∪
          (⋃ l : ℤ, {ω : Ω | OriginSelected (decode (R.env ω)) (R.grid ω) m l})ᶜ := by
      ext ω
      simp only [mem_preimage, mem_singleton_iff, mem_union, mem_compl_iff, mem_iUnion,
        mem_setOf_eq, not_exists]
      constructor
      · intro hω
        by_cases hex : ∃ l : ℤ, OriginSelected (decode (R.env ω)) (R.grid ω) m l
        · refine Or.inl ?_
          have hspec := originSelected_blockLevel hex
          rwa [show blockLevel (decode (R.env ω)) (R.grid ω) m = k from hω] at hspec
        · refine Or.inr ?_
          push_neg at hex
          exact hex
      · rintro (h | h)
        · exact hlevel ω k h
        · have hex : ¬ ∃ l : ℤ, OriginSelected (decode (R.env ω)) (R.grid ω) m l := by
            rintro ⟨l, hl⟩
            exact h l hl
          rw [hk]
          exact blockLevel_eq_defaultLevel hex
    rw [hEq]
    exact (hsel k).union (MeasurableSet.iUnion hsel).compl
  · have hEq : R.blockLevelAt m ⁻¹' {k}
        = {ω : Ω | OriginSelected (decode (R.env ω)) (R.grid ω) m k} := by
      ext ω
      simp only [mem_preimage, mem_singleton_iff, mem_setOf_eq]
      constructor
      · intro hω
        by_cases hex : ∃ l : ℤ, OriginSelected (decode (R.env ω)) (R.grid ω) m l
        · have hspec := originSelected_blockLevel hex
          rwa [show blockLevel (decode (R.env ω)) (R.grid ω) m = k from hω] at hspec
        · refine absurd ?_ hk
          rw [← hω]
          exact blockLevel_eq_defaultLevel hex
      · exact hlevel ω k
    rw [hEq]
    exact hsel k

/-- The manuscript's `ℓ(S_m(0))` is measurable: the consumer's `hside`. -/
theorem measurable_blockSideAt (henv : Measurable R.env) (hgrid : Measurable R.grid)
    (huniq : UniqueOriginSelection R m) : Measurable (R.blockSideAt m) := by
  have hlevel := measurable_blockLevelAt henv hgrid huniq
  have hprod : Measurable fun q : ℤ × Ω => side (R.grid q.2) q.1 :=
    measurable_from_prod_countable_right fun k => (measurable_side k).comp hgrid
  exact hprod.comp (hlevel.prodMk measurable_id)

theorem measurableSet_halfOpenSquareGraph (hgrid : Measurable R.grid) (k : ℤ) :
    MeasurableSet {p : Ω × Plane | p.2 ∈ halfOpenSquare (R.grid p.1) (originIndex k)} := by
  have hEq : {p : Ω × Plane | p.2 ∈ halfOpenSquare (R.grid p.1) (originIndex k)}
      = ⋂ i : Fin 2,
        ({p : Ω × Plane | (square (R.grid p.1) (originIndex k)).lower i ≤ p.2 i} ∩
          {p : Ω × Plane | p.2 i < (square (R.grid p.1) (originIndex k)).upper i}) :=
    Set.ext fun p =>
      ⟨fun hp => mem_iInter.2 fun i => ⟨(hp i).1, (hp i).2⟩,
       fun hp i => ⟨(mem_iInter.1 hp i).1, (mem_iInter.1 hp i).2⟩⟩
  rw [hEq]
  refine MeasurableSet.iInter fun i => ?_
  have hlow : Measurable fun p : Ω × Plane =>
      (square (R.grid p.1) (originIndex k)).lower i :=
    (measurable_squareLower (originIndex k) i).comp (hgrid.comp measurable_fst)
  have hupp : Measurable fun p : Ω × Plane =>
      (square (R.grid p.1) (originIndex k)).upper i :=
    (measurable_squareUpper (originIndex k) i).comp (hgrid.comp measurable_fst)
  have hz : Measurable fun p : Ω × Plane => p.2 i :=
    (measurable_planeCoord i).comp measurable_snd
  exact (measurableSet_le hlow hz).inter (measurableSet_lt hz hupp)

/-- The selected origin block has a measurable graph: the consumer's
`hgraph`. -/
theorem measurableBlockGraph (henv : Measurable R.env) (hgrid : Measurable R.grid)
    (huniq : UniqueOriginSelection R m) : R.MeasurableBlockGraph m := by
  have hgraph : MeasurableSet {p : Ω × Plane |
      p.2 ∈ halfOpenSquare (R.grid p.1) (originIndex (R.blockLevelAt m p.1))} :=
    measurableSet_graph_of_countable_index (measurable_blockLevelAt henv hgrid huniq)
      (S := fun k ω => halfOpenSquare (R.grid ω) (originIndex k))
      fun k => measurableSet_halfOpenSquareGraph hgrid k
  have hset : {p : Ω × Plane | p.2 ∈ R.blockSetAt m p.1}
      = {p : Ω × Plane |
          p.2 ∈ halfOpenSquare (R.grid p.1) (originIndex (R.blockLevelAt m p.1))} :=
    Set.ext fun p => by
      show p.2 ∈ R.blockSetAt m p.1 ↔
        p.2 ∈ halfOpenSquare (R.grid p.1) (originIndex (R.blockLevelAt m p.1))
      rw [blockSetAt_eq]
  show MeasurableSet {p : Ω × Plane | p.2 ∈ R.blockSetAt m p.1}
  rw [hset]
  exact hgraph

/-- Strict monotonicity of `κ` along the origin chain gives the uniqueness
hypothesis, by the checked `MarkedBlockAveraging.originSelected_unique`. -/
theorem uniqueOriginSelection_of_strictMono
    (hmono : ∀ ω : Ω, StrictMono fun k : ℤ =>
      blockIndex (decode (R.env ω)) (R.grid ω) (originIndex k)) :
    UniqueOriginSelection R m :=
  fun ω _ _ hk hl => originSelected_unique (hmono ω) hk hl

/-- **The measurable selected origin block.**  For a marked configuration with
measurable environment and grid observables whose origin selection is pathwise
unique, both measurability dependencies of
`MarkedBlockAveraging.MarkedReRooting.blockAverage_ae_eq_condExp` hold. -/
theorem measurableSelectedBlock (henv : Measurable R.env) (hgrid : Measurable R.grid)
    (huniq : UniqueOriginSelection R m) :
    R.MeasurableBlockGraph m ∧ Measurable (R.blockSideAt m) :=
  ⟨measurableBlockGraph henv hgrid huniq, measurable_blockSideAt henv hgrid huniq⟩

/-- The same conclusion from strict monotonicity of `κ` along the origin
chain. -/
theorem measurableSelectedBlock_of_strictMono (henv : Measurable R.env)
    (hgrid : Measurable R.grid)
    (hmono : ∀ ω : Ω, StrictMono fun k : ℤ =>
      blockIndex (decode (R.env ω)) (R.grid ω) (originIndex k)) :
    R.MeasurableBlockGraph m ∧ Measurable (R.blockSideAt m) :=
  measurableSelectedBlock henv hgrid (uniqueOriginSelection_of_strictMono hmono)

end Marked

end ReflectedGMS.MeasurableSelectedBlocks
