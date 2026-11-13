/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module ReflectedGMS.GMS.ValidCodeSet at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.ReflectedGMS.GMS.HypothesisTransferGMS
import Mathlib.Util.AssertNoSorry

/-!
# A Borel set of valid codes containing every GMS code

`supportedOnValidGeneral_map_gms` (`GMS/HypothesisTransferGMS.lean`) needs a **Borel** set `C` of
raw codes with `C ⊆ {r | ValidGeneral r}` containing the code of every line-connected GMS cell
configuration.  This file constructs one, `goodCodes`, by countably many Borel conditions on the slot
and conductance coordinates (`IsGoodCode`):

* admissible conductances (`Code.RawAdmissible`);
* canonical labels, slot by slot (a least rational interior label is a finite Boolean combination of
  interior-hit events, `CanonicalSimilarity.measurableSet_interiorPoint`);
* every active cell is connected — `ValidCodeSet.isClosed_setOf_isPreconnected`: a Hausdorff limit of
  preconnected compact sets is preconnected (a separation of the limit into two compact pieces has
  disjoint thickenings, which would separate the approximants);
* distinct active cells meet in a Lebesgue-null set — the area of the intersection is a measurable
  function of the code, by Tonelli, as in `Spatial.measurable_cellVolume`;
* every rational point lies in an active cell;
* every ball `B(0,R)`, `R ∈ ℕ`, meets only finitely many active cells (`SlotNear`);
* adjacent active cells intersect — `{(K,K') | K ∩ K' ≠ ∅}` is closed, the complement of mathlib's
  open disjointness set in the Vietoris topology, which is the Hausdorff-metric topology;
* point connectivity, `pointConnectedCodes` (`GMS/LineConnectedMeasurable.lean`).

**Validity** (`validGeneral_of_mem_goodCodes`): a good code decodes to a cell configuration
`ValidCodeSet.decodeConfig r` — cells the active slots, conductances read at their (unique) labels —
satisfying GMS Definition 1.15 (`IsGoodCode.isCellConfiguration`; the covering clause follows from
coverage of the dense rational points and local finiteness, which makes the union of the cells
closed), whose code is `r` itself (`IsGoodCode.decodeConfig_code`, by canonical labels), and which is
connected along lines (`code_mem_pointConnectedCodes_iff_lineConnected`).  Hence `r` is a GMS code
(`CellConfig.validGMS_code`) and a general code.

**Coverage** (`code_mem_goodCodes`): the code of every line-connected cell configuration is good,
clause by clause from `GMS/CodingValid.lean`.

**Corollary** (`supportedOnValidGeneral_codeMap`): for every GMS law `μ` connected along lines,
`GeneralLaws.SupportedOnValidGeneral (μ.map codeMap)` — the last upstream input of the hypothesis
transfer, now discharged.
-/

set_option autoImplicit false

open MeasureTheory Set Topology Metric
open scoped ENNReal

namespace ReflectedGMS.GMS

open Code

namespace ValidCodeSet

/-! ## Two Hausdorff-closed conditions on compact cells -/

/-- A cell within Hausdorff edistance `δ` of `K` lies in the `δ`-thickening of `K`. -/
theorem coe_subset_thickening_of_edist_lt {K L : CompactCell} {δ : ℝ}
    (h : edist K L < ENNReal.ofReal δ) : (L : Set Plane) ⊆ thickening δ (K : Set Plane) := by
  intro x hx
  rw [mem_thickening_iff_infEDist_lt]
  have h' : hausdorffEDist (L : Set Plane) (K : Set Plane) < ENNReal.ofReal δ := by
    rw [hausdorffEDist_comm]
    exact h
  exact lt_of_le_of_lt (infEDist_le_hausdorffEDist_of_mem hx) h'

/-- **A Hausdorff limit of preconnected compact sets is preconnected.** -/
theorem isClosed_setOf_isPreconnected :
    IsClosed {K : CompactCell | IsPreconnected (K : Set Plane)} := by
  refine isClosed_of_closure_subset fun K hK => ?_
  show IsPreconnected (K : Set Plane)
  rw [isPreconnected_iff_subset_of_fully_disjoint_closed K.isCompact.isClosed]
  intro u v hu hv hKuv huv
  by_contra hne
  rw [not_or] at hne
  obtain ⟨x, hxK, hxu⟩ := not_subset.1 hne.1
  obtain ⟨y, hyK, hyv⟩ := not_subset.1 hne.2
  have hxv : x ∈ v := (hKuv hxK).resolve_left hxu
  have hyu : y ∈ u := (hKuv hyK).resolve_right hyv
  have hdisj : Disjoint ((K : Set Plane) ∩ u) ((K : Set Plane) ∩ v) :=
    huv.mono inter_subset_right inter_subset_right
  obtain ⟨δ, hδ, hδd⟩ :=
    hdisj.exists_thickenings (K.isCompact.inter_right hu) (K.isCompact.isClosed.inter hv)
  obtain ⟨L, hLS, hKL⟩ :=
    EMetric.mem_closure_iff.1 hK (ENNReal.ofReal δ) (ENNReal.ofReal_pos.2 hδ)
  have hL : IsPreconnected (L : Set Plane) := hLS
  have hsub : (L : Set Plane) ⊆
      thickening δ ((K : Set Plane) ∩ u) ∪ thickening δ ((K : Set Plane) ∩ v) := by
    rw [← thickening_union, ← inter_union_distrib_left, inter_eq_left.2 hKuv]
    exact coe_subset_thickening_of_edist_lt hKL
  rcases hL.subset_or_subset isOpen_thickening isOpen_thickening hδd hsub with h | h
  · obtain ⟨z, hzL, hz⟩ := exists_edist_lt_of_hausdorffEDist_lt hxK hKL
    refine Set.disjoint_left.1 hδd (h hzL) ?_
    rw [mem_thickening_iff_exists_edist_lt]
    exact ⟨x, ⟨hxK, hxv⟩, by rw [edist_comm]; exact hz⟩
  · obtain ⟨z, hzL, hz⟩ := exists_edist_lt_of_hausdorffEDist_lt hyK hKL
    refine Set.disjoint_left.1 hδd ?_ (h hzL)
    rw [mem_thickening_iff_exists_edist_lt]
    exact ⟨y, ⟨hyK, hyu⟩, by rw [edist_comm]; exact hz⟩

/-- **Connectedness of a cell is a Borel condition.** -/
theorem measurableSet_setOf_isConnected :
    MeasurableSet {K : CompactCell | IsConnected (K : Set Plane)} := by
  have heq : {K : CompactCell | IsConnected (K : Set Plane)} =
      {K : CompactCell | IsPreconnected (K : Set Plane)} := by
    ext K
    exact ⟨fun h => h.isPreconnected, fun h => ⟨K.nonempty, h⟩⟩
  rw [heq]
  exact isClosed_setOf_isPreconnected.measurableSet

/-- **Meeting is a closed condition on pairs of cells**: its complement, disjointness, is open in the
Vietoris topology, which is the Hausdorff-metric topology of `NonemptyCompacts`. -/
theorem isClosed_setOf_inter_nonempty :
    IsClosed {p : CompactCell × CompactCell | ((p.1 : Set Plane) ∩ p.2).Nonempty} := by
  have heq : {p : CompactCell × CompactCell | ((p.1 : Set Plane) ∩ p.2).Nonempty} =
      {p : CompactCell × CompactCell | Disjoint (p.1 : Set Plane) p.2}ᶜ := by
    ext p
    simp only [mem_setOf_eq, mem_compl_iff, not_disjoint_iff_nonempty_inter]
  rw [heq]
  exact TopologicalSpace.NonemptyCompacts.isOpen_setOfPred_disjoint_coe.isClosed_compl

/-! ## Reading the slots of a raw code -/

/-- The cell in slot `n` of a raw code (`Spatial.referenceCell` if the slot is empty). -/
noncomputable def slotCell (r : RawCode) (n : ℕ) : CompactCell :=
  (r.1 n).getD Spatial.referenceCell

theorem slotCell_of_eq_some {r : RawCode} {n : ℕ} {K : CompactCell} (h : r.1 n = some K) :
    slotCell r n = K := by
  simp [slotCell, h]

theorem isSome_of_eq_some {r : RawCode} {n : ℕ} {K : CompactCell} (h : r.1 n = some K) :
    (r.1 n).isSome := by
  simp [h]

theorem measurable_codeSlot (n : ℕ) : Measurable fun r : RawCode => r.1 n :=
  (measurable_pi_apply n).comp measurable_fst

theorem measurable_slotCell (n : ℕ) : Measurable fun r : RawCode => slotCell r n :=
  Spatial.measurable_slotCell.comp (measurable_codeSlot n)

theorem measurable_rawCond (n m : ℕ) : Measurable fun r : RawCode => r.2 n m :=
  (measurable_pi_apply m).comp ((measurable_pi_apply n).comp measurable_snd)

theorem measurable_isSome (n : ℕ) : Measurable fun r : RawCode => (r.1 n).isSome = true :=
  measurableSet_setOfPred.1 ((measurable_codeSlot n) Spatial.measurableSet_slotIsSome)

theorem measurable_slot_eq_none (n : ℕ) : Measurable fun r : RawCode => r.1 n = none := by
  have h : (fun r : RawCode => r.1 n = none) = fun r => ¬ ((r.1 n).isSome = true) := by
    funext r
    exact propext Option.not_isSome_iff_eq_none.symm
  rw [h]
  exact (measurable_isSome n).not

theorem measurable_mem_slotCell (y : Plane) (n : ℕ) :
    Measurable fun r : RawCode => y ∈ (slotCell r n : Set Plane) :=
  measurableSet_setOfPred.1 ((measurable_slotCell n) (Spatial.measurableSet_mem_cell y))

theorem measurable_mem_interior_slotCell (y : Plane) (n : ℕ) :
    Measurable fun r : RawCode => y ∈ interior (slotCell r n : Set Plane) :=
  measurableSet_setOfPred.1
    ((measurable_slotCell n) (CanonicalSimilarity.measurableSet_interiorPoint y))

theorem measurable_leastInteriorLabel_slotCell (n : ℕ) :
    Measurable fun r : RawCode => LeastInteriorLabel (slotCell r n) n := by
  show Measurable fun r : RawCode => rationalPoint n ∈ interior (slotCell r n : Set Plane) ∧
    ∀ m : ℕ, m < n → rationalPoint m ∉ interior (slotCell r n : Set Plane)
  exact (measurable_mem_interior_slotCell _ n).and
    (Measurable.forall fun m => measurable_const.imp (measurable_mem_interior_slotCell _ n).not)

theorem measurable_isConnected_slotCell (n : ℕ) :
    Measurable fun r : RawCode => IsConnected (slotCell r n : Set Plane) :=
  measurableSet_setOfPred.1 ((measurable_slotCell n) measurableSet_setOf_isConnected)

theorem measurable_inter_nonempty_slotCell (n m : ℕ) :
    Measurable fun r : RawCode => ((slotCell r n : Set Plane) ∩ slotCell r m).Nonempty :=
  measurableSet_setOfPred.1 (((measurable_slotCell n).prodMk (measurable_slotCell m))
    isClosed_setOf_inter_nonempty.measurableSet)

/-- The area of the intersection of two slot cells is measurable in the code (Tonelli, as in
`Spatial.measurable_cellVolume`). -/
theorem measurable_volume_slotCell_inter (n m : ℕ) :
    Measurable fun r : RawCode => volume ((slotCell r n : Set Plane) ∩ slotCell r m) := by
  let S : Set (RawCode × Plane) :=
    {p | p.2 ∈ (slotCell p.1 n : Set Plane) ∩ (slotCell p.1 m : Set Plane)}
  have h1 : MeasurableSet {p : RawCode × Plane | p.2 ∈ (slotCell p.1 n : Set Plane)} :=
    (((measurable_slotCell n).comp measurable_fst).prodMk measurable_snd)
      Spatial.measurableSet_cellMem
  have h2 : MeasurableSet {p : RawCode × Plane | p.2 ∈ (slotCell p.1 m : Set Plane)} :=
    (((measurable_slotCell m).comp measurable_fst).prodMk measurable_snd)
      Spatial.measurableSet_cellMem
  have hS : MeasurableSet S := h1.inter h2
  have hf : Measurable (S.indicator fun _ => (1 : ℝ≥0∞)) := measurable_const.indicator hS
  have hint : Measurable fun r : RawCode =>
      ∫⁻ z : Plane, S.indicator (fun _ => (1 : ℝ≥0∞)) (r, z) ∂volume :=
    hf.lintegral_prod_right' (ν := (volume : Measure Plane))
  have hpt : ∀ r : RawCode, (∫⁻ z : Plane, S.indicator (fun _ => (1 : ℝ≥0∞)) (r, z) ∂volume) =
      volume ((slotCell r n : Set Plane) ∩ slotCell r m) := by
    intro r
    have hz : ∀ z : Plane, S.indicator (fun _ => (1 : ℝ≥0∞)) (r, z) =
        ((slotCell r n : Set Plane) ∩ slotCell r m).indicator (fun _ => (1 : ℝ≥0∞)) z := by
      intro z
      by_cases hzK : z ∈ (slotCell r n : Set Plane) ∩ slotCell r m
      · have hmem : (r, z) ∈ S := hzK
        rw [Set.indicator_of_mem hmem, Set.indicator_of_mem hzK]
      · have hmem : (r, z) ∉ S := hzK
        rw [Set.indicator_of_notMem hmem, Set.indicator_of_notMem hzK]
    simp_rw [hz]
    rw [lintegral_indicator_const ((slotCell r n).isCompact.isClosed.measurableSet.inter
      (slotCell r m).isCompact.isClosed.measurableSet), one_mul]
  have hEq : (fun r : RawCode => volume ((slotCell r n : Set Plane) ∩ slotCell r m)) =
      fun r : RawCode => ∫⁻ z : Plane, S.indicator (fun _ => (1 : ℝ≥0∞)) (r, z) ∂volume := by
    funext r
    exact (hpt r).symm
  rw [hEq]
  exact hint

theorem measurable_volume_slotCell_inter_eq_zero (n m : ℕ) :
    Measurable fun r : RawCode => volume ((slotCell r n : Set Plane) ∩ slotCell r m) = 0 := by
  have h : MeasurableSet {r : RawCode | volume ((slotCell r n : Set Plane) ∩ slotCell r m) = 0} :=
    (measurable_volume_slotCell_inter n m) (measurableSet_singleton 0)
  exact measurableSet_setOfPred.1 h

/-! ## The good codes -/

/-- **A good code**: countably many Borel conditions on the coordinates of a raw code, which
together force it to be the code of a GMS cell configuration connected along lines. -/
structure IsGoodCode (r : RawCode) : Prop where
  admissible : RawAdmissible r
  canonical : ∀ n, (r.1 n).isSome → LeastInteriorLabel (slotCell r n) n
  connected : ∀ n, (r.1 n).isSome → IsConnected (slotCell r n : Set Plane)
  nullInter : ∀ n m, n ≠ m → (r.1 n).isSome → (r.1 m).isSome →
    volume ((slotCell r n : Set Plane) ∩ slotCell r m) = 0
  cover : ∀ j, ∃ n, (r.1 n).isSome ∧ rationalPoint j ∈ (slotCell r n : Set Plane)
  locFin : ∀ R : ℕ, ∃ N : ℕ, ∀ n, N ≤ n → ¬ SlotNear 0 R (r.1 n)
  adjInter : ∀ n m, 0 < r.2 n m → (r.1 n).isSome → (r.1 m).isSome →
    ((slotCell r n : Set Plane) ∩ slotCell r m).Nonempty
  pointConnected : r ∈ pointConnectedCodes

theorem measurable_rawAdmissible : Measurable fun r : RawCode => RawAdmissible r := by
  have h : (fun r : RawCode => RawAdmissible r) = fun r =>
      (∀ n m, r.2 n m = r.2 m n) ∧ (∀ n m, 0 ≤ r.2 n m) ∧ (∀ n, r.2 n n = 0) ∧
        ∀ n m, r.1 n = none ∨ r.1 m = none → r.2 n m = 0 := by
    funext r
    exact propext ⟨fun h => ⟨h.symm, h.nonneg, h.self, h.absent⟩,
      fun h => ⟨h.1, h.2.1, h.2.2.1, h.2.2.2⟩⟩
  have heq : ∀ n m k l : ℕ, Measurable fun r : RawCode => r.2 n m = r.2 k l := fun n m k l =>
    measurableSet_setOfPred.1 (measurableSet_eq_fun (measurable_rawCond n m)
      (measurable_rawCond k l))
  have hnonneg : ∀ n m : ℕ, Measurable fun r : RawCode => 0 ≤ r.2 n m := fun n m =>
    measurableSet_setOfPred.1 (measurableSet_le measurable_const (measurable_rawCond n m))
  have hzero : ∀ n m : ℕ, Measurable fun r : RawCode => r.2 n m = 0 := fun n m =>
    measurableSet_setOfPred.1 (measurableSet_eq_fun (measurable_rawCond n m) measurable_const)
  rw [h]
  exact (Measurable.forall fun n => Measurable.forall fun m => heq n m m n).and
    ((Measurable.forall fun n => Measurable.forall fun m => hnonneg n m).and
      ((Measurable.forall fun n => hzero n n).and
        (Measurable.forall fun n => Measurable.forall fun m =>
          ((measurable_slot_eq_none n).or (measurable_slot_eq_none m)).imp (hzero n m))))

/-- **Goodness of a code is a Borel condition.** -/
theorem measurable_isGoodCode : Measurable fun r : RawCode => IsGoodCode r := by
  have h : (fun r : RawCode => IsGoodCode r) = fun r =>
      RawAdmissible r ∧ (∀ n, (r.1 n).isSome → LeastInteriorLabel (slotCell r n) n) ∧
        (∀ n, (r.1 n).isSome → IsConnected (slotCell r n : Set Plane)) ∧
        (∀ n m, n ≠ m → (r.1 n).isSome → (r.1 m).isSome →
          volume ((slotCell r n : Set Plane) ∩ slotCell r m) = 0) ∧
        (∀ j, ∃ n, (r.1 n).isSome ∧ rationalPoint j ∈ (slotCell r n : Set Plane)) ∧
        (∀ R : ℕ, ∃ N : ℕ, ∀ n, N ≤ n → ¬ SlotNear 0 R (r.1 n)) ∧
        (∀ n m, 0 < r.2 n m → (r.1 n).isSome → (r.1 m).isSome →
          ((slotCell r n : Set Plane) ∩ slotCell r m).Nonempty) ∧
        r ∈ pointConnectedCodes := by
    funext r
    exact propext ⟨fun h => ⟨h.1, h.2, h.3, h.4, h.5, h.6, h.7, h.8⟩,
      fun h => ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2.1, h.2.2.2.2.2.2.1,
        h.2.2.2.2.2.2.2⟩⟩
  have hpos : ∀ n m : ℕ, Measurable fun r : RawCode => 0 < r.2 n m := fun n m =>
    measurableSet_setOfPred.1 (measurableSet_lt measurable_const (measurable_rawCond n m))
  have hpc : Measurable fun r : RawCode => r ∈ pointConnectedCodes :=
    measurableSet_setOfPred.1 measurableSet_pointConnectedCodes
  rw [h]
  refine measurable_rawAdmissible.and ?_
  refine (Measurable.forall fun n =>
    (measurable_isSome n).imp (measurable_leastInteriorLabel_slotCell n)).and ?_
  refine (Measurable.forall fun n =>
    (measurable_isSome n).imp (measurable_isConnected_slotCell n)).and ?_
  refine (Measurable.forall fun n => Measurable.forall fun m => measurable_const.imp
    ((measurable_isSome n).imp ((measurable_isSome m).imp
      (measurable_volume_slotCell_inter_eq_zero n m)))).and ?_
  refine (Measurable.forall fun j => Measurable.exists fun n =>
    (measurable_isSome n).and (measurable_mem_slotCell _ n)).and ?_
  refine (Measurable.forall fun R => Measurable.exists fun N => Measurable.forall fun n =>
    measurable_const.imp (measurable_slotNear _ _ n).not).and ?_
  refine (Measurable.forall fun n => Measurable.forall fun m => (hpos n m).imp
    ((measurable_isSome n).imp ((measurable_isSome m).imp
      (measurable_inter_nonempty_slotCell n m)))).and ?_
  exact hpc

theorem IsGoodCode.leastLabel {r : RawCode} (hr : IsGoodCode r) {n : ℕ} {K : CompactCell}
    (hn : r.1 n = some K) : LeastInteriorLabel K n := by
  have h := hr.canonical n (isSome_of_eq_some hn)
  rwa [slotCell_of_eq_some hn] at h

/-- Under canonical labels, a cell occupies at most one slot. -/
theorem IsGoodCode.eq_of_slot {r : RawCode} (hr : IsGoodCode r) {n m : ℕ} {K : CompactCell}
    (hn : r.1 n = some K) (hm : r.1 m = some K) : n = m :=
  LeastInteriorLabel.unique (hr.leastLabel hn) (hr.leastLabel hm)

/-! ## Decoding a good code -/

/-- A slot holding the cell `K` (`0` if there is none). -/
noncomputable def cellLabel (r : RawCode) (K : Cell) : ℕ :=
  open Classical in if h : ∃ n, r.1 n = some K then h.choose else 0

theorem slot_cellLabel {r : RawCode} {K : Cell} (h : ∃ n, r.1 n = some K) :
    r.1 (cellLabel r K) = some K := by
  unfold cellLabel
  rw [dif_pos h]
  exact h.choose_spec

theorem IsGoodCode.cellLabel_eq {r : RawCode} (hr : IsGoodCode r) {n : ℕ} {K : Cell}
    (hn : r.1 n = some K) : cellLabel r K = n :=
  hr.eq_of_slot (slot_cellLabel ⟨n, hn⟩) hn

/-- The conductance of two cells read at their labels (`0` unless both are active). -/
noncomputable def decodeCond (r : RawCode) (K K' : Cell) : ℝ :=
  open Classical in
  if (∃ n, r.1 n = some K) ∧ ∃ m, r.1 m = some K' then r.2 (cellLabel r K) (cellLabel r K')
  else 0

/-- **The cell configuration decoded from a raw code**: the cells are the active slots, and the
conductance of two cells is read at their labels. -/
noncomputable def decodeConfig (r : RawCode) : CellConfig where
  cells := {K | ∃ n, r.1 n = some K}
  c := decodeCond r

theorem mem_decodeConfig_cells {r : RawCode} {K : Cell} :
    K ∈ (decodeConfig r).cells ↔ ∃ n, r.1 n = some K := Iff.rfl

theorem decodeConfig_c_of_not {r : RawCode} {K K' : Cell}
    (h : ¬ ((∃ n, r.1 n = some K) ∧ ∃ m, r.1 m = some K')) : (decodeConfig r).c K K' = 0 := by
  show decodeCond r K K' = 0
  unfold decodeCond
  rw [if_neg h]

theorem decodeConfig_c_of_mem {r : RawCode} {K K' : Cell}
    (h : (∃ n, r.1 n = some K) ∧ ∃ m, r.1 m = some K') :
    (decodeConfig r).c K K' = r.2 (cellLabel r K) (cellLabel r K') := by
  show decodeCond r K K' = _
  unfold decodeCond
  rw [if_pos h]

theorem IsGoodCode.decodeConfig_c {r : RawCode} (hr : IsGoodCode r) {n m : ℕ} {K K' : Cell}
    (hn : r.1 n = some K) (hm : r.1 m = some K') : (decodeConfig r).c K K' = r.2 n m := by
  rw [decodeConfig_c_of_mem ⟨⟨n, hn⟩, ⟨m, hm⟩⟩, hr.cellLabel_eq hn, hr.cellLabel_eq hm]

/-- Spatial local finiteness of the decoded configuration: the cells meeting `B(z,1)` are held by
the finitely many slots below the bound of `locFin` at a radius `R ≥ ‖z‖ + 1`. -/
theorem IsGoodCode.locallyFinite_decodeConfig {r : RawCode} (hr : IsGoodCode r) (z : Plane) :
    ∃ U ∈ 𝓝 z, ((decodeConfig r).restrict U).Finite := by
  obtain ⟨R, hR⟩ := exists_nat_ge (‖z‖ + 1)
  obtain ⟨N, hN⟩ := hr.locFin R
  refine ⟨ball z 1, ball_mem_nhds z one_pos, ?_⟩
  refine (((Set.finite_Iio N).image fun n => r.1 n).preimage
    (Option.some_injective _).injOn).subset ?_
  rintro K ⟨⟨n, hn⟩, w, hwK, hwU⟩
  refine ⟨n, Set.mem_Iio.2 ?_, hn⟩
  by_contra hnN
  apply hN n (not_lt.1 hnN)
  refine ⟨K, hn, ?_⟩
  have hwz : dist w z < 1 := mem_ball.1 hwU
  have htri : dist (0 : Plane) w ≤ dist (0 : Plane) z + dist z w := dist_triangle _ _ _
  have h0w : dist (0 : Plane) w = ‖w‖ := by rw [dist_zero_left]
  have h0z : dist (0 : Plane) z = ‖z‖ := by rw [dist_zero_left]
  have hzw : dist z w = dist w z := dist_comm z w
  calc infDist (0 : Plane) (K : Set Plane) ≤ dist (0 : Plane) w := infDist_le_dist_of_mem hwK
    _ < (R : ℝ) := by linarith

/-- The cells of the decoded configuration cover the plane: their union is closed (a locally
finite union of compact sets) and contains every rational point. -/
theorem IsGoodCode.iUnion_decodeConfig {r : RawCode} (hr : IsGoodCode r) :
    (⋃ K ∈ (decodeConfig r).cells, (K : Set Plane)) = univ := by
  have hlf : LocallyFinite fun K : (decodeConfig r).cells => ((K : Cell) : Set Plane) := by
    intro z
    obtain ⟨U, hU, hfin⟩ := hr.locallyFinite_decodeConfig z
    exact ⟨U, hU, (hfin.preimage Subtype.val_injective.injOn).subset fun K hK => ⟨K.2, hK⟩⟩
  have hclosed : IsClosed (⋃ K : (decodeConfig r).cells, ((K : Cell) : Set Plane)) :=
    hlf.isClosed_iUnion fun K => (K : Cell).isCompact.isClosed
  have hall : ∀ z : Plane, z ∈ ⋃ K : (decodeConfig r).cells, ((K : Cell) : Set Plane) := by
    intro z
    by_contra hz
    obtain ⟨j, hj⟩ := exists_rationalPoint_mem hclosed.isOpen_compl ⟨z, hz⟩
    obtain ⟨n, hns, hjn⟩ := hr.cover j
    obtain ⟨K, hK⟩ := Option.isSome_iff_exists.1 hns
    rw [slotCell_of_eq_some hK] at hjn
    exact hj (mem_iUnion.2 ⟨⟨K, n, hK⟩, hjn⟩)
  refine eq_univ_of_forall fun z => ?_
  obtain ⟨K, hzK⟩ := mem_iUnion.1 (hall z)
  exact mem_iUnion₂.2 ⟨K, K.2, hzK⟩

/-- **A good code decodes to a GMS cell configuration** (Definition 1.15). -/
theorem IsGoodCode.isCellConfiguration {r : RawCode} (hr : IsGoodCode r) :
    (decodeConfig r).IsCellConfiguration where
  locallyFinite := hr.locallyFinite_decodeConfig
  isConnected K hK := by
    obtain ⟨n, hn⟩ := hK
    have h := hr.connected n (isSome_of_eq_some hn)
    rwa [slotCell_of_eq_some hn] at h
  interior_nonempty K hK := by
    obtain ⟨n, hn⟩ := hK
    exact ⟨rationalPoint n, (hr.leastLabel hn).1⟩
  iUnion_eq_univ := hr.iUnion_decodeConfig
  volume_inter K hK K' hK' hne := by
    obtain ⟨n, hn⟩ := hK
    obtain ⟨m, hm⟩ := hK'
    have hnm : n ≠ m := by
      rintro rfl
      exact hne (Option.some_inj.1 (hn.symm.trans hm))
    have h := hr.nullInter n m hnm (isSome_of_eq_some hn) (isSome_of_eq_some hm)
    rwa [slotCell_of_eq_some hn, slotCell_of_eq_some hm] at h
  c_nonneg K K' := by
    by_cases h : (∃ n, r.1 n = some K) ∧ ∃ m, r.1 m = some K'
    · rw [decodeConfig_c_of_mem h]
      exact hr.admissible.nonneg _ _
    · rw [decodeConfig_c_of_not h]
  c_symm K K' := by
    by_cases h : (∃ n, r.1 n = some K) ∧ ∃ m, r.1 m = some K'
    · rw [decodeConfig_c_of_mem h, decodeConfig_c_of_mem ⟨h.2, h.1⟩]
      exact hr.admissible.symm _ _
    · rw [decodeConfig_c_of_not h, decodeConfig_c_of_not fun h' => h ⟨h'.2, h'.1⟩]
  adj_mem K K' hpos := by
    by_contra h
    have h' : ¬ ((∃ n, r.1 n = some K) ∧ ∃ m, r.1 m = some K') := h
    have hpos' : 0 < (decodeConfig r).c K K' := hpos
    rw [decodeConfig_c_of_not h'] at hpos'
    exact lt_irrefl _ hpos'
  adj_ne K K' hpos hKK := by
    subst hKK
    have hpos' : 0 < (decodeConfig r).c K K := hpos
    by_cases h : (∃ n, r.1 n = some K) ∧ ∃ m, r.1 m = some K
    · rw [decodeConfig_c_of_mem h, hr.admissible.self] at hpos'
      exact lt_irrefl _ hpos'
    · rw [decodeConfig_c_of_not h] at hpos'
      exact lt_irrefl _ hpos'
  adj_inter K K' hpos := by
    have hpos' : 0 < (decodeConfig r).c K K' := hpos
    by_cases h : (∃ n, r.1 n = some K) ∧ ∃ m, r.1 m = some K'
    · obtain ⟨⟨n, hn⟩, ⟨m, hm⟩⟩ := h
      rw [hr.decodeConfig_c hn hm] at hpos'
      have h' := hr.adjInter n m hpos' (isSome_of_eq_some hn) (isSome_of_eq_some hm)
      rwa [slotCell_of_eq_some hn, slotCell_of_eq_some hm] at h'
    · rw [decodeConfig_c_of_not h] at hpos'
      exact absurd hpos' (lt_irrefl _)

/-- The slots of the decoded configuration are those of the code (canonical labels). -/
theorem IsGoodCode.decodeConfig_slot {r : RawCode} (hr : IsGoodCode r) (n : ℕ) :
    (decodeConfig r).slot n = r.1 n := by
  have hH := hr.isCellConfiguration
  cases hn : r.1 n with
  | none =>
    refine (CellConfig.slot_eq_none_iff hH).2 fun K hK hl => ?_
    obtain ⟨m, hm⟩ := hK
    have hnm : n = m := LeastInteriorLabel.unique hl (hr.leastLabel hm)
    subst hnm
    rw [hn] at hm
    cases hm
  | some K => exact (CellConfig.slot_eq_some_iff hH).2 ⟨⟨n, hn⟩, hr.leastLabel hn⟩

/-- **A good code is the code of its decoded configuration.** -/
theorem IsGoodCode.decodeConfig_code {r : RawCode} (hr : IsGoodCode r) :
    (decodeConfig r).code = r := by
  have hslot : (decodeConfig r).slot = r.1 := funext hr.decodeConfig_slot
  refine Prod.ext hslot (funext fun n => funext fun m => ?_)
  show (decodeConfig r).codeCond n m = r.2 n m
  cases hn : r.1 n with
  | none =>
    rw [CellConfig.codeCond_of_none_left (by rw [hr.decodeConfig_slot, hn]),
      hr.admissible.absent n m (Or.inl hn)]
  | some K =>
    cases hm : r.1 m with
    | none =>
      rw [CellConfig.codeCond_of_none_right (by rw [hr.decodeConfig_slot, hm]),
        hr.admissible.absent n m (Or.inr hm)]
    | some K' =>
      rw [CellConfig.codeCond_of_some (by rw [hr.decodeConfig_slot, hn])
        (by rw [hr.decodeConfig_slot, hm]), hr.decodeConfig_c hn hm]

/-- The decoded configuration of a good code is connected along lines. -/
theorem IsGoodCode.lineConnected_decodeConfig {r : RawCode} (hr : IsGoodCode r) :
    (decodeConfig r).LineConnected := by
  refine (CellConfig.code_mem_pointConnectedCodes_iff_lineConnected hr.isCellConfiguration).1 ?_
  rw [hr.decodeConfig_code]
  exact hr.pointConnected

/-- **A good code is a GMS code.** -/
theorem IsGoodCode.validGMS {r : RawCode} (hr : IsGoodCode r) : ValidGMS r := by
  have h := CellConfig.validGMS_code hr.isCellConfiguration hr.lineConnected_decodeConfig
  rwa [hr.decodeConfig_code] at h

/-! ## Codes of GMS configurations are good -/

section Coverage

variable {H : CellConfig}

theorem exists_cell_of_isSome (hH : H.IsCellConfiguration) {n : ℕ} (hs : (H.code.1 n).isSome) :
    ∃ K : Cell, H.slot n = some K ∧ K ∈ H.cells ∧ LeastInteriorLabel K n ∧
      slotCell H.code n = K := by
  obtain ⟨K, hK⟩ := Option.isSome_iff_exists.1 hs
  have hK' : H.slot n = some K := hK
  obtain ⟨hKc, hl⟩ := (CellConfig.slot_eq_some_iff hH).1 hK'
  exact ⟨K, hK', hKc, hl, slotCell_of_eq_some hK⟩

/-- **The code of a line-connected GMS cell configuration is good.** -/
theorem isGoodCode_code (hH : H.IsCellConfiguration) (hL : H.LineConnected) :
    IsGoodCode H.code where
  admissible := CellConfig.rawAdmissible_code hH
  canonical n hs := by
    obtain ⟨K, -, -, hl, hsl⟩ := exists_cell_of_isSome hH hs
    rw [hsl]
    exact hl
  connected n hs := by
    obtain ⟨K, -, hKc, -, hsl⟩ := exists_cell_of_isSome hH hs
    rw [hsl]
    exact hH.isConnected K hKc
  nullInter n m hnm hn hm := by
    obtain ⟨K, hK, hKc, -, hsl⟩ := exists_cell_of_isSome hH hn
    obtain ⟨K', hK', hK'c, -, hsl'⟩ := exists_cell_of_isSome hH hm
    rw [hsl, hsl']
    refine hH.volume_inter K hKc K' hK'c fun hKK => hnm ?_
    subst hKK
    exact CellConfig.subsingleton_slot_eq hH K hK hK'
  cover j := by
    have hz : rationalPoint j ∈ ⋃ K ∈ H.cells, (K : Set Plane) := by
      rw [hH.iUnion_eq_univ]
      exact mem_univ _
    obtain ⟨K, hK, hjK⟩ := mem_iUnion₂.1 hz
    have hsl : H.slot (CellConfig.label hH ⟨K, hK⟩) = some K := CellConfig.slot_label hH ⟨K, hK⟩
    refine ⟨CellConfig.label hH ⟨K, hK⟩, isSome_of_eq_some (r := H.code) hsl, ?_⟩
    rw [slotCell_of_eq_some (r := H.code) hsl]
    exact hjK
  locFin R := by
    have hfin : {n : ℕ | SlotNear 0 R (H.code.1 n)}.Finite := by
      refine ((CellConfig.finite_restrict_of_isCompact hH (isCompact_closedBall (0 : Plane) R)).biUnion
        fun K _ => (CellConfig.subsingleton_slot_eq hH K).finite).subset ?_
      rintro n ⟨K, hK, hlt⟩
      have hK' : H.slot n = some K := hK
      obtain ⟨y, hyK, hy⟩ := (infDist_lt_iff K.nonempty).1 hlt
      refine mem_biUnion (x := K) ⟨((CellConfig.slot_eq_some_iff hH).1 hK').1, y, hyK, ?_⟩ hK'
      rw [mem_closedBall, dist_comm]
      exact hy.le
    obtain ⟨B, hB⟩ := hfin.bddAbove
    refine ⟨B + 1, fun n hn hnear => ?_⟩
    have hle : n ≤ B := hB hnear
    omega
  adjInter n m hpos hn hm := by
    obtain ⟨K, hK, -, -, hsl⟩ := exists_cell_of_isSome hH hn
    obtain ⟨K', hK', -, -, hsl'⟩ := exists_cell_of_isSome hH hm
    rw [hsl, hsl']
    have hpos' : 0 < H.c K K' := by
      rw [← CellConfig.codeCond_of_some hK hK']
      exact hpos
    exact hH.adj_inter K K' hpos'
  pointConnected := (CellConfig.code_mem_pointConnectedCodes_iff_lineConnected hH).2 hL

end Coverage

end ValidCodeSet

open ValidCodeSet

/-! ## The Borel set of good codes -/

/-- **The good codes**: a Borel set of raw codes, all of them GMS codes, containing the code of
every line-connected GMS cell configuration. -/
def goodCodes : Set RawCode := {r | IsGoodCode r}

/-- **The good codes form a Borel set.** -/
theorem measurableSet_goodCodes : MeasurableSet goodCodes :=
  measurableSet_setOfPred.2 measurable_isGoodCode

/-- **Every good code is a GMS code.** -/
theorem validGMS_of_mem_goodCodes {r : RawCode} (hr : r ∈ goodCodes) : ValidGMS r :=
  IsGoodCode.validGMS hr

/-- **Every good code is a code of the general manuscript.** -/
theorem validGeneral_of_mem_goodCodes {r : RawCode} (hr : r ∈ goodCodes) : ValidGeneral r :=
  validGeneral_of_validGMS (validGMS_of_mem_goodCodes hr)

/-- **The code of every line-connected GMS cell configuration is good.** -/
theorem code_mem_goodCodes {H : CellConfig} (hH : H.IsCellConfiguration) (hL : H.LineConnected) :
    H.code ∈ goodCodes :=
  isGoodCode_code hH hL

/-- **The coded law of a GMS law connected along lines is carried by general codes.** -/
theorem supportedOnValidGeneral_codeMap {μ : Measure GMSSpace} [IsProbabilityMeasure μ]
    (hL : ConnectedAlongLines μ) : GeneralLaws.SupportedOnValidGeneral (μ.map codeMap) :=
  supportedOnValidGeneral_map_gms hL measurableSet_goodCodes
    (fun _ hr => validGeneral_of_mem_goodCodes hr) (fun H hH => code_mem_goodCodes H.2 hH)

end ReflectedGMS.GMS

assert_no_sorry ReflectedGMS.GMS.ValidCodeSet.isClosed_setOf_isPreconnected
assert_no_sorry ReflectedGMS.GMS.ValidCodeSet.isClosed_setOf_inter_nonempty
assert_no_sorry ReflectedGMS.GMS.ValidCodeSet.measurable_volume_slotCell_inter
assert_no_sorry ReflectedGMS.GMS.ValidCodeSet.measurable_isGoodCode
assert_no_sorry ReflectedGMS.GMS.ValidCodeSet.IsGoodCode.isCellConfiguration
assert_no_sorry ReflectedGMS.GMS.ValidCodeSet.IsGoodCode.decodeConfig_code
assert_no_sorry ReflectedGMS.GMS.ValidCodeSet.IsGoodCode.validGMS
assert_no_sorry ReflectedGMS.GMS.ValidCodeSet.isGoodCode_code
assert_no_sorry ReflectedGMS.GMS.measurableSet_goodCodes
assert_no_sorry ReflectedGMS.GMS.validGMS_of_mem_goodCodes
assert_no_sorry ReflectedGMS.GMS.validGeneral_of_mem_goodCodes
assert_no_sorry ReflectedGMS.GMS.code_mem_goodCodes
assert_no_sorry ReflectedGMS.GMS.supportedOnValidGeneral_codeMap

#print axioms ReflectedGMS.GMS.ValidCodeSet.isClosed_setOf_isPreconnected
#print axioms ReflectedGMS.GMS.ValidCodeSet.IsGoodCode.isCellConfiguration
#print axioms ReflectedGMS.GMS.ValidCodeSet.IsGoodCode.decodeConfig_code
#print axioms ReflectedGMS.GMS.measurableSet_goodCodes
#print axioms ReflectedGMS.GMS.validGMS_of_mem_goodCodes
#print axioms ReflectedGMS.GMS.validGeneral_of_mem_goodCodes
#print axioms ReflectedGMS.GMS.code_mem_goodCodes
#print axioms ReflectedGMS.GMS.supportedOnValidGeneral_codeMap
