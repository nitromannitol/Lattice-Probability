/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module ReflectedGMS.GMS.LineConnectedMeasurable at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.ReflectedGMS.GMS.LineConnectedPoint
import LatticeProb.Bonanno.ReflectedGMS.GMS.CodeMeasurable
import Mathlib.Util.AssertNoSorry

/-!
# Connectedness along lines is a Borel, similarity-invariant event

GMS's mass-transport hypothesis tests only kernels that are Borel for `d^CC` and covariant for every
pair of similar configurations.  To use `1_{connected along lines} · T(code H, w₀, w₁)` as such a
kernel we need the event `{H | H.LineConnected}` to be Borel and similarity invariant.

* `CellConfig.lineConnected_iff_forall_singleton` (in `GMS/LineConnectedPoint.lean`) reduces
  connectedness along lines to connectedness of the point graphs `H({z})`.
* `pointConnectedCodes` is a **Borel set of raw codes** (`measurableSet_pointConnectedCodes`): for
  every nonempty finite label set `S` that is the set of labels of the cells through some point
  (`PointSetOccurs`, detected along the fixed rational points with a uniform margin from all other
  cells), the labels in `S` induce a connected subgraph of the code graph (`codeGraph`: `n ∼ m` iff
  `n ≠ m` and both conductances are positive).
* `CellConfig.code_mem_pointConnectedCodes_iff` — for a cell configuration,
  `H.code ∈ pointConnectedCodes ↔ ∀ z, (H.inducedGraph {z}).Connected`.  The label set of the cells
  through `z` is finite (local finiteness) and nonempty (covering), and a label set `S` passes the
  rational-point test iff it is the label set of some point (compactness of the cells for one
  direction, local finiteness for the other).
* `measurableSet_lineConnected` — `{H : GMSSpace | H.1.LineConnected}` is Borel for `d^CC`
  (from `measurableSet_lineConnected_of_measurable_codeMap` and `measurable_codeMap`,
  `GMS/CodeMeasurable.lean`).
* `lineConnected_iff_of_isSimilar` (in `GMS/LineConnectedPoint.lean`) — the event is invariant
  under every positive similarity.
-/

set_option autoImplicit false

open MeasureTheory Set Filter Topology

namespace ReflectedGMS.GMS

/-! ## Slot distances -/

/-- `q` lies within distance `t` of the cell in slot `o` (false for an empty slot). -/
def SlotNear (q : Plane) (t : ℝ) (o : Option Code.CompactCell) : Prop :=
  ∃ K : Code.CompactCell, o = some K ∧ Metric.infDist q (K : Set Plane) < t

theorem isOpen_setOf_slotNear (q : Plane) (t : ℝ) :
    IsOpen {o : Option Code.CompactCell | SlotNear q t o} := by
  have hU : IsOpen {K : Code.CompactCell | Metric.infDist q (K : Set Plane) < t} :=
    isOpen_lt (TopologicalSpace.NonemptyCompacts.lipschitz_infDist_const q).continuous
      continuous_const
  have heq : {o : Option Code.CompactCell | SlotNear q t o} =
      Code.slotEquiv ⁻¹'
        (Sum.inl '' {K : Code.CompactCell | Metric.infDist q (K : Set Plane) < t}) := by
    ext o
    cases o with
    | none => simp [SlotNear, Code.slotEquiv]
    | some K => simp [SlotNear, Code.slotEquiv]
  rw [heq]
  exact (isOpenMap_inl _ hU).preimage continuous_induced_dom

theorem measurable_slotNear (q : Plane) (t : ℝ) (n : ℕ) :
    Measurable fun r : Code.RawCode => SlotNear q t (r.1 n) := by
  have hm : Measurable fun r : Code.RawCode => r.1 n := (measurable_pi_apply n).comp measurable_fst
  exact measurableSet_setOfPred.1 (hm (isOpen_setOf_slotNear q t).measurableSet)

/-! ## Label sets of points -/

/-- **The finite label set `S` is the label set of a point**, tested along the fixed rational
points: for some margin `1/(e+1)` and every precision `1/(k+1)` there is a rational point within
`1/(k+1)` of every cell labelled in `S` and at distance at least `1/(e+1)` from every other cell of
the code. -/
def PointSetOccurs (r : Code.RawCode) (S : Finset ℕ) : Prop :=
  ∃ e : ℕ, ∀ k : ℕ, ∃ j : ℕ,
    (∀ n ∈ S, SlotNear (Code.rationalPoint j) (1 / ((k : ℝ) + 1)) (r.1 n)) ∧
      ∀ m, m ∉ S → ¬ SlotNear (Code.rationalPoint j) (1 / ((e : ℝ) + 1)) (r.1 m)

theorem measurable_pointSetOccurs (S : Finset ℕ) :
    Measurable fun r : Code.RawCode => PointSetOccurs r S := by
  unfold PointSetOccurs
  refine Measurable.exists fun e => Measurable.forall fun k => Measurable.exists fun j => ?_
  refine Measurable.and ?_ ?_
  · exact Measurable.forall fun n => measurable_const.imp (measurable_slotNear _ _ n)
  · exact Measurable.forall fun m => measurable_const.imp (measurable_slotNear _ _ m).not

/-! ## The code graph -/

/-- The graph of a raw code on labels: `n ∼ m` iff `n ≠ m` and both conductances are positive. -/
def codeGraph (r : Code.RawCode) : SimpleGraph ℕ where
  Adj n m := n ≠ m ∧ 0 < r.2 n m ∧ 0 < r.2 m n
  symm := ⟨fun _ _ h => ⟨Ne.symm h.1, h.2.2, h.2.1⟩⟩
  loopless := ⟨fun _ h => h.1 rfl⟩

theorem measurable_codeGraph_adj (n m : ℕ) :
    Measurable fun r : Code.RawCode => (codeGraph r).Adj n m := by
  have hc : ∀ a b : ℕ, Measurable fun r : Code.RawCode => r.2 a b := fun a b =>
    (measurable_pi_apply b).comp ((measurable_pi_apply a).comp measurable_snd)
  have hpos : ∀ a b : ℕ, Measurable fun r : Code.RawCode => 0 < r.2 a b := fun a b =>
    measurableSet_setOfPred.1 (measurableSet_lt measurable_const (hc a b))
  show Measurable fun r : Code.RawCode => n ≠ m ∧ 0 < r.2 n m ∧ 0 < r.2 m n
  exact measurable_const.and ((hpos n m).and (hpos m n))

/-- A predicate that factors through a measurable map into a countable space with measurable
singletons is measurable. -/
theorem measurable_of_measurable_factor {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    [Countable β] [MeasurableSingletonClass β] {f : α → β} (hf : Measurable f) {P : α → Prop}
    (hP : ∀ a b, f a = f b → (P a ↔ P b)) : Measurable P := by
  have heq : {a | P a} = f ⁻¹' (f '' {a | P a}) := by
    ext a
    constructor
    · intro ha
      exact ⟨a, ha, rfl⟩
    · rintro ⟨b, hb, hba⟩
      exact (hP b a hba).1 hb
  have hs : MeasurableSet {a | P a} := by
    rw [heq]
    exact hf (Set.to_countable _).measurableSet
  exact measurableSet_setOfPred.1 hs

/-- Connectedness of the code graph on a fixed finite label set is measurable: it depends only on
the finitely many adjacencies between those labels. -/
theorem measurable_induce_codeGraph_connected (S : Finset ℕ) :
    Measurable fun r : Code.RawCode => ((codeGraph r).induce (S : Set ℕ)).Connected := by
  haveI : Finite (S : Set ℕ) := S.finite_toSet.to_subtype
  refine measurable_of_measurable_factor
    (f := fun (r : Code.RawCode) (a b : (S : Set ℕ)) => (codeGraph r).Adj a b)
    (Measurable.of_eval fun a => Measurable.of_eval fun b => measurable_codeGraph_adj a b) ?_
  intro r r' h
  have hG : (codeGraph r).induce (S : Set ℕ) = (codeGraph r').induce (S : Set ℕ) := by
    ext a b
    exact iff_of_eq (congrFun (congrFun h a) b)
  rw [hG]

/-! ## The Borel set of point-connected codes -/

/-- **Point-connected codes**: every nonempty finite label set that is the label set of a point
induces a connected subgraph of the code graph. -/
def pointConnectedCodes : Set Code.RawCode :=
  {r | ∀ S : Finset ℕ, S.Nonempty → PointSetOccurs r S →
    ((codeGraph r).induce (S : Set ℕ)).Connected}

/-- **The point-connected codes form a Borel set.** -/
theorem measurableSet_pointConnectedCodes : MeasurableSet pointConnectedCodes :=
  measurableSet_setOfPred.2 (Measurable.forall fun S => measurable_const.imp
    ((measurable_pointSetOccurs S).imp (measurable_induce_codeGraph_connected S)))

namespace CellConfig

variable {H : CellConfig}

/-! ## Labels of the cells through a point -/

/-- The labels of the cells of `H` through `z`. -/
def labelsAt (H : CellConfig) (z : Plane) : Set ℕ :=
  {n | ∃ K : Cell, H.slot n = some K ∧ z ∈ (K : Set Plane)}

theorem finite_labelsAt (hH : H.IsCellConfiguration) (z : Plane) : (H.labelsAt z).Finite := by
  obtain ⟨U, hU, hfin⟩ := hH.locallyFinite z
  refine Set.Finite.of_finite_image (f := H.slot) ((hfin.image some).subset ?_) ?_
  · rintro _ ⟨n, ⟨K, hK, hzK⟩, rfl⟩
    exact ⟨K, ⟨((slot_eq_some_iff hH).1 hK).1, z, hzK, mem_of_mem_nhds hU⟩, hK.symm⟩
  · rintro n ⟨K, hK, -⟩ m ⟨K', hK', -⟩ hnm
    have hKK : K = K' := Option.some_inj.1 (hK.symm.trans (hnm.trans hK'))
    subst hKK
    exact subsingleton_slot_eq hH K hK hK'

theorem labelsAt_nonempty (hH : H.IsCellConfiguration) (z : Plane) :
    (H.labelsAt z).Nonempty := by
  have hz : z ∈ ⋃ K ∈ H.cells, (K : Set Plane) := by
    rw [hH.iUnion_eq_univ]
    exact Set.mem_univ z
  obtain ⟨K, hK, hzK⟩ := Set.mem_iUnion₂.1 hz
  exact ⟨label hH ⟨K, hK⟩, K, slot_label hH ⟨K, hK⟩, hzK⟩

theorem label_injective (hH : H.IsCellConfiguration) : Function.Injective (label hH) := by
  intro K K' h
  have h1 := slot_label hH K
  rw [h, slot_label hH K'] at h1
  exact Subtype.ext (Option.some_inj.1 h1).symm

theorem label_mem_labelsAt (hH : H.IsCellConfiguration) {z : Plane}
    (K : {K : H.cells | ((K : Set Plane) ∩ {z}).Nonempty}) : label hH K.1 ∈ H.labelsAt z :=
  ⟨K.1.1, slot_label hH K.1, Set.inter_singleton_nonempty.1 K.2⟩

/-- The cells through `z` are in bijection with their labels. -/
noncomputable def singletonLabelEquiv (hH : H.IsCellConfiguration) (z : Plane) :
    {K : H.cells | ((K : Set Plane) ∩ {z}).Nonempty} ≃ H.labelsAt z :=
  Equiv.ofBijective (fun K => ⟨label hH K.1, label_mem_labelsAt hH K⟩)
    ⟨fun K K' h => Subtype.ext (label_injective hH (congrArg Subtype.val h)), fun n => by
      obtain ⟨n, K, hK, hzK⟩ := n
      have hK' := (slot_eq_some_iff hH).1 hK
      refine ⟨⟨⟨K, hK'.1⟩, Set.inter_singleton_nonempty.2 hzK⟩, Subtype.ext ?_⟩
      exact Code.LeastInteriorLabel.unique (leastInteriorLabel_label hH ⟨K, hK'.1⟩) hK'.2⟩

/-- **The point graph `H({z})` is the code graph on the labels of the cells through `z`.** -/
noncomputable def singletonLabelIso (hH : H.IsCellConfiguration) (z : Plane) :
    H.inducedGraph {z} ≃g (codeGraph H.code).induce (H.labelsAt z) where
  toEquiv := singletonLabelEquiv hH z
  map_rel_iff' {K K'} := by
    change (label hH K.1 ≠ label hH K'.1 ∧ 0 < H.codeCond (label hH K.1) (label hH K'.1) ∧
        0 < H.codeCond (label hH K'.1) (label hH K.1)) ↔
      (K.1 ≠ K'.1 ∧ 0 < H.c K.1 K'.1 ∧ 0 < H.c K'.1 K.1)
    rw [codeCond_of_some (slot_label hH K.1) (slot_label hH K'.1),
      codeCond_of_some (slot_label hH K'.1) (slot_label hH K.1), (label_injective hH).ne_iff]

theorem inducedGraph_singleton_connected_iff (hH : H.IsCellConfiguration) (z : Plane) :
    (H.inducedGraph {z}).Connected ↔ ((codeGraph H.code).induce (H.labelsAt z)).Connected :=
  (singletonLabelIso hH z).connected_iff

/-! ## The rational-point test recognises label sets of points -/

/-- The label set of the cells through a point passes the rational-point test. -/
theorem pointSetOccurs_of_coe_eq_labelsAt (hH : H.IsCellConfiguration) {z : Plane}
    {S : Finset ℕ} (hS : (S : Set ℕ) = H.labelsAt z) : PointSetOccurs H.code S := by
  obtain ⟨δ, hδ, hnear⟩ := exists_pos_mem_of_inter_closedBall hH z
  obtain ⟨e, he⟩ := exists_nat_one_div_lt (half_pos hδ)
  refine ⟨e, fun k => ?_⟩
  have hk : (0 : ℝ) < 1 / ((k : ℝ) + 1) := Nat.one_div_pos_of_nat
  obtain ⟨j, hj⟩ := Code.exists_rationalPoint_mem
    (U := Metric.ball z (min (1 / ((k : ℝ) + 1)) (δ / 2))) Metric.isOpen_ball
    (Metric.nonempty_ball.2 (lt_min hk (half_pos hδ)))
  have hjz : dist (Code.rationalPoint j) z < min (1 / ((k : ℝ) + 1)) (δ / 2) :=
    Metric.mem_ball.1 hj
  refine ⟨j, fun n hn => ?_, fun m hm => ?_⟩
  · have hn' : n ∈ H.labelsAt z := by
      rw [← hS]
      exact hn
    obtain ⟨K, hK, hzK⟩ := hn'
    exact ⟨K, hK, lt_of_le_of_lt (Metric.infDist_le_dist_of_mem hzK)
      (lt_of_lt_of_le hjz (min_le_left _ _))⟩
  · rintro ⟨K, hK, hlt⟩
    have hK₀ : H.slot m = some K := hK
    have hKc := ((slot_eq_some_iff hH).1 hK₀).1
    obtain ⟨y, hyK, hy⟩ := (Metric.infDist_lt_iff K.nonempty).1 hlt
    have hzK : z ∈ (K : Set Plane) := by
      refine hnear K hKc ⟨y, hyK, ?_⟩
      rw [Metric.mem_closedBall]
      have h1 : dist y z ≤ dist y (Code.rationalPoint j) + dist (Code.rationalPoint j) z :=
        dist_triangle _ _ _
      have h2 : dist y (Code.rationalPoint j) < δ / 2 := by
        rw [dist_comm]
        linarith
      have h3 : dist (Code.rationalPoint j) z < δ / 2 := lt_of_lt_of_le hjz (min_le_right _ _)
      linarith
    have hmem : m ∈ (S : Set ℕ) := by
      rw [hS]
      exact ⟨K, hK₀, hzK⟩
    exact hm hmem

/-- A nonempty label set passing the rational-point test is the label set of a point. -/
theorem exists_coe_eq_labelsAt_of_pointSetOccurs (hH : H.IsCellConfiguration) {S : Finset ℕ}
    (hne : S.Nonempty) (hS : PointSetOccurs H.code S) :
    ∃ z : Plane, (S : Set ℕ) = H.labelsAt z := by
  obtain ⟨e, he⟩ := hS
  choose j hjnear hjfar using he
  obtain ⟨n₀, hn₀⟩ := hne
  obtain ⟨K₀, hK₀, -⟩ := hjnear 0 n₀ hn₀
  have hxK₀ : ∀ k, Code.rationalPoint (j k) ∈ Metric.cthickening 1 (K₀ : Set Plane) := by
    intro k
    obtain ⟨K, hK, hlt⟩ := hjnear k n₀ hn₀
    have hKK : K = K₀ := Option.some_inj.1 (hK.symm.trans hK₀)
    subst hKK
    obtain ⟨y, hyK, hy⟩ := (Metric.infDist_lt_iff K.nonempty).1 hlt
    refine Metric.mem_cthickening_of_dist_le _ y 1 _ hyK ?_
    have hle : 1 / ((k : ℝ) + 1) ≤ 1 := by
      rw [div_le_one (by positivity)]
      linarith [(Nat.cast_nonneg k : (0 : ℝ) ≤ k)]
    linarith
  obtain ⟨z, -, φ, hφ, hlim⟩ := (K₀.isCompact.cthickening (r := 1)).tendsto_subseq hxK₀
  refine ⟨z, Set.ext fun n => ⟨fun hn => ?_, fun hn => ?_⟩⟩
  · obtain ⟨K, hK, -⟩ := hjnear 0 n hn
    refine ⟨K, hK, ?_⟩
    have hdist : ∀ k, Metric.infDist (Code.rationalPoint (j k)) (K : Set Plane) <
        1 / ((k : ℝ) + 1) := by
      intro k
      obtain ⟨K', hK', hlt⟩ := hjnear k n hn
      have hKK : K' = K := Option.some_inj.1 (hK'.symm.trans hK)
      rw [← hKK]
      exact hlt
    have h1 : Tendsto (fun i => Metric.infDist (Code.rationalPoint (j (φ i))) (K : Set Plane))
        atTop (𝓝 (Metric.infDist z (K : Set Plane))) :=
      ((Metric.continuous_infDist_pt (K : Set Plane)).tendsto z).comp hlim
    have h2 : Tendsto (fun i => 1 / ((φ i : ℝ) + 1)) atTop (𝓝 0) :=
      tendsto_one_div_add_atTop_nhds_zero_nat.comp hφ.tendsto_atTop
    have hle : Metric.infDist z (K : Set Plane) ≤ 0 :=
      le_of_tendsto_of_tendsto' h1 h2 fun i => (hdist (φ i)).le
    exact (K.isCompact.isClosed.mem_iff_infDist_zero K.nonempty).2
      (le_antisymm hle Metric.infDist_nonneg)
  · obtain ⟨K, hK, hzK⟩ := hn
    by_contra hnS
    have hpos : (0 : ℝ) < 1 / ((e : ℝ) + 1) := Nat.one_div_pos_of_nat
    obtain ⟨i, hi⟩ := (hlim.eventually (Metric.ball_mem_nhds z hpos)).exists
    exact hjfar (φ i) n hnS ⟨K, hK, lt_of_le_of_lt (Metric.infDist_le_dist_of_mem hzK)
      (Metric.mem_ball.1 hi)⟩

/-- **The code of a cell configuration is point-connected iff every point graph is connected.** -/
theorem code_mem_pointConnectedCodes_iff (hH : H.IsCellConfiguration) :
    H.code ∈ pointConnectedCodes ↔ ∀ z : Plane, (H.inducedGraph {z}).Connected := by
  constructor
  · intro h z
    have hfin := finite_labelsAt hH z
    have hS : ((hfin.toFinset : Finset ℕ) : Set ℕ) = H.labelsAt z := hfin.coe_toFinset
    have hne : hfin.toFinset.Nonempty := by
      rw [← Finset.coe_nonempty, hS]
      exact labelsAt_nonempty hH z
    have hc := h hfin.toFinset hne (pointSetOccurs_of_coe_eq_labelsAt hH hS)
    rw [hS] at hc
    exact (inducedGraph_singleton_connected_iff hH z).2 hc
  · intro h S hne hocc
    obtain ⟨z, hz⟩ := exists_coe_eq_labelsAt_of_pointSetOccurs hH hne hocc
    rw [hz]
    exact (inducedGraph_singleton_connected_iff hH z).1 (h z)

/-- **The code of a cell configuration is point-connected iff the configuration is connected along
lines.** -/
theorem code_mem_pointConnectedCodes_iff_lineConnected (hH : H.IsCellConfiguration) :
    H.code ∈ pointConnectedCodes ↔ H.LineConnected :=
  (code_mem_pointConnectedCodes_iff hH).trans (lineConnected_iff_forall_singleton hH).symm

end CellConfig

/-! ## Borel measurability on the GMS space -/

/-- The configurations connected along lines are exactly the preimage of the point-connected
codes under the coding map. -/
theorem setOf_lineConnected_eq_preimage :
    {H : GMSSpace | H.1.LineConnected} = codeMap ⁻¹' pointConnectedCodes := by
  ext H
  exact (CellConfig.code_mem_pointConnectedCodes_iff_lineConnected H.2).symm

/-- **Connectedness along lines is a Borel event for `d^CC`**, given the measurability of the coding
map (proved as `measurable_codeMap` in `GMS/CodeMeasurable.lean`). -/
theorem measurableSet_lineConnected_of_measurable_codeMap (hmeas : Measurable codeMap) :
    MeasurableSet {H : GMSSpace | H.1.LineConnected} := by
  rw [setOf_lineConnected_eq_preimage]
  exact hmeas measurableSet_pointConnectedCodes

/-- **Connectedness along lines is a Borel event for `d^CC`.** -/
theorem measurableSet_lineConnected : MeasurableSet {H : GMSSpace | H.1.LineConnected} :=
  measurableSet_lineConnected_of_measurable_codeMap measurable_codeMap

/-- **Connectedness along lines is a similarity-invariant event**: membership is unchanged by every
positive similarity `H ↦ C(H − u)`. -/
theorem mem_setOf_lineConnected_iff_of_isSimilar {s : ℝ} {u : Plane} {hs : 0 < s}
    {H H' : GMSSpace} (h : IsSimilar s u hs H H') :
    H ∈ {H : GMSSpace | H.1.LineConnected} ↔ H' ∈ {H : GMSSpace | H.1.LineConnected} :=
  lineConnected_iff_of_isSimilar h

end ReflectedGMS.GMS

assert_no_sorry ReflectedGMS.GMS.measurableSet_pointConnectedCodes
assert_no_sorry ReflectedGMS.GMS.CellConfig.code_mem_pointConnectedCodes_iff
assert_no_sorry ReflectedGMS.GMS.CellConfig.code_mem_pointConnectedCodes_iff_lineConnected
assert_no_sorry ReflectedGMS.GMS.setOf_lineConnected_eq_preimage
assert_no_sorry ReflectedGMS.GMS.measurableSet_lineConnected_of_measurable_codeMap
assert_no_sorry ReflectedGMS.GMS.measurableSet_lineConnected
assert_no_sorry ReflectedGMS.GMS.mem_setOf_lineConnected_iff_of_isSimilar

#print axioms ReflectedGMS.GMS.measurableSet_pointConnectedCodes
#print axioms ReflectedGMS.GMS.CellConfig.code_mem_pointConnectedCodes_iff
#print axioms ReflectedGMS.GMS.measurableSet_lineConnected_of_measurable_codeMap
#print axioms ReflectedGMS.GMS.measurableSet_lineConnected
#print axioms ReflectedGMS.GMS.mem_setOf_lineConnected_iff_of_isSimilar
