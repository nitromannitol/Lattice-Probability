/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module ReflectedGMS.GeomTop.ValidGeneralBorelLocal at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.ReflectedGMS.GeomTop.ValidGeneralBorelStar
import LatticeProb.Bonanno.ReflectedGMS.GMS.ValidCodeSet
import LatticeProb.Bonanno.ReflectedGMS.Environment.GeneralLaws
import Mathlib.Util.AssertNoSorry

/-!
# Absence of singular points on an open set is a Borel condition on codes

For a raw code `r` with admissible conductances, write `C = rawConfig r h`.  For an **open** set
`O ⊆ ℂ`, the statement "no point of `O` is an accumulation, uncovered or bad point of `C`"
(`ValidBorel.accSet`, `uncSet`, `badSet`) is equivalent to a countable Boolean combination of Borel
conditions on the slot and conductance coordinates (`goodOn_iff`, `measurable_goodOn`):

* `LocFinOn` — every closed rational ball inside `O` is met by only finitely many slots
  (compactness of the ball for one direction; a rational ball around a point for the other);
* `CoverOn` — every rational point of `O` lies in an active slot cell (given local finiteness the
  union of the cells is relatively closed in `O`, `mem_iUnion_cell_of_notMem_accSet`);
* `PointConnOn` — every finite label set that is the label set of a point of `O`
  (`PointSetOccursIn`, tested along rational points of a fixed closed rational ball inside `O`, with
  a uniform margin from all other cells) induces a connected subgraph of the code graph.  This adapts
  `GMS.pointConnectedCodes` (`GMS/LineConnectedMeasurable.lean`) to points of a region; the point
  graph `H({z})` is the code graph on the labels through `z` (`pointLabelIso`).
-/

set_option autoImplicit false

open MeasureTheory Set Filter Topology Metric

namespace ReflectedGMS.GeomTop.ValidBorel

open Code GMS GMS.ValidCodeSet

/-! ## Vertices and slots -/

theorem slot_eq_some_cell (r : RawCode) (v : Vertex r) : r.1 v.val = some (Code.cell r v) :=
  (Option.some_get v.property).symm

theorem slotCell_val (r : RawCode) (v : Vertex r) : slotCell r v.val = Code.cell r v :=
  slotCell_of_eq_some (slot_eq_some_cell r v)

theorem slotCell_eq_cell (r : RawCode) {n : ℕ} (hn : (r.1 n).isSome) :
    slotCell r n = Code.cell r ⟨n, hn⟩ :=
  slotCell_val r ⟨n, hn⟩

theorem cell_mk_of_eq_some {r : RawCode} {n : ℕ} {K : CompactCell} (h : r.1 n = some K) :
    Code.cell r ⟨n, isSome_of_eq_some h⟩ = K :=
  Option.some_inj.1 ((slot_eq_some_cell r ⟨n, isSome_of_eq_some h⟩).symm.trans h)

theorem slotNear_iff_hits {r : RawCode} (h : RawAdmissible r) (q : Plane) (t : ℝ)
    (v : Vertex r) : SlotNear q t (r.1 v.val) ↔ (rawConfig r h).Hits (ball q t) v := by
  rw [slot_eq_some_cell r v]
  constructor
  · rintro ⟨K, hK, hlt⟩
    obtain ⟨y, hyK, hy⟩ := (infDist_lt_iff K.nonempty).1 hlt
    have hKK : Code.cell r v = K := Option.some_inj.1 hK
    have hyv : y ∈ (Code.cell r v : Set Plane) := by
      rw [hKK]
      exact hyK
    refine ⟨y, hyv, ?_⟩
    rw [mem_ball, dist_comm]
    exact hy
  · rintro ⟨y, hyK, hy⟩
    refine ⟨Code.cell r v, rfl, ?_⟩
    exact lt_of_le_of_lt (infDist_le_dist_of_mem hyK) (by rw [dist_comm]; exact mem_ball.1 hy)

/-- A rational open ball around a point of an open set whose closure stays in the set. -/
theorem exists_ratBall_mem_subset {O : Set Plane} (hO : IsOpen O) {z : Plane} (hz : z ∈ O) :
    ∃ (j : ℕ) (ρ : ℚ), z ∈ ball (rationalPoint j) (ρ : ℝ) ∧
      closedBall (rationalPoint j) (ρ : ℝ) ⊆ O := by
  obtain ⟨ε, hε, hεO⟩ := Metric.isOpen_iff.mp hO z hz
  obtain ⟨j, hj⟩ := exists_rationalPoint_mem (isOpen_ball (x := z) (ε := ε / 3))
    (nonempty_ball.2 (by linarith))
  obtain ⟨ρ, hρ1, hρ2⟩ := exists_rat_btwn (show ε / 3 < 2 * ε / 3 by linarith)
  have hjz : dist (rationalPoint j) z < ε / 3 := mem_ball.1 hj
  refine ⟨j, ρ, ?_, fun y hy => hεO ?_⟩
  · rw [mem_ball, dist_comm]
    linarith
  · rw [mem_ball]
    have hy' := mem_closedBall.1 hy
    calc dist y z ≤ dist y (rationalPoint j) + dist (rationalPoint j) z := dist_triangle _ _ _
      _ < ε := by linarith

/-! ## Local finiteness -/

/-- Every closed rational ball inside `O` meets only finitely many slots. -/
def LocFinOn (r : RawCode) (O : Set Plane) : Prop :=
  ∀ (j : ℕ) (ρ : ℚ), closedBall (rationalPoint j) (ρ : ℝ) ⊆ O →
    ∃ M : ℕ, ∀ m, M ≤ m → ¬ SlotNear (rationalPoint j) (ρ : ℝ) (r.1 m)

theorem locFinOn_iff {r : RawCode} (h : RawAdmissible r) {O : Set Plane} (hO : IsOpen O) :
    LocFinOn r O ↔ ∀ z ∈ O, z ∉ accSet (rawConfig r h) := by
  constructor
  · intro hloc z hz hacc
    obtain ⟨j, ρ, hzj, hjO⟩ := exists_ratBall_mem_subset hO hz
    obtain ⟨M, hM⟩ := hloc j ρ hjO
    apply hacc
    refine ⟨ball (rationalPoint j) (ρ : ℝ), isOpen_ball.mem_nhds hzj, ?_⟩
    refine ((Set.finite_Iio M).preimage Subtype.val_injective.injOn).subset fun v hv => ?_
    show v.val < M
    by_contra hvM
    exact hM v.val (not_lt.1 hvM) ((slotNear_iff_hits h _ _ v).2 hv)
  · intro hgood j ρ hjO
    have hfin := finite_hits_of_isCompact (C := rawConfig r h) (isCompact_closedBall _ _)
      fun z hz => hgood z (hjO hz)
    obtain ⟨B, hB⟩ := (hfin.image Subtype.val).bddAbove
    refine ⟨B + 1, fun m hm hnear => ?_⟩
    obtain ⟨K, hK, hlt⟩ := hnear
    have hv : (rawConfig r h).Hits (closedBall (rationalPoint j) (ρ : ℝ))
        ⟨m, isSome_of_eq_some hK⟩ := by
      have h1 := (slotNear_iff_hits h (rationalPoint j) (ρ : ℝ) ⟨m, isSome_of_eq_some hK⟩).1
        ⟨K, hK, hlt⟩
      obtain ⟨y, hy1, hy2⟩ := h1
      exact ⟨y, hy1, ball_subset_closedBall hy2⟩
    have hle : m ≤ B := hB ⟨_, hv, rfl⟩
    omega

/-! ## Coverage -/

/-- Every rational point of `O` lies in an active slot cell. -/
def CoverOn (r : RawCode) (O : Set Plane) : Prop :=
  ∀ j : ℕ, rationalPoint j ∈ O → ∃ n, (r.1 n).isSome ∧ rationalPoint j ∈ (slotCell r n : Set Plane)

theorem coverOn_iff {r : RawCode} (h : RawAdmissible r) {O : Set Plane} (hO : IsOpen O)
    (hacc : ∀ z ∈ O, z ∉ accSet (rawConfig r h)) :
    CoverOn r O ↔ ∀ z ∈ O, z ∉ uncSet (rawConfig r h) := by
  constructor
  · intro hcov z hz hunc
    refine hunc (mem_iUnion_cell_of_notMem_accSet (hacc z hz) fun W hW => ?_)
    have hWO : W ∩ O ∈ 𝓝 z := Filter.inter_mem hW (hO.mem_nhds hz)
    obtain ⟨ε, hε, hεW⟩ := Metric.mem_nhds_iff.1 hWO
    obtain ⟨j, hj⟩ := exists_rationalPoint_mem (isOpen_ball (x := z) (ε := ε))
      (nonempty_ball.2 hε)
    obtain ⟨n, hn, hjn⟩ := hcov j (hεW hj).2
    have hc : slotCell r n = Code.cell r ⟨n, hn⟩ := slotCell_eq_cell r hn
    rw [hc] at hjn
    exact ⟨⟨n, hn⟩, rationalPoint j, hjn, (hεW hj).1⟩
  · intro hgood j hj
    have hj' : rationalPoint j ∈ ⋃ v, ((rawConfig r h).cell v : Set Plane) := by
      by_contra hne
      exact hgood _ hj hne
    obtain ⟨v, hv⟩ := mem_iUnion.1 hj'
    refine ⟨v.val, v.property, ?_⟩
    rw [slotCell_val]
    exact hv

/-! ## Point connectivity -/

/-- The labels of the active slots whose cells contain `z`. -/
def labelsAtCode (r : RawCode) (z : Plane) : Set ℕ :=
  {n | ∃ K : CompactCell, r.1 n = some K ∧ z ∈ (K : Set Plane)}

/-- **The finite label set `S` is the label set of a point of `O`**, tested along the rational
points of a fixed closed rational ball inside `O`: for a margin `1/(e+1)` and every precision
`1/(k+1)` some rational point of the ball is within `1/(k+1)` of every cell labelled in `S` and at
distance at least `1/(e+1)` from every other slot cell. -/
def PointSetOccursIn (r : RawCode) (O : Set Plane) (S : Finset ℕ) : Prop :=
  ∃ (j : ℕ) (ρ : ℚ), closedBall (rationalPoint j) (ρ : ℝ) ⊆ O ∧ ∃ e : ℕ, ∀ k : ℕ, ∃ i : ℕ,
    rationalPoint i ∈ closedBall (rationalPoint j) (ρ : ℝ) ∧
      (∀ n ∈ S, SlotNear (rationalPoint i) (1 / ((k : ℝ) + 1)) (r.1 n)) ∧
      ∀ m, m ∉ S → ¬ SlotNear (rationalPoint i) (1 / ((e : ℝ) + 1)) (r.1 m)

/-- Every nonempty label set of a point of `O` induces a connected subgraph of the code graph. -/
def PointConnOn (r : RawCode) (O : Set Plane) : Prop :=
  ∀ S : Finset ℕ, S.Nonempty → PointSetOccursIn r O S →
    ((codeGraph r).induce (S : Set ℕ)).Connected

/-- A label set passing the test is the label set of a point of `O` (the rational test points
accumulate in the compact ball). -/
theorem exists_eq_labelsAtCode_of_pointSetOccursIn {r : RawCode} {O : Set Plane} {S : Finset ℕ}
    (hS : PointSetOccursIn r O S) : ∃ z ∈ O, (S : Set ℕ) = labelsAtCode r z := by
  obtain ⟨j, ρ, hjO, e, he⟩ := hS
  choose i hiB hinear hifar using he
  obtain ⟨z, hzB, φ, hφ, hlim⟩ :=
    (isCompact_closedBall (rationalPoint j) (ρ : ℝ)).tendsto_subseq hiB
  refine ⟨z, hjO hzB, Set.ext fun n => ⟨fun hn => ?_, fun hn => ?_⟩⟩
  · obtain ⟨K, hK, -⟩ := hinear 0 n hn
    refine ⟨K, hK, ?_⟩
    have hdist : ∀ k, infDist (rationalPoint (i k)) (K : Set Plane) < 1 / ((k : ℝ) + 1) := by
      intro k
      obtain ⟨K', hK', hlt⟩ := hinear k n hn
      have hKK : K' = K := Option.some_inj.1 (hK'.symm.trans hK)
      rw [← hKK]
      exact hlt
    have h1 : Tendsto (fun k => infDist (rationalPoint (i (φ k))) (K : Set Plane)) atTop
        (𝓝 (infDist z (K : Set Plane))) :=
      ((continuous_infDist_pt (K : Set Plane)).tendsto z).comp hlim
    have h2 : Tendsto (fun k => 1 / ((φ k : ℝ) + 1)) atTop (𝓝 0) :=
      tendsto_one_div_add_atTop_nhds_zero_nat.comp hφ.tendsto_atTop
    have hle : infDist z (K : Set Plane) ≤ 0 :=
      le_of_tendsto_of_tendsto' h1 h2 fun k => (hdist (φ k)).le
    exact (K.isCompact.isClosed.mem_iff_infDist_zero K.nonempty).2
      (le_antisymm hle infDist_nonneg)
  · obtain ⟨K, hK, hzK⟩ := hn
    by_contra hnS
    have hpos : (0 : ℝ) < 1 / ((e : ℝ) + 1) := Nat.one_div_pos_of_nat
    obtain ⟨k, hk⟩ := (hlim.eventually (ball_mem_nhds z hpos)).exists
    exact hifar (φ k) n hnS ⟨K, hK, lt_of_le_of_lt (infDist_le_dist_of_mem hzK) (mem_ball.1 hk)⟩

/-- At a non-accumulation point of `O` the label set is finite and passes the test. -/
theorem finite_labelsAtCode_and_occurs {r : RawCode} (h : RawAdmissible r) {O : Set Plane}
    (hO : IsOpen O) {z : Plane} (hzO : z ∈ O) (hz : z ∉ accSet (rawConfig r h)) :
    (labelsAtCode r z).Finite ∧
      ∀ S : Finset ℕ, (S : Set ℕ) = labelsAtCode r z → PointSetOccursIn r O S := by
  refine ⟨?_, fun S hS => ?_⟩
  · have hz' : ∃ U ∈ 𝓝 z, {v | (rawConfig r h).Hits U v}.Finite := not_not.1 hz
    obtain ⟨U, hU, hfin⟩ := hz'
    refine (hfin.image Subtype.val).subset ?_
    rintro n ⟨K, hK, hzK⟩
    refine ⟨⟨n, isSome_of_eq_some hK⟩, ⟨z, ?_, mem_of_mem_nhds hU⟩, rfl⟩
    show z ∈ (Code.cell r ⟨n, isSome_of_eq_some hK⟩ : Set Plane)
    rw [cell_mk_of_eq_some hK]
    exact hzK
  · obtain ⟨δ, hδ, hnear⟩ := exists_pos_closedBall_hits_imp_mem hz
    obtain ⟨j, ρ, hzj, hjO⟩ := exists_ratBall_mem_subset hO hzO
    have hτ : 0 < (ρ : ℝ) - dist z (rationalPoint j) := by
      have := mem_ball.1 hzj
      linarith
    obtain ⟨e, he⟩ := exists_nat_one_div_lt (half_pos hδ)
    refine ⟨j, ρ, hjO, e, fun k => ?_⟩
    have hk : (0 : ℝ) < 1 / ((k : ℝ) + 1) := Nat.one_div_pos_of_nat
    obtain ⟨i, hi⟩ := exists_rationalPoint_mem
      (isOpen_ball (x := z) (ε := min (1 / ((k : ℝ) + 1)) (min (δ / 2)
        ((ρ : ℝ) - dist z (rationalPoint j)))))
      (nonempty_ball.2 (lt_min hk (lt_min (half_pos hδ) hτ)))
    have hiz : dist (rationalPoint i) z < min (1 / ((k : ℝ) + 1)) (min (δ / 2)
        ((ρ : ℝ) - dist z (rationalPoint j))) := mem_ball.1 hi
    have hiz1 : dist (rationalPoint i) z < 1 / ((k : ℝ) + 1) :=
      lt_of_lt_of_le hiz (min_le_left _ _)
    have hiz2 : dist (rationalPoint i) z < δ / 2 :=
      lt_of_lt_of_le hiz (le_trans (min_le_right _ _) (min_le_left _ _))
    have hiz3 : dist (rationalPoint i) z < (ρ : ℝ) - dist z (rationalPoint j) :=
      lt_of_lt_of_le hiz (le_trans (min_le_right _ _) (min_le_right _ _))
    refine ⟨i, ?_, fun n hn => ?_, fun m hm => ?_⟩
    · rw [mem_closedBall]
      have := dist_triangle (rationalPoint i) z (rationalPoint j)
      linarith
    · have hn' : n ∈ labelsAtCode r z := by
        rw [← hS]
        exact hn
      obtain ⟨K, hK, hzK⟩ := hn'
      exact ⟨K, hK, lt_of_le_of_lt (infDist_le_dist_of_mem hzK) hiz1⟩
    · rintro ⟨K, hK, hlt⟩
      obtain ⟨y, hyK, hy⟩ := (infDist_lt_iff K.nonempty).1 hlt
      have hyz : dist y z ≤ δ := by
        have h1 := dist_triangle y (rationalPoint i) z
        rw [dist_comm] at hy
        linarith
      have hyv : y ∈ (Code.cell r ⟨m, isSome_of_eq_some hK⟩ : Set Plane) := by
        rw [cell_mk_of_eq_some hK]
        exact hyK
      have hzv := hnear ⟨m, isSome_of_eq_some hK⟩ ⟨y, hyv, mem_closedBall.2 hyz⟩
      have hzK : z ∈ (K : Set Plane) := by
        have hc : ((rawConfig r h).cell ⟨m, isSome_of_eq_some hK⟩ : Set Plane) = K := by
          show ((Code.cell r ⟨m, isSome_of_eq_some hK⟩ : CompactCell) : Set Plane) = K
          rw [cell_mk_of_eq_some hK]
        rw [hc] at hzv
        exact hzv
      have hmS : m ∈ (S : Set ℕ) := by
        rw [hS]
        exact ⟨K, hK, hzK⟩
      exact hm hmS

/-- **The point graph `H({z})` of the configuration of an admissible code is the code graph on the
labels through `z`.** -/
noncomputable def pointLabelIso {r : RawCode} (h : RawAdmissible r) (z : Plane) :
    (rawConfig r h).graph.induce {v | (rawConfig r h).Hits {z} v} ≃g
      (codeGraph r).induce (labelsAtCode r z) where
  toEquiv :=
    { toFun := fun v => ⟨v.1.val, Code.cell r v.1, slot_eq_some_cell r v.1,
        Set.inter_singleton_nonempty.1 v.2⟩
      invFun := fun n => ⟨⟨n.1, isSome_of_eq_some n.2.choose_spec.1⟩,
        Set.inter_singleton_nonempty.2 (by
          show z ∈ (Code.cell r ⟨n.1, isSome_of_eq_some n.2.choose_spec.1⟩ : Set Plane)
          rw [cell_mk_of_eq_some n.2.choose_spec.1]
          exact n.2.choose_spec.2)⟩
      left_inv := fun v => Subtype.ext (Subtype.ext rfl)
      right_inv := fun n => Subtype.ext rfl }
  map_rel_iff' {v w} := by
    show (codeGraph r).Adj v.1.val w.1.val ↔ 0 < r.2 v.1.val w.1.val
    constructor
    · rintro ⟨-, hpos, -⟩
      exact hpos
    · intro hpos
      refine ⟨fun heq => ?_, hpos, by rw [h.symm]; exact hpos⟩
      rw [heq, h.self] at hpos
      exact lt_irrefl _ hpos

theorem pointConnOn_iff {r : RawCode} (h : RawAdmissible r) {O : Set Plane} (hO : IsOpen O)
    (hacc : ∀ z ∈ O, z ∉ accSet (rawConfig r h)) :
    PointConnOn r O ↔ ∀ z ∈ O, z ∉ badSet (rawConfig r h) := by
  constructor
  · intro hpc z hz hbad
    apply hbad
    obtain ⟨hfin, hocc⟩ := finite_labelsAtCode_and_occurs h hO hz (hacc z hz)
    have hcode : ((codeGraph r).induce (labelsAtCode r z)).Preconnected := by
      by_cases hne : (labelsAtCode r z).Nonempty
      · have hS : ((hfin.toFinset : Finset ℕ) : Set ℕ) = labelsAtCode r z := hfin.coe_toFinset
        have hc := hpc hfin.toFinset (by rw [← Finset.coe_nonempty, hS]; exact hne) (hocc _ hS)
        rw [hS] at hc
        exact hc.preconnected
      · intro a
        exact absurd ⟨a.1, a.2⟩ hne
    exact (pointLabelIso h z).preconnected_iff.2 hcode
  · intro hgood S hne hocc
    obtain ⟨z, hzO, hz⟩ := exists_eq_labelsAtCode_of_pointSetOccursIn hocc
    have hpt : (rawConfig r h).InducedConnected {z} := by
      by_contra hb
      exact hgood z hzO hb
    have hpre : ((codeGraph r).induce (labelsAtCode r z)).Preconnected :=
      (pointLabelIso h z).preconnected_iff.1 hpt
    rw [← hz] at hpre
    obtain ⟨n, hn⟩ := hne
    haveI : Nonempty (S : Set ℕ) := ⟨⟨n, Finset.mem_coe.2 hn⟩⟩
    exact (SimpleGraph.connected_iff _).2 ⟨hpre, inferInstance⟩

/-! ## The combined condition -/

/-- **No accumulation, uncovered or bad point in `O`**, as Borel conditions on the code. -/
def GoodOn (r : RawCode) (O : Set Plane) : Prop :=
  LocFinOn r O ∧ CoverOn r O ∧ PointConnOn r O

theorem goodOn_iff {r : RawCode} (h : RawAdmissible r) {O : Set Plane} (hO : IsOpen O) :
    GoodOn r O ↔ ∀ z ∈ O,
      z ∉ accSet (rawConfig r h) ∪ uncSet (rawConfig r h) ∪ badSet (rawConfig r h) := by
  constructor
  · rintro ⟨hl, hc, hp⟩ z hz hzA
    have hacc := (locFinOn_iff h hO).1 hl
    rcases hzA with (ha | hu) | hb
    · exact hacc z hz ha
    · exact (coverOn_iff h hO hacc).1 hc z hz hu
    · exact (pointConnOn_iff h hO hacc).1 hp z hz hb
  · intro hg
    have hacc : ∀ z ∈ O, z ∉ accSet (rawConfig r h) := fun z hz ha =>
      hg z hz (Or.inl (Or.inl ha))
    exact ⟨(locFinOn_iff h hO).2 hacc,
      (coverOn_iff h hO hacc).2 fun z hz hu => hg z hz (Or.inl (Or.inr hu)),
      (pointConnOn_iff h hO hacc).2 fun z hz hb => hg z hz (Or.inr hb)⟩

/-! ## Measurability -/

theorem measurable_locFinOn (O : Set Plane) : Measurable fun r : RawCode => LocFinOn r O :=
  Measurable.forall fun _ => Measurable.forall fun _ => measurable_const.imp
    (Measurable.exists fun _ => Measurable.forall fun m => measurable_const.imp
      (measurable_slotNear _ _ m).not)

theorem measurable_coverOn (O : Set Plane) : Measurable fun r : RawCode => CoverOn r O :=
  Measurable.forall fun _ => measurable_const.imp (Measurable.exists fun n =>
    (measurable_isSome n).and (measurable_mem_slotCell _ n))

theorem measurable_pointSetOccursIn (O : Set Plane) (S : Finset ℕ) :
    Measurable fun r : RawCode => PointSetOccursIn r O S :=
  Measurable.exists fun _ => Measurable.exists fun _ => measurable_const.and
    (Measurable.exists fun _ => Measurable.forall fun _ => Measurable.exists fun _ =>
      measurable_const.and
        ((Measurable.forall fun n => measurable_const.imp (measurable_slotNear _ _ n)).and
          (Measurable.forall fun m => measurable_const.imp (measurable_slotNear _ _ m).not)))

theorem measurable_pointConnOn (O : Set Plane) : Measurable fun r : RawCode => PointConnOn r O :=
  Measurable.forall fun S => measurable_const.imp ((measurable_pointSetOccursIn O S).imp
    (measurable_induce_codeGraph_connected S))

/-- **`GoodOn r O` is a Borel condition on the code**, for every fixed set `O`. -/
theorem measurable_goodOn (O : Set Plane) : Measurable fun r : RawCode => GoodOn r O :=
  (measurable_locFinOn O).and ((measurable_coverOn O).and (measurable_pointConnOn O))

end ReflectedGMS.GeomTop.ValidBorel

assert_no_sorry ReflectedGMS.GeomTop.ValidBorel.locFinOn_iff
assert_no_sorry ReflectedGMS.GeomTop.ValidBorel.coverOn_iff
assert_no_sorry ReflectedGMS.GeomTop.ValidBorel.exists_eq_labelsAtCode_of_pointSetOccursIn
assert_no_sorry ReflectedGMS.GeomTop.ValidBorel.finite_labelsAtCode_and_occurs
assert_no_sorry ReflectedGMS.GeomTop.ValidBorel.pointLabelIso
assert_no_sorry ReflectedGMS.GeomTop.ValidBorel.pointConnOn_iff
assert_no_sorry ReflectedGMS.GeomTop.ValidBorel.goodOn_iff
assert_no_sorry ReflectedGMS.GeomTop.ValidBorel.measurable_goodOn

#print axioms ReflectedGMS.GeomTop.ValidBorel.goodOn_iff
#print axioms ReflectedGMS.GeomTop.ValidBorel.measurable_goodOn
