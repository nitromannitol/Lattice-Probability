/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.CONF.S3T39J3c at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.CONF.S3T39J3b

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# The canonical arcs of a curve and their Effros-measurability (DEC-120 §4, packet J3)

Level `L`: the cut points `t39jPt j Γ`, `j < L` valid (S3T39J2b), as one-point arcs (first
occurrence of each point), and the chain classes `t39jClass L Γ (t39jPt i Γ)` of the free labels
`i` (valid, not a cut point) whose class contains no earlier free label (`t39jNew`).
The level used for `m` arcs is the largest `L ≤ m` for which every class of a free label contains a
free label `< m` (`t39jQ`, `t39jLev`, a `Γ`-dependent level).

* `t39jArcL L i Γ`, `t39jArcs m i Γ := t39jArcL (t39jLev m Γ) i Γ`;
* **`t39j_arcs_meas`**: the hit events `{Γ | (t39jArcs m i Γ ∩ U).Nonempty}` are
  Effros-measurable (`t39j_class_hit_meas`, `t39j_rc_meas`, `t39jPt_meas`);
* `t39j_arcs_subset`: `t39jArcs m i Γ ⊆ closure Γ`.

CONF C:1740–1744 (DV-D120-1: the arcs of equal harmonic measure are replaced by this canonical
subdivision; the proof uses only covering and eventual separation). Own construction.
-/

noncomputable section

open MeasureTheory Set Metric Filter Topology

namespace LQGMetric.CONF

attribute [local instance 2000] effrosSigma

/-- the label `j` is free at level `L`: valid and not a cut point -/
def t39jFree (L j : ℕ) (Γ : Set ℂ) : Prop := t39jValid j Γ ∧ t39jPt j Γ ∉ t39jCut L Γ

/-- every class of a free label contains a free label `< m` -/
def t39jQ (L m : ℕ) (Γ : Set ℂ) : Prop :=
  ∀ j, t39jFree L j Γ → ∃ i < m, t39jFree L i Γ ∧ t39jRC L Γ (t39jPt i Γ) (t39jPt j Γ)

open Classical in
/-- the level of the `m`-th family -/
def t39jLev (m : ℕ) (Γ : Set ℂ) : ℕ := Nat.findGreatest (fun L => t39jQ L m Γ) m

/-- `i` is the first label of its point -/
def t39jFirst (i : ℕ) (Γ : Set ℂ) : Prop := ∀ i' < i, t39jValid i' Γ → t39jPt i' Γ ≠ t39jPt i Γ

/-- `i` is free and its class contains no earlier free label -/
def t39jNew (L i : ℕ) (Γ : Set ℂ) : Prop :=
  t39jFree L i Γ ∧ ∀ i' < i, ¬ (t39jFree L i' Γ ∧ t39jRC L Γ (t39jPt i' Γ) (t39jPt i Γ))

open Classical in
/-- the `i`-th arc of level `L` -/
def t39jArcL (L i : ℕ) (Γ : Set ℂ) : Set ℂ :=
  if i < L ∧ t39jValid i Γ ∧ t39jFirst i Γ then {t39jPt i Γ}
  else if t39jNew L i Γ then t39jClass L Γ (t39jPt i Γ) else ∅

/-- **the canonical arcs** -/
def t39jArcs (m : ℕ) (i : Fin m) (Γ : Set ℂ) : Set ℂ := t39jArcL (t39jLev m Γ) i Γ

/-! ### measurability -/

theorem t39j_ne_meas (i j : ℕ) :
    MeasurableSet[effrosSigma] {Γ | t39jPt i Γ ≠ t39jPt j Γ} := by
  have : {Γ | t39jPt i Γ ≠ t39jPt j Γ} = {Γ | 0 < dist (t39jPt i Γ) (t39jPt j Γ)} := by
    ext Γ; simp only [mem_setOf_eq, dist_pos]
  rw [this]; exact measurableSet_lt measurable_const ((t39jPt_meas i).dist (t39jPt_meas j))

theorem t39j_free_meas (L j : ℕ) : MeasurableSet[effrosSigma] {Γ | t39jFree L j Γ} := by
  have : {Γ | t39jFree L j Γ} = {Γ | t39jValid j Γ} ∩
      {Γ | ∀ p ∈ t39jCut L Γ, (0 : ℝ) < dist (t39jPt j Γ) p} := by
    ext Γ
    simp only [t39jFree, mem_setOf_eq, mem_inter_iff, dist_pos, and_congr_right_iff]
    exact fun _ => ⟨fun h p hp hpe => h (hpe ▸ hp), fun h hp => h _ hp rfl⟩
  rw [this]; exact (t39jValid_meas j).inter (t39j_cutAvoid_meas L 0 (t39jPt_meas j))

theorem t39j_freeRC_meas (L i j : ℕ) : MeasurableSet[effrosSigma]
    {Γ | t39jFree L i Γ ∧ t39jRC L Γ (t39jPt i Γ) (t39jPt j Γ)} :=
  (t39j_free_meas L i).inter (t39j_rc_meas L (t39jPt_meas i) (t39jPt_meas j))

theorem t39j_Q_meas (L m : ℕ) : MeasurableSet[effrosSigma] {Γ | t39jQ L m Γ} := by
  have : {Γ | t39jQ L m Γ} = ⋂ j, ({Γ | t39jFree L j Γ}ᶜ ∪ ⋃ i ∈ Finset.range m,
      {Γ | t39jFree L i Γ ∧ t39jRC L Γ (t39jPt i Γ) (t39jPt j Γ)}) := by
    ext Γ
    simp only [t39jQ, mem_setOf_eq, mem_iInter, mem_union, mem_compl_iff, mem_iUnion,
      Finset.mem_range, exists_prop]
    exact forall_congr' fun j => imp_iff_not_or
  rw [this]
  exact MeasurableSet.iInter fun j => (t39j_free_meas L j).compl.union
    (Finset.measurableSet_biUnion _ fun i _ => t39j_freeRC_meas L i j)

open Classical in
theorem t39j_findGreatest_meas (Pr : ℕ → Set ℂ → Prop)
    (hPr : ∀ L, MeasurableSet[effrosSigma] {Γ | Pr L Γ}) (k : ℕ) :
    Measurable[effrosSigma] fun Γ => Nat.findGreatest (fun L => Pr L Γ) k := by
  induction k with
  | zero => simp
  | succ k ih =>
    simp only [Nat.findGreatest_succ]
    exact Measurable.ite (hPr (k + 1)) measurable_const ih

theorem t39j_lev_meas (m : ℕ) : Measurable[effrosSigma] (t39jLev m) := by
  unfold t39jLev
  exact t39j_findGreatest_meas (fun L Γ => t39jQ L m Γ) (fun L => t39j_Q_meas L m) m

open Classical in
theorem t39j_lev_le (m : ℕ) (Γ : Set ℂ) : t39jLev m Γ ≤ m := by
  unfold t39jLev; exact Nat.findGreatest_le m

theorem t39j_first_meas (i : ℕ) : MeasurableSet[effrosSigma] {Γ | t39jFirst i Γ} := by
  have : {Γ | t39jFirst i Γ} = ⋂ i' ∈ Finset.range i,
      ({Γ | t39jValid i' Γ}ᶜ ∪ {Γ | t39jPt i' Γ ≠ t39jPt i Γ}) := by
    ext Γ
    simp only [t39jFirst, mem_setOf_eq, mem_iInter, mem_union, mem_compl_iff, Finset.mem_range]
    exact forall₂_congr fun _ _ => imp_iff_not_or
  rw [this]
  exact Finset.measurableSet_biInter _ fun i' _ => (t39jValid_meas i').compl.union
    (t39j_ne_meas i' i)

theorem t39j_new_meas (L i : ℕ) : MeasurableSet[effrosSigma] {Γ | t39jNew L i Γ} := by
  have : {Γ | t39jNew L i Γ} = {Γ | t39jFree L i Γ} ∩ ⋂ i' ∈ Finset.range i,
      {Γ | t39jFree L i' Γ ∧ t39jRC L Γ (t39jPt i' Γ) (t39jPt i Γ)}ᶜ := by
    ext Γ
    simp only [t39jNew, mem_setOf_eq, mem_inter_iff, mem_iInter, mem_compl_iff,
      Finset.mem_range]
  rw [this]
  exact (t39j_free_meas L i).inter
    (Finset.measurableSet_biInter _ fun i' _ => (t39j_freeRC_meas L i' i).compl)

theorem t39j_arcL_meas (L i : ℕ) {U : Set ℂ} (hU : IsOpen U) :
    MeasurableSet[effrosSigma] {Γ | (t39jArcL L i Γ ∩ U).Nonempty} := by
  classical
  set S1 := {Γ : Set ℂ | i < L ∧ t39jValid i Γ ∧ t39jFirst i Γ}
  have hS1 : MeasurableSet[effrosSigma] S1 :=
    (MeasurableSet.const (i < L)).inter ((t39jValid_meas i).inter (t39j_first_meas i))
  have : {Γ | (t39jArcL L i Γ ∩ U).Nonempty} = (S1 ∩ {Γ | t39jPt i Γ ∈ U}) ∪
      (S1ᶜ ∩ {Γ | t39jNew L i Γ} ∩ {Γ | (t39jClass L Γ (t39jPt i Γ) ∩ U).Nonempty}) := by
    ext Γ
    by_cases h1 : Γ ∈ S1
    · have h1' : i < L ∧ t39jValid i Γ ∧ t39jFirst i Γ := h1
      simp [t39jArcL, h1', h1]
    · have h1' : ¬ (i < L ∧ t39jValid i Γ ∧ t39jFirst i Γ) := h1
      by_cases h2 : t39jNew L i Γ
      · simp [t39jArcL, h1', h1, h2]
      · simp [t39jArcL, h1', h1, h2]
  rw [this]
  exact (hS1.inter (t39jPt_meas i hU.measurableSet)).union ((hS1.compl.inter (t39j_new_meas L i)).inter
    (t39j_class_hit_meas L (t39jPt_meas i) hU))

/-- **the hit events of the canonical arcs are Effros-measurable** -/
theorem t39j_arcs_meas (m : ℕ) (i : Fin m) {U : Set ℂ} (hU : IsOpen U) :
    MeasurableSet[effrosSigma] {Γ | (t39jArcs m i Γ ∩ U).Nonempty} := by
  have : {Γ | (t39jArcs m i Γ ∩ U).Nonempty} = ⋃ L ∈ Finset.range (m + 1),
      (t39jLev m ⁻¹' {L} ∩ {Γ | (t39jArcL L i Γ ∩ U).Nonempty}) := by
    ext Γ
    simp only [t39jArcs, mem_setOf_eq, mem_iUnion, mem_inter_iff, mem_preimage,
      mem_singleton_iff, Finset.mem_range, exists_prop]
    constructor
    · intro h; exact ⟨_, Nat.lt_succ_of_le (t39j_lev_le m Γ), rfl, h⟩
    · rintro ⟨L, -, hL, h⟩; rw [hL]; exact h
  rw [this]
  exact Finset.measurableSet_biUnion _ fun L _ =>
    ((t39j_lev_meas m) (measurableSet_singleton L)).inter (t39j_arcL_meas L i hU)

theorem t39j_arcL_subset (L i : ℕ) (Γ : Set ℂ) : t39jArcL L i Γ ⊆ closure Γ := by
  unfold t39jArcL
  split_ifs with h1 h2
  · exact singleton_subset_iff.2 (t39jPt_mem h1.2.1).1
  · exact fun z hz => hz.1
  · exact empty_subset _

theorem t39j_arcs_subset (m : ℕ) (i : Fin m) (Γ : Set ℂ) : t39jArcs m i Γ ⊆ closure Γ :=
  t39j_arcL_subset _ _ _

end LQGMetric.CONF
