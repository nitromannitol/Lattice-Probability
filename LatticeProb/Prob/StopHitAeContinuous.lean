import Mathlib
import LatticeProb.Prob.StopHitContinuity

/-!
# Almost every level, almost every path: continuity of the stopped path at its first hit time

For a continuous path `w : C(ℝ≥0, ℝ)` and a level `c`, let `F_c(v) = stopAt (hitFrom c 0 v) v` be the path `v` stopped
at its first hit of `c`.  For a fixed path `w` the map `F_c` is continuous at `w` outside a countable set of levels
(`exists_countable_forall_continuousAt_stopAt_hitFrom`).  Here the exceptional levels are enclosed in a *measurable*
subset of `ℝ × C(ℝ≥0, ℝ)`: the starting value `c = w 0` together with the levels `c` which are the running maximum
(respectively minimum) of `w` over the rational times `< q`, `q ∈ ℚ`.  Fubini's theorem then gives continuity at almost
every path for almost every level.

## Main statements

* `LatticeProb.measurableSet_exceptionalLevels` : the enclosing set is measurable in `ℝ × C(ℝ≥0, ℝ)`.
* `LatticeProb.countable_section_exceptionalLevels` : each path has countably many exceptional levels.
* `LatticeProb.ae_ae_continuousAt_stopAtHit` : for every probability measure `ν` on path space, for almost every level
  `c > 0` the map `v ↦ stopAt (hitFrom c 0 v) v` is continuous at `ν`-almost every path.
-/

open Filter Set MeasureTheory
open scoped ENNReal NNReal Topology

namespace LatticeProb

/-- Pairs `(c, w)` such that `c` is the running maximum of `w` over the rational times `r < q`. -/
def runMaxLevel (q : ℚ) : Set (ℝ × C(ℝ≥0, ℝ)) :=
  {p | (∀ r : ℚ, 0 ≤ r → r < q → p.2 (Real.toNNReal r) ≤ p.1) ∧
    ∀ ε : ℚ, 0 < ε → ∃ r : ℚ, 0 ≤ r ∧ r < q ∧ p.1 - ε < p.2 (Real.toNNReal r)}

/-- Pairs `(c, w)` such that `c` is the running minimum of `w` over the rational times `r < q`. -/
def runMinLevel (q : ℚ) : Set (ℝ × C(ℝ≥0, ℝ)) :=
  {p | (-p.1, -p.2) ∈ runMaxLevel q}

/-- The enclosing set of exceptional pairs. -/
def exceptionalLevels : Set (ℝ × C(ℝ≥0, ℝ)) :=
  {p | p.1 = p.2 0} ∪ ((⋃ q : ℚ, runMaxLevel q) ∪ ⋃ q : ℚ, runMinLevel q)

lemma measurable_eval_snd (t : ℝ≥0) : Measurable fun p : ℝ × C(ℝ≥0, ℝ) => p.2 t :=
  (continuous_eval_const t).measurable.comp measurable_snd

lemma measurableSet_runMaxLevel (q : ℚ) : MeasurableSet (runMaxLevel q) := by
  have h1 : MeasurableSet {p : ℝ × C(ℝ≥0, ℝ) |
      ∀ r : ℚ, 0 ≤ r → r < q → p.2 (Real.toNNReal r) ≤ p.1} := by
    simp only [Set.ofPred_forall]
    refine MeasurableSet.iInter fun r => MeasurableSet.iInter fun _ => MeasurableSet.iInter fun _ => ?_
    exact measurableSet_le (measurable_eval_snd _) measurable_fst
  have h2 : MeasurableSet {p : ℝ × C(ℝ≥0, ℝ) |
      ∀ ε : ℚ, 0 < ε → ∃ r : ℚ, 0 ≤ r ∧ r < q ∧ p.1 - ε < p.2 (Real.toNNReal r)} := by
    simp only [Set.ofPred_forall, Set.ofPred_exists, Set.ofPred_and]
    refine MeasurableSet.iInter fun ε => MeasurableSet.iInter fun _ => MeasurableSet.iUnion fun r => ?_
    refine MeasurableSet.inter (MeasurableSet.const _) (MeasurableSet.inter (MeasurableSet.const _) ?_)
    exact measurableSet_lt (measurable_fst.sub_const _) (measurable_eval_snd _)
  exact h1.inter h2

lemma measurableSet_runMinLevel (q : ℚ) : MeasurableSet (runMinLevel q) :=
  (measurableSet_runMaxLevel q).preimage (measurable_fst.neg.prodMk measurable_snd.neg)

lemma measurableSet_exceptionalLevels : MeasurableSet exceptionalLevels := by
  refine MeasurableSet.union ?_ (MeasurableSet.union ?_ ?_)
  · exact measurableSet_eq_fun measurable_fst (measurable_eval_snd 0)
  · exact MeasurableSet.iUnion measurableSet_runMaxLevel
  · exact MeasurableSet.iUnion measurableSet_runMinLevel

/-- A level at which `w` does not exceed `c` immediately after its first hit of `c` is the running maximum of `w`
over the rational times `< q`, for some rational `q`. -/
lemma exists_mem_runMaxLevel_of_not_strictCross_up (w : C(ℝ≥0, ℝ)) {c : ℝ}
    (hc : ¬ ∀ b : ℝ≥0∞, hitFrom c 0 w < b → ∃ s : ℝ≥0, (s : ℝ≥0∞) < b ∧ c < w s) :
    ∃ q : ℚ, (c, w) ∈ runMaxLevel q := by
  rw [not_forall] at hc
  obtain ⟨b, hb⟩ := hc
  rw [Classical.not_imp] at hb
  obtain ⟨hb, hle⟩ := hb
  obtain ⟨q, -, hq1, hq2⟩ := ENNReal.lt_iff_exists_rat_btwn.1 hb
  have hmax : ∀ s : ℝ≥0, (s : ℝ≥0∞) < (Real.toNNReal q : ℝ≥0∞) → w s ≤ c := by
    intro s hs
    by_contra hcon
    exact hle ⟨s, hs.trans hq2, not_le.1 hcon⟩
  obtain ⟨s0, hs0, -, hws0, -⟩ := exists_hitFrom_eq w.continuous (ne_top_of_lt hq1)
  have hs0q : s0 < Real.toNNReal q := ENNReal.coe_lt_coe.1 (hs0 ▸ hq1)
  have hq0 : (0 : ℝ) < q := Real.toNNReal_pos.1 (lt_of_le_of_lt (zero_le : (0 : ℝ≥0) ≤ s0) hs0q)
  have hsq : (s0 : ℝ) < q := by
    have := NNReal.coe_lt_coe.2 hs0q
    rwa [Real.coe_toNNReal (q : ℝ) hq0.le] at this
  refine ⟨q, fun r hr0 hrq => ?_, fun ε hε => ?_⟩
  · refine hmax _ (ENNReal.coe_lt_coe.2 ((Real.toNNReal_lt_toNNReal_iff hq0).2 (by exact_mod_cast hrq)))
  · have hε' : (0 : ℝ) < ε := by exact_mod_cast hε
    obtain ⟨δ, hδ, hδ'⟩ := Metric.continuous_iff.1 w.continuous s0 ε hε'
    obtain ⟨r, hr1, hr2⟩ := exists_rat_btwn (lt_min (lt_add_of_pos_right (s0 : ℝ) hδ) hsq)
    have hr0 : (0 : ℝ) ≤ r := (s0.2.trans hr1.le)
    have hrr : ((Real.toNNReal r : ℝ≥0) : ℝ) = r := Real.coe_toNNReal _ hr0
    refine ⟨r, by exact_mod_cast hr0, by exact_mod_cast hr2.trans_le (min_le_right _ _), ?_⟩
    have hd : dist (Real.toNNReal r) s0 < δ := by
      rw [NNReal.dist_eq, hrr, abs_of_pos (sub_pos.2 hr1)]
      linarith [(hr2.trans_le (min_le_left _ _))]
    have := hδ' _ hd
    rw [Real.dist_eq, abs_lt] at this
    show c - ε < w (Real.toNNReal r)
    rw [← hws0]
    linarith [this.1]

/-- The downward version: a level at which `w` does not fall below `c` immediately after its first hit of `c` is the
running minimum of `w` over the rational times `< q`, for some rational `q`. -/
lemma exists_mem_runMinLevel_of_not_strictCross_down (w : C(ℝ≥0, ℝ)) {c : ℝ}
    (hc : ¬ ∀ b : ℝ≥0∞, hitFrom c 0 w < b → ∃ s : ℝ≥0, (s : ℝ≥0∞) < b ∧ w s < c) :
    ∃ q : ℚ, (c, w) ∈ runMinLevel q := by
  have hc' : ¬ ∀ b : ℝ≥0∞, hitFrom (-c) 0 ⇑(-w) < b → ∃ s : ℝ≥0, (s : ℝ≥0∞) < b ∧ -c < (-w) s := by
    intro h
    apply hc
    intro b hb
    have hb' : hitFrom (-c) 0 ⇑(-w) < b := by
      rwa [show hitFrom (-c) 0 ⇑(-w) = hitFrom c 0 ⇑w from hitFrom_neg c 0 _]
    obtain ⟨s, hs, hws⟩ := h b hb'
    exact ⟨s, hs, by simpa using hws⟩
  obtain ⟨q, hq⟩ := exists_mem_runMaxLevel_of_not_strictCross_up (-w) hc'
  exact ⟨q, hq⟩

/-- For a given path, at most one level is the running maximum over the rational times `< q`. -/
lemma runMaxLevel_subsingleton (q : ℚ) (w : C(ℝ≥0, ℝ)) :
    {c : ℝ | (c, w) ∈ runMaxLevel q}.Subsingleton := by
  have key : ∀ c c' : ℝ, (c, w) ∈ runMaxLevel q → (c', w) ∈ runMaxLevel q → c ≤ c' := by
    intro c c' hc hc'
    by_contra hlt
    rw [not_le] at hlt
    obtain ⟨ε, hε0, hε1⟩ := exists_rat_btwn (sub_pos.2 hlt)
    obtain ⟨r, hr0, hrq, hr⟩ := hc.2 ε (by exact_mod_cast hε0)
    have h1 : w (Real.toNNReal r) ≤ c' := hc'.1 r hr0 hrq
    have h2 : c - ε < w (Real.toNNReal r) := hr
    linarith
  intro c hc c' hc'
  exact le_antisymm (key c c' hc hc') (key c' c hc' hc)

/-- For a given path, at most one level is the running minimum over the rational times `< q`. -/
lemma runMinLevel_subsingleton (q : ℚ) (w : C(ℝ≥0, ℝ)) :
    {c : ℝ | (c, w) ∈ runMinLevel q}.Subsingleton := fun _ hc _ hc' =>
  neg_injective (runMaxLevel_subsingleton q (-w) hc hc')

/-- Each path has countably many exceptional levels. -/
lemma countable_section_exceptionalLevels (w : C(ℝ≥0, ℝ)) :
    {c : ℝ | (c, w) ∈ exceptionalLevels}.Countable := by
  refine Set.Countable.mono (s₂ := {w 0} ∪ ((⋃ q : ℚ, {c : ℝ | (c, w) ∈ runMaxLevel q}) ∪
    ⋃ q : ℚ, {c : ℝ | (c, w) ∈ runMinLevel q})) ?_ ?_
  · intro c hc
    rcases hc with h | h | h
    · exact Or.inl h
    · obtain ⟨q, hq⟩ := mem_iUnion.1 h
      exact Or.inr (Or.inl (mem_iUnion.2 ⟨q, hq⟩))
    · obtain ⟨q, hq⟩ := mem_iUnion.1 h
      exact Or.inr (Or.inr (mem_iUnion.2 ⟨q, hq⟩))
  · exact (Set.countable_singleton _).union
      ((Set.countable_iUnion fun q => (runMaxLevel_subsingleton q w).countable).union
        (Set.countable_iUnion fun q => (runMinLevel_subsingleton q w).countable))

/-- Off the exceptional set, stopping at the first hit of the level is continuous at the path. -/
lemma continuousAt_stopAt_hitFrom_of_notMem {c : ℝ} {w : C(ℝ≥0, ℝ)}
    (h : (c, w) ∉ exceptionalLevels) :
    ContinuousAt (fun v : C(ℝ≥0, ℝ) => stopAt (hitFrom c 0 (v : ℝ≥0 → ℝ)) v) w := by
  have hc0 : c ≠ w 0 := fun h0 => h (Or.inl h0)
  have hup : ∀ b : ℝ≥0∞, hitFrom c 0 w < b → ∃ s : ℝ≥0, (s : ℝ≥0∞) < b ∧ c < w s := by
    by_contra hcon
    obtain ⟨q, hq⟩ := exists_mem_runMaxLevel_of_not_strictCross_up w hcon
    exact h (Or.inr (Or.inl (mem_iUnion.2 ⟨q, hq⟩)))
  have hdown : ∀ b : ℝ≥0∞, hitFrom c 0 w < b → ∃ s : ℝ≥0, (s : ℝ≥0∞) < b ∧ w s < c := by
    by_contra hcon
    obtain ⟨q, hq⟩ := exists_mem_runMinLevel_of_not_strictCross_down w hcon
    exact h (Or.inr (Or.inr (mem_iUnion.2 ⟨q, hq⟩)))
  refine continuousAt_stopAt_hitFrom ?_
  rcases lt_or_gt_of_ne hc0 with h' | h'
  · exact continuousAt_hitFrom_zero_of_gt h' hdown
  · exact continuousAt_hitFrom_zero_of_lt h' hup

/-- **Almost every level, almost every path.** For every probability measure `ν` on path space, for Lebesgue-almost
every level `c > 0` the map `v ↦ stopAt (hitFrom c 0 v) v` (a path stopped at its first hit of `c`) is continuous at
`ν`-almost every path (compact-open topology). -/
theorem ae_ae_continuousAt_stopAtHit (ν : Measure C(ℝ≥0, ℝ)) [IsProbabilityMeasure ν] :
    ∀ᵐ c ∂(volume.restrict (Ioi (0 : ℝ))), ∀ᵐ w ∂ν,
      ContinuousAt (fun v : C(ℝ≥0, ℝ) => stopAt (hitFrom c 0 (v : ℝ≥0 → ℝ)) v) w := by
  have hmeas : MeasurableSet {p : ℝ × C(ℝ≥0, ℝ) | (p.1, p.2) ∉ exceptionalLevels} :=
    measurableSet_exceptionalLevels.compl
  have h2 : ∀ᵐ w ∂ν, ∀ᵐ c ∂(volume.restrict (Ioi (0 : ℝ))), (c, w) ∉ exceptionalLevels :=
    Eventually.of_forall fun w =>
      (countable_section_exceptionalLevels w).ae_notMem (volume.restrict (Ioi (0 : ℝ)))
  have h3 := (Measure.ae_ae_comm (μ := volume.restrict (Ioi (0 : ℝ))) (ν := ν)
    (p := fun c w => (c, w) ∉ exceptionalLevels) hmeas).2 h2
  filter_upwards [h3] with c hc
  filter_upwards [hc] with w hw
  exact continuousAt_stopAt_hitFrom_of_notMem hw

end LatticeProb
