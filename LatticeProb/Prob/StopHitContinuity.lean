import Mathlib
import LatticeProb.Prob.BrownianRestartPath
import LatticeProb.Prob.UpcrossIntervals

/-!
# Continuity of the stopped path at a first-hit time

For a continuous path `w : C(ℝ≥0, ℝ)` and a level `c`, the first time `hitFrom c 0 w` at which `w` equals `c` and the
path `w` stopped at that time depend continuously on `w` (compact-open topology) at every level `c` other than the
starting value `w 0` for which `w` crosses `c` strictly right after its first hit. The levels `c` where this fails are
countably many: such a level is a local maximum value (or a local minimum value) of the path on an initial segment
`[0, q)` with `q` rational.

## Main statements

* `LatticeProb.continuous_stopAt_uncurry` : `(T, w) ↦ stopAt T w` is jointly continuous on `ℝ≥0∞ × C(ℝ≥0, ℝ)`.
* `LatticeProb.continuousAt_hitFrom_zero_of_lt`, `LatticeProb.continuousAt_hitFrom_zero_of_gt` : continuity of the
  first hit time when `w 0 < c`, respectively `c < w 0`, and `w` crosses `c` strictly after its first hit.
* `LatticeProb.exists_countable_forall_continuousAt_stopAt_hitFrom` : for every path, outside a countable set of levels
  the map `v ↦ stopAt (hitFrom c 0 v) v` is continuous at the path.
-/

open Filter Set
open scoped ENNReal NNReal Topology

namespace LatticeProb

private lemma zero_le' (s : ℝ≥0) : (0 : ℝ≥0) ≤ s := zero_le

/-- Stopping a path is jointly continuous in the stopping time `T ∈ [0, ∞]` and the path. -/
theorem continuous_stopAt_uncurry :
    Continuous fun p : ℝ≥0∞ × C(ℝ≥0, ℝ) => stopAt p.1 p.2 := by
  refine ContinuousMap.continuous_of_continuous_uncurry _ ?_
  have h1 : Continuous fun x : (ℝ≥0∞ × C(ℝ≥0, ℝ)) × ℝ≥0 => (min (x.2 : ℝ≥0∞) x.1.1).toNNReal :=
    ENNReal.continuousOn_toNNReal.comp_continuous
      ((ENNReal.continuous_coe.comp continuous_snd).min (continuous_fst.comp continuous_fst))
      fun _ => ((min_le_left _ _).trans_lt ENNReal.coe_lt_top).ne
  exact continuous_eval.comp ((continuous_snd.comp continuous_fst).prodMk h1)

/-- Paths close to `w` in the compact-open topology are uniformly close to `w` on `[0, K]`. -/
lemma eventually_forall_dist_lt (w : C(ℝ≥0, ℝ)) (K : ℝ≥0) {δ : ℝ} (hδ : 0 < δ) :
    ∀ᶠ v in 𝓝 w, ∀ s ≤ K, dist (w s) (v s) < δ := by
  have h := ContinuousMap.tendsto_iff_forall_isCompact_tendstoUniformlyOn.1
    (tendsto_id : Tendsto (id : C(ℝ≥0, ℝ) → C(ℝ≥0, ℝ)) (𝓝 w) (𝓝 w)) (Icc 0 K) isCompact_Icc
  rw [Metric.tendstoUniformlyOn_iff] at h
  filter_upwards [h δ hδ] with v hv s hs
  exact hv s ⟨zero_le, hs⟩

/-- **Continuity of the first hit time of a level above the starting value.** If `w 0 < c` and `w` takes values
`> c` at times arbitrarily close after its first hit of `c`, then `v ↦ hitFrom c 0 v` is continuous at `w`. -/
theorem continuousAt_hitFrom_zero_of_lt {w : C(ℝ≥0, ℝ)} {c : ℝ} (h0 : w 0 < c)
    (hcross : ∀ b : ℝ≥0∞, hitFrom c 0 w < b → ∃ s : ℝ≥0, (s : ℝ≥0∞) < b ∧ c < w s) :
    ContinuousAt (fun v : C(ℝ≥0, ℝ) => hitFrom c 0 (v : ℝ≥0 → ℝ)) w := by
  refine tendsto_order.2 ⟨fun a ha => ?_, fun b hb => ?_⟩
  · obtain ⟨K, haK, hKτ⟩ := ENNReal.lt_iff_exists_nnreal_btwn.1 ha
    have hlt : ∀ s ≤ K, w s < c := by
      intro s hs
      by_contra hcon
      rw [not_lt] at hcon
      obtain ⟨t, ht, hwt⟩ :=
        intermediate_value_Icc (zero_le' s) w.continuous.continuousOn ⟨h0.le, hcon⟩
      exact absurd (hKτ.trans_le' (ENNReal.coe_le_coe.2 (ht.2.trans hs)))
        (not_lt.2 (hitFrom_le zero_le hwt))
    obtain ⟨x, hx, hxmax⟩ :=
      isCompact_Icc.exists_isMaxOn (Set.nonempty_Icc.2 (zero_le' K)) w.continuous.continuousOn
    have hδ : 0 < c - w x := sub_pos.2 (hlt x hx.2)
    filter_upwards [eventually_forall_dist_lt w K hδ] with v hv
    have hvlt : ∀ s ≤ K, v s < c := fun s hs => by
      have h1 := hv s hs
      have h2 : w s ≤ w x := hxmax ⟨zero_le, hs⟩
      rw [Real.dist_eq, abs_lt] at h1
      linarith [h1.1, h1.2]
    refine lt_of_lt_of_le haK (le_iInf₂ fun s hs => ?_)
    by_contra hKs
    rw [not_le] at hKs
    exact absurd hs.2 (hvlt s (ENNReal.coe_lt_coe.1 hKs).le).ne
  · obtain ⟨s0, hs0b, hs0⟩ := hcross b hb
    have e1 : ∀ᶠ v : C(ℝ≥0, ℝ) in 𝓝 w, c < v s0 :=
      (continuous_eval_const s0).continuousAt.eventually (lt_mem_nhds hs0)
    have e0 : ∀ᶠ v : C(ℝ≥0, ℝ) in 𝓝 w, v 0 < c :=
      (continuous_eval_const (0 : ℝ≥0)).continuousAt.eventually (gt_mem_nhds h0)
    filter_upwards [e0, e1] with v hv0 hv1
    obtain ⟨t, ht, hvt⟩ :=
      intermediate_value_Icc (zero_le' s0) v.continuous.continuousOn ⟨hv0.le, hv1.le⟩
    exact (hitFrom_le zero_le hvt).trans_lt
      (lt_of_le_of_lt (ENNReal.coe_le_coe.2 ht.2) hs0b)

/-- The first hit of `-a` by `-w` is the first hit of `a` by `w`. -/
lemma hitFrom_neg (a : ℝ) (r : ℝ≥0∞) (w : ℝ≥0 → ℝ) : hitFrom (-a) r (-w) = hitFrom a r w := by
  simp only [hitFrom, Pi.neg_apply, neg_inj]

/-- **Continuity of the first hit time of a level below the starting value.** The mirror image of
`continuousAt_hitFrom_zero_of_lt`. -/
theorem continuousAt_hitFrom_zero_of_gt {w : C(ℝ≥0, ℝ)} {c : ℝ} (h0 : c < w 0)
    (hcross : ∀ b : ℝ≥0∞, hitFrom c 0 w < b → ∃ s : ℝ≥0, (s : ℝ≥0∞) < b ∧ w s < c) :
    ContinuousAt (fun v : C(ℝ≥0, ℝ) => hitFrom c 0 (v : ℝ≥0 → ℝ)) w := by
  have h := continuousAt_hitFrom_zero_of_lt (w := -w) (c := -c) (by simpa using h0) (fun b hb => by
    rw [show hitFrom (-c) 0 ⇑(-w) = hitFrom c 0 ⇑w from hitFrom_neg c 0 _] at hb
    obtain ⟨s, hs, hws⟩ := hcross b hb
    exact ⟨s, hs, by simpa using hws⟩)
  have key : (fun v : C(ℝ≥0, ℝ) => hitFrom c 0 (v : ℝ≥0 → ℝ)) =
      (fun v : C(ℝ≥0, ℝ) => hitFrom (-c) 0 (⇑(-v))) := by
    funext v
    exact (hitFrom_neg c 0 v).symm
  rw [key]
  exact h.comp_of_eq continuous_neg.continuousAt rfl

/-- Stopping at the first hit time is continuous wherever the first hit time is. -/
theorem continuousAt_stopAt_hitFrom {w : C(ℝ≥0, ℝ)} {c : ℝ}
    (h : ContinuousAt (fun v : C(ℝ≥0, ℝ) => hitFrom c 0 (v : ℝ≥0 → ℝ)) w) :
    ContinuousAt (fun v : C(ℝ≥0, ℝ) => stopAt (hitFrom c 0 (v : ℝ≥0 → ℝ)) v) w :=
  continuous_stopAt_uncurry.continuousAt.comp (f := fun v : C(ℝ≥0, ℝ) => (hitFrom c 0 (v : ℝ≥0 → ℝ), v))
    (h.prodMk continuousAt_id)

/-- The levels `c` at which `w` does not exceed `c` immediately after its first hit of `c` form a countable set:
each such level is the value of `w` at its first hit time, which is the maximum of `w` on `[0, q)` for some rational
`q`. -/
lemma countable_not_strictCross_up (w : C(ℝ≥0, ℝ)) :
    {c : ℝ | ¬ ∀ b : ℝ≥0∞, hitFrom c 0 w < b → ∃ s : ℝ≥0, (s : ℝ≥0∞) < b ∧ c < w s}.Countable := by
  have hsub : {c : ℝ | ¬ ∀ b : ℝ≥0∞, hitFrom c 0 w < b → ∃ s : ℝ≥0, (s : ℝ≥0∞) < b ∧ c < w s} ⊆
      ⋃ q : ℚ, {c : ℝ | hitFrom c 0 w < (Real.toNNReal q : ℝ≥0∞) ∧
        ∀ s : ℝ≥0, (s : ℝ≥0∞) < (Real.toNNReal q : ℝ≥0∞) → w s ≤ c} := by
    intro c hc
    simp only [mem_ofPred_eq, not_forall] at hc
    obtain ⟨b, hb, hle⟩ := hc
    obtain ⟨q, -, hq1, hq2⟩ := ENNReal.lt_iff_exists_rat_btwn.1 hb
    refine mem_iUnion.2 ⟨q, hq1, fun s hs => ?_⟩
    by_contra hcon
    exact hle ⟨s, hs.trans hq2, not_le.1 hcon⟩
  refine Set.Countable.mono hsub (Set.countable_iUnion fun q => Set.Subsingleton.countable ?_)
  have hwit : ∀ c : ℝ, hitFrom c 0 w < (Real.toNNReal q : ℝ≥0∞) →
      ∃ s : ℝ≥0, (s : ℝ≥0∞) < (Real.toNNReal q : ℝ≥0∞) ∧ w s = c := by
    intro c hc
    obtain ⟨s, hs, -, hws, -⟩ := exists_hitFrom_eq w.continuous (ne_top_of_lt hc)
    exact ⟨s, hs ▸ hc, hws⟩
  intro c hc c' hc'
  obtain ⟨s, hs, hws⟩ := hwit c hc.1
  obtain ⟨s', hs', hws'⟩ := hwit c' hc'.1
  exact le_antisymm (hws ▸ hc'.2 s hs) (hws' ▸ hc.2 s' hs')

/-- The levels `c` at which `w` does not fall below `c` immediately after its first hit of `c` form a countable
set. -/
lemma countable_not_strictCross_down (w : C(ℝ≥0, ℝ)) :
    {c : ℝ | ¬ ∀ b : ℝ≥0∞, hitFrom c 0 w < b → ∃ s : ℝ≥0, (s : ℝ≥0∞) < b ∧ w s < c}.Countable := by
  refine ((countable_not_strictCross_up (-w)).preimage neg_injective).mono ?_
  intro c hc
  simp only [mem_preimage, mem_ofPred_eq] at hc ⊢
  contrapose! hc
  intro b hb
  have hb' : hitFrom (-c) 0 ⇑(-w) < b := by
    rwa [show hitFrom (-c) 0 ⇑(-w) = hitFrom c 0 ⇑w from hitFrom_neg c 0 _]
  obtain ⟨s, hs, hws⟩ := hc b hb'
  exact ⟨s, hs, by simpa using hws⟩

/-- **Countably many exceptional levels.** For every path `w` there is a countable set `E` of levels such that for
every `c ∉ E` the map `v ↦ stopAt (hitFrom c 0 v) v` is continuous at `w` (compact-open topology). -/
theorem exists_countable_forall_continuousAt_stopAt_hitFrom (w : C(ℝ≥0, ℝ)) :
    ∃ E : Set ℝ, E.Countable ∧ ∀ c ∉ E,
      ContinuousAt (fun v : C(ℝ≥0, ℝ) => stopAt (hitFrom c 0 (v : ℝ≥0 → ℝ)) v) w := by
  refine ⟨{w 0} ∪ ({c : ℝ | ¬ ∀ b : ℝ≥0∞, hitFrom c 0 w < b → ∃ s : ℝ≥0, (s : ℝ≥0∞) < b ∧ c < w s} ∪
    {c : ℝ | ¬ ∀ b : ℝ≥0∞, hitFrom c 0 w < b → ∃ s : ℝ≥0, (s : ℝ≥0∞) < b ∧ w s < c}),
    (Set.countable_singleton _).union ((countable_not_strictCross_up w).union
      (countable_not_strictCross_down w)), fun c hc => ?_⟩
  simp only [mem_union, mem_singleton_iff, mem_ofPred_eq, not_or, not_not] at hc
  obtain ⟨hc0, hup, hdown⟩ := hc
  refine continuousAt_stopAt_hitFrom ?_
  rcases lt_or_gt_of_ne hc0 with h | h
  · exact continuousAt_hitFrom_zero_of_gt h hdown
  · exact continuousAt_hitFrom_zero_of_lt h hup

end LatticeProb
