import LatticeProb.Analysis.StraddlingLevelPairs

/-!
# First and last passage below a level: time reversal, continuity in the level, restart

For `f : ℝ → ℝ`, a base time `v` and a level `l`, `firstBelow f v l` is the first time at or after `v` at which
`f ≤ l`, and `lastBelow f v l` is the last time at or before `v` at which `f ≤ l`
(`LatticeProb.Analysis.StraddlingLevelPairs`). This file proves three deterministic facts about these passage
times, used for the first passage processes `a ↦ firstBelow B 0 (-a)` of continuous paths.

* `lastBelow_eq_neg_firstBelow`: the last passage before `v` is minus the first passage after `-v` of the
  time-reversed function `u ↦ f (-u)`.
* `tendsto_firstBelow_nhdsGE`, `tendsto_lastBelow_nhdsGE`: for continuous `f`, both passage times are right
  continuous in the level; equivalently (`tendsto_firstBelow_neg_nhdsLE`, `tendsto_lastBelow_neg_nhdsLE`) they are
  left continuous in the depth `a = -l`.
* `firstBelow_eq_add_firstBelow`, `lastBelow_eq_sub_firstBelow`: the passage below a lower level `l' ≤ l` is the
  passage `t` below `l` followed by the first passage of the restarted increment `u ↦ f (t + u) - f t` (resp.
  `u ↦ f (t - u) - f t`) below `l' - l`. This is the additivity of the first passage process of a continuous path.
-/

open Set Filter Topology

namespace LatticeProb

section OneFunction

variable {f : ℝ → ℝ} {v l : ℝ}

/-- **Time reversal.** The last time at or before `v` at which `f ≤ l` is minus the first time at or after `-v`
at which the reversed function `u ↦ f (-u)` is `≤ l`. This holds without any hypothesis: when the sets are empty
both sides take the value `0` of `sSup ∅` and `sInf ∅`. -/
theorem lastBelow_eq_neg_firstBelow (f : ℝ → ℝ) (v l : ℝ) :
    lastBelow f v l = -firstBelow (fun u => f (-u)) (-v) l := by
  unfold lastBelow firstBelow
  rw [Real.sInf_def, neg_neg]
  congr 1
  ext u
  show (u ≤ v ∧ f u ≤ l) ↔ (-v ≤ -u ∧ f (-(-u)) ≤ l)
  rw [neg_neg, neg_le_neg_iff]

/-- **Right continuity in the level of the first passage.** If `f` is continuous and `f ≤ l` somewhere after `v`,
then `firstBelow f v l' → firstBelow f v l` as `l' ↓ l`. -/
theorem tendsto_firstBelow_nhdsGE (hf : Continuous f) (hb : ∃ b, v ≤ b ∧ f b ≤ l) :
    Tendsto (fun l' => firstBelow f v l') (𝓝[≥] l) (𝓝 (firstBelow f v l)) := by
  refine tendsto_order.2 ⟨fun c hc => ?_, fun c hc => ?_⟩
  · obtain ⟨l₁, hl₁, h⟩ := exists_firstBelow_sub_lt hf hb (sub_pos.2 hc)
    filter_upwards [Ico_mem_nhdsGE hl₁] with l' hl'
    have := h l' hl'.1 hl'.2
    linarith
  · filter_upwards [self_mem_nhdsWithin] with l' hl'
    exact (firstBelow_anti hl' hb).trans_lt hc

/-- **Right continuity in the level of the last passage.** If `f` is continuous and `f ≤ l` somewhere before `v`,
then `lastBelow f v l' → lastBelow f v l` as `l' ↓ l`. -/
theorem tendsto_lastBelow_nhdsGE (hf : Continuous f) (ha : ∃ a ≤ v, f a ≤ l) :
    Tendsto (fun l' => lastBelow f v l') (𝓝[≥] l) (𝓝 (lastBelow f v l)) := by
  refine tendsto_order.2 ⟨fun c hc => ?_, fun c hc => ?_⟩
  · filter_upwards [self_mem_nhdsWithin] with l' hl'
    exact hc.trans_le (lastBelow_mono hl' ha)
  · obtain ⟨l₁, hl₁, h⟩ := exists_lastBelow_lt_add hf ha (sub_pos.2 hc)
    filter_upwards [Ico_mem_nhdsGE hl₁] with l' hl'
    have := h l' hl'.1 hl'.2
    linarith

/-- Negation maps left neighbourhoods of `a` to right neighbourhoods of `-a`. -/
theorem tendsto_neg_nhdsLE_nhdsGE (a : ℝ) : Tendsto (fun b : ℝ => -b) (𝓝[≤] a) (𝓝[≥] (-a)) :=
  tendsto_nhdsWithin_iff.2 ⟨(continuous_neg.tendsto a).mono_left nhdsWithin_le_nhds,
    eventually_nhdsWithin_of_forall fun _ hb => mem_Ici.2 (neg_le_neg (mem_Iic.1 hb))⟩

/-- **Left continuity in the depth of the first passage.** If `f` is continuous and `f ≤ -a` somewhere after `v`,
then `firstBelow f v (-b) → firstBelow f v (-a)` as `b ↑ a`. -/
theorem tendsto_firstBelow_neg_nhdsLE {a : ℝ} (hf : Continuous f) (hb : ∃ b, v ≤ b ∧ f b ≤ -a) :
    Tendsto (fun b => firstBelow f v (-b)) (𝓝[≤] a) (𝓝 (firstBelow f v (-a))) :=
  (tendsto_firstBelow_nhdsGE hf hb).comp (tendsto_neg_nhdsLE_nhdsGE a)

/-- **Left continuity in the depth of the last passage.** If `f` is continuous and `f ≤ -a` somewhere before `v`,
then `lastBelow f v (-b) → lastBelow f v (-a)` as `b ↑ a`. -/
theorem tendsto_lastBelow_neg_nhdsLE {a : ℝ} (hf : Continuous f) (ha : ∃ c ≤ v, f c ≤ -a) :
    Tendsto (fun b => lastBelow f v (-b)) (𝓝[≤] a) (𝓝 (lastBelow f v (-a))) :=
  (tendsto_lastBelow_nhdsGE hf ha).comp (tendsto_neg_nhdsLE_nhdsGE a)

/-- **Restart at a first passage.** Let `f` be continuous with `l < f v`, and let `f ≤ l'` somewhere after `v`,
where `l' ≤ l`. Put `t = firstBelow f v l`, and let `g` agree on `[0, ∞)` with the restarted increment
`u ↦ f (t + u) - f t`. Then the first passage below `l'` after `v` is `t` plus the first passage of `g` below
`l' - l` after `0`. -/
theorem firstBelow_eq_add_firstBelow (hf : Continuous f) (hl : l < f v) {l' : ℝ} (hll' : l' ≤ l)
    (hb : ∃ b, v ≤ b ∧ f b ≤ l') {g : ℝ → ℝ}
    (hg : ∀ u, 0 ≤ u → g u = f (firstBelow f v l + u) - f (firstBelow f v l)) :
    firstBelow f v l' = firstBelow f v l + firstBelow g 0 (l' - l) := by
  obtain ⟨b, hvb, hfb⟩ := hb
  have hft : f (firstBelow f v l) = l := apply_firstBelow hf hl ⟨b, hvb, hfb.trans hll'⟩
  have hvt : v ≤ firstBelow f v l := (firstBelow_mem hf ⟨b, hvb, hfb.trans hll'⟩).1
  have hmem : ∀ u, 0 ≤ u → (g u ≤ l' - l ↔ f (firstBelow f v l + u) ≤ l') := by
    intro u hu
    rw [hg u hu, hft]
    constructor <;> intro h <;> linarith
  have hbt : firstBelow f v l ≤ b := firstBelow_le hvb (hfb.trans hll')
  apply le_antisymm
  · rw [← sub_le_iff_le_add']
    show _ ≤ sInf {u | 0 ≤ u ∧ g u ≤ l' - l}
    refine le_csInf ⟨b - firstBelow f v l, sub_nonneg.2 hbt, (hmem _ (sub_nonneg.2 hbt)).2 ?_⟩
      fun u hu => ?_
    · rw [show firstBelow f v l + (b - firstBelow f v l) = b by ring]
      exact hfb
    · have := firstBelow_le (f := f) (v := v) (l := l') (u := firstBelow f v l + u) (by linarith [hu.1])
        ((hmem u hu.1).1 hu.2)
      linarith
  · obtain ⟨hvT, hfT⟩ := firstBelow_mem hf ⟨b, hvb, hfb⟩
    have htT : firstBelow f v l ≤ firstBelow f v l' := firstBelow_le hvT (hfT.trans hll')
    have := firstBelow_le (f := g) (v := 0) (l := l' - l) (u := firstBelow f v l' - firstBelow f v l)
      (sub_nonneg.2 htT) ((hmem _ (sub_nonneg.2 htT)).2 (by
        rw [show firstBelow f v l + (firstBelow f v l' - firstBelow f v l) = firstBelow f v l' by ring]
        exact hfT))
    linarith

/-- **Restart at a last passage.** Let `f` be continuous with `l < f v`, and let `f ≤ l'` somewhere before `v`,
where `l' ≤ l`. Put `s = lastBelow f v l`, and let `g` agree on `[0, ∞)` with the backward restarted increment
`u ↦ f (s - u) - f s`. Then the last passage below `l'` before `v` is `s` minus the first passage of `g` below
`l' - l` after `0`. -/
theorem lastBelow_eq_sub_firstBelow (hf : Continuous f) (hl : l < f v) {l' : ℝ} (hll' : l' ≤ l)
    (ha : ∃ a ≤ v, f a ≤ l') {g : ℝ → ℝ}
    (hg : ∀ u, 0 ≤ u → g u = f (lastBelow f v l - u) - f (lastBelow f v l)) :
    lastBelow f v l' = lastBelow f v l - firstBelow g 0 (l' - l) := by
  obtain ⟨a, hav, hfa⟩ := ha
  have hr : Continuous fun u => f (-u) := hf.comp continuous_neg
  have key := firstBelow_eq_add_firstBelow (f := fun u => f (-u)) (v := -v) hr (by simpa using hl) hll'
    ⟨-a, neg_le_neg hav, by simpa using hfa⟩ (g := g) fun u hu => by
      rw [hg u hu, lastBelow_eq_neg_firstBelow f v l,
        show -firstBelow (fun u => f (-u)) (-v) l - u = -(firstBelow (fun u => f (-u)) (-v) l + u) by ring]
  rw [lastBelow_eq_neg_firstBelow f v l', lastBelow_eq_neg_firstBelow f v l]
  linarith

end OneFunction

end LatticeProb
