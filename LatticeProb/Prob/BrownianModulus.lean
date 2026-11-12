/-
Copyright (c) 2026. Released under the Apache 2.0 license.
-/
import Mathlib
import LatticeProb.Prob.BrownianExit

/-!
# Modulus of continuity of Brownian motion

For a real Brownian motion `B` on a probability space, the probability that two times in `[0, T]`
at distance at most `η` see values of `B` at distance at least `a` is at most
`(⌈T/η⌉ + 1) · 4 exp (-(a/2)² / (64 η))`.  The proof covers `[0, T]` by the blocks
`[kη, (k+2)η]`, shifts the motion to the start of each block and applies the maximal estimate.

For a countable dense set `D` of times, `badMod B D T η a` is the measurable event that two times
of `D` in `[0, T]` at distance at most `η` see values at distance larger than `a`; for continuous
paths its complement controls all pairs of real times with slightly smaller parameters.

## Main results

* `LatticeProb.measure_exists_modulus_le`: the probability bound.
* `LatticeProb.measurableSet_badMod`: measurability of the event `badMod`.
* `LatticeProb.measure_badMod_le`: the bound for `badMod`.
* `LatticeProb.abs_sub_le_of_not_badMod`: outside `badMod B D T' η' a`, with `T < T'`, `η < η'`
  and continuous paths, all pairs of times in `[0, T]` at distance at most `η` see values at
  distance at most `a`.
-/

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal

namespace LatticeProb

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {B : ℝ≥0 → Ω → ℝ}

/-- The motion started again at time `h` moves by `a` within a time `2 η` with probability at most
`4 exp (-a² / (64 η))`. -/
theorem measure_exists_abs_sub_shift_le [IsProbabilityMeasure P] (hB : IsBrownianReal B P)
    (h η : ℝ≥0) {a : ℝ} (ha : 0 < a) :
    P {ω | ∃ r : ℝ≥0, r ≤ 2 * η ∧ a ≤ |B (h + r) ω - B h ω|} ≤
      4 * ENNReal.ofReal (Real.exp (-(a ^ 2 / (32 * (2 * (η : ℝ)))))) := by
  have := measure_exists_abs_sub_ge_le' (hB.shift h) (2 * η) ha
  simpa using this

/-- Every pair of times `s ≤ T`, `t ≤ s + η` lies in a block `[kη, kη + 2η]` with
`k ≤ ⌈T/η⌉`. -/
theorem exists_block {T η : ℝ≥0} (hη : 0 < η) {s t : ℝ≥0} (hs : s ≤ T)
    (htd : (t : ℝ) - s ≤ η) :
    ∃ k : ℕ, k ≤ ⌈(T : ℝ) / η⌉₊ ∧ (k : ℝ) * η ≤ s ∧ (t : ℝ) ≤ k * η + 2 * η := by
  have hη' : (0 : ℝ) < η := hη
  have hs0 : (0 : ℝ) ≤ (s : ℝ) / η := by positivity
  refine ⟨⌊(s : ℝ) / η⌋₊, ?_, ?_, ?_⟩
  · refine le_trans (Nat.floor_le_floor ?_) (Nat.floor_le_ceil _)
    exact div_le_div_of_nonneg_right (by exact_mod_cast hs) hη'.le
  · exact (le_div_iff₀ hη').1 (Nat.floor_le hs0)
  · have h1 : (s : ℝ) / η < ⌊(s : ℝ) / η⌋₊ + 1 := Nat.lt_floor_add_one _
    have h2 : (s : ℝ) < (⌊(s : ℝ) / η⌋₊ + 1) * η := (div_lt_iff₀ hη').1 h1
    nlinarith

/-- **Modulus of continuity of Brownian motion.** -/
theorem measure_exists_modulus_le [IsProbabilityMeasure P] (hB : IsBrownianReal B P)
    (T η : ℝ≥0) (hη : 0 < η) {a : ℝ} (ha : 0 < a) :
    P {ω | ∃ s t : ℝ≥0, s ≤ T ∧ t ≤ T ∧ |(s : ℝ) - t| ≤ η ∧ a ≤ |B s ω - B t ω|} ≤
      ((⌈(T : ℝ) / η⌉₊ + 1 : ℕ) : ℝ≥0∞) *
        (4 * ENNReal.ofReal (Real.exp (-((a / 2) ^ 2 / (32 * (2 * (η : ℝ))))))) := by
  set N := ⌈(T : ℝ) / η⌉₊ with hN
  have ha2 : 0 < a / 2 := by positivity
  let E : ℕ → Set Ω := fun k =>
    {ω | ∃ r : ℝ≥0, r ≤ 2 * η ∧ a / 2 ≤ |B ((k : ℝ≥0) * η + r) ω - B ((k : ℝ≥0) * η) ω|}
  have key : ∀ (ω : Ω) (s t : ℝ≥0), s ≤ T → (s : ℝ) ≤ t → (t : ℝ) - s ≤ η →
      a ≤ |B s ω - B t ω| → ω ∈ ⋃ k ∈ Finset.range (N + 1), E k := by
    intro ω s t hs hst htd hab
    obtain ⟨k, hk, hks, hkt⟩ := exists_block hη hs htd
    set h : ℝ≥0 := (k : ℝ≥0) * η with hh
    have hhR : (h : ℝ) = k * η := by simp [hh]
    have hhs : h ≤ s := by rw [← NNReal.coe_le_coe, hhR]; exact hks
    have hht : h ≤ t := by
      rw [← NNReal.coe_le_coe, hhR]; exact hks.trans hst
    have hr1 : h + (s - h) = s := add_tsub_cancel_of_le hhs
    have hr2 : h + (t - h) = t := add_tsub_cancel_of_le hht
    have hr1le : s - h ≤ 2 * η := by
      rw [← NNReal.coe_le_coe, NNReal.coe_sub hhs]; push_cast; rw [hhR]; nlinarith
    have hr2le : t - h ≤ 2 * η := by
      rw [← NNReal.coe_le_coe, NNReal.coe_sub hht]; push_cast; rw [hhR]; nlinarith
    have hmem : ∀ r : ℝ≥0, r ≤ 2 * η → a / 2 ≤ |B (h + r) ω - B h ω| → ω ∈ E k := fun r hr hr' =>
      ⟨r, hr, hr'⟩
    refine Set.mem_iUnion₂.2 ⟨k, Finset.mem_range.2 (Nat.lt_succ_of_le hk), ?_⟩
    have htri : |B s ω - B t ω| ≤ |B s ω - B h ω| + |B t ω - B h ω| := by
      calc |B s ω - B t ω| = |(B s ω - B h ω) - (B t ω - B h ω)| := by ring_nf
        _ ≤ _ := abs_sub _ _
    by_cases hc : a / 2 ≤ |B s ω - B h ω|
    · exact hmem (s - h) hr1le (by rw [hr1]; exact hc)
    · push Not at hc
      exact hmem (t - h) hr2le (by rw [hr2]; linarith)
  have hsub : {ω | ∃ s t : ℝ≥0, s ≤ T ∧ t ≤ T ∧ |(s : ℝ) - t| ≤ η ∧ a ≤ |B s ω - B t ω|} ⊆
      ⋃ k ∈ Finset.range (N + 1), E k := by
    rintro ω ⟨s, t, hs, ht, hd, hab⟩
    rcases le_total (s : ℝ) t with hst | hts
    · refine key ω s t hs hst ?_ hab
      have := (abs_le.1 hd).1
      linarith
    · refine key ω t s ht hts ?_ (by rwa [abs_sub_comm])
      have := (abs_le.1 hd).2
      linarith
  calc P _ ≤ P (⋃ k ∈ Finset.range (N + 1), E k) := measure_mono hsub
    _ ≤ ∑ k ∈ Finset.range (N + 1), P (E k) := measure_biUnion_finset_le _ _
    _ ≤ ∑ _k ∈ Finset.range (N + 1),
        4 * ENNReal.ofReal (Real.exp (-((a / 2) ^ 2 / (32 * (2 * (η : ℝ)))))) :=
      Finset.sum_le_sum fun k _ => measure_exists_abs_sub_shift_le hB _ η ha2
    _ = _ := by simp

/-- The event that two times of the set `D` in `[0, T]`, at distance at most `η`, see values of `B`
at distance larger than `a`. -/
def badMod (B : ℝ≥0 → Ω → ℝ) (D : Set ℝ≥0) (T η : ℝ≥0) (a : ℝ) : Set Ω :=
  {ω | ∃ s ∈ D, ∃ t ∈ D, s ≤ T ∧ t ≤ T ∧ |(s : ℝ) - t| ≤ η ∧ a < |B s ω - B t ω|}

omit [MeasurableSpace Ω] in
theorem badMod_eq (D : Set ℝ≥0) (T η : ℝ≥0) (a : ℝ) :
    badMod B D T η a = ⋃ s ∈ D, ⋃ t ∈ D, ⋃ (_ : s ≤ T ∧ t ≤ T ∧ |(s : ℝ) - t| ≤ η),
      {ω | a < |B s ω - B t ω|} := by
  ext ω
  simp only [badMod, Set.mem_ofPred_eq, Set.mem_iUnion, exists_prop, and_assoc]

/-- The event `badMod` is measurable. -/
theorem measurableSet_badMod {D : Set ℝ≥0} (hD : D.Countable) (hm : ∀ t, Measurable (B t))
    (T η : ℝ≥0) (a : ℝ) : MeasurableSet (badMod B D T η a) := by
  rw [badMod_eq]
  refine MeasurableSet.biUnion hD fun s _ => MeasurableSet.biUnion hD fun t _ =>
    MeasurableSet.iUnion fun _ => ?_
  exact measurableSet_lt measurable_const
    (continuous_abs.measurable.comp ((hm s).sub (hm t)))

/-- The probability bound for `badMod`. -/
theorem measure_badMod_le [IsProbabilityMeasure P] (hB : IsBrownianReal B P) (D : Set ℝ≥0)
    (T η : ℝ≥0) (hη : 0 < η) {a : ℝ} (ha : 0 < a) :
    P (badMod B D T η a) ≤
      ((⌈(T : ℝ) / η⌉₊ + 1 : ℕ) : ℝ≥0∞) *
        (4 * ENNReal.ofReal (Real.exp (-((a / 2) ^ 2 / (32 * (2 * (η : ℝ))))))) := by
  refine le_trans (measure_mono ?_) (measure_exists_modulus_le hB T η hη ha)
  rintro ω ⟨s, -, t, -, h1, h2, h3, h4⟩
  exact ⟨s, t, h1, h2, h3, h4.le⟩

omit [MeasurableSpace Ω] in
/-- Outside `badMod B D T' η' a`, for a dense set `D` and continuous paths, every pair of times in
`[0, T]` at distance at most `η` sees values at distance at most `a` (`T < T'`, `η < η'`). -/
theorem abs_sub_le_of_not_badMod {D : Set ℝ≥0} (hD : Dense D)
    (hcont : ∀ ω, Continuous fun t => B t ω) {T T' η η' : ℝ≥0} (hT : T < T') (hη : η < η')
    {a : ℝ} {ω : Ω} (hω : ω ∉ badMod B D T' η' a) {s t : ℝ≥0} (hs : s ≤ T) (ht : t ≤ T)
    (hst : |(s : ℝ) - t| ≤ η) : |B s ω - B t ω| ≤ a := by
  obtain ⟨x, hxD, hx⟩ := mem_closure_iff_seq_limit.1 (hD.closure_eq ▸ Set.mem_univ s)
  obtain ⟨y, hyD, hy⟩ := mem_closure_iff_seq_limit.1 (hD.closure_eq ▸ Set.mem_univ t)
  have hxT : ∀ᶠ n in atTop, x n < T' := hx.eventually (gt_mem_nhds (lt_of_le_of_lt hs hT))
  have hyT : ∀ᶠ n in atTop, y n < T' := hy.eventually (gt_mem_nhds (lt_of_le_of_lt ht hT))
  have hd : Tendsto (fun n => |((x n : ℝ≥0) : ℝ) - (y n : ℝ≥0)|) atTop
      (𝓝 |(s : ℝ) - t|) :=
    ((NNReal.continuous_coe.tendsto s).comp hx |>.sub ((NNReal.continuous_coe.tendsto t).comp hy)).abs
  have hdη : ∀ᶠ n in atTop, |((x n : ℝ≥0) : ℝ) - (y n : ℝ≥0)| < η' :=
    hd.eventually (gt_mem_nhds (lt_of_le_of_lt hst (by exact_mod_cast hη)))
  have hle : ∀ᶠ n in atTop, |B (x n) ω - B (y n) ω| ≤ a := by
    filter_upwards [hxT, hyT, hdη] with n h1 h2 h3
    by_contra hcon
    push Not at hcon
    exact hω ⟨x n, hxD n, y n, hyD n, h1.le, h2.le, h3.le, hcon⟩
  have hlim : Tendsto (fun n => |B (x n) ω - B (y n) ω|) atTop (𝓝 |B s ω - B t ω|) :=
    (((hcont ω).tendsto s).comp hx |>.sub ((hcont ω).tendsto t |>.comp hy)).abs
  exact le_of_tendsto hlim hle

end LatticeProb
