/-
Copyright (c) 2026. All rights reserved.
-/
import Mathlib
import LatticeProb.Prob.BrownianDriftConditionedTight
import LatticeProb.Prob.ModulusCompact
import LatticeProb.Prob.BrownianPathMap

/-!
# Tightness of the drifted Brownian motion conditioned to stay above `-δₙ`, `δₙ → 0`

Let `B` be a real Brownian motion with continuous paths, `c > 0`, `Y t = B t + c t` and
`G δ = {Y t > -δ for all t}`.  For a sequence `δₙ > 0` tending to `0`, the laws on `C(ℝ≥0, ℝ)` of
`Y` under `P (· | G δₙ)` form a tight family.

* `LatticeProb.exists_scale_measure_not_hasModulus_le`: for one finite measure, the probability that
  the continuous path `Y` has no modulus `w` at scale `η` on `[0, T]` tends to `0` with `η`.
* `LatticeProb.exists_scale_stayAbove_seq`: a scale `η`, valid for all `n`, with
  `P (G δₙ ∩ {no modulus}) ≤ ρ P (G δₙ)`: the uniform estimate holds for `δₙ` small, and the finitely
  many remaining indices are handled by the previous statement.
* `LatticeProb.exists_compact_measure_stayAbove_seq`: a compact set `K ⊆ C(ℝ≥0, ℝ)` (a set
  `modulusSet η`) with `P (G δₙ ∩ {Y ∉ K}) ≤ ρ P (G δₙ)` for all `n`.
* `LatticeProb.isTightMeasureSet_stayAbove_law`: tightness of the conditioned laws.
-/

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal

noncomputable section

namespace LatticeProb

section Tightness

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} {B : ℝ≥0 → Ω → ℝ}

/-- A modulus at a larger scale is a modulus at a smaller scale. -/
theorem hasModulus_mono_scale {g : ℝ≥0 → ℝ} {T η η' : ℝ≥0} {a : ℝ} (h : η ≤ η')
    (hg : HasModulus g T η' a) : HasModulus g T η a :=
  fun s t hs ht hst => hg s t hs ht (hst.trans (by exact_mod_cast h))

/-- For a finite measure, the probability that the continuous drifted path has no modulus `w` at
scale `η` on `[0, T]` is eventually below any positive threshold as `η → 0`. -/
theorem exists_scale_measure_not_hasModulus_le [IsFiniteMeasure P]
    (hm : ∀ t, Measurable (B t)) (hcont : ∀ ω, Continuous fun s => B s ω) (c : ℝ) (T : ℝ≥0)
    {w : ℝ} (hw : 0 < w) {r : ℝ≥0∞} (hr : 0 < r) :
    ∃ η : ℝ≥0, 0 < η ∧
      P {ω | ¬ HasModulus (fun t : ℝ≥0 => B t ω + c * t) T η w} ≤ r := by
  obtain ⟨D, hDc, hDd⟩ := TopologicalSpace.exists_countable_dense ℝ≥0
  have hpm : Measurable fun ω => fun t : ℝ≥0 => B t ω + c * t :=
    measurable_pi_iff.2 fun t => (hm t).add_const _
  let A : ℕ → Set Ω := fun k =>
    (fun ω => fun t : ℝ≥0 => B t ω + c * t) ⁻¹' badPath D (T + 1) (((k : ℝ≥0) + 1)⁻¹) w
  have hAm : ∀ k, MeasurableSet (A k) := fun k => hpm (measurableSet_badPath hDc _ _ _)
  have hAanti : Antitone A := by
    intro k l hkl ω hω
    obtain ⟨s, hs, t, ht, hsT, htT, hst, hlt⟩ := hω
    refine ⟨s, hs, t, ht, hsT, htT, hst.trans ?_, hlt⟩
    have : (((l : ℝ≥0) + 1)⁻¹ : ℝ≥0) ≤ ((k : ℝ≥0) + 1)⁻¹ :=
      inv_anti₀ (by positivity) (by gcongr)
    exact_mod_cast this
  have hinter : ⋂ k, A k = ∅ := by
    ext ω
    simp only [Set.mem_iInter, Set.mem_empty_iff_false, iff_false]
    intro h
    have huc := (isCompact_Icc (a := (0 : ℝ≥0)) (b := T + 1)).uniformContinuousOn_of_continuous
      (continuous_drift hcont c ω).continuousOn
    rw [Metric.uniformContinuousOn_iff] at huc
    obtain ⟨d, hd, hdd⟩ := huc w hw
    obtain ⟨k, hk⟩ := exists_nat_one_div_lt hd
    obtain ⟨s, hs, t, ht, hsT, htT, hst, hlt⟩ := h k
    have hsm : s ∈ Set.Icc (0 : ℝ≥0) (T + 1) := ⟨zero_le, hsT⟩
    have htm : t ∈ Set.Icc (0 : ℝ≥0) (T + 1) := ⟨zero_le, htT⟩
    have hdist : dist s t < d := by
      rw [NNReal.dist_eq]
      refine lt_of_le_of_lt hst (lt_of_le_of_lt (le_of_eq ?_) hk)
      push_cast
      rw [one_div]
    have := hdd s hsm t htm hdist
    rw [Real.dist_eq] at this
    exact absurd hlt (not_lt.2 this.le)
  have hT := tendsto_measure_iInter_atTop (μ := P) (fun k => (hAm k).nullMeasurableSet) hAanti
    ⟨0, measure_ne_top _ _⟩
  rw [hinter, measure_empty] at hT
  obtain ⟨k, hk⟩ := ((tendsto_order.1 hT).2 r hr).exists
  refine ⟨((k : ℝ≥0) + 1)⁻¹ / 2, by positivity, ?_⟩
  refine le_trans (measure_mono ?_) hk.le
  intro ω hω
  by_contra hωA
  refine hω ?_
  exact hasModulus_of_not_mem_badPath hDd (continuous_drift hcont c ω) (T := T) (T' := T + 1)
    (by simp) (NNReal.half_lt_self (by positivity)) hωA

omit mΩ in
/-- A modulus-failure event is monotone in the scale. -/
theorem inter_not_hasModulus_mono (G : Set Ω) (Y : Ω → ℝ≥0 → ℝ) {T η η' : ℝ≥0} {a : ℝ}
    (h : η ≤ η') :
    G ∩ {ω | ¬ HasModulus (Y ω) T η a} ⊆ G ∩ {ω | ¬ HasModulus (Y ω) T η' a} :=
  Set.inter_subset_inter_right _ fun _ hω h' => hω (hasModulus_mono_scale h h')

/-- **One scale for all `n`.**  If `δₙ > 0` tends to `0`, there is a scale `η` such that, for every
`n`, the conditional probability of `Y` having no modulus `w` at scale `η` on `[0, T]` given
`G δₙ` is at most `ρ`.  For `δₙ` small this is the uniform estimate; the finitely many other indices
are handled with their own scale (continuity of one law). -/
theorem exists_scale_stayAbove_seq [IsProbabilityMeasure P] (hB : IsBrownianReal B P)
    (hm : ∀ t, Measurable (B t)) (hcont : ∀ ω, Continuous fun s => B s ω) {c : ℝ} (hc : 0 < c)
    {δ : ℕ → ℝ} (hδ0 : Tendsto δ atTop (𝓝 0)) (hδ : ∀ n, 0 < δ n)
    (T : ℝ≥0) {w ρ : ℝ} (hw : 0 < w) (hρ : 0 < ρ) :
    ∃ η : ℝ≥0, 0 < η ∧ ∀ n, P ({ω | ∀ t : ℝ≥0, -δ n < B t ω + c * t} ∩
          {ω | ¬ HasModulus (fun t : ℝ≥0 => B t ω + c * t) T η w}) ≤
        ENNReal.ofReal ρ * P {ω | ∀ t : ℝ≥0, -δ n < B t ω + c * t} := by
  obtain ⟨ε, η₁, hε, hη₁, hunif⟩ := exists_uniform_modulus hB hm hcont hc T hw hρ
  have hev : ∀ᶠ n in atTop, δ n ≤ ε := ((tendsto_order.1 hδ0).2 ε hε).mono fun n h => h.le
  obtain ⟨N, hN⟩ := eventually_atTop.1 hev
  have hsingle : ∀ n, ∃ η : ℝ≥0, 0 < η ∧
      P ({ω | ∀ t : ℝ≥0, -δ n < B t ω + c * t} ∩
          {ω | ¬ HasModulus (fun t : ℝ≥0 => B t ω + c * t) T η w}) ≤
        ENNReal.ofReal ρ * P {ω | ∀ t : ℝ≥0, -δ n < B t ω + c * t} := by
    intro n
    by_cases h0 : P {ω | ∀ t : ℝ≥0, -δ n < B t ω + c * t} = 0
    · refine ⟨1, one_pos, ?_⟩
      rw [h0, mul_zero]
      exact (measure_mono Set.inter_subset_left).trans h0.le
    · have hr : 0 < ENNReal.ofReal ρ * P {ω | ∀ t : ℝ≥0, -δ n < B t ω + c * t} :=
        ENNReal.mul_pos (by simpa using hρ) h0
      obtain ⟨η, hη, hlt⟩ := exists_scale_measure_not_hasModulus_le (P := P) hm hcont c T hw hr
      exact ⟨η, hη, (measure_mono Set.inter_subset_right).trans hlt⟩
  choose g hg0 hg using hsingle
  have hmin : ∀ M : ℕ, ∃ η : ℝ≥0, 0 < η ∧ ∀ n < M, η ≤ g n := by
    intro M
    induction M with
    | zero => exact ⟨1, one_pos, fun n hn => absurd hn (Nat.not_lt_zero n)⟩
    | succ M ih =>
      obtain ⟨η, hη, h⟩ := ih
      refine ⟨min η (g M), lt_min hη (hg0 M), fun n hn => ?_⟩
      rcases Nat.lt_succ_iff_lt_or_eq.1 hn with hlt | rfl
      · exact (min_le_left _ _).trans (h n hlt)
      · exact min_le_right _ _
  obtain ⟨η₂, hη₂, hle⟩ := hmin N
  refine ⟨min η₁ η₂, lt_min hη₁ hη₂, fun n => ?_⟩
  by_cases hn : n < N
  · exact (measure_mono (inter_not_hasModulus_mono _ (fun ω t => B t ω + c * t)
      ((min_le_right _ _).trans (hle n hn)))).trans (hg n)
  · exact (measure_mono (inter_not_hasModulus_mono _ (fun ω t => B t ω + c * t)
      (min_le_left _ _))).trans (hunif (δ n) (hδ n) (hN n (not_lt.1 hn)))

/-- The double geometric series `∑ⱼ ∑ₘ ρ 2^{-(j+1)} 2^{-(m+1)} = ρ` in `ℝ≥0∞`. -/
theorem tsum_tsum_ofReal_geometric (ρ : ℝ) (hρ : 0 ≤ ρ) :
    ∑' j : ℕ, ∑' m : ℕ, ENNReal.ofReal (ρ * (1 / 2 / 2 ^ j) * (1 / 2 / 2 ^ m)) =
      ENNReal.ofReal ρ := by
  have h1 : ∀ j : ℕ, ∑' m : ℕ, ENNReal.ofReal (ρ * (1 / 2 / 2 ^ j) * (1 / 2 / 2 ^ m)) =
      ENNReal.ofReal (ρ * (1 / 2 / 2 ^ j)) := by
    intro j
    rw [← ENNReal.ofReal_tsum_of_nonneg (fun m => by positivity)
      ((summable_geometric_two' 1).mul_left _)]
    congr 1
    rw [tsum_mul_left, tsum_geometric_two']
    ring
  simp_rw [h1]
  rw [← ENNReal.ofReal_tsum_of_nonneg (fun j => by positivity)
    ((summable_geometric_two' 1).mul_left _)]
  congr 1
  rw [tsum_mul_left, tsum_geometric_two']
  ring

/-- **A compact set carrying all the conditional laws up to `ρ`.**  There is a compact
`K ⊆ C(ℝ≥0, ℝ)` such that for every `n`, `P (G δₙ ∩ {Y ∉ K}) ≤ ρ P (G δₙ)`. -/
theorem exists_compact_measure_stayAbove_seq [IsProbabilityMeasure P] (hB : IsBrownianReal B P)
    (hm : ∀ t, Measurable (B t)) (hcont : ∀ ω, Continuous fun s => B s ω) {c : ℝ} (hc : 0 < c)
    {δ : ℕ → ℝ} (hδ0 : Tendsto δ atTop (𝓝 0)) (hδ : ∀ n, 0 < δ n) {ρ : ℝ} (hρ : 0 < ρ) :
    ∃ K : Set C(ℝ≥0, ℝ), IsCompact K ∧ ∀ n,
      P ({ω | ∀ t : ℝ≥0, -δ n < B t ω + c * t} ∩
          {ω | pathMap (fun t ω => B t ω + c * t) (continuous_drift hcont c) ω ∉ K}) ≤
        ENNReal.ofReal ρ * P {ω | ∀ t : ℝ≥0, -δ n < B t ω + c * t} := by
  have hex : ∀ j m : ℕ, ∃ η : ℝ≥0, 0 < η ∧ ∀ n,
      P ({ω | ∀ t : ℝ≥0, -δ n < B t ω + c * t} ∩
          {ω | ¬ HasModulus (fun t : ℝ≥0 => B t ω + c * t) (j : ℝ≥0) η (1 / ((m : ℝ) + 1))}) ≤
        ENNReal.ofReal (ρ * (1 / 2 / 2 ^ j) * (1 / 2 / 2 ^ m)) *
          P {ω | ∀ t : ℝ≥0, -δ n < B t ω + c * t} := fun j m =>
    exists_scale_stayAbove_seq hB hm hcont hc hδ0 hδ (j : ℝ≥0) (by positivity) (by positivity)
  choose η hη0 hη using hex
  refine ⟨{f : C(ℝ≥0, ℝ) | (f : ℝ≥0 → ℝ) ∈ modulusSet η}, isCompact_modulusSet hη0, fun n => ?_⟩
  set G : Set Ω := {ω | ∀ t : ℝ≥0, -δ n < B t ω + c * t} with hG
  have hB0 : P {ω | B 0 ω ≠ 0} = 0 := by
    have h0 : ∀ᵐ ω ∂P, B 0 ω = 0 := hB.toIsPreBrownianReal.eval_zero_ae_eq_zero.mono fun ω h => h
    exact h0
  have hsub : G ∩ {ω | pathMap (fun t ω => B t ω + c * t) (continuous_drift hcont c) ω ∉
        {f : C(ℝ≥0, ℝ) | (f : ℝ≥0 → ℝ) ∈ modulusSet η}} ⊆
      (G ∩ {ω | B 0 ω ≠ 0}) ∪ ⋃ j : ℕ, ⋃ m : ℕ, (G ∩
        {ω | ¬ HasModulus (fun t : ℝ≥0 => B t ω + c * t) (j : ℝ≥0) (η j m) (1 / ((m : ℝ) + 1))}) := by
    rintro ω ⟨hωG, hω⟩
    by_cases h0 : B 0 ω = 0
    · right
      have hnot : ¬ ∀ j m : ℕ, HasModulus (fun t : ℝ≥0 => B t ω + c * t) (j : ℝ≥0) (η j m)
          (1 / ((m : ℝ) + 1)) := by
        intro hall
        exact hω ⟨by simp [pathMap, h0], hall⟩
      push Not at hnot
      obtain ⟨j, m, hjm⟩ := hnot
      exact Set.mem_iUnion.2 ⟨j, Set.mem_iUnion.2 ⟨m, hωG, hjm⟩⟩
    · exact Or.inl ⟨hωG, h0⟩
  calc P _ ≤ P ((G ∩ {ω | B 0 ω ≠ 0}) ∪ ⋃ j : ℕ, ⋃ m : ℕ, (G ∩
        {ω | ¬ HasModulus (fun t : ℝ≥0 => B t ω + c * t) (j : ℝ≥0) (η j m)
          (1 / ((m : ℝ) + 1))})) := measure_mono hsub
    _ ≤ P (G ∩ {ω | B 0 ω ≠ 0}) + ∑' j : ℕ, ∑' m : ℕ, P (G ∩
        {ω | ¬ HasModulus (fun t : ℝ≥0 => B t ω + c * t) (j : ℝ≥0) (η j m)
          (1 / ((m : ℝ) + 1))}) := by
        refine (measure_union_le _ _).trans (add_le_add le_rfl ?_)
        refine (measure_iUnion_le _).trans (ENNReal.tsum_le_tsum fun j => ?_)
        exact measure_iUnion_le _
    _ ≤ 0 + ∑' j : ℕ, ∑' m : ℕ, ENNReal.ofReal (ρ * (1 / 2 / 2 ^ j) * (1 / 2 / 2 ^ m)) * P G := by
        refine add_le_add ?_ (ENNReal.tsum_le_tsum fun j => ENNReal.tsum_le_tsum fun m => hη j m n)
        exact ((measure_mono Set.inter_subset_right).trans hB0.le)
    _ = ENNReal.ofReal ρ * P G := by
        rw [zero_add]
        simp_rw [ENNReal.tsum_mul_right]
        rw [tsum_tsum_ofReal_geometric ρ hρ.le]

/-- **Tightness of the conditioned laws.**  For `δₙ > 0` tending to `0`, the laws on
`C(ℝ≥0, ℝ)` of the drifted Brownian motion `B t + c t` under `P (· | B s + c s > -δₙ ∀ s)` form a
tight family of measures. -/
theorem isTightMeasureSet_stayAbove_law [IsProbabilityMeasure P] (hB : IsBrownianReal B P)
    (hm : ∀ t, Measurable (B t)) (hcont : ∀ ω, Continuous fun s => B s ω) {c : ℝ} (hc : 0 < c)
    {δ : ℕ → ℝ} (hδ0 : Tendsto δ atTop (𝓝 0)) (hδ : ∀ n, 0 < δ n) :
    IsTightMeasureSet (Set.range fun n =>
      (ProbabilityTheory.cond P {ω | ∀ t : ℝ≥0, -δ n < B t ω + c * t}).map
        (pathMap (fun t ω => B t ω + c * t) (continuous_drift hcont c))) := by
  rw [isTightMeasureSet_iff_exists_isCompact_measure_compl_le]
  intro ε hε
  obtain ⟨ρ, hρ, hρε⟩ : ∃ ρ : ℝ, 0 < ρ ∧ ENNReal.ofReal ρ ≤ ε := by
    rcases eq_or_ne ε ⊤ with rfl | h
    · exact ⟨1, one_pos, le_top⟩
    · exact ⟨ε.toReal, ENNReal.toReal_pos hε.ne' h, (ENNReal.ofReal_toReal h).le⟩
  obtain ⟨K, hK, hKP⟩ := exists_compact_measure_stayAbove_seq hB hm hcont hc hδ0 hδ hρ
  refine ⟨K, hK, ?_⟩
  rintro _ ⟨n, rfl⟩
  have hmeas : Measurable (pathMap (fun t ω => B t ω + c * t) (continuous_drift hcont c)) :=
    measurable_pathMap _ (fun t => (hm t).add_const _) (continuous_drift hcont c)
  have hKc : MeasurableSet Kᶜ := hK.isClosed.measurableSet.compl
  rw [Measure.map_apply hmeas hKc, cond_apply' (hmeas hKc)]
  by_cases h0 : P {ω | ∀ t : ℝ≥0, -δ n < B t ω + c * t} = 0
  · have : P ({ω | ∀ t : ℝ≥0, -δ n < B t ω + c * t} ∩
        (pathMap (fun t ω => B t ω + c * t) (continuous_drift hcont c)) ⁻¹' Kᶜ) = 0 :=
      measure_mono_null Set.inter_subset_left h0
    rw [this, mul_zero]
    exact zero_le
  · calc (P {ω | ∀ t : ℝ≥0, -δ n < B t ω + c * t})⁻¹ *
          P ({ω | ∀ t : ℝ≥0, -δ n < B t ω + c * t} ∩
            (pathMap (fun t ω => B t ω + c * t) (continuous_drift hcont c)) ⁻¹' Kᶜ)
        ≤ (P {ω | ∀ t : ℝ≥0, -δ n < B t ω + c * t})⁻¹ *
            (ENNReal.ofReal ρ * P {ω | ∀ t : ℝ≥0, -δ n < B t ω + c * t}) :=
          mul_le_mul' le_rfl (hKP n)
      _ = ENNReal.ofReal ρ := by
          rw [mul_comm (ENNReal.ofReal ρ), ← mul_assoc, ENNReal.inv_mul_cancel h0
            (measure_ne_top _ _), one_mul]
      _ ≤ ε := hρε

end Tightness

end LatticeProb
