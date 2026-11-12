/-
Copyright (c) 2026. All rights reserved.
-/
import Mathlib
import LatticeProb.Prob.BrownianDriftConditionedTightness
import LatticeProb.Prob.BrownianDriftSurvival

/-!
# Tightness of the conditioned laws over the whole family `δ > 0`

Let `B` be a real Brownian motion with continuous paths, `c > 0`, `Y t = B t + c t` and
`G δ = {Y t > -δ for all t}`.  The laws on `C(ℝ≥0, ℝ)` of `Y` (and of `B`) under `P (· | G δ)`,
`δ > 0`, form a tight family: the family is indexed by the continuum `δ > 0`, not by a sequence.

* `LatticeProb.measure_stayAbove_pos`: `P (G δ) > 0`, by the gambler's ruin formula.
* `LatticeProb.exists_scale_stayAbove`: one scale `η` with `P (G δ ∩ {no modulus}) ≤ ρ P (G δ)` for
  all `δ > 0` (uniform estimate for `δ ≤ ε`; for `δ > ε` the bound `P (G δ) ≥ P (G ε) > 0`).
* `LatticeProb.exists_compact_measure_stayAbove`: a compact `K ⊆ C(ℝ≥0, ℝ)` with
  `P (G δ ∩ {Y ∉ K}) ≤ ρ P (G δ)` for all `δ > 0`.
* `LatticeProb.isTightMeasureSet_stayAbove_law_family`, `isTightMeasureSet_stayAbove_law_base`:
  tightness of the laws of `Y`, respectively of `B`.
-/

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal

noncomputable section

namespace LatticeProb

section TightnessFamily

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} {B : ℝ≥0 → Ω → ℝ}

/-- The event `{B t + c t > -δ for all t}` has positive probability when `c, δ > 0`. -/
theorem measure_stayAbove_pos (hB : IsBrownianReal B P) (hm : ∀ t, Measurable (B t))
    (hcont : ∀ ω, Continuous fun s => B s ω) {c : ℝ} (hc : 0 < c) {δ : ℝ} (hδ : 0 < δ) :
    0 < P {ω | ∀ t : ℝ≥0, -δ < B t ω + c * t} := by
  rw [measure_forall_drift_gt hB.toIsPreBrownianReal hm hcont hc hδ]
  refine ENNReal.ofReal_pos.2 (sub_pos.2 ?_)
  have h2 : 0 < 2 * c * δ := by positivity
  have := Real.exp_lt_exp.2 (show -(2 * c * δ) < 0 by linarith)
  rwa [Real.exp_zero] at this

omit mΩ in
/-- The events `{B t + c t > -δ for all t}` increase with `δ`. -/
theorem stayAbove_mono (c : ℝ) {δ δ' : ℝ} (h : δ ≤ δ') :
    {ω : Ω | ∀ t : ℝ≥0, -δ < B t ω + c * t} ⊆ {ω | ∀ t : ℝ≥0, -δ' < B t ω + c * t} :=
  fun _ hω t => lt_of_le_of_lt (neg_le_neg h) (hω t)

/-- **One scale for all `δ > 0`.**  There is a scale `η` such that, for every `δ > 0`, the
conditional probability of `Y` having no modulus `w` at scale `η` on `[0, T]` given `G δ` is at
most `ρ`.  For `δ ≤ ε` this is the uniform estimate; for `δ > ε` the unconditional probability of
no modulus is at most `ρ P (G ε) ≤ ρ P (G δ)`. -/
theorem exists_scale_stayAbove [IsProbabilityMeasure P] (hB : IsBrownianReal B P)
    (hm : ∀ t, Measurable (B t)) (hcont : ∀ ω, Continuous fun s => B s ω) {c : ℝ} (hc : 0 < c)
    (T : ℝ≥0) {w ρ : ℝ} (hw : 0 < w) (hρ : 0 < ρ) :
    ∃ η : ℝ≥0, 0 < η ∧ ∀ δ : ℝ, 0 < δ → P ({ω | ∀ t : ℝ≥0, -δ < B t ω + c * t} ∩
          {ω | ¬ HasModulus (fun t : ℝ≥0 => B t ω + c * t) T η w}) ≤
        ENNReal.ofReal ρ * P {ω | ∀ t : ℝ≥0, -δ < B t ω + c * t} := by
  obtain ⟨ε, η₁, hε, hη₁, hunif⟩ := exists_uniform_modulus hB hm hcont hc T hw hρ
  have hr : 0 < ENNReal.ofReal ρ * P {ω | ∀ t : ℝ≥0, -ε < B t ω + c * t} :=
    ENNReal.mul_pos (by simpa using hρ) (measure_stayAbove_pos hB hm hcont hc hε).ne'
  obtain ⟨η₂, hη₂, hlt⟩ := exists_scale_measure_not_hasModulus_le (P := P) hm hcont c T hw hr
  refine ⟨min η₁ η₂, lt_min hη₁ hη₂, fun δ hδ => ?_⟩
  by_cases hδε : δ ≤ ε
  · exact (measure_mono (inter_not_hasModulus_mono _ (fun ω t => B t ω + c * t)
      (min_le_left _ _))).trans (hunif δ hδ hδε)
  · have hεδ : ε ≤ δ := (not_le.1 hδε).le
    calc P ({ω | ∀ t : ℝ≥0, -δ < B t ω + c * t} ∩
          {ω | ¬ HasModulus (fun t : ℝ≥0 => B t ω + c * t) T (min η₁ η₂) w})
        ≤ P {ω | ¬ HasModulus (fun t : ℝ≥0 => B t ω + c * t) T (min η₁ η₂) w} :=
          measure_mono Set.inter_subset_right
      _ ≤ P {ω | ¬ HasModulus (fun t : ℝ≥0 => B t ω + c * t) T η₂ w} := by
          refine measure_mono fun ω hω => ?_
          exact fun h => hω (hasModulus_mono_scale (min_le_right _ _) h)
      _ ≤ ENNReal.ofReal ρ * P {ω | ∀ t : ℝ≥0, -ε < B t ω + c * t} := hlt
      _ ≤ ENNReal.ofReal ρ * P {ω | ∀ t : ℝ≥0, -δ < B t ω + c * t} :=
          mul_le_mul' le_rfl (measure_mono (stayAbove_mono c hεδ))

/-- **A compact set carrying all the conditional laws up to `ρ`.**  There is a compact
`K ⊆ C(ℝ≥0, ℝ)` such that for every `δ > 0`, `P (G δ ∩ {Y ∉ K}) ≤ ρ P (G δ)`. -/
theorem exists_compact_measure_stayAbove [IsProbabilityMeasure P] (hB : IsBrownianReal B P)
    (hm : ∀ t, Measurable (B t)) (hcont : ∀ ω, Continuous fun s => B s ω) {c : ℝ} (hc : 0 < c)
    {ρ : ℝ} (hρ : 0 < ρ) :
    ∃ K : Set C(ℝ≥0, ℝ), IsCompact K ∧ ∀ δ : ℝ, 0 < δ →
      P ({ω | ∀ t : ℝ≥0, -δ < B t ω + c * t} ∩
          {ω | pathMap (fun t ω => B t ω + c * t) (continuous_drift hcont c) ω ∉ K}) ≤
        ENNReal.ofReal ρ * P {ω | ∀ t : ℝ≥0, -δ < B t ω + c * t} := by
  have hex : ∀ j m : ℕ, ∃ η : ℝ≥0, 0 < η ∧ ∀ δ : ℝ, 0 < δ →
      P ({ω | ∀ t : ℝ≥0, -δ < B t ω + c * t} ∩
          {ω | ¬ HasModulus (fun t : ℝ≥0 => B t ω + c * t) (j : ℝ≥0) η (1 / ((m : ℝ) + 1))}) ≤
        ENNReal.ofReal (ρ * (1 / 2 / 2 ^ j) * (1 / 2 / 2 ^ m)) *
          P {ω | ∀ t : ℝ≥0, -δ < B t ω + c * t} := fun j m =>
    exists_scale_stayAbove hB hm hcont hc (j : ℝ≥0) (by positivity) (by positivity)
  choose η hη0 hη using hex
  refine ⟨{f : C(ℝ≥0, ℝ) | (f : ℝ≥0 → ℝ) ∈ modulusSet η}, isCompact_modulusSet hη0,
    fun δ hδ => ?_⟩
  set G : Set Ω := {ω | ∀ t : ℝ≥0, -δ < B t ω + c * t} with hG
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
        refine add_le_add ?_
          (ENNReal.tsum_le_tsum fun j => ENNReal.tsum_le_tsum fun m => hη j m δ hδ)
        exact ((measure_mono Set.inter_subset_right).trans hB0.le)
    _ = ENNReal.ofReal ρ * P G := by
        rw [zero_add]
        simp_rw [ENNReal.tsum_mul_right]
        rw [tsum_tsum_ofReal_geometric ρ hρ.le]

/-- **Tightness of the conditioned laws, whole family.**  The laws on `C(ℝ≥0, ℝ)` of the drifted
Brownian motion `B t + c t` under `P (· | B s + c s > -δ ∀ s)`, `δ > 0`, form a tight family. -/
theorem isTightMeasureSet_stayAbove_law_family [IsProbabilityMeasure P] (hB : IsBrownianReal B P)
    (hm : ∀ t, Measurable (B t)) (hcont : ∀ ω, Continuous fun s => B s ω) {c : ℝ} (hc : 0 < c) :
    IsTightMeasureSet ((fun δ : ℝ =>
      (ProbabilityTheory.cond P {ω | ∀ t : ℝ≥0, -δ < B t ω + c * t}).map
        (pathMap (fun t ω => B t ω + c * t) (continuous_drift hcont c))) '' Set.Ioi 0) := by
  rw [isTightMeasureSet_iff_exists_isCompact_measure_compl_le]
  intro ε hε
  obtain ⟨ρ, hρ, hρε⟩ : ∃ ρ : ℝ, 0 < ρ ∧ ENNReal.ofReal ρ ≤ ε := by
    rcases eq_or_ne ε ⊤ with rfl | h
    · exact ⟨1, one_pos, le_top⟩
    · exact ⟨ε.toReal, ENNReal.toReal_pos hε.ne' h, (ENNReal.ofReal_toReal h).le⟩
  obtain ⟨K, hK, hKP⟩ := exists_compact_measure_stayAbove hB hm hcont hc hρ
  refine ⟨K, hK, ?_⟩
  rintro _ ⟨δ, hδ, rfl⟩
  have hmeas : Measurable (pathMap (fun t ω => B t ω + c * t) (continuous_drift hcont c)) :=
    measurable_pathMap _ (fun t => (hm t).add_const _) (continuous_drift hcont c)
  have hKc : MeasurableSet Kᶜ := hK.isClosed.measurableSet.compl
  have hpos : P {ω | ∀ t : ℝ≥0, -δ < B t ω + c * t} ≠ 0 :=
    (measure_stayAbove_pos hB hm hcont hc hδ).ne'
  rw [Measure.map_apply hmeas hKc, cond_apply' (hmeas hKc)]
  calc (P {ω | ∀ t : ℝ≥0, -δ < B t ω + c * t})⁻¹ *
        P ({ω | ∀ t : ℝ≥0, -δ < B t ω + c * t} ∩
          (pathMap (fun t ω => B t ω + c * t) (continuous_drift hcont c)) ⁻¹' Kᶜ)
      ≤ (P {ω | ∀ t : ℝ≥0, -δ < B t ω + c * t})⁻¹ *
          (ENNReal.ofReal ρ * P {ω | ∀ t : ℝ≥0, -δ < B t ω + c * t}) :=
        mul_le_mul' le_rfl (hKP δ hδ)
    _ = ENNReal.ofReal ρ := by
        rw [mul_comm (ENNReal.ofReal ρ), ← mul_assoc, ENNReal.inv_mul_cancel hpos
          (measure_ne_top _ _), one_mul]
    _ ≤ ε := hρε

/-- Subtracting the drift `t ↦ c t` is a continuous self-map of `C(ℝ≥0, ℝ)`. -/
def subDrift (c : ℝ) (f : C(ℝ≥0, ℝ)) : C(ℝ≥0, ℝ) :=
  f + ⟨fun t : ℝ≥0 => -(c * (t : ℝ)), by fun_prop⟩

theorem continuous_subDrift (c : ℝ) : Continuous (subDrift c) :=
  continuous_id.add continuous_const

omit mΩ in
theorem subDrift_pathMap (hcont : ∀ ω, Continuous fun s => B s ω) (c : ℝ) (ω : Ω) :
    subDrift c (pathMap (fun t ω => B t ω + c * t) (continuous_drift hcont c) ω) =
      pathMap B hcont ω := by
  ext t
  simp [subDrift]

/-- **Tightness of the conditioned laws of `B`, whole family.**  The laws on `C(ℝ≥0, ℝ)` of the
Brownian motion `B` under `P (· | B s + c s > -δ ∀ s)`, `δ > 0`, form a tight family. -/
theorem isTightMeasureSet_stayAbove_law_base [IsProbabilityMeasure P] (hB : IsBrownianReal B P)
    (hm : ∀ t, Measurable (B t)) (hcont : ∀ ω, Continuous fun s => B s ω) {c : ℝ} (hc : 0 < c) :
    IsTightMeasureSet ((fun δ : ℝ =>
      (ProbabilityTheory.cond P {ω | ∀ t : ℝ≥0, -δ < B t ω + c * t}).map
        (pathMap B hcont)) '' Set.Ioi 0) := by
  have h := (isTightMeasureSet_stayAbove_law_family hB hm hcont hc).map (continuous_subDrift c)
  have hmeas : Measurable (pathMap (fun t ω => B t ω + c * t) (continuous_drift hcont c)) :=
    measurable_pathMap _ (fun t => (hm t).add_const _) (continuous_drift hcont c)
  have hsub : Measurable (subDrift c) := (continuous_subDrift c).measurable
  convert h using 1
  simp only [Set.image_image]
  refine Set.image_congr fun δ _ => ?_
  rw [Measure.map_map hsub hmeas]
  congr 1
  funext ω
  exact (subDrift_pathMap hcont c ω).symm

end TightnessFamily

end LatticeProb
