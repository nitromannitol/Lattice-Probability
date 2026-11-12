/-
Copyright (c) 2026. Released under the Apache 2.0 license.
-/
import Mathlib
import LatticeProb.Prob.BrownianDriftConditionedTight
import LatticeProb.Prob.BrownianDriftConditionedTightFamily
import LatticeProb.Prob.NestedConditioning

/-!
# Cylinder averages of the Brownian motion conditioned to stay above `-δ`

Let `B` be a real Brownian motion with continuous paths, `c > 0`, and
`G_δ = {B t + c t > -δ for all t}`.  This file prepares the proof that, for a bounded
Lipschitz cylinder functional `Φ`, the conditional averages `E[Φ(B) | G_δ]` converge as
`δ → 0+`.

* `LatticeProb.stayAboveHat`: a measurable event almost surely equal to `G_δ` (the event `G_δ`
  itself is an uncountable intersection, and is not known to be measurable).
* `LatticeProb.integral_stayAbove_inter_hitDrift_le`: the real-valued restart identity at the
  hitting time of the level `ε`.
* `LatticeProb.abs_sub_levelShiftPath_le`: on the event that the upper level is reached first by time
  `η`, the path `B` and the restarted path (shifted to start at the level `ε`) are uniformly
  close on `[0, T]` once the drifted motion has a modulus of continuity.
-/

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal

noncomputable section

namespace LatticeProb

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} {B : ℝ≥0 → Ω → ℝ}

/-- A measurable version of the event `{B t + c t > -l for all t}`: the drifted path lies in
`posOn D l` for a countable set `D`. -/
def stayAboveHat (D : Set ℝ≥0) (B : ℝ≥0 → Ω → ℝ) (c l : ℝ) : Set Ω :=
  {ω | (fun t : ℝ≥0 => B t ω + c * (t : ℝ)) ∈ posOn D l}

theorem measurableSet_stayAboveHat (hm : ∀ t, Measurable (B t)) {D : Set ℝ≥0}
    (hD : D.Countable) (c l : ℝ) : MeasurableSet (stayAboveHat D B c l) :=
  (measurable_pi_iff.2 fun t => (hm t).add measurable_const) (measurableSet_posOn hD l)

omit mΩ in
theorem stayAboveHat_mono (D : Set ℝ≥0) (B : ℝ≥0 → Ω → ℝ) (c : ℝ) {l l' : ℝ} (h : l ≤ l') :
    stayAboveHat D B c l ⊆ stayAboveHat D B c l' := by
  intro ω hω
  have hω' : (fun t : ℝ≥0 => B t ω + c * (t : ℝ)) ∈ posOn D l := hω
  obtain ⟨n, hn⟩ := Set.mem_iUnion.1 hω'
  exact Set.mem_iUnion.2 ⟨n, fun q hq => by have := hn q hq; linarith⟩

theorem measure_stayAboveHat [IsProbabilityMeasure P] (hB : IsBrownianReal B P)
    (hm : ∀ t, Measurable (B t)) (hcont : ∀ ω, Continuous fun s => B s ω) {c : ℝ} (hc : 0 < c)
    {l : ℝ} (hl : 0 < l) {D : Set ℝ≥0} (hDd : Dense D) :
    P (stayAboveHat D B c l) = ENNReal.ofReal (1 - Real.exp (-(2 * c * l))) :=
  measure_drift_mem_posOn hB.toIsPreBrownianReal hm hcont hc hl hDd

/-- Up to a null set, `G_l` is the measurable event `stayAboveHat D B c l`. -/
theorem ae_eq_stayAboveHat [IsProbabilityMeasure P] (hB : IsBrownianReal B P)
    (hm : ∀ t, Measurable (B t)) (hcont : ∀ ω, Continuous fun s => B s ω) {c : ℝ} (hc : 0 < c)
    {l : ℝ} (hl : 0 < l) {D : Set ℝ≥0} (hDc : D.Countable) (hDd : Dense D) :
    stayAboveHat D B c l =ᵐ[P] {ω | ∀ t : ℝ≥0, -l < B t ω + c * t} := by
  refine ae_eq_of_subset_of_measure_ge (fun ω hω =>
    forall_gt_of_posOn hDd (continuous_drift hcont c ω) hω) ?_
    (measurableSet_stayAboveHat hm hDc c l).nullMeasurableSet (measure_ne_top P _)
  rw [measure_forall_drift_gt hB.toIsPreBrownianReal hm hcont hc hl,
    measure_stayAboveHat hB hm hcont hc hl hDd]

/-- The path `ε + z - c · id`: a drifted increment `z`, seen again as a path of the motion
without drift started at the level `ε`. -/
def levelShiftPath (ε c : ℝ) (z : ℝ≥0 → ℝ) : ℝ≥0 → ℝ := fun u => ε + z u - c * (u : ℝ)

theorem measurable_levelShiftPath (ε c : ℝ) : Measurable (levelShiftPath ε c) :=
  measurable_pi_iff.2 fun u => by
    show Measurable fun z : ℝ≥0 → ℝ => ε + z u - c * (u : ℝ)
    have hu : Measurable fun z : ℝ≥0 → ℝ => z u := measurable_pi_apply u
    exact (hu.const_add ε).sub_const _

omit mΩ in
theorem levelShiftPath_drift (ε c : ℝ) (ω : Ω) :
    levelShiftPath ε c (fun t : ℝ≥0 => B t ω + c * (t : ℝ)) = fun u => ε + B u ω := by
  funext u; unfold levelShiftPath; ring

/-- **Restart identity for real functionals.**  For a measurable `Φ ≥ 0` on path space,
`∫_{G_δ ∩ {τ_ε ≤ η}} Φ (ε + increments of the drifted motion after τ_ε - c · id)` equals
`P(upper level first, by time η) * ∫_{G_{ε+δ}} Φ (ε + B)`. -/
theorem integral_stayAbove_inter_hitDrift_le [IsProbabilityMeasure P] (hB : IsBrownianReal B P)
    (hm : ∀ t, Measurable (B t)) (hcont : ∀ ω, Continuous fun s => B s ω) {c : ℝ} (hc : 0 < c)
    {ε δ : ℝ} (hε : 0 < ε) (hδ : 0 < δ) (η : ℝ≥0) {Φ : (ℝ≥0 → ℝ) → ℝ} (hΦ : Measurable Φ)
    (h0 : ∀ g, 0 ≤ Φ g) :
    ∫ ω in {ω | ∀ t : ℝ≥0, -δ < B t ω + c * t} ∩ {ω | hitDrift B c ε ω ≤ (η : ℝ≥0∞)},
        Φ (levelShiftPath ε c (driftIncr B c (hitDriftTrunc B c ε η) ω)) ∂P =
      (P (topFirst B c ε δ ∩ {ω | hitDrift B c ε ω ≤ (η : ℝ≥0∞)})).toReal *
        ∫ ω in {ω | ∀ t : ℝ≥0, -(ε + δ) < B t ω + c * t}, Φ (fun u => ε + B u ω) ∂P := by
  have hτ := isStoppingTime_hitDriftTrunc hm hcont c ε η
  have hincr := measurable_driftIncr hm hcont c (measurable_of_isStoppingTime_nnreal hm hτ)
  have hY : Measurable (fun ω (t : ℝ≥0) => B t ω + c * (t : ℝ)) :=
    measurable_pi_iff.2 fun t => (hm t).add measurable_const
  have key := lintegral_stayAbove_inter_hitDrift_le hB hm hcont hc hε hδ η
    (Φ := fun z => ENNReal.ofReal (Φ (levelShiftPath ε c z)))
    (ENNReal.measurable_ofReal.comp (hΦ.comp (measurable_levelShiftPath ε c)))
  simp only [levelShiftPath_drift] at key
  have hm1 : Measurable fun ω => Φ (levelShiftPath ε c (driftIncr B c (hitDriftTrunc B c ε η) ω)) :=
    hΦ.comp ((measurable_levelShiftPath ε c).comp hincr)
  have hm2 : Measurable fun ω => Φ (fun u => ε + B u ω) :=
    hΦ.comp (measurable_pi_iff.2 fun u => measurable_const.add (hm u))
  rw [integral_eq_lintegral_of_nonneg_ae (Filter.Eventually.of_forall fun ω => h0 _)
      hm1.aestronglyMeasurable,
    integral_eq_lintegral_of_nonneg_ae (Filter.Eventually.of_forall fun ω => h0 _)
      hm2.aestronglyMeasurable, key, ENNReal.toReal_mul]

omit mΩ in
/-- **Pathwise comparison after the hitting time.**  If the upper level `ε` is reached first by
time `η ≤ min η₁ 1` and the drifted path has modulus `w` at scale `η₁` on `[0, T + 1]`, then `B`
and the restarted path `levelShiftPath ε c (driftIncr ..)` differ by at most `w` on `[0, T]`. -/
theorem abs_sub_levelShiftPath_le (hcont : ∀ ω, Continuous fun s => B s ω) (c : ℝ) {ε δ : ℝ}
    (hε : 0 < ε) (hδ : 0 < δ) (η : ℝ≥0) {ω : Ω} (h0 : B 0 ω = 0)
    (hω : ω ∈ topFirst B c ε δ ∩ {ω | hitDrift B c ε ω ≤ (η : ℝ≥0∞)}) {T η₁ : ℝ≥0} {w : ℝ}
    (hη : η ≤ η₁) (hη1 : η ≤ 1)
    (hmod : HasModulus (fun t : ℝ≥0 => B t ω + c * t) (T + 1) η₁ w) {t : ℝ≥0} (ht : t ≤ T) :
    |B t ω - levelShiftPath ε c (driftIncr B c (hitDriftTrunc B c ε η) ω) t| ≤ w := by
  set σ := hitDriftTrunc B c ε η ω with hσ
  have hv := value_at_hitDriftTrunc hcont c hε hδ η h0 hω
  have hσle : σ ≤ η := by
    have h1 : (σ : ℝ≥0∞) ≤ η := by
      rw [hσ, coe_hitDriftTrunc_of_le B c ε η ω hω.2]; exact hω.2
    exact_mod_cast h1
  have hs : σ + t ≤ T + 1 := by
    have := add_le_add (hσle.trans hη1) ht
    rwa [add_comm 1 T] at this
  have habs : |(t : ℝ) - ((σ + t : ℝ≥0) : ℝ)| ≤ η₁ := by
    have : (t : ℝ) - ((σ + t : ℝ≥0) : ℝ) = -(σ : ℝ) := by push_cast; ring
    rw [this, abs_neg, abs_of_nonneg (NNReal.coe_nonneg σ)]
    exact_mod_cast hσle.trans hη
  have h := hmod t (σ + t) (ht.trans (le_self_add)) hs habs
  have e : B t ω - levelShiftPath ε c (driftIncr B c (hitDriftTrunc B c ε η) ω) t =
      (B t ω + c * t) - (B (σ + t) ω + c * ((σ + t : ℝ≥0) : ℝ)) := by
    simp only [levelShiftPath, driftIncr]; push_cast; linarith [hv]
  rw [e]; exact h


/-- The event `{B t + c t > -l for all t}`. -/
abbrev stayAboveSet (B : ℝ≥0 → Ω → ℝ) (c l : ℝ) : Set Ω := {ω | ∀ t : ℝ≥0, -l < B t ω + c * t}

/-- The average of `Ψ` over the event `{B t + c t > -l for all t}`. -/
def stayAboveAvg (P : Measure Ω) (B : ℝ≥0 → Ω → ℝ) (c l : ℝ) (Ψ : Ω → ℝ) : ℝ :=
  (∫ ω in stayAboveSet B c l, Ψ ω ∂P) / (P (stayAboveSet B c l)).toReal

section Helpers

variable {α : Type*} [MeasurableSpace α] {μ : Measure α}

theorem integrable_of_unit [IsFiniteMeasure μ] {f : α → ℝ} (hf : Measurable f)
    (h0 : ∀ x, 0 ≤ f x) (h1 : ∀ x, f x ≤ 1) : Integrable f μ :=
  Integrable.mono' (integrable_const (1 : ℝ)) hf.aestronglyMeasurable
    (Filter.Eventually.of_forall fun x => by
      rw [Real.norm_eq_abs, abs_of_nonneg (h0 x)]; exact h1 x)

theorem setIntegral_mem_Icc [IsFiniteMeasure μ] (s : Set α) {f : α → ℝ} (hf : Measurable f)
    (h0 : ∀ x, 0 ≤ f x) (h1 : ∀ x, f x ≤ 1) :
    0 ≤ ∫ x in s, f x ∂μ ∧ ∫ x in s, f x ∂μ ≤ μ.real s := by
  refine ⟨integral_nonneg h0, ?_⟩
  have h := integral_mono (integrable_of_unit (μ := μ.restrict s) hf h0 h1)
    (integrable_const (1 : ℝ)) (fun x => h1 x)
  simpa [Measure.real] using h

theorem abs_setIntegral_sub_mul_le [IsFiniteMeasure μ] (s : Set α) {f : α → ℝ}
    (hf : Measurable f) (h0 : ∀ x, 0 ≤ f x) (h1 : ∀ x, f x ≤ 1) {a : ℝ} (ha0 : 0 ≤ a)
    (ha1 : a ≤ 1) : |∫ x in s, f x ∂μ - μ.real s * a| ≤ μ.real s := by
  obtain ⟨h2, h3⟩ := setIntegral_mem_Icc (μ := μ) s hf h0 h1
  have h4 : 0 ≤ μ.real s := measureReal_nonneg
  rw [abs_le]
  constructor <;> nlinarith [mul_nonneg h4 ha0, mul_le_mul_of_nonneg_left ha1 h4]

theorem abs_setIntegral_sub_le [IsFiniteMeasure μ] {S U : Set α} (hU : MeasurableSet U)
    {f g : α → ℝ} (hfi : Integrable f μ) (hgi : Integrable g μ) {b : ℝ}
    (hbound : ∀ᵐ x ∂μ.restrict S, |f x - g x| ≤ b + U.indicator (fun _ => (1 : ℝ)) x) :
    |∫ x in S, f x ∂μ - ∫ x in S, g x ∂μ| ≤ b * μ.real S + μ.real U := by
  rw [← integral_sub hfi.integrableOn hgi.integrableOn]
  have hind : Integrable (U.indicator fun _ => (1 : ℝ)) (μ.restrict S) :=
    (integrable_const (1 : ℝ)).indicator hU
  have hG : Integrable (fun x => b + U.indicator (fun _ => (1 : ℝ)) x) (μ.restrict S) :=
    (integrable_const b).add hind
  have h1 : ‖∫ x in S, (f x - g x) ∂μ‖ ≤
      ∫ x, (b + U.indicator (fun _ => (1 : ℝ)) x) ∂(μ.restrict S) :=
    norm_integral_le_of_norm_le hG (hbound.mono fun x hx => by simpa [Real.norm_eq_abs] using hx)
  rw [Real.norm_eq_abs, integral_add (integrable_const b) hind, integral_const,
    integral_indicator_const _ hU] at h1
  have h2 : (μ.restrict S).real U ≤ μ.real U := by
    unfold Measure.real
    refine ENNReal.toReal_mono (measure_ne_top μ U) ?_
    rw [Measure.restrict_apply hU]
    exact measure_mono Set.inter_subset_left
  have h3 : (μ.restrict S).real Set.univ = μ.real S := by simp [Measure.real]
  rw [h3, smul_eq_mul, smul_eq_mul, mul_one] at h1
  linarith [mul_comm b (μ.real S)]

end Helpers


section Approx

variable [IsProbabilityMeasure P]

/-- **Comparison on the event that the level `ε` is reached by time `η`.**  On
`G_δ ∩ {τ_ε ≤ η}` the average of a bounded Lipschitz cylinder functional of `B` is within
`K w + ρ` (times the mass of `G_δ`) of the average of the same functional of the restarted path,
which is `ε + B` conditioned on `G_{ε+δ}`. -/
theorem abs_integral_part1_le (hB : IsBrownianReal B P) (hm : ∀ t, Measurable (B t))
    (hcont : ∀ ω, Continuous fun s => B s ω) {c : ℝ} (hc : 0 < c) {ε δ : ℝ} (hε : 0 < ε)
    (hδ : 0 < δ) {η η₁ T : ℝ≥0} (hη1 : η ≤ 1) (hηη : η ≤ η₁) {Φ : (ℝ≥0 → ℝ) → ℝ}
    (hΦ : Measurable Φ) (h0 : ∀ g, 0 ≤ Φ g) (h1 : ∀ g, Φ g ≤ 1) {I : Set ℝ≥0}
    (hI : ∀ t ∈ I, t ≤ T) {K : ℝ} (hK : 0 ≤ K)
    (hlip : ∀ g g' : ℝ≥0 → ℝ, ∀ r : ℝ, 0 ≤ r → (∀ t ∈ I, |g t - g' t| ≤ r) →
      |Φ g - Φ g'| ≤ K * r)
    {w ρ : ℝ} (hw : 0 ≤ w) (hρ : 0 ≤ ρ)
    (hbad : P (stayAboveSet B c δ ∩
        {ω | ¬ HasModulus (fun t : ℝ≥0 => B t ω + c * t) (T + 1) η₁ w}) ≤
      ENNReal.ofReal ρ * P (stayAboveSet B c δ)) :
    |(∫ ω in stayAboveSet B c δ ∩ {ω | hitDrift B c ε ω ≤ (η : ℝ≥0∞)},
        Φ (fun t => B t ω) ∂P) -
      (P (stayAboveSet B c δ ∩ {ω | hitDrift B c ε ω ≤ (η : ℝ≥0∞)})).toReal *
        stayAboveAvg P B c (ε + δ) (fun ω => Φ (fun u => ε + B u ω))| ≤
      K * w * (P (stayAboveSet B c δ ∩ {ω | hitDrift B c ε ω ≤ (η : ℝ≥0∞)})).toReal +
        ρ * (P (stayAboveSet B c δ)).toReal := by
  obtain ⟨D, hDc, hDd⟩ := TopologicalSpace.exists_countable_dense ℝ≥0
  have hl : 0 < ε + δ := add_pos hε hδ
  have hτ := isStoppingTime_hitDriftTrunc hm hcont c ε η
  have hincr := measurable_driftIncr hm hcont c (measurable_of_isStoppingTime_nnreal hm hτ)
  have hτm : MeasurableSet {ω | hitDrift B c ε ω ≤ (η : ℝ≥0∞)} :=
    measurableSet_le
      (measurable_of_isStoppingTime_enn (isStoppingTime_hitDrift_brownian hm hcont c ε))
      measurable_const
  have hEm : MeasurableSet (topFirst B c ε δ ∩ {ω | hitDrift B c ε ω ≤ (η : ℝ≥0∞)}) :=
    (measurableSet_topFirst hm hcont c ε δ).inter hτm
  set S := stayAboveSet B c δ ∩ {ω | hitDrift B c ε ω ≤ (η : ℝ≥0∞)} with hSdef
  set Ev := topFirst B c ε δ ∩ {ω | hitDrift B c ε ω ≤ (η : ℝ≥0∞)} with hEvdef
  set Zf : Ω → ℝ≥0 → ℝ := fun ω => levelShiftPath ε c (driftIncr B c (hitDriftTrunc B c ε η) ω)
    with hZf
  have hZm : Measurable Zf := (measurable_levelShiftPath ε c).comp hincr
  set S' := Ev ∩ {ω | driftIncr B c (hitDriftTrunc B c ε η) ω ∈ posOn D (ε + δ)} with hS'def
  have hS'm : MeasurableSet S' := hEm.inter (hincr (measurableSet_posOn hDc (ε + δ)))
  have hSS' : S =ᵐ[P] S' := ae_eq_stayAbove_inter_hitDrift_le hB hm hcont hc hε hδ η hDc hDd
  -- the value of the restarted average
  have hL2 := integral_stayAbove_inter_hitDrift_le hB hm hcont hc hε hδ η hΦ h0
  have hPS := measure_stayAbove_inter_hitDrift_le hB hm hcont hc hε hδ η
  have hPG2 := measure_forall_drift_gt hB.toIsPreBrownianReal hm hcont hc hl
  have hp0 : 0 < 1 - Real.exp (-(2 * c * (ε + δ))) := by
    have : Real.exp (-(2 * c * (ε + δ))) < 1 :=
      Real.exp_lt_one_iff.2 (by nlinarith [mul_pos hc hl])
    linarith
  have hPS' : (P S).toReal = (P Ev).toReal * (1 - Real.exp (-(2 * c * (ε + δ)))) := by
    rw [hPS, ENNReal.toReal_mul, ENNReal.toReal_ofReal hp0.le]
  have hPG2' : (P (stayAboveSet B c (ε + δ))).toReal = 1 - Real.exp (-(2 * c * (ε + δ))) := by
    rw [hPG2, ENNReal.toReal_ofReal hp0.le]
  have hmain : (P S).toReal * stayAboveAvg P B c (ε + δ) (fun ω => Φ (fun u => ε + B u ω)) =
      ∫ ω in S, Φ (Zf ω) ∂P := by
    rw [show ∫ ω in S, Φ (Zf ω) ∂P = _ from hL2]
    unfold stayAboveAvg
    rw [hPS', hPG2']
    field_simp
    ring
  -- the bound
  set X := {ω : Ω | ¬ HasModulus (fun t : ℝ≥0 => B t ω + c * t) (T + 1) η₁ w} with hX
  set U := toMeasurable P (stayAboveSet B c δ ∩ X) with hUdef
  have hU : MeasurableSet U := measurableSet_toMeasurable _ _
  have hPU : P U = P (stayAboveSet B c δ ∩ X) := measure_toMeasurable _
  have hfm : Measurable fun ω => Φ (fun t => B t ω) := hΦ.comp (measurable_pi_iff.2 hm)
  have h0f : ∀ ω, 0 ≤ Φ (fun t => B t ω) := fun ω => h0 _
  have h1f : ∀ ω, Φ (fun t => B t ω) ≤ 1 := fun ω => h1 _
  have hgm : Measurable fun ω => Φ (Zf ω) := hΦ.comp hZm
  have hB0 : ∀ᵐ ω ∂P, B 0 ω = 0 := hB.toIsPreBrownianReal.eval_zero_ae_eq_zero.mono fun ω h => h
  have hmem := hSS'.mem_iff
  have hbound : ∀ᵐ ω ∂P.restrict S',
      |Φ (fun t => B t ω) - Φ (Zf ω)| ≤ K * w + U.indicator (fun _ => (1 : ℝ)) ω := by
    filter_upwards [ae_restrict_mem hS'm, ae_restrict_of_ae hB0, ae_restrict_of_ae hmem]
      with ω hω hb0 hm'
    have hSω : ω ∈ S := hm'.2 hω
    have hEω : ω ∈ Ev := hω.1
    by_cases hmod : HasModulus (fun t : ℝ≥0 => B t ω + c * t) (T + 1) η₁ w
    · have := hlip (fun t => B t ω) (Zf ω) w hw (fun t ht =>
        abs_sub_levelShiftPath_le hcont c hε hδ η hb0 hEω hηη hη1 hmod (hI t ht))
      exact this.trans (le_add_of_nonneg_right
        (Set.indicator_nonneg (fun _ _ => zero_le_one) ω))
    · have hωU : ω ∈ U := subset_toMeasurable _ _ ⟨hSω.1, hmod⟩
      rw [Set.indicator_of_mem hωU]
      have ha := h0 (fun t => B t ω)
      have hb := h1 (fun t => B t ω)
      have hc' := h0 (Zf ω)
      have hd := h1 (Zf ω)
      calc |Φ (fun t => B t ω) - Φ (Zf ω)| ≤ 1 := by
            rw [abs_le]; constructor <;> linarith
        _ ≤ K * w + 1 := by nlinarith [mul_nonneg hK hw]
  have hbd := abs_setIntegral_sub_le (μ := P) (S := S') hU
    (integrable_of_unit hfm h0f h1f) (integrable_of_unit hgm (fun ω => h0 _) (fun ω => h1 _))
    hbound
  have e1 : ∫ ω in S, Φ (fun t => B t ω) ∂P = ∫ ω in S', Φ (fun t => B t ω) ∂P :=
    setIntegral_congr_set hSS'
  have e2 : ∫ ω in S, Φ (Zf ω) ∂P = ∫ ω in S', Φ (Zf ω) ∂P := setIntegral_congr_set hSS'
  have e3 : P.real S' = (P S).toReal := by
    rw [Measure.real, measure_congr hSS'.symm]
  have e4 : P.real U ≤ ρ * (P (stayAboveSet B c δ)).toReal := by
    rw [Measure.real, hPU]
    calc (P (stayAboveSet B c δ ∩ X)).toReal
        ≤ (ENNReal.ofReal ρ * P (stayAboveSet B c δ)).toReal :=
          ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofReal_ne_top (measure_ne_top _ _)) hbad
      _ = ρ * (P (stayAboveSet B c δ)).toReal := by
          rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal hρ]
  rw [hmain, e1]
  rw [← e2] at hbd
  rw [e3] at hbd
  linarith


/-- **The conditioned average at depth `δ` is close to the restarted one.**  For a measurable
`Φ` with values in `[0, 1]` that is `K`-Lipschitz for the supremum distance of the values on a
set `I ⊆ [0, T]`, if the conditional probability that the drifted motion has no modulus `w` at
scale `η₁` on `[0, T + 1]` is at most `ρ`, then, for `η ≤ min η₁ 1`,
`|E[Φ(B) | G_δ] - E[Φ(ε + B) | G_{ε+δ}]| ≤ K w + ρ + (ε + δ)² / η`. -/
theorem abs_stayAboveAvg_sub_le (hB : IsBrownianReal B P) (hm : ∀ t, Measurable (B t))
    (hcont : ∀ ω, Continuous fun s => B s ω) {c : ℝ} (hc : 0 < c) {ε δ : ℝ} (hε : 0 < ε)
    (hδ : 0 < δ) {η η₁ T : ℝ≥0} (hη0 : 0 < η) (hη1 : η ≤ 1) (hηη : η ≤ η₁)
    {Φ : (ℝ≥0 → ℝ) → ℝ} (hΦ : Measurable Φ) (h0 : ∀ g, 0 ≤ Φ g) (h1 : ∀ g, Φ g ≤ 1)
    {I : Set ℝ≥0} (hI : ∀ t ∈ I, t ≤ T) {K : ℝ} (hK : 0 ≤ K)
    (hlip : ∀ g g' : ℝ≥0 → ℝ, ∀ r : ℝ, 0 ≤ r → (∀ t ∈ I, |g t - g' t| ≤ r) →
      |Φ g - Φ g'| ≤ K * r)
    {w ρ : ℝ} (hw : 0 ≤ w) (hρ : 0 ≤ ρ)
    (hbad : P (stayAboveSet B c δ ∩
        {ω | ¬ HasModulus (fun t : ℝ≥0 => B t ω + c * t) (T + 1) η₁ w}) ≤
      ENNReal.ofReal ρ * P (stayAboveSet B c δ)) :
    |stayAboveAvg P B c δ (fun ω => Φ (fun t => B t ω)) -
        stayAboveAvg P B c (ε + δ) (fun ω => Φ (fun u => ε + B u ω))| ≤
      K * w + ρ + (ε + δ) ^ 2 / η := by
  have hl : 0 < ε + δ := add_pos hε hδ
  have hη0' : (0 : ℝ) < η := by exact_mod_cast hη0
  have hτm : MeasurableSet {ω | hitDrift B c ε ω ≤ (η : ℝ≥0∞)} :=
    measurableSet_le
      (measurable_of_isStoppingTime_enn (isStoppingTime_hitDrift_brownian hm hcont c ε))
      measurable_const
  have hp1 := abs_integral_part1_le hB hm hcont hc hε hδ hη1 hηη hΦ h0 h1 hI hK hlip hw hρ hbad
  set Gd := stayAboveSet B c δ with hGd
  set Tm := {ω : Ω | hitDrift B c ε ω ≤ (η : ℝ≥0∞)} with hTm
  set f : Ω → ℝ := fun ω => Φ (fun t => B t ω) with hf
  set A' := stayAboveAvg P B c (ε + δ) (fun ω => Φ (fun u => ε + B u ω)) with hA'
  have hfm : Measurable f := hΦ.comp (measurable_pi_iff.2 hm)
  have h0f : ∀ ω, 0 ≤ f ω := fun ω => h0 _
  have h1f : ∀ ω, f ω ≤ 1 := fun ω => h1 _
  have hG2pos : 0 < (P (stayAboveSet B c (ε + δ))).toReal :=
    ENNReal.toReal_pos (measure_stayAbove_pos hB hm hcont hc hl).ne' (measure_ne_top _ _)
  have hA'0 : 0 ≤ A' ∧ A' ≤ 1 := by
    have hfm2 : Measurable fun ω => Φ (fun u => ε + B u ω) :=
      hΦ.comp (measurable_pi_iff.2 fun u => measurable_const.add (hm u))
    obtain ⟨h2, h3⟩ := setIntegral_mem_Icc (μ := P) (stayAboveSet B c (ε + δ)) hfm2
      (fun ω => h0 _) (fun ω => h1 _)
    exact ⟨div_nonneg h2 hG2pos.le, (div_le_one hG2pos).2 h3⟩
  have hm0 : 0 < (P Gd).toReal :=
    ENNReal.toReal_pos (measure_stayAbove_pos hB hm hcont hc hδ).ne' (measure_ne_top _ _)
  have hint : Integrable f P := integrable_of_unit hfm h0f h1f
  have hsplit := integral_inter_add_sdiff (μ := P) (s := Gd) (t := Tm) hτm hint.integrableOn
  have hmsplit : (P (Gd ∩ Tm)).toReal + (P (Gd \ Tm)).toReal = (P Gd).toReal := by
    rw [← ENNReal.toReal_add (measure_ne_top _ _) (measure_ne_top _ _),
      measure_inter_add_sdiff Gd hτm]
  have hp2 := abs_setIntegral_sub_mul_le (μ := P) (Gd \ Tm) hfm h0f h1f hA'0.1 hA'0.2
  have hp2' : |(∫ ω in Gd \ Tm, f ω ∂P) - (P (Gd \ Tm)).toReal * A'| ≤ (P (Gd \ Tm)).toReal :=
    hp2
  have hp3 : (η : ℝ) * (P (Gd \ Tm)).toReal ≤ (ε + δ) ^ 2 * (P Gd).toReal := by
    have hset : Gd \ Tm = Gd ∩ {ω | (η : ℝ≥0∞) < hitDrift B c ε ω} := by
      ext ω; simp [Gd, Tm, not_le]
    have := mul_measure_stayAbove_inter_lt_hitDrift_le hB hm hcont hc hε hδ η
    have h' := ENNReal.toReal_mono
      (ENNReal.mul_ne_top ENNReal.ofReal_ne_top (measure_ne_top _ _)) this
    rw [ENNReal.toReal_mul, ENNReal.toReal_mul, ENNReal.toReal_ofReal (sq_nonneg _),
      ENNReal.coe_toReal, ← hset] at h'
    exact h'
  have hm1 : (P (Gd ∩ Tm)).toReal ≤ (P Gd).toReal := by
    rw [← hmsplit]; linarith [ENNReal.toReal_nonneg (a := P (Gd \ Tm))]
  have hm2 : (P (Gd \ Tm)).toReal ≤ (ε + δ) ^ 2 / η * (P Gd).toReal := by
    rw [div_mul_eq_mul_div, le_div_iff₀ hη0']; linarith
  have hKw : 0 ≤ K * w := mul_nonneg hK hw
  have key : |(∫ ω in Gd, f ω ∂P) - (P Gd).toReal * A'| ≤
      (K * w + ρ + (ε + δ) ^ 2 / η) * (P Gd).toReal := by
    have e : (∫ ω in Gd, f ω ∂P) - (P Gd).toReal * A' =
        ((∫ ω in Gd ∩ Tm, f ω ∂P) - (P (Gd ∩ Tm)).toReal * A') +
          ((∫ ω in Gd \ Tm, f ω ∂P) - (P (Gd \ Tm)).toReal * A') := by
      rw [← hsplit, ← hmsplit]; ring
    rw [e]
    refine (abs_add_le _ _).trans ?_
    nlinarith [hp1, hp2', hm1, hm2, mul_le_mul_of_nonneg_left hm1 hKw]
  have hrw : stayAboveAvg P B c δ (fun ω => Φ (fun t => B t ω)) - A' =
      ((∫ ω in Gd, f ω ∂P) - (P Gd).toReal * A') / (P Gd).toReal := by
    show (∫ ω in Gd, f ω ∂P) / (P Gd).toReal - A' = _
    field_simp
  rw [hrw, abs_div, abs_of_pos hm0, div_le_iff₀ hm0]
  exact key


/-- Real estimate behind the slow variation of the conditioned averages in the depth. -/
theorem ratio_le {c ε l l' : ℝ} (hc : 0 < c) (hε : 0 < ε) (hl : ε ≤ l) (hll' : l ≤ l') :
    ((1 - Real.exp (-(2 * c * l'))) - (1 - Real.exp (-(2 * c * l)))) /
        (1 - Real.exp (-(2 * c * l'))) ≤ (1 + 2 * c * ε) * (l' - l) / ε := by
  have hx : 0 < 2 * c * ε := by positivity
  have hl'pos : 0 < l' := hε.trans_le (hl.trans hll')
  have he1 : Real.exp (-(2 * c * l)) ≤ 1 := Real.exp_le_one_iff.2 (by nlinarith)
  have he0 : 0 < Real.exp (-(2 * c * l)) := Real.exp_pos _
  have hN : Real.exp (-(2 * c * l)) - Real.exp (-(2 * c * l')) ≤ 2 * c * (l' - l) := by
    have h1 := Real.add_one_le_exp (-(2 * c * (l' - l)))
    have h2 : Real.exp (-(2 * c * l')) =
        Real.exp (-(2 * c * l)) * Real.exp (-(2 * c * (l' - l))) := by
      rw [← Real.exp_add]; congr 1; ring
    have h3 : 0 ≤ 2 * c * (l' - l) := by nlinarith
    nlinarith [mul_le_mul_of_nonneg_left h1 he0.le, mul_le_mul_of_nonneg_right he1 h3]
  have hD : 2 * c * ε ≤ (1 - Real.exp (-(2 * c * l'))) * (1 + 2 * c * ε) := by
    have h1 : Real.exp (-(2 * c * l')) ≤ Real.exp (-(2 * c * ε)) :=
      Real.exp_le_exp.2 (by nlinarith)
    have h2 := Real.add_one_le_exp (2 * c * ε)
    have h3 : Real.exp (-(2 * c * ε)) * Real.exp (2 * c * ε) = 1 := by
      rw [← Real.exp_add]; simp
    have h4 : Real.exp (-(2 * c * ε)) * (2 * c * ε + 1) ≤ 1 :=
      calc _ ≤ Real.exp (-(2 * c * ε)) * Real.exp (2 * c * ε) :=
            mul_le_mul_of_nonneg_left h2 (Real.exp_pos _).le
        _ = 1 := h3
    nlinarith [mul_le_mul_of_nonneg_right h1 (by positivity : (0 : ℝ) ≤ 1 + 2 * c * ε)]
  have hDpos : 0 < 1 - Real.exp (-(2 * c * l')) := by
    have : Real.exp (-(2 * c * l')) < 1 :=
      Real.exp_lt_one_iff.2 (by nlinarith [mul_pos hc hl'pos])
    linarith
  rw [div_le_div_iff₀ hDpos hε]
  nlinarith [mul_le_mul_of_nonneg_right hN hε.le, mul_le_mul_of_nonneg_right hD (sub_nonneg.2 hll')]

/-- **The restarted average varies slowly with the depth.**  For `0 < ε ≤ l ≤ l'` and a
measurable `Ψ` with values in `[0, 1]`,
`|E[Ψ | G_l] - E[Ψ | G_{l'}]| ≤ (1 + 2 c ε) (l' - l) / ε`. -/
theorem abs_stayAboveAvg_sub_stayAboveAvg_le (hB : IsBrownianReal B P)
    (hm : ∀ t, Measurable (B t)) (hcont : ∀ ω, Continuous fun s => B s ω) {c : ℝ} (hc : 0 < c)
    {ε l l' : ℝ} (hε : 0 < ε) (hl : ε ≤ l) (hll' : l ≤ l') {Ψ : Ω → ℝ} (hΨ : Measurable Ψ)
    (h0 : ∀ ω, 0 ≤ Ψ ω) (h1 : ∀ ω, Ψ ω ≤ 1) :
    |stayAboveAvg P B c l Ψ - stayAboveAvg P B c l' Ψ| ≤ (1 + 2 * c * ε) * (l' - l) / ε := by
  obtain ⟨D, hDc, hDd⟩ := TopologicalSpace.exists_countable_dense ℝ≥0
  have hlpos : 0 < l := hε.trans_le hl
  have hl'pos : 0 < l' := hlpos.trans_le hll'
  have hae := ae_eq_stayAboveHat hB hm hcont hc hlpos hDc hDd
  have hae' := ae_eq_stayAboveHat hB hm hcont hc hl'pos hDc hDd
  have e1 : stayAboveAvg P B c l Ψ =
      (∫ ω in stayAboveHat D B c l, Ψ ω ∂P) / P.real (stayAboveHat D B c l) := by
    unfold stayAboveAvg
    rw [setIntegral_congr_set hae, Measure.real, measure_congr hae]
  have e2 : stayAboveAvg P B c l' Ψ =
      (∫ ω in stayAboveHat D B c l', Ψ ω ∂P) / P.real (stayAboveHat D B c l') := by
    unfold stayAboveAvg
    rw [setIntegral_congr_set hae', Measure.real, measure_congr hae']
  have hnn : ∀ x : ℝ, 0 < x → 0 ≤ 1 - Real.exp (-(2 * c * x)) := fun x hx =>
    sub_nonneg.2 (Real.exp_le_one_iff.2 (by nlinarith [mul_pos hc hx]))
  have hr1 : P.real (stayAboveHat D B c l) = 1 - Real.exp (-(2 * c * l)) := by
    rw [Measure.real, measure_stayAboveHat hB hm hcont hc hlpos hDd,
      ENNReal.toReal_ofReal (hnn l hlpos)]
  have hr2 : P.real (stayAboveHat D B c l') = 1 - Real.exp (-(2 * c * l')) := by
    rw [Measure.real, measure_stayAboveHat hB hm hcont hc hl'pos hDd,
      ENNReal.toReal_ofReal (hnn l' hl'pos)]
  have hpos : P (stayAboveHat D B c l) ≠ 0 := by
    rw [measure_stayAboveHat hB hm hcont hc hlpos hDd]
    refine (ENNReal.ofReal_pos.2 (sub_pos.2 ?_)).ne'
    exact Real.exp_lt_one_iff.2 (by nlinarith [mul_pos hc hlpos])
  have hnest := abs_setAverage_sub_setAverage_le P (measurableSet_stayAboveHat hm hDc c l)
    (measurableSet_stayAboveHat hm hDc c l') (stayAboveHat_mono D B c hll') hpos hΨ h0 h1
  rw [e1, e2]
  refine hnest.trans ?_
  rw [hr1, hr2]
  exact ratio_le hc hε hl hll'


/-- **Cauchy estimate for the cylinder averages.**  For a measurable `Φ` with values in `[0, 1]`
that is `K`-Lipschitz for the supremum distance of the values on a set `I ⊆ [0, T]`, and every
`θ > 0`, there is `δ₀ > 0` such that the averages `E[Φ(B) | G_δ]` for `0 < δ ≤ δ' ≤ δ₀` differ by
at most `θ / 2`. -/
theorem exists_delta_abs_stayAboveAvg_sub_le (hB : IsBrownianReal B P)
    (hm : ∀ t, Measurable (B t)) (hcont : ∀ ω, Continuous fun s => B s ω) {c : ℝ} (hc : 0 < c)
    {Φ : (ℝ≥0 → ℝ) → ℝ} (hΦ : Measurable Φ) (h0 : ∀ g, 0 ≤ Φ g) (h1 : ∀ g, Φ g ≤ 1)
    {I : Set ℝ≥0} {T : ℝ≥0} (hI : ∀ t ∈ I, t ≤ T) {K : ℝ} (hK : 0 ≤ K)
    (hlip : ∀ g g' : ℝ≥0 → ℝ, ∀ r : ℝ, 0 ≤ r → (∀ t ∈ I, |g t - g' t| ≤ r) →
      |Φ g - Φ g'| ≤ K * r) {θ : ℝ} (hθ : 0 < θ) :
    ∃ δ₀ : ℝ, 0 < δ₀ ∧ ∀ δ δ' : ℝ, 0 < δ → δ ≤ δ' → δ' ≤ δ₀ →
      |stayAboveAvg P B c δ (fun ω => Φ (fun t => B t ω)) -
        stayAboveAvg P B c δ' (fun ω => Φ (fun t => B t ω))| ≤ θ / 2 := by
  have hK1 : 0 < K + 1 := by linarith
  set w : ℝ := θ / (16 * (K + 1)) with hw
  have hwpos : 0 < w := by positivity
  have hKw : K * w ≤ θ / 16 := by
    rw [hw, ← mul_div_assoc, div_le_div_iff₀ (by positivity) (by norm_num)]; nlinarith
  obtain ⟨ε₀, η₁, hε₀, hη₁, hunif⟩ :=
    exists_uniform_modulus hB hm hcont hc (T + 1) hwpos (ρ := θ / 16) (by positivity)
  set η : ℝ≥0 := min η₁ 1 with hηdef
  have hη0 : 0 < η := lt_min hη₁ one_pos
  have hηη : η ≤ η₁ := min_le_left _ _
  have hη1 : η ≤ 1 := min_le_right _ _
  have hη0' : (0 : ℝ) < η := by exact_mod_cast hη0
  set ε : ℝ := min (min ε₀ 1) (min (η * θ / 64) (θ / (8 * (1 + 2 * c)))) with hεdef
  have hεpos : 0 < ε := lt_min (lt_min hε₀ one_pos) (lt_min (by positivity) (by positivity))
  have hε1 : ε ≤ 1 := (min_le_left _ _).trans (min_le_right _ _)
  have hεε₀ : ε ≤ ε₀ := (min_le_left _ _).trans (min_le_left _ _)
  have hε2 : ε ≤ η * θ / 64 := (min_le_right _ _).trans (min_le_left _ _)
  have hε3 : ε ≤ θ / (8 * (1 + 2 * c)) := (min_le_right _ _).trans (min_le_right _ _)
  have hε3' : (1 + 2 * c) * ε ≤ θ / 8 := by
    rw [le_div_iff₀ (by positivity)] at hε3; nlinarith
  have hΨ : Measurable fun ω => Φ (fun u => ε + B u ω) :=
    hΦ.comp (measurable_pi_iff.2 fun u => measurable_const.add (hm u))
  refine ⟨ε ^ 2, by positivity, fun δ δ' hδ hδδ' hδ' => ?_⟩
  have hδ'pos : 0 < δ' := hδ.trans_le hδδ'
  have hδ'ε : δ' ≤ ε := by nlinarith
  have hsq : ∀ x : ℝ, 0 < x → x ≤ ε ^ 2 → (ε + x) ^ 2 / η ≤ θ / 16 := by
    intro x hx hxε
    have hxε' : x ≤ ε := by nlinarith
    rw [div_le_iff₀ hη0']
    nlinarith [mul_le_mul_of_nonneg_left hε2 hεpos.le,
      mul_le_mul_of_nonneg_right hε1 (by positivity : (0 : ℝ) ≤ η * θ)]
  have est : ∀ x : ℝ, 0 < x → x ≤ ε ^ 2 →
      |stayAboveAvg P B c x (fun ω => Φ (fun t => B t ω)) -
        stayAboveAvg P B c (ε + x) (fun ω => Φ (fun u => ε + B u ω))| ≤ 3 * θ / 16 := by
    intro x hx hxε
    have hxε' : x ≤ ε := by nlinarith
    have := abs_stayAboveAvg_sub_le hB hm hcont hc hεpos hx hη0 hη1 hηη hΦ h0 h1 hI hK hlip
      hwpos.le (ρ := θ / 16) (by positivity) (hunif x hx (hxε'.trans hεε₀))
    linarith [hsq x hx hxε]
  have hnest := abs_stayAboveAvg_sub_stayAboveAvg_le hB hm hcont hc hεpos (l := ε + δ)
    (l' := ε + δ') (by linarith) (by linarith) hΨ (fun ω => h0 _) (fun ω => h1 _)
  have hnest' : (1 + 2 * c * ε) * (ε + δ' - (ε + δ)) / ε ≤ θ / 8 := by
    rw [div_le_iff₀ hεpos]
    nlinarith [mul_le_mul_of_nonneg_left hε1 (by positivity : (0 : ℝ) ≤ c),
      mul_nonneg hδ.le hεpos.le, mul_nonneg hεpos.le hεpos.le]
  have e1 := est δ hδ (hδδ'.trans hδ')
  have e2 := est δ' hδ'pos hδ'
  calc _ ≤ |stayAboveAvg P B c δ (fun ω => Φ (fun t => B t ω)) -
          stayAboveAvg P B c (ε + δ) (fun ω => Φ (fun u => ε + B u ω))| +
        |stayAboveAvg P B c (ε + δ) (fun ω => Φ (fun u => ε + B u ω)) -
          stayAboveAvg P B c δ' (fun ω => Φ (fun t => B t ω))| := abs_sub_le _ _ _
    _ ≤ _ := by
      have h3 := abs_sub_le (stayAboveAvg P B c (ε + δ) (fun ω => Φ (fun u => ε + B u ω)))
        (stayAboveAvg P B c (ε + δ') (fun ω => Φ (fun u => ε + B u ω)))
        (stayAboveAvg P B c δ' (fun ω => Φ (fun t => B t ω)))
      rw [abs_sub_comm (stayAboveAvg P B c (ε + δ') _)] at h3
      linarith

/-- **Existence of the limit of the cylinder averages.**  For `Φ` as above, the conditional
averages `E[Φ(B) | G_δ]` converge as `δ → 0+`. -/
theorem exists_tendsto_stayAboveAvg (hB : IsBrownianReal B P) (hm : ∀ t, Measurable (B t))
    (hcont : ∀ ω, Continuous fun s => B s ω) {c : ℝ} (hc : 0 < c) {Φ : (ℝ≥0 → ℝ) → ℝ}
    (hΦ : Measurable Φ) (h0 : ∀ g, 0 ≤ Φ g) (h1 : ∀ g, Φ g ≤ 1) {I : Set ℝ≥0} {T : ℝ≥0}
    (hI : ∀ t ∈ I, t ≤ T) {K : ℝ} (hK : 0 ≤ K)
    (hlip : ∀ g g' : ℝ≥0 → ℝ, ∀ r : ℝ, 0 ≤ r → (∀ t ∈ I, |g t - g' t| ≤ r) →
      |Φ g - Φ g'| ≤ K * r) :
    ∃ a : ℝ, Tendsto (fun δ : ℝ => stayAboveAvg P B c δ (fun ω => Φ (fun t => B t ω)))
      (𝓝[>] (0 : ℝ)) (𝓝 a) := by
  rw [← cauchy_map_iff_exists_tendsto, Metric.cauchy_iff]
  refine ⟨inferInstance, fun θ hθ => ?_⟩
  obtain ⟨δ₀, hδ₀, hcore⟩ :=
    exists_delta_abs_stayAboveAvg_sub_le hB hm hcont hc hΦ h0 h1 hI hK hlip hθ
  refine ⟨(fun δ : ℝ => stayAboveAvg P B c δ (fun ω => Φ (fun t => B t ω))) '' Set.Ioc 0 δ₀,
    Filter.image_mem_map (Ioc_mem_nhdsGT hδ₀), ?_⟩
  rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
  rw [Real.dist_eq]
  rcases le_total x y with h | h
  · have := hcore x y hx.1 h hy.2; linarith
  · rw [abs_sub_comm]; have := hcore y x hy.1 h hx.2; linarith

end Approx

end LatticeProb

end
