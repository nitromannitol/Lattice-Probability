/-
Copyright (c) 2026. Released under the Apache 2.0 license.
-/
import Mathlib
import LatticeProb.Prob.BrownianDriftConditionedShift

/-!
# Restarting a Brownian motion with drift at the time it reaches a level

Let `B` be a real Brownian motion with continuous paths, `c` a drift and `τ` a finite stopping
time of the natural filtration of `B`.  The increments of `B + c ·` after `τ`,
`driftIncr B c τ ω t = (B (τ + t) + c (τ + t)) - (B τ + c τ)`, form a measurable map into path
space, and restricted to an event of the past at `τ` their law is `P E` times the law of
`B + c ·` (a restatement of the strong Markov property as an identity of measures, and of lower
integrals).

For the event `{upper level `ε` reached before the lower level `-δ`, and reached by time `η`}` the
file shows that it lies in the past of the hitting time truncated at `η`.

## Main results

* `LatticeProb.measurable_driftIncr`: measurability of the restarted increments.
* `LatticeProb.restrict_map_driftIncr`, `LatticeProb.lintegral_restrict_driftIncr`: the law of the
  restarted increments on an event of the past, as a measure identity and for measurable
  nonnegative path functionals.
* `LatticeProb.measurableSet_topFirst_inter_le`: the event that the upper level is reached first,
  and by time `η`, lies in the past at the hitting time truncated at `η`.
* `LatticeProb.posOn`, `LatticeProb.clOn`: measurable inner and outer approximations of the event of
  staying above a level, through a countable dense set of times.
* `LatticeProb.ae_eq_stayAbove_inter_hitDrift_le`: up to a null set, `{B t + c t > -δ for all t}`
  with level `ε` reached by time `η` is the event that `ε` is reached first, by time `η`, and the
  increments after the hitting time stay above `-(ε + δ)`.
* `LatticeProb.lintegral_stayAbove_inter_hitDrift_le`, `LatticeProb.measure_stayAbove_inter_hitDrift_le`:
  consequently, under the conditioning on staying above `-δ` and reaching `ε` by time `η`, the
  path after the hitting time has the law of `B + c ·` conditioned to stay above `-(ε + δ)`, and
  the conditioned event has probability `P(ε first, by time η) (1 - e^{-2c(ε+δ)})`.
-/

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal

noncomputable section

namespace LatticeProb

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} {B : ℝ≥0 → Ω → ℝ}

/-- The increments of the drifted motion `B s + c s` after the time `τ ω`. -/
def driftIncr (B : ℝ≥0 → Ω → ℝ) (c : ℝ) (τ : Ω → ℝ≥0) (ω : Ω) : ℝ≥0 → ℝ :=
  fun t => (B (τ ω + t) ω + c * ((τ ω + t : ℝ≥0) : ℝ)) - (B (τ ω) ω + c * (τ ω : ℝ))

/-- The restarted increments after a measurable time are a measurable map into path space. -/
theorem measurable_driftIncr (hm : ∀ t, Measurable (B t))
    (hcont : ∀ ω, Continuous fun t => B t ω) (c : ℝ) {τ : Ω → ℝ≥0} (hτ : Measurable τ) :
    Measurable (driftIncr B c τ) := by
  have hjoint : Measurable (Function.uncurry B) :=
    measurable_uncurry_of_continuous_of_measurable hcont hm
  refine measurable_pi_iff.2 fun t => ?_
  have h1 : Measurable fun ω => B (τ ω + t) ω :=
    hjoint.comp ((hτ.add_const t).prodMk measurable_id)
  have h2 : Measurable fun ω => B (τ ω) ω := hjoint.comp (hτ.prodMk measurable_id)
  have h3 : Measurable fun ω => ((τ ω : ℝ≥0) : ℝ) := measurable_coe_nnreal_real.comp hτ
  have h4 : Measurable fun ω => (((τ ω + t : ℝ≥0)) : ℝ) :=
    measurable_coe_nnreal_real.comp (hτ.add_const t)
  exact (h1.add (h4.const_mul c)).sub (h2.add (h3.const_mul c))

/-- A finite stopping time of the natural filtration of the lift of `B` is measurable. -/
theorem measurable_of_isStoppingTime_nnreal (hm : ∀ t, Measurable (B t)) {τ : Ω → ℝ≥0}
    (hτ : IsStoppingTime (natFiltration (liftOne B) (stronglyMeasurable_liftOne hm))
      fun ω => (τ ω : ℝ≥0∞)) : Measurable τ :=
  measurable_coe_nnreal_ennreal_iff.mp (measurable_of_isStoppingTime_enn hτ)

/-- **The restarted increments on an event of the past, as a measure.**  Restricted to an event
`E` of the past at a finite stopping time, the law of the restarted increments of `B + c ·` is
`P E` times the law of `B + c ·`. -/
theorem restrict_map_driftIncr [IsProbabilityMeasure P] (hB : IsBrownianReal B P)
    (hm : ∀ t, Measurable (B t)) (hcont : ∀ ω, Continuous fun t => B t ω) (c : ℝ)
    (τ : Ω → ℝ≥0)
    (hτ : IsStoppingTime (natFiltration (liftOne B) (stronglyMeasurable_liftOne hm))
      fun ω => (τ ω : ℝ≥0∞))
    {E : Set Ω} (hE : MeasurableSet[hτ.measurableSpace] E) :
    (P.restrict E).map (driftIncr B c τ) =
      P E • P.map (fun ω (t : ℝ≥0) => B t ω + c * (t : ℝ)) := by
  have hincr := measurable_driftIncr hm hcont c (measurable_of_isStoppingTime_nnreal hm hτ)
  have hY : Measurable (fun ω (t : ℝ≥0) => B t ω + c * (t : ℝ)) :=
    measurable_pi_iff.2 fun t => (hm t).add measurable_const
  ext Γ hΓ
  rw [Measure.map_apply hincr hΓ, Measure.restrict_apply (hincr hΓ), Measure.smul_apply,
    Measure.map_apply hY hΓ, smul_eq_mul, Set.inter_comm]
  exact restart_drift hB hm hcont c τ hτ E hE Γ hΓ

/-- **The restarted increments on an event of the past, for path functionals.**  For a measurable
nonnegative path functional `Φ`, `∫⁻_E Φ(increments after τ) = P E * ∫⁻ Φ(B + c ·)`. -/
theorem lintegral_restrict_driftIncr [IsProbabilityMeasure P] (hB : IsBrownianReal B P)
    (hm : ∀ t, Measurable (B t)) (hcont : ∀ ω, Continuous fun t => B t ω) (c : ℝ)
    (τ : Ω → ℝ≥0)
    (hτ : IsStoppingTime (natFiltration (liftOne B) (stronglyMeasurable_liftOne hm))
      fun ω => (τ ω : ℝ≥0∞))
    {E : Set Ω} (hE : MeasurableSet[hτ.measurableSpace] E)
    {Φ : (ℝ≥0 → ℝ) → ℝ≥0∞} (hΦ : Measurable Φ) :
    ∫⁻ ω in E, Φ (driftIncr B c τ ω) ∂P =
      P E * ∫⁻ ω, Φ (fun t : ℝ≥0 => B t ω + c * (t : ℝ)) ∂P := by
  have hincr := measurable_driftIncr hm hcont c (measurable_of_isStoppingTime_nnreal hm hτ)
  have hY : Measurable (fun ω (t : ℝ≥0) => B t ω + c * (t : ℝ)) :=
    measurable_pi_iff.2 fun t => (hm t).add measurable_const
  rw [← lintegral_map hΦ hincr, restrict_map_driftIncr hB hm hcont c τ hτ hE,
    lintegral_smul_measure, lintegral_map hΦ hY, smul_eq_mul]

/-! ### The top-first event lies in the past at the truncated hitting time -/

theorem brownianFiltration_le_natFiltration_liftOne (hm : ∀ t, Measurable (B t)) (t : ℝ≥0) :
    brownianFiltration B hm t ≤ natFiltration (liftOne B) (stronglyMeasurable_liftOne hm) t := by
  rw [brownianFiltration, Filtration.natural_eq_comap,
    natFiltration_eq_comap (liftOne B) (stronglyMeasurable_liftOne hm) t]
  exact comap_le_comap_liftOne t

/-- The first time `B s + c s ≤ -b` is a stopping time of the natural filtration of the lift. -/
theorem isStoppingTime_hitDrift_neg_natFiltration (hm : ∀ t, Measurable (B t))
    (hcont : ∀ ω, Continuous fun s => B s ω) (c b : ℝ) :
    IsStoppingTime (natFiltration (liftOne B) (stronglyMeasurable_liftOne hm))
      (hitDrift (fun t ω => -B t ω) (-c) b) := fun t =>
  brownianFiltration_le_natFiltration_liftOne hm t _
    (isStoppingTime_hitDrift_neg_brownian hm hcont c b t)

theorem measurableSpace_congr {f : Filtration ℝ≥0 mΩ} {τ π : Ω → WithTop ℝ≥0}
    (hτ : IsStoppingTime f τ) (hπ : IsStoppingTime f π) (h : τ = π) :
    hτ.measurableSpace = hπ.measurableSpace := by
  subst h
  rfl

/-- The event that the upper level `ε` is reached strictly before the lower level `-δ`, and by
time `η`, lies in the past at the hitting time of `ε` truncated at `η`. -/
theorem measurableSet_topFirst_inter_le (hm : ∀ t, Measurable (B t))
    (hcont : ∀ ω, Continuous fun s => B s ω) (c ε δ : ℝ) (η : ℝ≥0) :
    MeasurableSet[(isStoppingTime_hitDriftTrunc hm hcont c ε η).measurableSpace]
      (topFirst B c ε δ ∩ {ω | hitDrift B c ε ω ≤ (η : ℝ≥0∞)}) := by
  have hτ := isStoppingTime_hitDrift hm hcont c ε
  have hσ := isStoppingTime_hitDrift_neg_natFiltration hm hcont c δ
  have h1 : MeasurableSet[hτ.measurableSpace] (topFirst B c ε δ) := by
    have := (IsStoppingTime.measurableSet_stopping_time_le hσ hτ).compl
    convert this using 1
    ext ω
    exact (not_le (α := ℝ≥0∞)).symm
  have h2 : MeasurableSet[hτ.measurableSpace] {ω | hitDrift B c ε ω ≤ (η : ℝ≥0∞)} :=
    hτ.measurableSet_le' η
  have h3 := (IsStoppingTime.measurableSet_inter_le_const_iff hτ (topFirst B c ε δ) η).1
    (h1.inter h2)
  have hfun : (fun ω => ((hitDriftTrunc B c ε η ω : ℝ≥0) : ℝ≥0∞)) =
      fun ω => min (hitDrift B c ε ω) (η : ℝ≥0∞) := by
    funext ω
    exact coe_hitDriftTrunc B c ε η ω
  rw [measurableSpace_congr (isStoppingTime_hitDriftTrunc hm hcont c ε η) (hτ.min_const (i := η))
    hfun]
  exact h3

/-! ### Measurable approximations of the event of staying above a level -/

/-- Paths that stay, on the set `D`, at or above a level strictly greater than `-l`. -/
def posOn (D : Set ℝ≥0) (l : ℝ) : Set (ℝ≥0 → ℝ) :=
  ⋃ n : ℕ, {g | ∀ q ∈ D, -l + 1 / ((n : ℝ) + 1) ≤ g q}

/-- Paths that stay, on the set `D`, at or above the level `-l`. -/
def clOn (D : Set ℝ≥0) (l : ℝ) : Set (ℝ≥0 → ℝ) := {g | ∀ q ∈ D, -l ≤ g q}

theorem measurableSet_posOn {D : Set ℝ≥0} (hD : D.Countable) (l : ℝ) :
    MeasurableSet (posOn D l) := by
  refine MeasurableSet.iUnion fun n => ?_
  have : {g : ℝ≥0 → ℝ | ∀ q ∈ D, -l + 1 / ((n : ℝ) + 1) ≤ g q} =
      ⋂ q ∈ D, {g : ℝ≥0 → ℝ | -l + 1 / ((n : ℝ) + 1) ≤ g q} := by
    ext g; simp
  rw [this]
  exact MeasurableSet.biInter hD fun q _ =>
    measurableSet_le measurable_const (measurable_pi_apply q)

theorem measurableSet_clOn {D : Set ℝ≥0} (hD : D.Countable) (l : ℝ) :
    MeasurableSet (clOn D l) := by
  have : clOn D l = ⋂ q ∈ D, {g : ℝ≥0 → ℝ | -l ≤ g q} := by
    ext g; simp [clOn]
  rw [this]
  exact MeasurableSet.biInter hD fun q _ =>
    measurableSet_le measurable_const (measurable_pi_apply q)

theorem forall_ge_of_clOn {D : Set ℝ≥0} (hDd : Dense D) {g : ℝ≥0 → ℝ} (hg : Continuous g)
    {l : ℝ} (h : g ∈ clOn D l) : ∀ t, -l ≤ g t := by
  intro t
  have hclosed : IsClosed {t : ℝ≥0 | -l ≤ g t} := isClosed_le continuous_const hg
  have hsub : D ⊆ {t : ℝ≥0 | -l ≤ g t} := fun q hq => h q hq
  have := hclosed.closure_subset_iff.mpr hsub
  rw [hDd.closure_eq] at this
  exact this (Set.mem_univ t)

theorem forall_gt_of_posOn {D : Set ℝ≥0} (hDd : Dense D) {g : ℝ≥0 → ℝ} (hg : Continuous g)
    {l : ℝ} (h : g ∈ posOn D l) : ∀ t, -l < g t := by
  obtain ⟨n, hn⟩ := Set.mem_iUnion.1 h
  have h1 := forall_ge_of_clOn hDd hg (l := l - 1 / ((n : ℝ) + 1)) (fun q hq => by
    have := hn q hq
    linarith)
  intro t
  have := h1 t
  have hpos : 0 < 1 / ((n : ℝ) + 1) := by positivity
  linarith

omit mΩ in
theorem continuous_drift (hcont : ∀ ω, Continuous fun s => B s ω) (c : ℝ) (ω : Ω) :
    Continuous fun t : ℝ≥0 => B t ω + c * (t : ℝ) :=
  (hcont ω).add (continuous_const.mul NNReal.continuous_coe)

/-- The measurable event `posOn` has the probability of staying above `-l` forever. -/
theorem measure_drift_mem_posOn (hB : IsPreBrownianReal B P) (hm : ∀ t, Measurable (B t))
    (hcont : ∀ ω, Continuous fun s => B s ω) {c : ℝ} (hc : 0 < c) {l : ℝ} (hl : 0 < l)
    {D : Set ℝ≥0} (hDd : Dense D) :
    P {ω | (fun t : ℝ≥0 => B t ω + c * (t : ℝ)) ∈ posOn D l} =
      ENNReal.ofReal (1 - Real.exp (-(2 * c * l))) := by
  refine le_antisymm ?_ ?_
  · refine le_trans (measure_mono fun ω hω => ?_) (measure_forall_drift_gt_le hB hm hc hl)
    exact forall_gt_of_posOn hDd (continuous_drift hcont c ω) hω
  · have hlim : Tendsto (fun n : ℕ => l + -(1 / ((n : ℝ) + 1))) atTop (𝓝 l) := by
      have := (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).neg
      simpa using (tendsto_const_nhds (x := l)).add this
    have hcontf : Continuous (fun u : ℝ => 1 - Real.exp (-(2 * c * u))) := by fun_prop
    have hlim2 : Tendsto (fun n : ℕ => ENNReal.ofReal
        (1 - Real.exp (-(2 * c * (l + -(1 / ((n : ℝ) + 1))))))) atTop
        (𝓝 (ENNReal.ofReal (1 - Real.exp (-(2 * c * l))))) :=
      ENNReal.tendsto_ofReal ((hcontf.tendsto l).comp hlim)
    refine le_of_tendsto hlim2 ?_
    filter_upwards [hlim.eventually (eventually_gt_nhds hl)] with n hn
    rw [← measure_forall_drift_gt hB hm hcont hc hn]
    refine measure_mono fun ω hω => ?_
    refine Set.mem_iUnion.2 ⟨n, fun q _ => ?_⟩
    have := hω q
    show -l + 1 / ((n : ℝ) + 1) ≤ B q ω + c * (q : ℝ)
    linarith

/-- The closed approximation has probability at most that of staying above `-l`. -/
theorem measure_drift_mem_clOn_le (hB : IsPreBrownianReal B P) (hm : ∀ t, Measurable (B t))
    (hcont : ∀ ω, Continuous fun s => B s ω) {c : ℝ} (hc : 0 < c) {l : ℝ} (hl : 0 < l)
    {D : Set ℝ≥0} (hDd : Dense D) :
    P {ω | (fun t : ℝ≥0 => B t ω + c * (t : ℝ)) ∈ clOn D l} ≤
      ENNReal.ofReal (1 - Real.exp (-(2 * c * l))) :=
  le_trans (measure_mono fun ω hω t =>
    forall_ge_of_clOn hDd (continuous_drift hcont c ω) hω t)
    (measure_forall_drift_ge_le hB hm hc hl)

/-! ### The conditioned restart -/

omit mΩ in
/-- At the truncated hitting time of an event on which the upper level is reached first, the
drifted motion is at the upper level. -/
theorem value_at_hitDriftTrunc (hcont : ∀ ω, Continuous fun s => B s ω) (c : ℝ) {ε δ : ℝ}
    (hε : 0 < ε) (hδ : 0 < δ) (η : ℝ≥0) {ω : Ω} (h0 : B 0 ω = 0)
    (hω : ω ∈ topFirst B c ε δ ∩ {ω | hitDrift B c ε ω ≤ (η : ℝ≥0∞)}) :
    B (hitDriftTrunc B c ε η ω) ω + c * ((hitDriftTrunc B c ε η ω : ℝ≥0) : ℝ) = ε := by
  obtain ⟨hlt, hle⟩ := hω
  have hlt' : hitDrift B c ε ω < hitDrift (fun t ω => -B t ω) (-c) δ ω := hlt
  have hle' : hitDrift B c ε ω ≤ (η : ℝ≥0∞) := hle
  have hcoe := coe_hitDriftTrunc_of_le B c ε η ω hle'
  have hexit : exitStrip B c ε δ ω = hitDrift B c ε ω := by
    unfold exitStrip; exact min_eq_left hlt'.le
  have hfin : exitStrip B c ε δ ω < ⊤ := by
    rw [hexit]; exact lt_of_le_of_lt hle' ENNReal.coe_lt_top
  have hv := (exitStrip_value hcont c hε hδ ω h0 hfin).1 hlt'
  have htn : (exitStrip B c ε δ ω).toNNReal = hitDriftTrunc B c ε η ω := by
    rw [hexit, ← hcoe]; exact ENNReal.toNNReal_coe _
  rw [htn] at hv
  exact hv

/-- **Identification of the conditioned restart.**  Up to a null set, staying above `-δ` forever
and reaching the level `ε` by time `η` is the event that the upper level is reached first, by
time `η`, and that the increments after the hitting time stay above `-(ε + δ)`. -/
theorem ae_eq_stayAbove_inter_hitDrift_le [IsProbabilityMeasure P] (hB : IsBrownianReal B P)
    (hm : ∀ t, Measurable (B t)) (hcont : ∀ ω, Continuous fun s => B s ω) {c : ℝ} (hc : 0 < c)
    {ε δ : ℝ} (hε : 0 < ε) (hδ : 0 < δ) (η : ℝ≥0) {D : Set ℝ≥0} (hDc : D.Countable)
    (hDd : Dense D) :
    ({ω | ∀ t : ℝ≥0, -δ < B t ω + c * t} ∩ {ω | hitDrift B c ε ω ≤ (η : ℝ≥0∞)}) =ᵐ[P]
      ((topFirst B c ε δ ∩ {ω | hitDrift B c ε ω ≤ (η : ℝ≥0∞)}) ∩
        {ω | driftIncr B c (hitDriftTrunc B c ε η) ω ∈ posOn D (ε + δ)}) := by
  have hl : 0 < ε + δ := add_pos hε hδ
  have hτ := isStoppingTime_hitDriftTrunc hm hcont c ε η
  have hE : MeasurableSet[hτ.measurableSpace] (topFirst B c ε δ ∩
      {ω | hitDrift B c ε ω ≤ (η : ℝ≥0∞)}) := measurableSet_topFirst_inter_le hm hcont c ε δ η
  have hEm : MeasurableSet (topFirst B c ε δ ∩ {ω | hitDrift B c ε ω ≤ (η : ℝ≥0∞)}) :=
    hτ.measurableSpace_le _ hE
  have hincr := measurable_driftIncr hm hcont c (measurable_of_isStoppingTime_nnreal hm hτ)
  have h0 : ∀ᵐ ω ∂P, B 0 ω = 0 :=
    hB.toIsPreBrownianReal.eval_zero_ae_eq_zero.mono fun ω h => h
  have hcontIncr : ∀ ω, Continuous (driftIncr B c (hitDriftTrunc B c ε η) ω) := fun ω => by
    unfold driftIncr
    exact ((continuous_drift hcont c ω).comp (continuous_const.add continuous_id)).sub
      continuous_const
  -- the three sets
  set E := topFirst B c ε δ ∩ {ω | hitDrift B c ε ω ≤ (η : ℝ≥0∞)} with hEdef
  set S1 := E ∩ {ω | driftIncr B c (hitDriftTrunc B c ε η) ω ∈ posOn D (ε + δ)} with hS1
  set S2 := {ω | ∀ t : ℝ≥0, -δ < B t ω + c * t} ∩ {ω | hitDrift B c ε ω ≤ (η : ℝ≥0∞)} with hS2
  set S3 := E ∩ {ω | driftIncr B c (hitDriftTrunc B c ε η) ω ∈ clOn D (ε + δ)} with hS3
  have hsub1 : S1 ≤ᵐ[P] S2 := by
    filter_upwards [h0] with ω h0ω hω
    obtain ⟨hωE, hωp⟩ := hω
    refine ⟨fun t => ?_, hωE.2⟩
    have hval := value_at_hitDriftTrunc hcont c hε hδ η h0ω hωE
    have hlt : hitDrift B c ε ω < hitDrift (fun t ω => -B t ω) (-c) δ ω := hωE.1
    have hle : hitDrift B c ε ω ≤ (η : ℝ≥0∞) := hωE.2
    have hcoe := coe_hitDriftTrunc_of_le B c ε η ω hle
    set s := hitDriftTrunc B c ε η ω with hs
    by_cases hts : t < s
    · by_contra hcon
      have hcon' : B t ω + c * (t : ℝ) ≤ -δ := not_lt.mp hcon
      have hcont' : ∀ ω, Continuous fun s => (fun t ω => -B t ω) s ω := fun ω => (hcont ω).neg
      have : hitDrift (fun t ω => -B t ω) (-c) δ ω ≤ (t : ℝ≥0∞) :=
        (hitDrift_le_iff hcont' (-c) δ ω t).2 ⟨t, le_rfl, by show δ ≤ -B t ω + -c * (t : ℝ); linarith⟩
      have h2 : (t : ℝ≥0∞) < (s : ℝ≥0∞) := by exact_mod_cast hts
      rw [hcoe] at h2
      exact absurd (lt_of_le_of_lt this h2) (not_lt.mpr hlt.le)
    · push Not at hts
      have hpos := forall_gt_of_posOn hDd (hcontIncr ω) hωp (t - s)
      have hts' : s + (t - s) = t := add_tsub_cancel_of_le hts
      have : driftIncr B c (hitDriftTrunc B c ε η) ω (t - s) =
          (B t ω + c * (t : ℝ)) - ε := by
        unfold driftIncr
        rw [← hs, hts', hval]
      rw [this] at hpos
      linarith
  have hsub2 : S2 ≤ᵐ[P] S3 := by
    filter_upwards [h0] with ω h0ω hω
    obtain ⟨hG, hle⟩ := hω
    have hlt : hitDrift B c ε ω < hitDrift (fun t ω => -B t ω) (-c) δ ω := by
      by_contra hcon
      have hcon' : hitDrift (fun t ω => -B t ω) (-c) δ ω ≤ hitDrift B c ε ω := not_lt.mp hcon
      have hcont' : ∀ ω, Continuous fun s => (fun t ω => -B t ω) s ω := fun ω => (hcont ω).neg
      have hle2 : hitDrift (fun t ω => -B t ω) (-c) δ ω ≤ (η : ℝ≥0∞) := hcon'.trans hle
      obtain ⟨s, -, hs⟩ := (hitDrift_le_iff hcont' (-c) δ ω η).1 hle2
      have := hG s
      have hs' : δ ≤ -B s ω + -c * (s : ℝ) := hs
      linarith
    have hωE : ω ∈ E := ⟨hlt, hle⟩
    refine ⟨hωE, fun q _ => ?_⟩
    have hval := value_at_hitDriftTrunc hcont c hε hδ η h0ω hωE
    have := hG (hitDriftTrunc B c ε η ω + q)
    show -(ε + δ) ≤ (B (hitDriftTrunc B c ε η ω + q) ω +
      c * (((hitDriftTrunc B c ε η ω + q : ℝ≥0)) : ℝ)) -
      (B (hitDriftTrunc B c ε η ω) ω + c * ((hitDriftTrunc B c ε η ω : ℝ≥0) : ℝ))
    rw [hval]
    push_cast at this ⊢
    linarith
  have hclm : MeasurableSet (clOn D (ε + δ)) := measurableSet_clOn hDc _
  have hpm : MeasurableSet (posOn D (ε + δ)) := measurableSet_posOn hDc _
  have hS3m : P S3 = P E * P {ω | (fun t : ℝ≥0 => B t ω + c * (t : ℝ)) ∈ clOn D (ε + δ)} :=
    restart_drift hB hm hcont c (hitDriftTrunc B c ε η) hτ E hE (clOn D (ε + δ)) hclm
  have hS1m : P S1 = P E * P {ω | (fun t : ℝ≥0 => B t ω + c * (t : ℝ)) ∈ posOn D (ε + δ)} :=
    restart_drift hB hm hcont c (hitDriftTrunc B c ε η) hτ E hE (posOn D (ε + δ)) hpm
  have hmeasS1 : MeasurableSet S1 := hEm.inter (hincr hpm)
  have hfin : P S2 ≠ ⊤ := measure_ne_top P S2
  have hge : P S2 ≤ P S1 := by
    calc P S2 ≤ P S3 := measure_mono_ae hsub2
      _ = P E * P {ω | (fun t : ℝ≥0 => B t ω + c * (t : ℝ)) ∈ clOn D (ε + δ)} := hS3m
      _ ≤ P E * ENNReal.ofReal (1 - Real.exp (-(2 * c * (ε + δ)))) :=
          mul_le_mul' le_rfl (measure_drift_mem_clOn_le hB.toIsPreBrownianReal hm hcont hc hl hDd)
      _ = P S1 := by
          rw [hS1m, measure_drift_mem_posOn hB.toIsPreBrownianReal hm hcont hc hl hDd]
  exact (ae_eq_of_ae_subset_of_measure_ge hsub1 hge hmeasS1.nullMeasurableSet hfin).symm

/-! ### The law of the restarted path under the conditioning -/

theorem setLIntegral_inter_preimage_eq' {X : Type*} [MeasurableSpace X] {f : Ω → X} {A : Set X}
    {μ : Measure Ω} (hf : Measurable f) (hA : MeasurableSet A)
    {Φ : X → ℝ≥0∞} (E : Set Ω) :
    ∫⁻ ω in E ∩ {ω | f ω ∈ A}, Φ (f ω) ∂μ = ∫⁻ ω in E, A.indicator Φ (f ω) ∂μ := by
  have h : ∀ ω, A.indicator Φ (f ω) = {ω | f ω ∈ A}.indicator (fun ω => Φ (f ω)) ω :=
    fun ω => by
      by_cases h : f ω ∈ A <;> simp [Set.indicator, h]
  have hs : MeasurableSet {ω | f ω ∈ A} := hf hA
  simp_rw [h]
  rw [setLIntegral_indicator hs, Set.inter_comm]

/-- **The path after the hitting time, under the conditioning.**  For `c > 0` and `ε, δ > 0`, and a
measurable nonnegative path functional `Φ`, the integral over the event
`{B t + c t > -δ for all t, level ε reached by time η}` of `Φ` applied to the increments of
`B + c ·` after the hitting time of `ε` is
`P(upper level `ε` first, reached by time η) *` the integral over `{B t + c t > -(ε + δ) for all t}`
of `Φ (B + c ·)`. -/
theorem lintegral_stayAbove_inter_hitDrift_le [IsProbabilityMeasure P] (hB : IsBrownianReal B P)
    (hm : ∀ t, Measurable (B t)) (hcont : ∀ ω, Continuous fun s => B s ω) {c : ℝ} (hc : 0 < c)
    {ε δ : ℝ} (hε : 0 < ε) (hδ : 0 < δ) (η : ℝ≥0) {Φ : (ℝ≥0 → ℝ) → ℝ≥0∞} (hΦ : Measurable Φ) :
    ∫⁻ ω in {ω | ∀ t : ℝ≥0, -δ < B t ω + c * t} ∩ {ω | hitDrift B c ε ω ≤ (η : ℝ≥0∞)},
        Φ (driftIncr B c (hitDriftTrunc B c ε η) ω) ∂P =
      P (topFirst B c ε δ ∩ {ω | hitDrift B c ε ω ≤ (η : ℝ≥0∞)}) *
        ∫⁻ ω in {ω | ∀ t : ℝ≥0, -(ε + δ) < B t ω + c * t},
          Φ (fun t : ℝ≥0 => B t ω + c * (t : ℝ)) ∂P := by
  obtain ⟨D, hDc, hDd⟩ := TopologicalSpace.exists_countable_dense ℝ≥0
  have hl : 0 < ε + δ := add_pos hε hδ
  have hτ := isStoppingTime_hitDriftTrunc hm hcont c ε η
  have hE := measurableSet_topFirst_inter_le hm hcont c ε δ η
  have hincr := measurable_driftIncr hm hcont c (measurable_of_isStoppingTime_nnreal hm hτ)
  have hY : Measurable (fun ω (t : ℝ≥0) => B t ω + c * (t : ℝ)) :=
    measurable_pi_iff.2 fun t => (hm t).add measurable_const
  have hpm := measurableSet_posOn hDc (ε + δ)
  have hae : {ω | (fun t : ℝ≥0 => B t ω + c * (t : ℝ)) ∈ posOn D (ε + δ)} =ᵐ[P]
      {ω | ∀ t : ℝ≥0, -(ε + δ) < B t ω + c * t} := by
    refine ae_eq_of_subset_of_measure_ge (fun ω hω =>
      forall_gt_of_posOn hDd (continuous_drift hcont c ω) hω) ?_ (hY hpm).nullMeasurableSet
      (measure_ne_top P _)
    rw [measure_forall_drift_gt hB.toIsPreBrownianReal hm hcont hc hl,
      measure_drift_mem_posOn hB.toIsPreBrownianReal hm hcont hc hl hDd]
  have hY' := setLIntegral_inter_preimage_eq' (μ := P) (Φ := Φ) hY hpm Set.univ
  rw [Measure.restrict_univ, Set.univ_inter] at hY'
  calc ∫⁻ ω in {ω | ∀ t : ℝ≥0, -δ < B t ω + c * t} ∩ {ω | hitDrift B c ε ω ≤ (η : ℝ≥0∞)},
        Φ (driftIncr B c (hitDriftTrunc B c ε η) ω) ∂P
      = ∫⁻ ω in (topFirst B c ε δ ∩ {ω | hitDrift B c ε ω ≤ (η : ℝ≥0∞)}) ∩
          {ω | driftIncr B c (hitDriftTrunc B c ε η) ω ∈ posOn D (ε + δ)},
          Φ (driftIncr B c (hitDriftTrunc B c ε η) ω) ∂P :=
        setLIntegral_congr (ae_eq_stayAbove_inter_hitDrift_le hB hm hcont hc hε hδ η hDc hDd)
    _ = ∫⁻ ω in topFirst B c ε δ ∩ {ω | hitDrift B c ε ω ≤ (η : ℝ≥0∞)},
          (posOn D (ε + δ)).indicator Φ (driftIncr B c (hitDriftTrunc B c ε η) ω) ∂P :=
        setLIntegral_inter_preimage_eq' hincr hpm _
    _ = P (topFirst B c ε δ ∩ {ω | hitDrift B c ε ω ≤ (η : ℝ≥0∞)}) *
          ∫⁻ ω, (posOn D (ε + δ)).indicator Φ (fun t : ℝ≥0 => B t ω + c * (t : ℝ)) ∂P :=
        lintegral_restrict_driftIncr hB hm hcont c (hitDriftTrunc B c ε η) hτ hE
          (hΦ.indicator hpm)
    _ = P (topFirst B c ε δ ∩ {ω | hitDrift B c ε ω ≤ (η : ℝ≥0∞)}) *
          ∫⁻ ω in {ω | (fun t : ℝ≥0 => B t ω + c * (t : ℝ)) ∈ posOn D (ε + δ)},
            Φ (fun t : ℝ≥0 => B t ω + c * (t : ℝ)) ∂P := by rw [hY']
    _ = _ := by rw [setLIntegral_congr hae]

/-- **The probability of the conditioned event at the hitting time.**  For `c > 0` and
`ε, δ > 0`,
`P(B t + c t > -δ for all t, level ε reached by time η) =`
`P(upper level ε first, reached by time η) (1 - e^{-2c(ε+δ)})`. -/
theorem measure_stayAbove_inter_hitDrift_le [IsProbabilityMeasure P] (hB : IsBrownianReal B P)
    (hm : ∀ t, Measurable (B t)) (hcont : ∀ ω, Continuous fun s => B s ω) {c : ℝ} (hc : 0 < c)
    {ε δ : ℝ} (hε : 0 < ε) (hδ : 0 < δ) (η : ℝ≥0) :
    P ({ω | ∀ t : ℝ≥0, -δ < B t ω + c * t} ∩ {ω | hitDrift B c ε ω ≤ (η : ℝ≥0∞)}) =
      P (topFirst B c ε δ ∩ {ω | hitDrift B c ε ω ≤ (η : ℝ≥0∞)}) *
        ENNReal.ofReal (1 - Real.exp (-(2 * c * (ε + δ)))) := by
  obtain ⟨D, hDc, hDd⟩ := TopologicalSpace.exists_countable_dense ℝ≥0
  have hl : 0 < ε + δ := add_pos hε hδ
  have hτ := isStoppingTime_hitDriftTrunc hm hcont c ε η
  have hE := measurableSet_topFirst_inter_le hm hcont c ε δ η
  calc P ({ω | ∀ t : ℝ≥0, -δ < B t ω + c * t} ∩ {ω | hitDrift B c ε ω ≤ (η : ℝ≥0∞)})
      = P ((topFirst B c ε δ ∩ {ω | hitDrift B c ε ω ≤ (η : ℝ≥0∞)}) ∩
          {ω | driftIncr B c (hitDriftTrunc B c ε η) ω ∈ posOn D (ε + δ)}) :=
        measure_congr (ae_eq_stayAbove_inter_hitDrift_le hB hm hcont hc hε hδ η hDc hDd)
    _ = P (topFirst B c ε δ ∩ {ω | hitDrift B c ε ω ≤ (η : ℝ≥0∞)}) *
          P {ω | (fun t : ℝ≥0 => B t ω + c * (t : ℝ)) ∈ posOn D (ε + δ)} :=
        restart_drift hB hm hcont c (hitDriftTrunc B c ε η) hτ _ hE _
          (measurableSet_posOn hDc (ε + δ))
    _ = _ := by rw [measure_drift_mem_posOn hB.toIsPreBrownianReal hm hcont hc hl hDd]

end LatticeProb

end
