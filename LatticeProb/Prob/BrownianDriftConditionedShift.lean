/-
Copyright (c) 2026. Released under the Apache 2.0 license.
-/
import Mathlib
import LatticeProb.Prob.BrownianDriftExitMoment
import LatticeProb.Prob.BrownianDriftSurvival

/-!
# Brownian motion with drift conditioned to stay above a negative level: the time to reach a level

Let `B` be a real Brownian motion with continuous paths, `c > 0`, and let
`G_δ = {B t + c t > -δ for all t}` be the event, of probability `1 - e^{-2cδ}`, that the drifted
motion never reaches the level `-δ`.  For `ε > 0` the first time `τ_ε` at which `B t + c t ≥ ε`
is finite almost surely.  This file proves that under the conditional law `P(· | G_δ)` the time
`τ_ε` is small for small `ε`, uniformly in `δ`:

`η P(G_δ ∩ {τ_ε > η}) ≤ (ε + δ)² P(G_δ)`.

The proof compares with the exit time `σ` of the strip `(-δ, ε)`.  On `G_δ` one has `σ = τ_ε`.
At the deterministic time `η`, on `{σ > η}` the drifted motion is below `ε`, so staying above
`-δ` afterwards forces the increments after `η` to stay above `-(ε + δ)`; the Markov property at
`η` gives `P(G_δ ∩ {σ > η}) ≤ P(σ > η) (1 - e^{-2c(ε+δ)})`.  Markov's inequality and Wald's identity
for `E[σ]` (`lintegral_exitStrip`) bound `P(σ > η)`, and the elementary inequality
`l f(x) - x f(l) ≤ c l² f(x)` for `f(u) = 1 - e^{-2cu}` finishes the estimate.

## Main results

* `LatticeProb.survival_cross_le`: `l f(x) - x f(l) ≤ c l² f(x)` for `f(u) = 1 - e^{-2cu}`.
* `LatticeProb.measure_forall_drift_ge_le`: the closed version of the survival probability bound.
* `LatticeProb.isStoppingTime_exitStrip_natFiltration`: the exit time of a strip is a stopping time
  of the natural filtration of the one-dimensional lift of `B`.
* `LatticeProb.measure_stayAbove_inter_lt_exitStrip_le`: the Markov bound at a fixed time.
* `LatticeProb.mul_measure_stayAbove_inter_lt_hitDrift_le`: the estimate displayed above.
-/

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal

noncomputable section

namespace LatticeProb

/-! ### Elementary inequalities for the survival function -/

theorem one_sub_exp_neg_nonneg {y : ℝ} (hy : 0 ≤ y) : 0 ≤ 1 - Real.exp (-y) := by
  have : Real.exp (-y) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
  linarith

theorem one_sub_exp_neg_le (y : ℝ) : 1 - Real.exp (-y) ≤ y := by
  have := Real.add_one_le_exp (-y)
  linarith

theorem sub_sq_div_two_le_one_sub_exp_neg {y : ℝ} (hy : 0 ≤ y) :
    y - y ^ 2 / 2 ≤ 1 - Real.exp (-y) := by
  have hq := Real.quadratic_le_exp_of_nonneg hy
  have hpos : 0 < Real.exp (-y) := Real.exp_pos _
  have h1 : Real.exp (-y) * Real.exp y = 1 := by rw [← Real.exp_add]; simp
  have hEq : Real.exp (-y) * (1 + y + y ^ 2 / 2) ≤ 1 :=
    calc Real.exp (-y) * (1 + y + y ^ 2 / 2) ≤ Real.exp (-y) * Real.exp y :=
          mul_le_mul_of_nonneg_left hq hpos.le
      _ = 1 := h1
  have hrq : 1 ≤ (1 - y + y ^ 2 / 2) * (1 + y + y ^ 2 / 2) := by
    nlinarith [sq_nonneg (y ^ 2)]
  have hqpos : 0 < 1 + y + y ^ 2 / 2 := by positivity
  have : Real.exp (-y) ≤ 1 - y + y ^ 2 / 2 := le_of_mul_le_mul_right (hEq.trans hrq) hqpos
  linarith

/-- For `f u = 1 - e^{-2 c u}` and `x, l > 0`: `l f(x) - x f(l) ≤ c l² f(x)`. -/
theorem survival_cross_le {c x l : ℝ} (hc : 0 < c) (hx : 0 < x) (hl : 0 < l) :
    l * (1 - Real.exp (-(2 * c * x))) - x * (1 - Real.exp (-(2 * c * l))) ≤
      c * l ^ 2 * (1 - Real.exp (-(2 * c * x))) := by
  have hfx0 := one_sub_exp_neg_nonneg (y := 2 * c * x) (by positivity)
  have hfx1 := one_sub_exp_neg_le (2 * c * x)
  have hfl0 := one_sub_exp_neg_nonneg (y := 2 * c * l) (by positivity)
  have hfl1 := sub_sq_div_two_le_one_sub_exp_neg (y := 2 * c * l) (by positivity)
  set fx := 1 - Real.exp (-(2 * c * x)) with hfx
  set fl := 1 - Real.exp (-(2 * c * l)) with hfl
  have key : l * fx * (1 - c * l) ≤ x * fl := by
    by_cases h : c * l ≤ 1
    · have h1 : x * (2 * c * l - (2 * c * l) ^ 2 / 2) ≤ x * fl :=
        mul_le_mul_of_nonneg_left hfl1 hx.le
      have h2 : fx * (l * (1 - c * l)) ≤ (2 * c * x) * (l * (1 - c * l)) :=
        mul_le_mul_of_nonneg_right hfx1 (mul_nonneg hl.le (by linarith))
      nlinarith
    · push Not at h
      have : l * fx * (1 - c * l) ≤ 0 :=
        mul_nonpos_of_nonneg_of_nonpos (mul_nonneg hl.le hfx0) (by linarith)
      nlinarith [mul_nonneg hx.le hfl0]
  have : l * fx - c * l ^ 2 * fx = l * fx * (1 - c * l) := by ring
  linarith

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} {B : ℝ≥0 → Ω → ℝ}

/-- The closed survival bound: `P(B t + c t ≥ -l for all t) ≤ 1 - e^{-2 c l}`. -/
theorem measure_forall_drift_ge_le (hB : IsPreBrownianReal B P) (hm : ∀ t, Measurable (B t))
    {c : ℝ} (hc : 0 < c) {l : ℝ} (hl : 0 < l) :
    P {ω | ∀ t : ℝ≥0, -l ≤ B t ω + c * t} ≤ ENNReal.ofReal (1 - Real.exp (-(2 * c * l))) := by
  have hsub : ∀ n : ℕ, {ω | ∀ t : ℝ≥0, -l ≤ B t ω + c * t} ⊆
      {ω | ∀ t : ℝ≥0, -(l + 1 / ((n : ℝ) + 1)) < B t ω + c * t} := fun n ω h t => by
    have h0 : 0 < 1 / ((n : ℝ) + 1) := by positivity
    have := h t
    linarith
  have hle : ∀ n : ℕ, P {ω | ∀ t : ℝ≥0, -l ≤ B t ω + c * t} ≤
      ENNReal.ofReal (1 - Real.exp (-(2 * c * (l + 1 / ((n : ℝ) + 1))))) := fun n =>
    (measure_mono (hsub n)).trans (measure_forall_drift_gt_le hB hm hc (by positivity))
  have hcontf : Continuous (fun u : ℝ => 1 - Real.exp (-(2 * c * (l + u)))) := by fun_prop
  have h1 : Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1)) atTop (𝓝 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  have h2 : Tendsto (fun n : ℕ => 1 - Real.exp (-(2 * c * (l + 1 / ((n : ℝ) + 1))))) atTop
      (𝓝 (1 - Real.exp (-(2 * c * l)))) := by
    simpa [Function.comp_def] using (hcontf.tendsto 0).comp h1
  exact ge_of_tendsto' (ENNReal.tendsto_ofReal h2) hle

/-! ### The exit time of a strip as a stopping time of the lifted filtration -/

omit mΩ in
theorem comap_le_comap_liftOne (t : ℝ≥0) :
    MeasurableSpace.comap (fun ω (s : Set.Iic t) => B (s : ℝ≥0) ω) inferInstance ≤
    MeasurableSpace.comap (fun ω (s : Set.Iic t) => liftOne B (s : ℝ≥0) ω) inferInstance := by
  have hφ : Measurable (fun (f : Set.Iic t → EuclideanSpace ℝ (Fin 1)) (s : Set.Iic t) => f s 0) :=
    Measurable.of_eval fun s =>
      (EuclideanSpace.proj (0 : Fin 1)).continuous.measurable.comp (measurable_pi_apply s)
  have h : (fun ω (s : Set.Iic t) => B (s : ℝ≥0) ω) =
      (fun (f : Set.Iic t → EuclideanSpace ℝ (Fin 1)) (s : Set.Iic t) => f s 0) ∘
      (fun ω (s : Set.Iic t) => liftOne B (s : ℝ≥0) ω) := rfl
  rw [h, ← MeasurableSpace.comap_comp]
  exact MeasurableSpace.comap_mono hφ.comap_le

/-- The exit time of the strip `(-b, a)` by `B s + c s` is a stopping time of the natural
filtration of the one-dimensional lift of `B`. -/
theorem isStoppingTime_exitStrip_natFiltration (hm : ∀ t, Measurable (B t))
    (hcont : ∀ ω, Continuous fun s => B s ω) (c a b : ℝ) :
    IsStoppingTime (natFiltration (liftOne B) (stronglyMeasurable_liftOne hm))
      (exitStrip B c a b) := by
  intro t
  have h := isStoppingTime_exitStrip hm hcont c a b t
  have hle : brownianFiltration B hm t ≤
      natFiltration (liftOne B) (stronglyMeasurable_liftOne hm) t := by
    rw [brownianFiltration, Filtration.natural_eq_comap,
      natFiltration_eq_comap (liftOne B) (stronglyMeasurable_liftOne hm) t]
    exact comap_le_comap_liftOne t
  exact hle _ h

/-! ### The Markov bound at a fixed time -/

/-- **Markov bound at a fixed time.**  The event that the drifted motion stays above `-δ` forever
and has not left the strip `(-δ, ε)` by time `η` has probability at most
`P(not left by η) (1 - e^{-2c(ε+δ)})`. -/
theorem measure_stayAbove_inter_lt_exitStrip_le [IsProbabilityMeasure P] (hB : IsBrownianReal B P)
    (hm : ∀ t, Measurable (B t)) (hcont : ∀ ω, Continuous fun s => B s ω) {c : ℝ} (hc : 0 < c)
    {ε δ : ℝ} (hε : 0 < ε) (hδ : 0 < δ) (η : ℝ≥0) :
    P ({ω | ∀ t : ℝ≥0, -δ < B t ω + c * t} ∩ {ω | (η : ℝ≥0∞) < exitStrip B c ε δ ω}) ≤
      P {ω | (η : ℝ≥0∞) < exitStrip B c ε δ ω} *
        ENNReal.ofReal (1 - Real.exp (-(2 * c * (ε + δ)))) := by
  set F := natFiltration (liftOne B) (stronglyMeasurable_liftOne hm) with hF
  have hτ : IsStoppingTime F (fun _ : Ω => ((η : ℝ≥0) : ℝ≥0∞)) := isStoppingTime_const F η
  set E : Set Ω := {ω | (η : ℝ≥0∞) < exitStrip B c ε δ ω} with hEdef
  have hE : MeasurableSet[hτ.measurableSpace] E := by
    have h1 : hτ.measurableSpace = F η := IsStoppingTime.measurableSpace_const F η
    rw [h1]
    have h2 : MeasurableSet[F η] {ω | exitStrip B c ε δ ω ≤ η} :=
      isStoppingTime_exitStrip_natFiltration hm hcont c ε δ η
    have h3 := h2.compl
    convert h3 using 1
    ext ω
    simp [hEdef, not_le]
  obtain ⟨D, hDc, hDd⟩ := TopologicalSpace.exists_countable_dense ℝ≥0
  set Γ : Set (ℝ≥0 → ℝ) := {g | ∀ q ∈ D, -(ε + δ) ≤ g q} with hΓdef
  have hΓ : MeasurableSet Γ := by
    have : Γ = ⋂ q ∈ D, {g : ℝ≥0 → ℝ | -(ε + δ) ≤ g q} := by
      ext g; simp [hΓdef]
    rw [this]
    exact MeasurableSet.biInter hDc fun q _ =>
      measurableSet_le measurable_const (measurable_pi_apply q)
  have key := restart_drift hB hm hcont c (fun _ => η) hτ E hE Γ hΓ
  have hsub : ({ω | ∀ t : ℝ≥0, -δ < B t ω + c * t} ∩ E) ⊆
      E ∩ {ω | (fun t => (B (η + t) ω + c * ((η + t : ℝ≥0) : ℝ)) -
        (B η ω + c * (η : ℝ))) ∈ Γ} := by
    rintro ω ⟨hG, hωE⟩
    refine ⟨hωE, fun q _ => ?_⟩
    have hlt : ¬ (hitDrift B c ε ω ≤ (η : ℝ≥0∞)) := by
      intro hle
      exact absurd (lt_of_lt_of_le hωE (min_le_left _ _)) (not_lt.mpr hle)
    rw [hitDrift_le_iff hcont] at hlt
    have hη : B η ω + c * (η : ℝ) < ε := by
      by_contra hcon
      exact hlt ⟨η, le_rfl, not_lt.mp hcon⟩
    have := hG (η + q)
    push_cast at this ⊢
    linarith
  have hΓP : P {ω | (fun t => B t ω + c * (t : ℝ)) ∈ Γ} ≤
      ENNReal.ofReal (1 - Real.exp (-(2 * c * (ε + δ)))) := by
    refine le_trans (measure_mono ?_)
      (measure_forall_drift_ge_le hB.toIsPreBrownianReal hm hc (add_pos hε hδ))
    intro ω hω t
    have hclosed : IsClosed {t : ℝ≥0 | -(ε + δ) ≤ B t ω + c * (t : ℝ)} :=
      isClosed_le continuous_const ((hcont ω).add (continuous_const.mul NNReal.continuous_coe))
    have hDsub : D ⊆ {t : ℝ≥0 | -(ε + δ) ≤ B t ω + c * (t : ℝ)} := fun q hq => hω q hq
    have := hclosed.closure_subset_iff.mpr hDsub
    rw [hDd.closure_eq] at this
    exact this (Set.mem_univ t)
  calc P ({ω | ∀ t : ℝ≥0, -δ < B t ω + c * t} ∩ E)
      ≤ P (E ∩ {ω | (fun t => (B (η + t) ω + c * ((η + t : ℝ≥0) : ℝ)) -
          (B η ω + c * (η : ℝ))) ∈ Γ}) := measure_mono hsub
    _ = P E * P {ω | (fun t => B t ω + c * (t : ℝ)) ∈ Γ} := key
    _ ≤ P E * ENNReal.ofReal (1 - Real.exp (-(2 * c * (ε + δ)))) := mul_le_mul' le_rfl hΓP

/-- **The time to reach a level is small under the conditioning, uniformly in the depth.**
For `c > 0` and `ε, δ > 0`, with `G_δ = {B t + c t > -δ for all t}` and `τ_ε` the first time
`B t + c t ≥ ε`,
`η P(G_δ ∩ {τ_ε > η}) ≤ (ε + δ)² P(G_δ)`,
that is, `P(τ_ε > η | G_δ) ≤ (ε + δ)² / η`. -/
theorem mul_measure_stayAbove_inter_lt_hitDrift_le [IsProbabilityMeasure P]
    (hB : IsBrownianReal B P) (hm : ∀ t, Measurable (B t))
    (hcont : ∀ ω, Continuous fun s => B s ω) {c : ℝ} (hc : 0 < c) {ε δ : ℝ} (hε : 0 < ε)
    (hδ : 0 < δ) (η : ℝ≥0) :
    (η : ℝ≥0∞) * P ({ω | ∀ t : ℝ≥0, -δ < B t ω + c * t} ∩
        {ω | (η : ℝ≥0∞) < hitDrift B c ε ω}) ≤
      ENNReal.ofReal ((ε + δ) ^ 2) * P {ω | ∀ t : ℝ≥0, -δ < B t ω + c * t} := by
  have hsub1 : ({ω | ∀ t : ℝ≥0, -δ < B t ω + c * t} ∩ {ω | (η : ℝ≥0∞) < hitDrift B c ε ω}) ⊆
      ({ω | ∀ t : ℝ≥0, -δ < B t ω + c * t} ∩ {ω | (η : ℝ≥0∞) < exitStrip B c ε δ ω}) := by
    rintro ω ⟨hG, hω⟩
    have hω' : (η : ℝ≥0∞) < hitDrift B c ε ω := hω
    refine ⟨hG, ?_⟩
    show (η : ℝ≥0∞) < min (hitDrift B c ε ω) (hitDrift (fun t ω => -B t ω) (-c) δ ω)
    refine lt_min hω' ?_
    by_contra hcon
    have hle : hitDrift (fun t ω => -B t ω) (-c) δ ω ≤ (η : ℝ≥0∞) := not_lt.mp hcon
    have hcont' : ∀ ω, Continuous fun s => (fun t ω => -B t ω) s ω := fun ω => (hcont ω).neg
    rw [hitDrift_le_iff hcont'] at hle
    obtain ⟨s, -, hs⟩ := hle
    have := hG s
    linarith
  have step2 := measure_stayAbove_inter_lt_exitStrip_le hB hm hcont hc hε hδ η
  have hmeasσ : Measurable (exitStrip B c ε δ) :=
    measurable_of_isStoppingTime_enn (isStoppingTime_exitStrip hm hcont c ε δ)
  have hmarkov : (η : ℝ≥0∞) * P {ω | (η : ℝ≥0∞) < exitStrip B c ε δ ω} ≤
      ∫⁻ ω, exitStrip B c ε δ ω ∂P :=
    calc (η : ℝ≥0∞) * P {ω | (η : ℝ≥0∞) < exitStrip B c ε δ ω}
        ≤ (η : ℝ≥0∞) * P {ω | (η : ℝ≥0∞) ≤ exitStrip B c ε δ ω} :=
          mul_le_mul' le_rfl (measure_mono fun ω (h : (η : ℝ≥0∞) < exitStrip B c ε δ ω) =>
            (le_of_lt h : (η : ℝ≥0∞) ≤ exitStrip B c ε δ ω))
      _ ≤ ∫⁻ ω, exitStrip B c ε δ ω ∂P := mul_meas_ge_le_lintegral₀ hmeasσ.aemeasurable _
  have hW := lintegral_exitStrip hB.toIsPreBrownianReal hm hcont hc hε hδ
  have hp := measureReal_topFirst hB.toIsPreBrownianReal hm hcont hc hε hδ
  have hG := measure_forall_drift_gt hB.toIsPreBrownianReal hm hcont hc hδ
  rw [hG]
  have hcross := survival_cross_le hc hδ (add_pos hε hδ)
  have hfl0 := one_sub_exp_neg_nonneg (y := 2 * c * (ε + δ)) (by positivity)
  set fl := 1 - Real.exp (-(2 * c * (ε + δ))) with hfl
  set fδ := 1 - Real.exp (-(2 * c * δ)) with hfδ
  set p := P.real (topFirst B c ε δ) with hpdef
  have hreal : ((-δ + p * (ε + δ)) / c) * fl ≤ (ε + δ) ^ 2 * fδ := by
    have e : ((-δ + p * (ε + δ)) / c) * fl = ((ε + δ) * fδ - δ * fl) / c := by
      rw [← hp]; field_simp; ring
    rw [e, div_le_iff₀ hc]
    nlinarith [hcross]
  calc (η : ℝ≥0∞) * P ({ω | ∀ t : ℝ≥0, -δ < B t ω + c * t} ∩
        {ω | (η : ℝ≥0∞) < hitDrift B c ε ω})
      ≤ (η : ℝ≥0∞) * (P {ω | (η : ℝ≥0∞) < exitStrip B c ε δ ω} * ENNReal.ofReal fl) :=
        mul_le_mul' le_rfl ((measure_mono hsub1).trans step2)
    _ = ((η : ℝ≥0∞) * P {ω | (η : ℝ≥0∞) < exitStrip B c ε δ ω}) * ENNReal.ofReal fl :=
        (mul_assoc _ _ _).symm
    _ ≤ ENNReal.ofReal ((-δ + p * (ε + δ)) / c) * ENNReal.ofReal fl :=
        mul_le_mul' (hmarkov.trans_eq hW) le_rfl
    _ = ENNReal.ofReal (((-δ + p * (ε + δ)) / c) * fl) := (ENNReal.ofReal_mul' hfl0).symm
    _ ≤ ENNReal.ofReal ((ε + δ) ^ 2 * fδ) := ENNReal.ofReal_le_ofReal hreal
    _ = ENNReal.ofReal ((ε + δ) ^ 2) * ENNReal.ofReal fδ := ENNReal.ofReal_mul (by positivity)

end LatticeProb

end
