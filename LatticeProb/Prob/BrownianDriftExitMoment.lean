/-
Copyright (c) 2026. Released under the Apache 2.0 license.
-/
import Mathlib
import LatticeProb.Prob.BrownianDriftRestartHit
import LatticeProb.Prob.BoundedStopping

/-!
# Exit of a Brownian motion with drift from a strip

For a real Brownian motion `B` with continuous paths and a drift `c`, the first time `B s + c s`
reaches a level from below or from above is a stopping time of the natural filtration
`brownianFiltration B hm`, for which `B` and `exp (-2 c (B t + c t))` are martingales.

* `isStoppingTime_hitDrift_brownian`, `isStoppingTime_hitDrift_neg_brownian`: the two hitting
  times are stopping times of this filtration; `martingale_brownian`: `B` is a martingale of it.
* `exitStrip B c a b`: the first exit time of `B s + c s` from the open strip `(-b, a)`; for a
  continuous path started at `0` it leaves the strip at `a` or `-b` (`exit_value_eq`,
  `exitStrip_value`), the value being `a` exactly when the upper level is reached strictly first.
* `integrable_and_integral_exp_exitTrunc`: optional stopping of the exponential martingale at the
  exit time truncated at a horizon `N` (bounded stopping time on real time), with expectation `1`.
* `ae_exitStrip_lt_top`: for `c > 0` the strip is left in finite time almost surely
  (Markov's inequality for the exponential martingale of parameter `c / 2`).
* `topFirst B c a b`, `measurableSet_topFirst`: the event that the upper level is reached strictly
  before the lower one is measurable.
* `measureReal_topFirst`: for `c > 0`, `P(topFirst) (1 - e^{-2c(a+b)}) = 1 - e^{-2cb}`, by dominated
  convergence in the optional stopping identity at the truncated exit times.
* `integrable_and_integral_brownian_exitTrunc`, `integrable_and_integral_drift_exitTrunc`: optional
  stopping of `B` at the truncated exit time, so that `E[B s + c s at the exit] = c E[exit time]`.
* `lintegral_exitStrip`: Wald's identity `c E[exit time] = (a + b) P(topFirst) - b` for `c > 0`
  (dominated convergence for the stopped drifted motion, monotone convergence for the times).
-/

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal

noncomputable section

namespace LatticeProb

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} {B : ℝ≥0 → Ω → ℝ}

omit mΩ in
theorem comap_liftOne_le (t : ℝ≥0) :
    MeasurableSpace.comap (fun ω (s : Set.Iic t) => liftOne B (s : ℝ≥0) ω) inferInstance ≤
    MeasurableSpace.comap (fun ω (s : Set.Iic t) => B (s : ℝ≥0) ω) inferInstance := by
  have hφ : Measurable (fun (f : Set.Iic t → ℝ) (s : Set.Iic t) =>
      (WithLp.toLp 2 (fun _ : Fin 1 => f s) : EuclideanSpace ℝ (Fin 1))) :=
    Measurable.of_eval fun s => (PiLp.continuous_toLp 2 (fun _ : Fin 1 => ℝ)).measurable.comp
      (Measurable.of_eval fun _ => measurable_pi_apply s)
  have h : (fun ω (s : Set.Iic t) => liftOne B (s : ℝ≥0) ω) =
      (fun (f : Set.Iic t → ℝ) (s : Set.Iic t) =>
        (WithLp.toLp 2 (fun _ : Fin 1 => f s) : EuclideanSpace ℝ (Fin 1))) ∘
      (fun ω (s : Set.Iic t) => B (s : ℝ≥0) ω) := rfl
  rw [h, ← MeasurableSpace.comap_comp]
  exact MeasurableSpace.comap_mono hφ.comap_le

omit mΩ in
theorem comap_neg_le (t : ℝ≥0) :
    MeasurableSpace.comap (fun ω (s : Set.Iic t) => -B (s : ℝ≥0) ω) inferInstance ≤
    MeasurableSpace.comap (fun ω (s : Set.Iic t) => B (s : ℝ≥0) ω) inferInstance := by
  have h : (fun ω (s : Set.Iic t) => -B (s : ℝ≥0) ω) =
      (fun (f : Set.Iic t → ℝ) (s : Set.Iic t) => -f s) ∘
      (fun ω (s : Set.Iic t) => B (s : ℝ≥0) ω) := rfl
  rw [h, ← MeasurableSpace.comap_comp]
  exact MeasurableSpace.comap_mono
    (Measurable.of_eval fun s => (measurable_pi_apply s).neg).comap_le

/-- The first time `B s + c s` reaches the level `a` is a stopping time of the natural filtration
of `B`. -/
theorem isStoppingTime_hitDrift_brownian (hm : ∀ t, Measurable (B t))
    (hcont : ∀ ω, Continuous fun s => B s ω) (c a : ℝ) :
    IsStoppingTime (brownianFiltration B hm) (hitDrift B c a) := by
  intro t
  refine MeasurableSet.congr (s := {ω | ∃ s ≤ t, a ≤ B s ω + c * s}) ?_ ?_
  · rw [brownianFiltration, Filtration.natural_eq_comap]
    exact comap_liftOne_le t _ (measurableSet_comap_exists_le_le_drift hcont c a t)
  · ext ω
    exact (hitDrift_le_iff hcont c a ω t).symm

/-- The first time `B s + c s` is at most `-b`, written as the upward hitting time of the level
`b` by `-B - c s`, is a stopping time of the natural filtration of `B`. -/
theorem isStoppingTime_hitDrift_neg_brownian (hm : ∀ t, Measurable (B t))
    (hcont : ∀ ω, Continuous fun s => B s ω) (c b : ℝ) :
    IsStoppingTime (brownianFiltration B hm) (hitDrift (fun t ω => -B t ω) (-c) b) := by
  intro t
  have hcont' : ∀ ω, Continuous fun s => (fun t ω => -B t ω) s ω := fun ω => (hcont ω).neg
  refine MeasurableSet.congr (s := {ω | ∃ s ≤ t, b ≤ -B s ω + -c * s}) ?_ ?_
  · rw [brownianFiltration, Filtration.natural_eq_comap]
    exact (comap_liftOne_le (B := fun t ω => -B t ω) t).trans (comap_neg_le t) _
      (measurableSet_comap_exists_le_le_drift hcont' (-c) b t)
  · ext ω
    exact (hitDrift_le_iff hcont' (-c) b ω t).symm

/-- A Brownian motion is a martingale of its natural filtration. -/
theorem martingale_brownian (hB : IsPreBrownianReal B P) (hm : ∀ t, Measurable (B t)) :
    Martingale B (brownianFiltration B hm) P := by
  have : IsProbabilityMeasure P := hB.isGaussianProcess.isProbabilityMeasure
  have hadapt : StronglyAdapted (brownianFiltration B hm) B :=
    Filtration.stronglyAdapted_natural (fun t => (hm t).stronglyMeasurable)
  refine ⟨hadapt, fun s t hst => ?_⟩
  have hindep := (brownian_indep_filtration_sub hB hm hst).symm
  have hsm : StronglyMeasurable[MeasurableSpace.comap (B t - B s) inferInstance] (B t - B s) :=
    (comap_measurable (B t - B s)).stronglyMeasurable
  have hle1 : MeasurableSpace.comap (B t - B s) inferInstance ≤ mΩ :=
    ((hm t).sub (hm s)).comap_le
  have h1 : P[B t - B s | brownianFiltration B hm s] =ᵐ[P] fun _ => P[B t - B s] :=
    condExp_indep_eq hle1 ((brownianFiltration B hm).le s) hsm hindep
  have h0 : P[B t - B s] = 0 := by
    rw [integral_sub' (hB.integrable_eval t) (hB.integrable_eval s), hB.integral_eval,
      hB.integral_eval]
    simp
  have h2 := condExp_add (hB.integrable_eval s)
    ((hB.integrable_eval t).sub (hB.integrable_eval s)) (brownianFiltration B hm s)
  have e : B s + (B t - B s) = B t := by abel
  rw [e] at h2
  have hBs : P[B s | brownianFiltration B hm s] = B s :=
    condExp_of_stronglyMeasurable ((brownianFiltration B hm).le s) (hadapt s)
      (hB.integrable_eval s)
  filter_upwards [h2, h1] with ω hω1 hω2
  simp only [Pi.add_apply] at hω1
  rw [hω1, hω2, h0, hBs]
  simp

/-! ### The exit time of a strip -/

/-- The first exit time of `B s + c s` from the open strip `(-b, a)`: the first time the drifted
motion is at least `a` or at most `-b`. -/
def exitStrip (B : ℝ≥0 → Ω → ℝ) (c a b : ℝ) (ω : Ω) : ℝ≥0∞ :=
  min (hitDrift B c a ω) (hitDrift (fun t ω => -B t ω) (-c) b ω)

omit mΩ in
theorem hitDrift_neg_le_iff (hcont : ∀ ω, Continuous fun s => B s ω) (c b : ℝ) (ω : Ω)
    (t : ℝ≥0) :
    hitDrift (fun t ω => -B t ω) (-c) b ω ≤ (t : ℝ≥0∞) ↔ ∃ s ≤ t, B s ω + c * s ≤ -b := by
  rw [hitDrift_le_iff (B := fun t ω => -B t ω) (fun ω => (hcont ω).neg) (-c) b ω t]
  constructor <;> rintro ⟨s, hs, h⟩ <;> exact ⟨s, hs, by linarith⟩

omit mΩ in
theorem exitStrip_le_iff (hcont : ∀ ω, Continuous fun s => B s ω) (c a b : ℝ) (ω : Ω)
    (t : ℝ≥0) :
    exitStrip B c a b ω ≤ (t : ℝ≥0∞) ↔
      ∃ s ≤ t, (a ≤ B s ω + c * s ∨ B s ω + c * s ≤ -b) := by
  unfold exitStrip
  rw [min_le_iff, hitDrift_le_iff hcont c a ω t, hitDrift_neg_le_iff hcont c b ω t]
  constructor
  · rintro (⟨s, hs, h⟩ | ⟨s, hs, h⟩)
    · exact ⟨s, hs, Or.inl h⟩
    · exact ⟨s, hs, Or.inr h⟩
  · rintro ⟨s, hs, h | h⟩
    · exact Or.inl ⟨s, hs, h⟩
    · exact Or.inr ⟨s, hs, h⟩

theorem isStoppingTime_exitStrip (hm : ∀ t, Measurable (B t))
    (hcont : ∀ ω, Continuous fun s => B s ω) (c a b : ℝ) :
    IsStoppingTime (brownianFiltration B hm) (exitStrip B c a b) :=
  (isStoppingTime_hitDrift_brownian hm hcont c a).min
    (isStoppingTime_hitDrift_neg_brownian hm hcont c b)

/-- A continuous function started at `0` that first leaves the strip `(-b, a)` at time `τ` takes
the value `a` or `-b` there and stays in the open strip before. -/
theorem exit_value_eq {g : ℝ≥0 → ℝ} (hg : Continuous g) (hg0 : g 0 = 0) {a b : ℝ} (ha : 0 < a)
    (hb : 0 < b) {τ : ℝ≥0} (hτ : IsLeast {s : ℝ≥0 | a ≤ g s ∨ g s ≤ -b} τ) :
    (g τ = a ∨ g τ = -b) ∧ ∀ s < τ, -b < g s ∧ g s < a := by
  have hbelow : ∀ s < τ, -b < g s ∧ g s < a := fun s hs => by
    by_contra hcon
    have : a ≤ g s ∨ g s ≤ -b := by
      by_cases h1 : a ≤ g s
      · exact Or.inl h1
      · right
        by_contra h2
        exact hcon ⟨not_le.1 h2, not_le.1 h1⟩
    exact absurd (hτ.2 this) (not_le.2 hs)
  refine ⟨?_, hbelow⟩
  have hτ0 : 0 < τ := by
    rcases hτ.1 with h | h
    · refine pos_iff_ne_zero.2 fun h0 => ?_
      rw [h0, hg0] at h
      linarith
    · refine pos_iff_ne_zero.2 fun h0 => ?_
      rw [h0, hg0] at h
      linarith
  have hcl : closure (Set.Iio τ) = Set.Iic τ := closure_Iio' ⟨0, hτ0⟩
  have hτcl : τ ∈ closure (Set.Iio τ) := by rw [hcl]; exact Set.mem_Iic.2 le_rfl
  have hup : g τ ≤ a :=
    (closure_minimal (fun s hs => (hbelow s hs).2.le) (isClosed_le hg continuous_const)) hτcl
  have hlo : -b ≤ g τ :=
    (closure_minimal (fun s hs => (hbelow s hs).1.le) (isClosed_le continuous_const hg)) hτcl
  rcases hτ.1 with h | h
  · exact Or.inl (le_antisymm hup h)
  · exact Or.inr (le_antisymm h hlo)

omit mΩ in
theorem isLeast_exitStrip (hcont : ∀ ω, Continuous fun s => B s ω) (c a b : ℝ) (ω : Ω)
    (h : exitStrip B c a b ω < ⊤) :
    IsLeast {s : ℝ≥0 | a ≤ B s ω + c * s ∨ B s ω + c * s ≤ -b}
      (exitStrip B c a b ω).toNNReal := by
  have hcoe : (((exitStrip B c a b ω).toNNReal : ℝ≥0) : ℝ≥0∞) = exitStrip B c a b ω :=
    ENNReal.coe_toNNReal h.ne
  have hmin : ∀ s : ℝ≥0, (a ≤ B s ω + c * s ∨ B s ω + c * s ≤ -b) →
      (exitStrip B c a b ω).toNNReal ≤ s := fun s hs => by
    have := (exitStrip_le_iff hcont c a b ω s).2 ⟨s, le_rfl, hs⟩
    rw [← hcoe] at this
    exact_mod_cast this
  obtain ⟨s, hsτ, hs⟩ := (exitStrip_le_iff hcont c a b ω _).1 hcoe.ge
  have : s = (exitStrip B c a b ω).toNNReal := le_antisymm hsτ (hmin s hs)
  rw [this] at hs
  exact ⟨hs, fun s' hs' => hmin s' hs'⟩

omit mΩ in
/-- **The value at the exit time.**  If the strip is left in finite time, the drifted motion is at
`a` when the upper level is reached first and at `-b` otherwise. -/
theorem exitStrip_value (hcont : ∀ ω, Continuous fun s => B s ω) (c : ℝ) {a b : ℝ} (ha : 0 < a)
    (hb : 0 < b) (ω : Ω) (h0 : B 0 ω = 0) (h : exitStrip B c a b ω < ⊤) :
    (hitDrift B c a ω < hitDrift (fun t ω => -B t ω) (-c) b ω →
      B (exitStrip B c a b ω).toNNReal ω + c * (exitStrip B c a b ω).toNNReal = a) ∧
    (¬ hitDrift B c a ω < hitDrift (fun t ω => -B t ω) (-c) b ω →
      B (exitStrip B c a b ω).toNNReal ω + c * (exitStrip B c a b ω).toNNReal = -b) := by
  have hL := isLeast_exitStrip hcont c a b ω h
  have hg : Continuous fun s : ℝ≥0 => B s ω + c * s :=
    (hcont ω).add (continuous_const.mul NNReal.continuous_coe)
  obtain ⟨hval, hbelow⟩ := exit_value_eq (g := fun s : ℝ≥0 => B s ω + c * s) hg
    (by simp [h0]) ha hb hL
  have hcoe : (((exitStrip B c a b ω).toNNReal : ℝ≥0) : ℝ≥0∞) = exitStrip B c a b ω :=
    ENNReal.coe_toNNReal h.ne
  set τ := (exitStrip B c a b ω).toNNReal with hτ
  constructor
  · intro hlt
    have hle : hitDrift B c a ω ≤ (τ : ℝ≥0∞) := by
      rw [hcoe]; unfold exitStrip; rw [min_eq_left hlt.le]
    obtain ⟨s, hsτ, hs⟩ := (hitDrift_le_iff hcont c a ω τ).1 hle
    have hsτ' : s = τ := by
      by_contra hne
      have := (hbelow s (lt_of_le_of_ne hsτ hne)).2
      linarith
    rw [hsτ'] at hs
    rcases hval with h1 | h1
    · exact h1
    · linarith
  · intro hnlt
    have hle : hitDrift (fun t ω => -B t ω) (-c) b ω ≤ (τ : ℝ≥0∞) := by
      rw [hcoe]; unfold exitStrip
      rw [min_eq_right (not_lt.1 hnlt)]
    obtain ⟨s, hsτ, hs⟩ := (hitDrift_neg_le_iff hcont c b ω τ).1 hle
    have hsτ' : s = τ := by
      by_contra hne
      have := (hbelow s (lt_of_le_of_ne hsτ hne)).1
      linarith
    rw [hsτ'] at hs
    rcases hval with h1 | h1
    · linarith
    · exact h1

/-! ### The truncated exit time and the exponential martingale -/

/-- The exit time truncated at the horizon `N`, with values in `ℝ≥0`. -/
def exitTrunc (B : ℝ≥0 → Ω → ℝ) (c a b : ℝ) (N : ℝ≥0) (ω : Ω) : ℝ≥0 :=
  (exitStrip B c a b ω ⊓ (N : ℝ≥0∞)).toNNReal

omit mΩ in
theorem coe_exitTrunc (B : ℝ≥0 → Ω → ℝ) (c a b : ℝ) (N : ℝ≥0) (ω : Ω) :
    ((exitTrunc B c a b N ω : ℝ≥0) : ℝ≥0∞) = exitStrip B c a b ω ⊓ (N : ℝ≥0∞) := by
  rw [exitTrunc, ENNReal.coe_toNNReal]
  exact (lt_of_le_of_lt inf_le_right ENNReal.coe_lt_top).ne

omit mΩ in
theorem exitTrunc_le (B : ℝ≥0 → Ω → ℝ) (c a b : ℝ) (N : ℝ≥0) (ω : Ω) :
    exitTrunc B c a b N ω ≤ N := by
  have h := coe_exitTrunc B c a b N ω
  have : ((exitTrunc B c a b N ω : ℝ≥0) : ℝ≥0∞) ≤ (N : ℝ≥0∞) := h ▸ inf_le_right
  exact_mod_cast this

theorem isStoppingTime_exitTrunc (hm : ∀ t, Measurable (B t))
    (hcont : ∀ ω, Continuous fun s => B s ω) (c a b : ℝ) (N : ℝ≥0) :
    IsStoppingTime (brownianFiltration B hm)
      fun ω => ((exitTrunc B c a b N ω : ℝ≥0) : ℝ≥0∞) := by
  have h := (isStoppingTime_exitStrip hm hcont c a b).min_const (i := N)
  have hfun : (fun ω => ((exitTrunc B c a b N ω : ℝ≥0) : ℝ≥0∞))
      = fun ω => min (exitStrip B c a b ω) (N : ℝ≥0∞) := by
    funext ω
    exact coe_exitTrunc B c a b N ω
  rw [hfun]
  exact h

omit mΩ in
/-- Before the exit time, and at the exit time, the drifted motion lies in the closed strip. -/
theorem exitTrunc_value_mem (hcont : ∀ ω, Continuous fun s => B s ω) (c : ℝ) {a b : ℝ}
    (ha : 0 < a) (hb : 0 < b) (N : ℝ≥0) (ω : Ω) (h0 : B 0 ω = 0) :
    -b ≤ B (exitTrunc B c a b N ω) ω + c * (exitTrunc B c a b N ω) ∧
      B (exitTrunc B c a b N ω) ω + c * (exitTrunc B c a b N ω) ≤ a := by
  by_cases hN : exitStrip B c a b ω ≤ (N : ℝ≥0∞)
  · have hlt : exitStrip B c a b ω < ⊤ := lt_of_le_of_lt hN ENNReal.coe_lt_top
    have hT : exitTrunc B c a b N ω = (exitStrip B c a b ω).toNNReal := by
      unfold exitTrunc; rw [inf_eq_left.2 hN]
    have hL := isLeast_exitStrip hcont c a b ω hlt
    have hg : Continuous fun s : ℝ≥0 => B s ω + c * s :=
      (hcont ω).add (continuous_const.mul NNReal.continuous_coe)
    obtain ⟨hval, -⟩ := exit_value_eq (g := fun s : ℝ≥0 => B s ω + c * s) hg
      (by simp [h0]) ha hb hL
    rw [hT]
    rcases hval with h | h
    · exact ⟨by linarith, by linarith⟩
    · exact ⟨by linarith, by linarith⟩
  · push Not at hN
    have hT : exitTrunc B c a b N ω = N := by
      have : ((exitTrunc B c a b N ω : ℝ≥0) : ℝ≥0∞) = N := by
        rw [coe_exitTrunc, inf_eq_right.2 hN.le]
      exact_mod_cast this
    have hno : ¬ exitStrip B c a b ω ≤ (N : ℝ≥0∞) := not_le.2 hN
    rw [exitStrip_le_iff hcont c a b ω N] at hno
    push Not at hno
    have := hno N le_rfl
    rw [hT]
    exact ⟨by linarith [this.2], by linarith [this.1]⟩

/-- **Optional stopping for the exponential martingale at the truncated exit time.** -/
theorem integrable_and_integral_exp_exitTrunc (hB : IsPreBrownianReal B P)
    (hm : ∀ t, Measurable (B t)) (hcont : ∀ ω, Continuous fun s => B s ω) (c a b : ℝ) (N : ℝ≥0) :
    Integrable (fun ω => Real.exp (-(2 * c) *
      (B (exitTrunc B c a b N ω) ω + c * (exitTrunc B c a b N ω)))) P ∧
    ∫ ω, Real.exp (-(2 * c) *
      (B (exitTrunc B c a b N ω) ω + c * (exitTrunc B c a b N ω))) ∂P = 1 := by
  have : IsProbabilityMeasure P := hB.isGaussianProcess.isProbabilityMeasure
  have hM := martingale_exp_drift hB hm c
  have hτ := isStoppingTime_exitTrunc hm hcont c a b N
  have hr : ∀ᵐ ω ∂P, ∀ t, ContinuousWithinAt
      (fun s : ℝ≥0 => Real.exp (-(2 * c) * (B s ω + c * s))) (Set.Ioi t) t :=
    Filter.Eventually.of_forall fun ω t =>
      (Real.continuous_exp.comp (continuous_const.mul ((hcont ω).add
        (continuous_const.mul NNReal.continuous_coe)))).continuousWithinAt
  have key := bounded_stopping_integrable_and_integral_eq_terminal hM hτ N
    (fun ω => ENNReal.coe_le_coe.2 (exitTrunc_le B c a b N ω)) hr
  rw [integral_exp_drift hB c N] at key
  exact key

/-! ### The exit time is finite almost surely -/

/-- Markov's inequality for the exponential martingale of parameter `c / 2` bounds the chance
that the strip has not been left by time `N`. -/
theorem measureReal_exitStrip_eq_top_mul_le (hB : IsPreBrownianReal B P)
    (hm : ∀ t, Measurable (B t)) (hcont : ∀ ω, Continuous fun s => B s ω) {c : ℝ} (hc : 0 < c)
    (a b : ℝ) (N : ℝ≥0) :
    P.real {ω | exitStrip B c a b ω = ⊤} * Real.exp (-(c * a) + c ^ 2 * N / 2) ≤ 1 := by
  have : IsProbabilityMeasure P := hB.isGaussianProcess.isProbabilityMeasure
  have hint : Integrable (fun ω => Real.exp (-(2 * (c / 2)) * (B N ω + (c / 2) * N))) P :=
    (martingale_exp_drift hB hm (c / 2)).integrable N
  have h1 := mul_meas_ge_le_integral_of_nonneg (μ := P)
    (f := fun ω => Real.exp (-(2 * (c / 2)) * (B N ω + (c / 2) * N)))
    (Filter.Eventually.of_forall fun ω => (Real.exp_pos _).le) hint
    (Real.exp (-(c * a) + c ^ 2 * N / 2))
  rw [integral_exp_drift hB (c / 2) N] at h1
  have hsub : {ω | exitStrip B c a b ω = ⊤} ⊆
      {ω | Real.exp (-(c * a) + c ^ 2 * N / 2) ≤
        Real.exp (-(2 * (c / 2)) * (B N ω + (c / 2) * N))} := by
    intro ω hω
    have hno : ¬ exitStrip B c a b ω ≤ (N : ℝ≥0∞) := by
      have : exitStrip B c a b ω = ⊤ := hω
      rw [this]; simp
    rw [exitStrip_le_iff hcont c a b ω N] at hno
    push Not at hno
    have h2 := (hno N le_rfl).1
    have h3 := mul_lt_mul_of_pos_left h2 hc
    show Real.exp _ ≤ Real.exp _
    apply Real.exp_le_exp.2
    nlinarith [h3]
  have h4 : P.real {ω | exitStrip B c a b ω = ⊤} ≤ P.real {ω | Real.exp (-(c * a) + c ^ 2 * N / 2) ≤
        Real.exp (-(2 * (c / 2)) * (B N ω + (c / 2) * N))} := measureReal_mono hsub
  have h5 := mul_le_mul_of_nonneg_right h4 (Real.exp_pos (-(c * a) + c ^ 2 * N / 2)).le
  rw [mul_comm (P.real {ω | Real.exp (-(c * a) + c ^ 2 * N / 2) ≤
        Real.exp (-(2 * (c / 2)) * (B N ω + (c / 2) * N))})] at h5
  exact h5.trans h1

/-- A Brownian motion with positive drift leaves every strip in finite time, almost surely. -/
theorem ae_exitStrip_lt_top (hB : IsPreBrownianReal B P) (hm : ∀ t, Measurable (B t))
    (hcont : ∀ ω, Continuous fun s => B s ω) {c : ℝ} (hc : 0 < c) (a b : ℝ) :
    ∀ᵐ ω ∂P, exitStrip B c a b ω < ⊤ := by
  have : IsProbabilityMeasure P := hB.isGaussianProcess.isProbabilityMeasure
  have hg : Tendsto (fun n : ℕ => Real.exp (c * a - c ^ 2 * n / 2)) atTop (nhds 0) := by
    refine Real.tendsto_exp_atBot.comp ?_
    have h : Tendsto (fun n : ℕ => (-(c ^ 2 / 2)) * (n : ℝ)) atTop atBot :=
      tendsto_natCast_atTop_atTop.const_mul_atTop_of_neg (by nlinarith)
    have h2 := tendsto_atBot_add_const_left atTop (c * a) h
    refine h2.congr fun n => ?_
    ring
  have hle : P.real {ω | exitStrip B c a b ω = ⊤} ≤ 0 := by
    refine ge_of_tendsto' hg fun n => ?_
    have h1 := measureReal_exitStrip_eq_top_mul_le hB hm hcont hc a b (n : ℝ≥0)
    have hpos := Real.exp_pos (-(c * a) + c ^ 2 * ((n : ℝ≥0) : ℝ) / 2)
    have e : Real.exp (c * a - c ^ 2 * n / 2) =
        (Real.exp (-(c * a) + c ^ 2 * ((n : ℝ≥0) : ℝ) / 2))⁻¹ := by
      rw [← Real.exp_neg]; push_cast; ring_nf
    rw [e]
    calc P.real {ω | exitStrip B c a b ω = ⊤}
        = P.real {ω | exitStrip B c a b ω = ⊤} * Real.exp (-(c * a) + c ^ 2 * ((n : ℝ≥0) : ℝ) / 2)
          * (Real.exp (-(c * a) + c ^ 2 * ((n : ℝ≥0) : ℝ) / 2))⁻¹ := by
            field_simp
      _ ≤ 1 * (Real.exp (-(c * a) + c ^ 2 * ((n : ℝ≥0) : ℝ) / 2))⁻¹ :=
            mul_le_mul_of_nonneg_right h1 (inv_nonneg.2 hpos.le)
      _ = _ := one_mul _
  have h0 : P.real {ω | exitStrip B c a b ω = ⊤} = 0 := le_antisymm hle measureReal_nonneg
  have h00 : P {ω | exitStrip B c a b ω = ⊤} = 0 := by
    exact (measureReal_eq_zero_iff (measure_ne_top P _)).1 h0
  rw [ae_iff]
  simpa [not_lt, top_le_iff] using h00

/-! ### Which level is reached first -/

omit mΩ in
/-- A stopping time of a filtration indexed by `ℝ≥0`, with values in `ℝ≥0∞`, is measurable for the
ambient σ-algebra. -/
theorem measurable_of_isStoppingTime_enn {m : MeasurableSpace Ω} {F : Filtration ℝ≥0 m}
    {τ : Ω → ℝ≥0∞} (hτ : IsStoppingTime F τ) : Measurable τ := by
  refine measurable_of_Iic fun x => ?_
  induction x using ENNReal.recTopCoe with
  | top => simp
  | coe t => exact F.le t _ (hτ.measurableSet_le t)

omit mΩ in
/-- The event that the drifted motion `B s + c s` reaches the level `a` strictly before the level
`-b`. -/
def topFirst (B : ℝ≥0 → Ω → ℝ) (c a b : ℝ) : Set Ω :=
  {ω | hitDrift B c a ω < hitDrift (fun t ω => -B t ω) (-c) b ω}

/-- The event that the upper level is reached first is measurable. -/
theorem measurableSet_topFirst (hm : ∀ t, Measurable (B t))
    (hcont : ∀ ω, Continuous fun s => B s ω) (c a b : ℝ) :
    MeasurableSet (topFirst B c a b) :=
  measurableSet_lt (measurable_of_isStoppingTime_enn (isStoppingTime_hitDrift_brownian hm hcont c a))
    (measurable_of_isStoppingTime_enn (isStoppingTime_hitDrift_neg_brownian hm hcont c b))

/-- **Probability of leaving the strip through the top.**  For `c > 0`,
`P(upper level first) (1 - e^{-2c(a+b)}) = 1 - e^{-2cb}`, by dominated convergence in the
optional stopping identity for the exponential martingale at the truncated exit times. -/
theorem measureReal_topFirst (hB : IsPreBrownianReal B P) (hm : ∀ t, Measurable (B t))
    (hcont : ∀ ω, Continuous fun s => B s ω) {c : ℝ} (hc : 0 < c) {a b : ℝ} (ha : 0 < a)
    (hb : 0 < b) :
    P.real (topFirst B c a b) * (1 - Real.exp (-(2 * c * (a + b)))) =
      1 - Real.exp (-(2 * c * b)) := by
  have : IsProbabilityMeasure P := hB.isGaussianProcess.isProbabilityMeasure
  set F : ℕ → Ω → ℝ := fun n ω => Real.exp (-(2 * c) *
    (B (exitTrunc B c a b (n : ℝ≥0) ω) ω + c * (exitTrunc B c a b (n : ℝ≥0) ω))) with hF
  set k : ℝ := Real.exp (-(2 * c) * a) - Real.exp (2 * c * b) with hk
  set U : Ω → ℝ := fun ω => Real.exp (2 * c * b) +
    (topFirst B c a b).indicator (fun _ => k) ω with hU
  have hmeas := measurableSet_topFirst hm hcont c a b
  have hint : ∀ n, Integrable (F n) P ∧ ∫ ω, F n ω ∂P = 1 := fun n =>
    integrable_and_integral_exp_exitTrunc hB hm hcont c a b (n : ℝ≥0)
  have hbound : ∀ n, ∀ᵐ ω ∂P, ‖F n ω‖ ≤ Real.exp (2 * c * b) := by
    intro n
    filter_upwards [hB.eval_zero_ae_eq_zero] with ω h0
    have := (exitTrunc_value_mem hcont c ha hb (n : ℝ≥0) ω h0).1
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    refine Real.exp_le_exp.mpr ?_
    nlinarith
  have hlim : ∀ᵐ ω ∂P, Tendsto (fun n => F n ω) atTop (nhds (U ω)) := by
    filter_upwards [hB.eval_zero_ae_eq_zero, ae_exitStrip_lt_top hB hm hcont hc a b] with ω h0 hlt
    have hval := exitStrip_value hcont c ha hb ω h0 hlt
    have hev : ∀ᶠ n : ℕ in atTop, F n ω =
        Real.exp (-(2 * c) * (B (exitStrip B c a b ω).toNNReal ω +
          c * (exitStrip B c a b ω).toNNReal)) := by
      filter_upwards [eventually_ge_atTop ⌈(exitStrip B c a b ω).toNNReal⌉₊] with n hn
      have hle : (exitStrip B c a b ω).toNNReal ≤ (n : ℝ≥0) := by
        have := Nat.le_ceil (exitStrip B c a b ω).toNNReal
        exact this.trans (by exact_mod_cast hn)
      have hT : exitTrunc B c a b (n : ℝ≥0) ω = (exitStrip B c a b ω).toNNReal := by
        unfold exitTrunc
        rw [inf_eq_left.mpr]
        rw [← ENNReal.coe_toNNReal hlt.ne]
        exact_mod_cast hle
      simp only [hF, hT]
    refine Tendsto.congr' (EventuallyEq.symm hev) ?_
    by_cases hω : ω ∈ topFirst B c a b
    · have h1 := hval.1 hω
      have : U ω = Real.exp (-(2 * c) * a) := by
        simp [hU, hω, hk]
      rw [this, h1]
      exact tendsto_const_nhds
    · have h2 := hval.2 hω
      have : U ω = Real.exp (2 * c * b) := by
        simp [hU, hω]
      rw [this, h2]
      have : -(2 * c) * -b = 2 * c * b := by ring
      rw [this]
      exact tendsto_const_nhds
  have hDCT := tendsto_integral_of_dominated_convergence (fun _ => Real.exp (2 * c * b))
    (fun n => (hint n).1.aestronglyMeasurable) (integrable_const _) hbound hlim
  have h1 : ∫ ω, U ω ∂P = 1 := by
    have := tendsto_nhds_unique hDCT (tendsto_const_nhds.congr (fun n => (hint n).2.symm))
    exact this
  have h2 : ∫ ω, U ω ∂P = Real.exp (2 * c * b) + P.real (topFirst B c a b) * k := by
    simp only [hU]
    rw [integral_add (integrable_const _) ((integrable_const k).indicator hmeas),
      integral_const, integral_indicator_const k hmeas]
    simp
  have hA : Real.exp (-(2 * c * (a + b))) =
      Real.exp (-(2 * c) * a) * Real.exp (-(2 * c * b)) := by
    rw [← Real.exp_add]; congr 1; ring
  have he : Real.exp (-(2 * c * b)) * Real.exp (2 * c * b) = 1 := by
    rw [← Real.exp_add]; simp
  rw [h2] at h1
  rw [hA]
  simp only [hk] at h1
  linear_combination (-(Real.exp (-(2 * c * b)))) * h1 +
    (1 - P.real (topFirst B c a b)) * he

/-! ### The expected exit time (Wald's identity) -/

/-- A Brownian motion has expectation zero at every time (martingale property from time `0`). -/
theorem integral_brownian_eq_zero (hB : IsPreBrownianReal B P) (hm : ∀ t, Measurable (B t))
    (t : ℝ≥0) : ∫ ω, B t ω ∂P = 0 := by
  have : IsProbabilityMeasure P := hB.isGaussianProcess.isProbabilityMeasure
  have h := (martingale_brownian hB hm).setIntegral_eq (zero_le : (0 : ℝ≥0) ≤ t) MeasurableSet.univ
  simp only [Measure.restrict_univ] at h
  rw [← h]
  exact integral_eq_zero_of_ae (by
    filter_upwards [hB.eval_zero_ae_eq_zero] with ω h0
    simpa using h0)

/-- **Optional stopping for the Brownian motion at the truncated exit time**: the stopped value is
integrable and has expectation `0`. -/
theorem integrable_and_integral_brownian_exitTrunc (hB : IsPreBrownianReal B P)
    (hm : ∀ t, Measurable (B t)) (hcont : ∀ ω, Continuous fun s => B s ω) (c a b : ℝ) (N : ℝ≥0) :
    Integrable (fun ω => B (exitTrunc B c a b N ω) ω) P ∧
      ∫ ω, B (exitTrunc B c a b N ω) ω ∂P = 0 := by
  have : IsProbabilityMeasure P := hB.isGaussianProcess.isProbabilityMeasure
  have hM := martingale_brownian hB hm
  have hτ := isStoppingTime_exitTrunc hm hcont c a b N
  have hr : ∀ᵐ ω ∂P, ∀ t, ContinuousWithinAt (fun s : ℝ≥0 => B s ω) (Set.Ioi t) t :=
    Filter.Eventually.of_forall fun ω t => (hcont ω).continuousWithinAt
  have key := bounded_stopping_integrable_and_integral_eq_terminal hM hτ N
    (fun ω => ENNReal.coe_le_coe.2 (exitTrunc_le B c a b N ω)) hr
  rw [integral_brownian_eq_zero hB hm N] at key
  exact key

/-- The truncated exit time is a measurable function. -/
theorem measurable_exitTrunc (hm : ∀ t, Measurable (B t))
    (hcont : ∀ ω, Continuous fun s => B s ω) (c a b : ℝ) (N : ℝ≥0) :
    Measurable (exitTrunc B c a b N) :=
  measurable_of_isStoppingTime (isStoppingTime_exitTrunc hm hcont c a b N)

/-- The truncated exit time is integrable: it is bounded by the horizon. -/
theorem integrable_exitTrunc (hB : IsPreBrownianReal B P) (hm : ∀ t, Measurable (B t))
    (hcont : ∀ ω, Continuous fun s => B s ω) (c a b : ℝ) (N : ℝ≥0) :
    Integrable (fun ω => (exitTrunc B c a b N ω : ℝ)) P := by
  have : IsProbabilityMeasure P := hB.isGaussianProcess.isProbabilityMeasure
  refine Integrable.of_bound
    (measurable_exitTrunc hm hcont c a b N).coe_nnreal_real.aestronglyMeasurable (N : ℝ) ?_
  exact Filter.Eventually.of_forall fun ω => by
    rw [Real.norm_of_nonneg (NNReal.coe_nonneg _)]
    exact NNReal.coe_le_coe.2 (exitTrunc_le B c a b N ω)

/-- **Wald's identity at the truncated exit time**: the drifted motion `B s + c s` stopped at the
truncated exit time is integrable, with expectation `c` times the expected stopping time. -/
theorem integrable_and_integral_drift_exitTrunc (hB : IsPreBrownianReal B P)
    (hm : ∀ t, Measurable (B t)) (hcont : ∀ ω, Continuous fun s => B s ω) (c a b : ℝ) (N : ℝ≥0) :
    Integrable (fun ω => B (exitTrunc B c a b N ω) ω + c * (exitTrunc B c a b N ω : ℝ)) P ∧
      ∫ ω, (B (exitTrunc B c a b N ω) ω + c * (exitTrunc B c a b N ω : ℝ)) ∂P =
        c * ∫ ω, (exitTrunc B c a b N ω : ℝ) ∂P := by
  obtain ⟨h1, h2⟩ := integrable_and_integral_brownian_exitTrunc hB hm hcont c a b N
  have h3 := integrable_exitTrunc hB hm hcont c a b N
  refine ⟨h1.add (h3.const_mul c), ?_⟩
  rw [integral_add h1 (h3.const_mul c), h2, integral_const_mul, zero_add]

omit mΩ in
/-- For a path leaving the strip in finite time, the truncation at the horizon `n` is eventually
the exit time itself. -/
theorem eventually_exitTrunc_eq (c a b : ℝ) (ω : Ω) (hlt : exitStrip B c a b ω < ⊤) :
    ∀ᶠ n : ℕ in atTop, exitTrunc B c a b (n : ℝ≥0) ω = (exitStrip B c a b ω).toNNReal := by
  filter_upwards [eventually_ge_atTop ⌈(exitStrip B c a b ω).toNNReal⌉₊] with n hn
  have hle : (exitStrip B c a b ω).toNNReal ≤ (n : ℝ≥0) :=
    (Nat.le_ceil _).trans (by exact_mod_cast hn)
  unfold exitTrunc
  rw [inf_eq_left.mpr]
  rw [← ENNReal.coe_toNNReal hlt.ne]
  exact_mod_cast hle

omit mΩ in
/-- The drifted motion stopped at the truncated exit times converges, along the horizons
`n → ∞`, to `a` if the upper level is reached first and to `-b` otherwise. -/
theorem tendsto_drift_exitTrunc (hcont : ∀ ω, Continuous fun s => B s ω) (c : ℝ) {a b : ℝ}
    (ha : 0 < a) (hb : 0 < b) (ω : Ω) (h0 : B 0 ω = 0) (hlt : exitStrip B c a b ω < ⊤) :
    Tendsto (fun n : ℕ => B (exitTrunc B c a b (n : ℝ≥0) ω) ω +
        c * (exitTrunc B c a b (n : ℝ≥0) ω : ℝ)) atTop
      (nhds (-b + (topFirst B c a b).indicator (fun _ => a + b) ω)) := by
  have hval := exitStrip_value hcont c ha hb ω h0 hlt
  have hev := eventually_exitTrunc_eq (B := B) c a b ω hlt
  by_cases hω : ω ∈ topFirst B c a b
  · have h1 := hval.1 hω
    have hU : -b + (topFirst B c a b).indicator (fun _ => a + b) ω = a := by
      rw [Set.indicator_of_mem hω]; ring
    rw [hU]
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [hev] with n hn
    simp only [hn]
    exact h1.symm
  · have h2 := hval.2 hω
    have hU : -b + (topFirst B c a b).indicator (fun _ => a + b) ω = -b := by simp [hω]
    rw [hU]
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [hev] with n hn
    simp only [hn]
    exact h2.symm

/-- For `c > 0`, the expectation of the drifted motion stopped at the truncated exit time
converges to `-b + P(upper level first) (a + b)` as the horizon tends to infinity (dominated
convergence). -/
theorem tendsto_integral_drift_exitTrunc (hB : IsPreBrownianReal B P)
    (hm : ∀ t, Measurable (B t)) (hcont : ∀ ω, Continuous fun s => B s ω) {c : ℝ} (hc : 0 < c)
    {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    Tendsto (fun n : ℕ => ∫ ω, (B (exitTrunc B c a b (n : ℝ≥0) ω) ω +
        c * (exitTrunc B c a b (n : ℝ≥0) ω : ℝ)) ∂P) atTop
      (nhds (-b + P.real (topFirst B c a b) * (a + b))) := by
  have : IsProbabilityMeasure P := hB.isGaussianProcess.isProbabilityMeasure
  have hmeas := measurableSet_topFirst hm hcont c a b
  have hbound : ∀ n : ℕ, ∀ᵐ ω ∂P, ‖B (exitTrunc B c a b (n : ℝ≥0) ω) ω +
      c * (exitTrunc B c a b (n : ℝ≥0) ω : ℝ)‖ ≤ a + b := by
    intro n
    filter_upwards [hB.eval_zero_ae_eq_zero] with ω h0
    have := exitTrunc_value_mem hcont c ha hb (n : ℝ≥0) ω h0
    rw [Real.norm_eq_abs, abs_le]
    constructor <;> linarith [this.1, this.2]
  have hlim : ∀ᵐ ω ∂P, Tendsto (fun n : ℕ => B (exitTrunc B c a b (n : ℝ≥0) ω) ω +
      c * (exitTrunc B c a b (n : ℝ≥0) ω : ℝ)) atTop
        (nhds (-b + (topFirst B c a b).indicator (fun _ => a + b) ω)) := by
    filter_upwards [hB.eval_zero_ae_eq_zero, ae_exitStrip_lt_top hB hm hcont hc a b] with ω h0 hlt
    exact tendsto_drift_exitTrunc hcont c ha hb ω h0 hlt
  have hDCT := tendsto_integral_of_dominated_convergence (fun _ => a + b)
    (fun n => (integrable_and_integral_drift_exitTrunc hB hm hcont c a b
      (n : ℝ≥0)).1.aestronglyMeasurable) (integrable_const _) hbound hlim
  have hI : ∫ ω, (-b + (topFirst B c a b).indicator (fun _ => a + b) ω) ∂P =
      -b + P.real (topFirst B c a b) * (a + b) := by
    rw [integral_add (integrable_const _) ((integrable_const _).indicator hmeas), integral_const,
      integral_indicator_const _ hmeas]
    simp
  rwa [hI] at hDCT

/-- **The expected exit time of a Brownian motion with positive drift from a strip**
(Wald's identity): `c E[exit time] = (a + b) P(upper level first) - b`. -/
theorem lintegral_exitStrip (hB : IsPreBrownianReal B P) (hm : ∀ t, Measurable (B t))
    (hcont : ∀ ω, Continuous fun s => B s ω) {c : ℝ} (hc : 0 < c) {a b : ℝ} (ha : 0 < a)
    (hb : 0 < b) :
    ∫⁻ ω, exitStrip B c a b ω ∂P =
      ENNReal.ofReal ((-b + P.real (topFirst B c a b) * (a + b)) / c) := by
  have : IsProbabilityMeasure P := hB.isGaussianProcess.isProbabilityMeasure
  set f : ℕ → Ω → ℝ≥0∞ := fun n ω => ((exitTrunc B c a b (n : ℝ≥0) ω : ℝ≥0) : ℝ≥0∞) with hf
  have hfmeas : ∀ n, Measurable (f n) := fun n =>
    (measurable_exitTrunc hm hcont c a b (n : ℝ≥0)).coe_nnreal_ennreal
  have hfeq : ∀ n ω, f n ω = min (exitStrip B c a b ω) (n : ℝ≥0∞) := fun n ω => by
    simp only [hf, coe_exitTrunc]
    norm_cast
  have hmono : Monotone f := fun n m hnm ω => by
    rw [hfeq, hfeq]
    exact min_le_min le_rfl (by exact_mod_cast hnm)
  have hsup : ∀ ω, ⨆ n, f n ω = exitStrip B c a b ω := by
    intro ω
    refine le_antisymm (iSup_le fun n => by rw [hfeq]; exact min_le_left _ _) ?_
    refine le_of_forall_lt fun r hr => ?_
    obtain ⟨n, hn⟩ := ENNReal.exists_nat_gt (hr.trans_le le_top).ne
    exact lt_of_lt_of_le (by rw [hfeq]; exact lt_min hr hn) (le_iSup (fun n => f n ω) n)
  have h1 : ∫⁻ ω, exitStrip B c a b ω ∂P = ⨆ n, ∫⁻ ω, f n ω ∂P :=
    (lintegral_congr fun ω => (hsup ω).symm).trans (lintegral_iSup hfmeas hmono)
  have hx : ∀ n : ℕ, ∫⁻ ω, f n ω ∂P =
      ENNReal.ofReal (∫ ω, (exitTrunc B c a b (n : ℝ≥0) ω : ℝ) ∂P) := by
    intro n
    rw [ofReal_integral_eq_lintegral_ofReal (integrable_exitTrunc hB hm hcont c a b (n : ℝ≥0))
      (Filter.Eventually.of_forall fun ω => NNReal.coe_nonneg _)]
    simp [hf]
  have hxlim : Tendsto (fun n : ℕ => ∫ ω, (exitTrunc B c a b (n : ℝ≥0) ω : ℝ) ∂P) atTop
      (nhds ((-b + P.real (topFirst B c a b) * (a + b)) / c)) := by
    have := (tendsto_integral_drift_exitTrunc hB hm hcont hc ha hb).div_const c
    refine this.congr fun n => ?_
    rw [(integrable_and_integral_drift_exitTrunc hB hm hcont c a b (n : ℝ≥0)).2]
    field_simp
  have hmono' : Monotone fun n : ℕ => ∫⁻ ω, f n ω ∂P := fun n m hnm => lintegral_mono (hmono hnm)
  have hT2 : Tendsto (fun n : ℕ => ∫⁻ ω, f n ω ∂P) atTop
      (nhds (ENNReal.ofReal ((-b + P.real (topFirst B c a b) * (a + b)) / c))) := by
    simp only [hx]
    exact ENNReal.tendsto_ofReal hxlim
  rw [h1]
  exact tendsto_nhds_unique (tendsto_atTop_iSup hmono') hT2

end LatticeProb

end
