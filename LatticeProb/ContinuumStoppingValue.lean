/-
The Brownian optimal-stopping value for a general reward, taking the supremum
over integrable payoffs. At reward `-Z_T`, this agrees with the noise-field
value because stopping at the horizon attains zero.
-/
import LatticeProb.ContinuumStoppingBounds

open MeasureTheory
open scoped NNReal ENNReal

noncomputable section

namespace LatticeProb.ContinuumStopping

/-- The payoffs `E_0 G(τ, B_τ)` attained by the stopping times of `B` bounded by
`T`.  The first argument of `G` is the elapsed time.

The payoff of a rule counts only when it exists.  Galmarino's criterion does not
make `τ` measurable, so for a general rule the integrand need not be
measurable and the Bochner integral is then the junk value zero; a supremum
over those junk values would be at least zero whatever the reward, and would
exceed the value of the problem whenever every genuine payoff is negative.
The definition therefore requires integrability of each admissible payoff. -/
def contPayoffs {ΩB : Type*} [MeasurableSpace ΩB] (B : ℝ≥0 → ΩB → ℝ) (PB : Measure ΩB)
    (G : ℝ → ℝ → ℝ) (T : ℝ) : Set ℝ :=
  {a : ℝ | ∃ τ : ΩB → ℝ≥0, IsContStopping B τ ∧ (∀ β, (τ β : ℝ) ≤ T) ∧
    Integrable (fun β => G (τ β) (B (τ β) β)) PB ∧
    a = ∫ β, G (τ β) (B (τ β) β) ∂PB}

/-- `sup_{τ ≤ T} E_0 G(τ, B_τ)`, the Brownian optimal-stopping value at the
reward `G`. -/
def contValue {ΩB : Type*} [MeasurableSpace ΩB] (B : ℝ≥0 → ΩB → ℝ) (PB : Measure ΩB)
    (G : ℝ → ℝ → ℝ) (T : ℝ) : ℝ :=
  sSup (contPayoffs B PB G T)

/-- **The rule that stops at the horizon collects exactly zero**, because the
field vanishes there: `Z_T(s,·) = 0` for `T ≤ s`.  So the value at this reward is never the junk value of an empty supremum, and it is never negative. -/
theorem zero_mem_contPayoffs_contZ {ΩB : Type*} [MeasurableSpace ΩB] (B : ℝ≥0 → ΩB → ℝ)
    (PB : Measure ΩB) (v : ℝ) {T : ℝ} (hT : 0 ≤ T) (ω : contNoiseSpace) :
    (0 : ℝ) ∈ contPayoffs B PB (fun s y => -contZ v T s y ω) T := by
  have hzero : (fun β => -contZ v T (((Real.toNNReal T : ℝ≥0)) : ℝ)
      (B (Real.toNNReal T) β) ω) = fun _ => (0 : ℝ) := by
    funext β
    rw [Real.coe_toNNReal T hT]
    have h := congrFun (contZ_of_le (le_refl T) v (B (Real.toNNReal T) β)) ω
    rw [h]
    simp
  refine ⟨fun _ => Real.toNNReal T, ?_, ?_, ?_, ?_⟩
  · intro t β β' h _
    exact h
  · intro β
    simp [Real.coe_toNNReal T hT]
  · rw [hzero]
    exact integrable_zero _ _ _
  · rw [hzero]
    simp

/-- **The noise-field value is the general value at the reward `-Z_T`.**  The two
sets of payoffs are equal: a rule whose payoff fails to exist contributes the
junk value zero, and zero is the payoff of the rule that stops at the horizon. -/
theorem contAttainable_eq_contPayoffs {ΩB : Type*} [MeasurableSpace ΩB] (B : ℝ≥0 → ΩB → ℝ)
    (PB : Measure ΩB) (v : ℝ) {T : ℝ} (hT : 0 ≤ T) (ω : contNoiseSpace) :
    contAttainable B PB v T ω = contPayoffs B PB (fun s y => -contZ v T s y ω) T := by
  ext a
  constructor
  · rintro ⟨τ, hτ, hle, rfl⟩
    by_cases hint : Integrable (fun β => -contZ v T (τ β) (B (τ β) β) ω) PB
    · exact ⟨τ, hτ, hle, hint, rfl⟩
    · rw [integral_undef hint]
      exact zero_mem_contPayoffs_contZ B PB v hT ω
  · rintro ⟨τ, hτ, hle, hint, rfl⟩
    exact ⟨τ, hτ, hle, rfl⟩

theorem contStopValue_eq_contValue {ΩB : Type*} [MeasurableSpace ΩB] (B : ℝ≥0 → ΩB → ℝ)
    (PB : Measure ΩB) (v : ℝ) {T : ℝ} (hT : 0 ≤ T) (ω : contNoiseSpace) :
    contStopValue B PB v T ω = contValue B PB (fun s y => -contZ v T s y ω) T := by
  unfold contStopValue contValue
  rw [contAttainable_eq_contPayoffs B PB v hT ω]

/-- The optimal-stopping part of `U(T)` is nonnegative, whether or not the set
of payoffs is bounded above. -/
theorem contStopValue_nonneg {ΩB : Type*} [MeasurableSpace ΩB] (B : ℝ≥0 → ΩB → ℝ)
    (PB : Measure ΩB) (v : ℝ) {T : ℝ} (hT : 0 ≤ T) (ω : contNoiseSpace) :
    0 ≤ contStopValue B PB v T ω := by
  have hmem : (0 : ℝ) ∈ contAttainable B PB v T ω := by
    rw [contAttainable_eq_contPayoffs B PB v hT ω]
    exact zero_mem_contPayoffs_contZ B PB v hT ω
  by_cases hb : BddAbove (contAttainable B PB v T ω)
  · exact le_csSup hb hmem
  · rw [contStopValue, Real.sSup_of_not_bddAbove hb]

/-- A bound on the reward bounds the value. -/
theorem contValue_le {ΩB : Type*} [MeasurableSpace ΩB] (B : ℝ≥0 → ΩB → ℝ)
    (PB : Measure ΩB) [IsProbabilityMeasure PB] (G : ℝ → ℝ → ℝ) (T : ℝ)
    {M : ℝ} (hM : 0 ≤ M) (hbound : ∀ s y : ℝ, G s y ≤ M) :
    contValue B PB G T ≤ M := by
  refine Real.sSup_le (fun a ha => ?_) hM
  obtain ⟨τ, hτ, hle, hint, rfl⟩ := ha
  have hmono : (∫ β, G (τ β) (B (τ β) β) ∂PB) ≤ ∫ _β : ΩB, M ∂PB :=
    integral_mono hint (integrable_const M) (fun β => hbound _ _)
  simpa using hmono

/-- Every attainable payoff is at most the value, once the reward is bounded. -/
theorem le_contValue {ΩB : Type*} [MeasurableSpace ΩB] (B : ℝ≥0 → ΩB → ℝ)
    (PB : Measure ΩB) [IsProbabilityMeasure PB] (G : ℝ → ℝ → ℝ) (T : ℝ)
    {M : ℝ} (hbound : ∀ s y : ℝ, G s y ≤ M) {a : ℝ} (ha : a ∈ contPayoffs B PB G T) :
    a ≤ contValue B PB G T := by
  refine le_csSup ⟨M, ?_⟩ ha
  rintro b ⟨τ, hτ, hle, hint, rfl⟩
  have hmono : (∫ β, G (τ β) (B (τ β) β) ∂PB) ≤ ∫ _β : ΩB, M ∂PB :=
    integral_mono hint (integrable_const M) (fun β => hbound _ _)
  simpa using hmono

/-- **The limit random variable read through the general value.**
`U(T) = Z_T(0,0) + sup_{τ≤T} E_0[G(τ,B_τ)]` at the reward `G = -Z_T`, which is the
form the cited stability estimate is stated for. -/
theorem contU_eq_contZ_add_contValue {ΩB : Type*} [MeasurableSpace ΩB] (B : ℝ≥0 → ΩB → ℝ)
    (PB : Measure ΩB) (v : ℝ) {T : ℝ} (hT : 0 ≤ T) (ω : contNoiseSpace) :
    contU B PB v T ω
      = contZ v T 0 0 ω + contValue B PB (fun s y => -contZ v T s y ω) T := by
  unfold contU
  rw [contStopValue_eq_contValue B PB v hT ω]

end LatticeProb.ContinuumStopping

end
