/- Adapted from nitromannitol/Parking-Sharpness, Apache-2.0. -/
/-
Bounds on the optimal-stopping value from bounds on the stopped field,
the Gaussian law of the field, and vanishing outside the time window.
-/
import LatticeProb.ContinuumNoiseField

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

noncomputable section

namespace LatticeProb.ContinuumStopping

/-- **The optimal stopping value is bounded by any bound on the stopped
field.**  A payoff that fails to be integrable contributes the value zero,
which the bound `0 ≤ M` covers. -/
theorem contStopValue_le {ΩB : Type*} [MeasurableSpace ΩB] (B : ℝ≥0 → ΩB → ℝ)
    (PB : Measure ΩB) [IsProbabilityMeasure PB] (v T : ℝ) (ω : contNoiseSpace)
    {M : ℝ} (hM : 0 ≤ M)
    (hbound : ∀ (τ : ΩB → ℝ≥0) (β : ΩB), -contZ v T (τ β) (B (τ β) β) ω ≤ M) :
    contStopValue B PB v T ω ≤ M := by
  refine Real.sSup_le (fun a ha => ?_) hM
  obtain ⟨τ, hτ, hle, rfl⟩ := ha
  by_cases hint : Integrable (fun β => -contZ v T (τ β) (B (τ β) β) ω) PB
  · have hmono : (∫ β, -contZ v T (τ β) (B (τ β) β) ω ∂PB) ≤ ∫ _β : ΩB, M ∂PB :=
      integral_mono hint (integrable_const M) (fun β => hbound τ β)
    simpa using hmono
  · rw [integral_undef hint]
    exact hM

/-- **Every attainable payoff is at most the optimal stopping value** when
the stopped field is bounded above. -/
theorem le_contStopValue {ΩB : Type*} [MeasurableSpace ΩB] (B : ℝ≥0 → ΩB → ℝ)
    (PB : Measure ΩB) [IsProbabilityMeasure PB] (v T : ℝ) (ω : contNoiseSpace)
    {M : ℝ} (hM : 0 ≤ M)
    (hbound : ∀ (τ : ΩB → ℝ≥0) (β : ΩB), -contZ v T (τ β) (B (τ β) β) ω ≤ M)
    {a : ℝ} (ha : a ∈ contAttainable B PB v T ω) :
    a ≤ contStopValue B PB v T ω := by
  refine le_csSup ⟨M, fun b hb => ?_⟩ ha
  obtain ⟨τ, hτ, hle, rfl⟩ := hb
  by_cases hint : Integrable (fun β => -contZ v T (τ β) (B (τ β) β) ω) PB
  · have hmono : (∫ β, -contZ v T (τ β) (B (τ β) β) ω ∂PB) ≤ ∫ _β : ΩB, M ∂PB :=
      integral_mono hint (integrable_const M) (fun β => hbound τ β)
    simpa using hmono
  · rw [integral_undef hint]
    exact hM

/-- The field is Gaussian: a constant multiple of a white-noise integral. -/
theorem hasGaussianLaw_contZ (v T s x : ℝ) :
    HasGaussianLaw (contZ v T s x) contNoiseLaw := by
  have hW : HasGaussianLaw
      (LatticeProb.whiteNoiseOf (volume : Measure (ℝ × ℝ)) (contNoiseTest T s x))
      contNoiseLaw :=
    (LatticeProb.isGaussianProcess_whiteNoiseOf (volume : Measure (ℝ × ℝ))).hasGaussianLaw_eval _
  exact hW.fun_smul (Real.sqrt v)

/-- **The law of the field**: `Z_T(s,x)` is centred Gaussian of variance
`2 v √(T-s)/√π`. -/
theorem hasLaw_contZ {v : ℝ} (hv : 0 ≤ v) {s T : ℝ} (hsT : s ≤ T) (x : ℝ) :
    HasLaw (contZ v T s x)
      (gaussianReal 0 (Real.toNNReal (v * (2 * Real.sqrt (T - s) / Real.sqrt Real.pi))))
      contNoiseLaw := by
  refine ⟨(measurable_contZ v T s x).aemeasurable, ?_⟩
  rw [(hasGaussianLaw_contZ v T s x).map_eq_gaussianReal, integral_contZ v T s x,
    variance_contZ hv hsT x]

/-- Outside the time window the test function vanishes. -/
theorem contNoiseTest_of_le {T s : ℝ} (hTs : T ≤ s) (x : ℝ) :
    contNoiseTest T s x = 0 := by
  funext p
  have hno : ¬ (s < p.1 ∧ p.1 < T) := by
    rintro ⟨h1, h2⟩
    linarith
  simp [contNoiseTest, hno]

/-- Outside the time window the field vanishes. -/
theorem contZ_of_le {T s : ℝ} (hTs : T ≤ s) (v x : ℝ) :
    contZ v T s x = 0 := by
  funext ω
  have h0 : LatticeProb.whiteNoiseOf (volume : Measure (ℝ × ℝ)) (contNoiseTest T s x) ω = 0 := by
    rw [contNoiseTest_of_le hTs x]
    have hzero : LatticeProb.toLpOrZero (volume : Measure (ℝ × ℝ)) (0 : ℝ × ℝ → ℝ) = 0 := by
      rw [LatticeProb.toLpOrZero_of_memLp (MeasureTheory.MemLp.zero (p := 2)
        (μ := (volume : Measure (ℝ × ℝ))))]
      simp
    show LatticeProb.whiteNoise (LatticeProb.l2HilbertBasis _) (0 : ℝ × ℝ → ℝ) ω = 0
    rw [LatticeProb.whiteNoise, hzero]
    simp [LatticeProb.isoProc]
  show Real.sqrt v * _ = 0
  rw [h0, mul_zero]

/-- **The limit random variable is bounded** by the field at the origin plus any
bound on the stopped field. -/
theorem contU_le {ΩB : Type*} [MeasurableSpace ΩB] (B : ℝ≥0 → ΩB → ℝ)
    (PB : Measure ΩB) [IsProbabilityMeasure PB] (v T : ℝ) (ω : contNoiseSpace)
    {M : ℝ} (hM : 0 ≤ M)
    (hbound : ∀ (τ : ΩB → ℝ≥0) (β : ΩB), -contZ v T (τ β) (B (τ β) β) ω ≤ M) :
    contU B PB v T ω ≤ contZ v T 0 0 ω + M := by
  unfold contU
  gcongr
  exact contStopValue_le B PB v T ω hM hbound

end LatticeProb.ContinuumStopping

end
