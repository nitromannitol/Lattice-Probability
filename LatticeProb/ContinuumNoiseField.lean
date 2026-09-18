/-
The space-time white-noise field with intensity `v`, its covariance and variance,
and the associated Brownian optimal-stopping value. The Brownian motion has
variance `t/4`; stopping rules are specified by Galmarino’s criterion.
-/
import LatticeProb.ContinuumHeatKernel
import LatticeProb.Gauss.WhiteNoise
import LatticeProb.Gauss.BrownianCont

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

noncomputable section

namespace LatticeProb.ContinuumStopping

/-- The probability space of the space-time white noise: the Gaussian product
over a countable orthonormal basis of `L²` of the plane. -/
abbrev contNoiseSpace : Type := ↥(LatticeProb.l2Basis (volume : Measure (ℝ × ℝ))) → ℝ

/-- The law of the space-time white noise. -/
abbrev contNoiseLaw : Measure contNoiseSpace :=
  LatticeProb.whiteNoiseLaw (volume : Measure (ℝ × ℝ))

/-- **The space-time noise field** `Z_T(s,x)` at
intensity `v`: the white noise of the plane paired with the heat
kernel of the elapsed time truncated to the window `(s,T)`. -/
def contZ (v T s x : ℝ) : contNoiseSpace → ℝ := fun ω =>
  Real.sqrt v * LatticeProb.whiteNoiseOf (volume : Measure (ℝ × ℝ)) (contNoiseTest T s x) ω

theorem measurable_contZ (v T s x : ℝ) : Measurable (contZ v T s x) :=
  (LatticeProb.measurable_whiteNoiseOf _ _).const_mul _

/-- The field is centred. -/
theorem integral_contZ (v T s x : ℝ) : ∫ ω, contZ v T s x ω ∂contNoiseLaw = 0 := by
  simp only [contZ]
  rw [MeasureTheory.integral_const_mul, LatticeProb.integral_whiteNoiseOf (volume : Measure (ℝ × ℝ)), mul_zero]

/-- **The covariance of the field** is `v` times the `L²` pairing of the two
test functions. -/
theorem integral_contZ_mul {v : ℝ} (hv : 0 ≤ v) (T s x T' s' x' : ℝ) :
    ∫ ω, contZ v T s x ω * contZ v T' s' x' ω ∂contNoiseLaw
      = v * ∫ p : ℝ × ℝ, contNoiseTest T s x p * contNoiseTest T' s' x' p := by
  have hmul : ∀ ω : contNoiseSpace, contZ v T s x ω * contZ v T' s' x' ω
      = (Real.sqrt v * Real.sqrt v) *
        (LatticeProb.whiteNoiseOf (volume : Measure (ℝ × ℝ)) (contNoiseTest T s x) ω *
          LatticeProb.whiteNoiseOf (volume : Measure (ℝ × ℝ)) (contNoiseTest T' s' x') ω) := by
    intro ω
    simp only [contZ]
    ring
  simp only [hmul]
  rw [MeasureTheory.integral_const_mul,
    LatticeProb.integral_whiteNoiseOf_mul (volume : Measure (ℝ × ℝ)) (memLp_contNoiseTest T s x)
      (memLp_contNoiseTest T' s' x'),
    Real.mul_self_sqrt hv]

/-- **Brownian motion with variance parameter `1/4`**: `Var(B_t) = t/4` and
`B_0 = 0`, which is exactly the statement that `2B` is a standard real Brownian
motion. -/
def IsQuarterBrownian {Ω : Type*} [MeasurableSpace Ω] (B : ℝ≥0 → Ω → ℝ)
    (P : Measure Ω) : Prop :=
  IsBrownianReal (fun t ω => 2 * B t ω) P

/-- Galmarino's criterion: `τ` is a stopping time of the natural filtration of
`B`.  If `τ` takes the value `t` at a path and a second path agrees with it up
to time `t`, then `τ` takes the value `t` there too. -/
def IsContStopping {Ω : Type*} (B : ℝ≥0 → Ω → ℝ) (τ : Ω → ℝ≥0) : Prop :=
  ∀ (t : ℝ≥0) (ω ω' : Ω), τ ω = t → (∀ s ≤ t, B s ω = B s ω') → τ ω' = t

/-- The payoffs `E_0[-Z_T(τ, B_τ)]` attained by the stopping times of `B`
bounded by `T`, at a fixed realization `ω` of the noise. -/
def contAttainable {ΩB : Type*} [MeasurableSpace ΩB] (B : ℝ≥0 → ΩB → ℝ) (PB : Measure ΩB)
    (v T : ℝ) (ω : contNoiseSpace) : Set ℝ :=
  {a : ℝ | ∃ τ : ΩB → ℝ≥0, IsContStopping B τ ∧ (∀ β, (τ β : ℝ) ≤ T) ∧
    a = ∫ β, -contZ v T (τ β) (B (τ β) β) ω ∂PB}

/-- `sup_{τ ≤ T} E_0[-Z_T(τ, B_τ)]`, the optimal-stopping part of `U(T)`. -/
def contStopValue {ΩB : Type*} [MeasurableSpace ΩB] (B : ℝ≥0 → ΩB → ℝ) (PB : Measure ΩB)
    (v T : ℝ) (ω : contNoiseSpace) : ℝ :=
  sSup (contAttainable B PB v T ω)

/-- **The limit random variable** `U(T) = Z_T(0,0) + sup_{τ≤T} E_0[-Z_T(τ,B_τ)]`
is a function of the noise alone: the Brownian
average has been taken. -/
def contU {ΩB : Type*} [MeasurableSpace ΩB] (B : ℝ≥0 → ΩB → ℝ) (PB : Measure ΩB)
    (v T : ℝ) (ω : contNoiseSpace) : ℝ :=
  contZ v T 0 0 ω + contStopValue B PB v T ω

/-- The stopping time `0` is admissible, so the set of attainable payoffs is
never empty and the supremum defining `U(T)` is not the junk value of
`sSup ∅`. -/
theorem contAttainable_nonempty {ΩB : Type*} [MeasurableSpace ΩB] (B : ℝ≥0 → ΩB → ℝ)
    (PB : Measure ΩB) (v : ℝ) {T : ℝ} (hT : 0 ≤ T) (ω : contNoiseSpace) :
    (contAttainable B PB v T ω).Nonempty := by
  refine ⟨∫ β, -contZ v T ((0 : ℝ≥0)) (B 0 β) ω ∂PB, (fun _ => (0 : ℝ≥0)), ?_, ?_, rfl⟩
  · intro t ω₁ ω₂ h _
    exact h
  · intro β
    simpa using hT

/-- **The second moment of the field**: `E Z_T(s,x)² = 2 v √(T-s)/√π`. -/
theorem integral_contZ_sq {v : ℝ} (hv : 0 ≤ v) {s T : ℝ} (hsT : s ≤ T) (x : ℝ) :
    (∫ ω, (contZ v T s x ω) ^ 2 ∂contNoiseLaw)
      = v * (2 * Real.sqrt (T - s) / Real.sqrt Real.pi) := by
  have h := integral_contZ_mul hv T s x T s x
  have hl : (∫ ω, contZ v T s x ω * contZ v T s x ω ∂contNoiseLaw)
      = ∫ ω, (contZ v T s x ω) ^ 2 ∂contNoiseLaw := by
    simp [pow_two]
  have hr : (∫ p : ℝ × ℝ, contNoiseTest T s x p * contNoiseTest T s x p)
      = ∫ p : ℝ × ℝ, (contNoiseTest T s x p) ^ 2 := by
    simp [pow_two]
  rw [hl, hr, integral_contNoiseTest_sq hsT x] at h
  exact h

/-- **The variance of the field** is `2 v √(T-s)/√π`: it grows like the
square root of the elapsed time. -/
theorem variance_contZ {v : ℝ} (hv : 0 ≤ v) {s T : ℝ} (hsT : s ≤ T) (x : ℝ) :
    variance (contZ v T s x) contNoiseLaw
      = v * (2 * Real.sqrt (T - s) / Real.sqrt Real.pi) := by
  rw [ProbabilityTheory.variance_eq_integral (measurable_contZ v T s x).aemeasurable,
    integral_contZ v T s x]
  simpa using integral_contZ_sq hv hsT x

end LatticeProb.ContinuumStopping

end
