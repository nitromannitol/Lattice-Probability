/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGDimension.Statement.Defs at commit 31e7483; only the module paths of local imports are changed. -/
import Mathlib.Probability.Distributions.Gaussian.Multivariate
import Mathlib.Probability.Distributions.Gaussian.IsGaussianProcess.Basic
import Mathlib.Probability.Moments.Covariance
import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.Data.EReal.Basic

/-!
# Statement-level definitions

Definitions entering the statement of Theorem 1.1 of *Small-parameter asymptotics for the
Liouville quantum gravity dimension* (manuscript dated September 21, 2026).

## The Gaussian variational problem (1.4)

* `V n` — continuous functions on `[0,1]`, zero at `0` and `1`, affine on every interval of the
  uniform mesh `16⁻ⁿ`.  They are extended by zero outside `[0,1]`.
* `energy f = ½ ∫₀¹ |f'|²`.
* `zCov f g = π ∫₀¹ (|f| + |g| - |f - g|)`, the covariance (1.2) of the process `Z_f = √(2π) W(A_f)`.
* `gaussianExpectedMax F C b = E[max_{i ∈ F} (X_i + b_i)]` for a centered Gaussian vector
  `(X_i)_{i ∈ F}` with covariance `C`, realised by mathlib's `multivariateGaussian`.
* `aE n = E sup_{f ∈ V_n} (Z_f - E(f))`, as an extended real.  The paper takes suprema in the
  separable version of the process.  Its expected supremum equals the supremum over finite
  subfamilies by monotone convergence, because `f = 0` gives the term `Z_0 - E(0) = 0`.  So
  `aE n` is the supremum over finite `F ⊆ V_n`, and it depends only on the finite-dimensional
  laws, which are centered Gaussian with covariance (1.2).
* `a n = (aE n).toReal` and `aStar = inf_{n ≥ 1} a n / n`.

## Liouville first passage percolation

* `IsGFFCircleAverage h P` — `h ε z` is the circle-average process of a whole-plane GFF
  normalized by `h_1(0) = 0`.  It is centered and jointly Gaussian, with covariance given by
  the Green's function `G(x,y) = log|x-y|⁻¹ + log max(|x|,1) + log max(|y|,1)` averaged over
  the two circles, and `z ↦ h ε z ω` is continuous.
* `IsAdmissiblePath γ` — a piecewise continuously differentiable path `[0,1] → U` from `0` to
  `1`, where `U = (-2,2)²`.
* `lfppDistance ξ φ = inf_P ∫_P e^{ξ φ(z)} |dz|` (arclength counted with multiplicity).
* `IsLFPPExponent h P ξ λ` — `log D^ξ_ε / log ε → λ` in probability as `ε ↓ 0`.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set Real
open scoped Classical

namespace LQGDimension

/-! ## The Gaussian variational problem -/

/-- `V n`: continuous functions on `[0,1]` vanishing at `0` and `1` that are affine on each
interval `[k 16⁻ⁿ, (k+1) 16⁻ⁿ]` of the uniform mesh, extended by zero outside `[0,1]`.
(Continuity on `[0,1]` is automatic, since consecutive closed pieces share endpoints.) -/
def V (n : ℕ) : Set (ℝ → ℝ) :=
  {f | f 0 = 0 ∧ f 1 = 0 ∧ (∀ x, x ∉ Icc (0 : ℝ) 1 → f x = 0) ∧
    ∀ k : ℕ, k < 16 ^ n → ∃ α β : ℝ,
      ∀ x ∈ Icc ((k : ℝ) / 16 ^ n) (((k : ℝ) + 1) / 16 ^ n), f x = α * x + β}

/-- The Dirichlet energy `E(f) = ½ ∫₀¹ |f'(x)|² dx`. -/
def energy (f : ℝ → ℝ) : ℝ :=
  (1 / 2) * ∫ x in (0 : ℝ)..1, (deriv f x) ^ 2

/-- The covariance (1.2) of the Gaussian process `Z`:
`Cov(Z_f, Z_g) = π ∫₀¹ (|f| + |g| - |f - g|) dx`. -/
def zCov (f g : ℝ → ℝ) : ℝ :=
  π * ∫ x in (0 : ℝ)..1, (|f x| + |g x| - |f x - g x|)

/-- `E[max_{i ∈ F} (X_i + b_i)]`, where `(X_i)_{i ∈ F}` is a centered Gaussian vector with
covariance matrix `(C i j)_{i,j ∈ F}`.  (For `F = ∅` the value is `0`.) -/
def gaussianExpectedMax {ι : Type*} (F : Finset ι) (C : ι → ι → ℝ) (b : ι → ℝ) : ℝ :=
  ∫ x, (⨆ i : F, x i + b i) ∂(multivariateGaussian 0 (Matrix.of fun i j : F => C i j))

/-- `a_n = E sup_{f ∈ V_n} {Z_f - E(f)}`, as an extended real: the supremum over finite
subfamilies of `V_n` of the expected maximum. -/
def aE (n : ℕ) : EReal :=
  ⨆ F : Finset (V n),
    ((gaussianExpectedMax F (fun f g => zCov f g) (fun f => -energy f) : ℝ) : EReal)

/-- The real number `a_n` (finite by Theorem 1.1). -/
def a (n : ℕ) : ℝ := (aE n).toReal

/-- `a* = inf_{n ≥ 1} a_n / n`. -/
def aStar : ℝ := ⨅ n : ℕ+, a n / (n : ℝ)

/-! ## Circle averages of the whole-plane Gaussian free field -/

/-- The open square `U = (-2, 2)²`. -/
def U : Set ℂ := {z | |z.re| < 2 ∧ |z.im| < 2}

/-- Covariance kernel of the whole-plane GFF normalized by `h_1(0) = 0`:
`G(x, y) = log |x - y|⁻¹ + log max(|x|, 1) + log max(|y|, 1)`. -/
def gffGreen (x y : ℂ) : ℝ :=
  -Real.log ‖x - y‖ + Real.log (max ‖x‖ 1) + Real.log (max ‖y‖ 1)

/-- Covariance of the circle averages `h_ε(z)` and `h_δ(w)`: the average of `gffGreen` over
the circles `∂B(z, ε)` and `∂B(w, δ)`. -/
def gffCircleCov (ε : ℝ) (z : ℂ) (δ : ℝ) (w : ℂ) : ℝ :=
  (2 * π)⁻¹ ^ 2 * ∫ θ in (0 : ℝ)..2 * π, ∫ φ in (0 : ℝ)..2 * π,
    gffGreen (z + ε * Complex.exp (θ * Complex.I)) (w + δ * Complex.exp (φ * Complex.I))

/-- `h ε z` is the circle-average process `h_ε(z)` of a whole-plane Gaussian free field
normalized by `h_1(0) = 0`, whose covariance has logarithmic singularity `log |z - w|⁻¹`:
a centered Gaussian process indexed by radii `ε > 0` and centers `z`, with the covariance of
circle averages, and continuous in `z` for every fixed radius. -/
structure IsGFFCircleAverage {Ω : Type*} [MeasurableSpace Ω] (h : ℝ → ℂ → Ω → ℝ)
    (P : Measure Ω) : Prop where
  isProbabilityMeasure : IsProbabilityMeasure P
  isGaussianProcess : IsGaussianProcess (fun p : Ioi (0 : ℝ) × ℂ => h p.1 p.2) P
  integral_eq_zero : ∀ ε > 0, ∀ z, ∫ ω, h ε z ω ∂P = 0
  covariance_eq : ∀ ε > 0, ∀ δ > 0, ∀ z w, cov[h ε z, h δ w; P] = gffCircleCov ε z δ w
  continuous : ∀ ε > 0, ∀ ω, Continuous fun z => h ε z ω

/-! ## Liouville first passage percolation -/

/-- An admissible path in the definition of `D^ξ_ε`: a continuous, piecewise continuously
differentiable path `γ : [0,1] → U` from `0` to `1`.  Piecewise `C¹` means that there is a
partition `0 = t₀ < ⋯ < t_k = 1` such that `γ` is `C¹` on each closed piece. -/
structure IsAdmissiblePath (γ : ℝ → ℂ) : Prop where
  source : γ 0 = 0
  target : γ 1 = 1
  mapsTo : MapsTo γ (Icc 0 1) U
  continuousOn : ContinuousOn γ (Icc 0 1)
  piecewise_contDiff : ∃ (k : ℕ) (t : Fin (k + 1) → ℝ), StrictMono t ∧ t 0 = 0 ∧
    t (Fin.last k) = 1 ∧ ∀ i : Fin k, ContDiffOn ℝ 1 γ (Icc (t i.castSucc) (t i.succ))

/-- The LFPP length `∫_P e^{ξ φ(z)} |dz| = ∫₀¹ e^{ξ φ(γ t)} |γ'(t)| dt` of a path
(arclength counts multiplicity). -/
def lfppLength (ξ : ℝ) (φ : ℂ → ℝ) (γ : ℝ → ℂ) : ℝ :=
  ∫ t in (0 : ℝ)..1, Real.exp (ξ * φ (γ t)) * ‖deriv γ t‖

/-- The LFPP distance `D^ξ = inf_{P : 0 → 1, P ⊂ U} ∫_P e^{ξ φ(z)} |dz|` for a field `φ`
(applied to `φ = h_ε`). -/
def lfppDistance (ξ : ℝ) (φ : ℂ → ℝ) : ℝ :=
  ⨅ γ : {γ : ℝ → ℂ // IsAdmissiblePath γ}, lfppLength ξ φ γ.1

/-- `λ` is the LFPP exponent at parameter `ξ`: `log D^ξ_ε / log ε → λ` in probability as
`ε ↓ 0`, where `D^ξ_ε = lfppDistance ξ h_ε`. -/
def IsLFPPExponent {Ω : Type*} [MeasurableSpace Ω] (h : ℝ → ℂ → Ω → ℝ) (P : Measure Ω)
    (ξ lam : ℝ) : Prop :=
  TendstoInMeasure P
    (fun ε ω => Real.log (lfppDistance ξ (fun z => h ε z ω)) / Real.log ε) (𝓝[>] 0)
    (fun _ => lam)

end LQGDimension
