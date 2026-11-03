/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGDimension.Blueprint.Existence at commit 31e7483; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGDimension.Blueprint.Gaussian
import Mathlib.Probability.ProductMeasure

/-!
# Blueprint: existence of the GFF circle-average process (non-vacuity)

`GFFCircleAverageExists` says the hypothesis `IsGFFCircleAverage` of Theorem 1.1 is
satisfiable.  Without it, (1.5) and (1.6) would hold vacuously.  This track does not affect
the proof of Theorem 1.1; it removes the non-vacuity caveat of `STATEMENT_SPEC.md`.

Planned route:

1. A countable dense set `T₀ ⊆ (0,∞) × ℂ` of radii and centres.
2. The kernel `gffCircleCov` is PSD on finite subsets of `(0,∞) × ℂ`, radii included
   (`GffCovPSD`).  So it has a Gram representation by finitely supported sequences on `T₀`
   (`CountableGramRep`), and `X_t(ω) = Σ_k v_t(k) ω_k` with i.i.d. standard Gaussians `ω_k` is
   a centered Gaussian family on `T₀` with covariance `gffCircleCov`.
3. The kernel is continuous and has Hölder-½ increments on compact boxes
   (`GffCovContinuous`, `GffIncrementBound`).  Hence `X` is almost surely locally uniformly
   continuous on `T₀` (`GaussianSeriesLocallyUnifCont`) and extends continuously to
   `(0,∞) × ℂ`.
4. The finite-dimensional laws of the extension are Gaussian limits with covariance
   `gffCircleCov`.  This is the assembly node.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set Real

namespace LQGDimension.Blueprint.Existence

/-- The compact box `[1/(m+1), m+1] × closedBall 0 (m+1)` of radii and centres. -/
def box (m : ℕ) : Set (ℝ × ℂ) :=
  Icc (1 / ((m : ℝ) + 1)) ((m : ℝ) + 1) ×ˢ Metric.closedBall (0 : ℂ) ((m : ℝ) + 1)

/-- **Goal.** The hypothesis of Theorem 1.1 is satisfiable. -/
def GFFCircleAverageExists : Prop :=
  ∃ (Ω : Type) (_ : MeasurableSpace Ω) (P : Measure Ω) (h : ℝ → ℂ → Ω → ℝ),
    IsGFFCircleAverage h P

/-- The covariance of circle averages is PSD on finite sets of (radius, centre) pairs with
positive radii, *including different radii*. -/
def GffCovPSD : Prop :=
  ∀ F : Finset (ℝ × ℂ), (∀ p ∈ F, 0 < p.1) →
    PSDOn F (fun p q => gffCircleCov p.1 p.2 q.1 q.2)

/-- `gffCircleCov` is jointly continuous on pairs of positive radii. -/
def GffCovContinuous : Prop :=
  ContinuousOn (fun x : (ℝ × ℂ) × (ℝ × ℂ) => gffCircleCov x.1.1 x.1.2 x.2.1 x.2.2)
    {x | 0 < x.1.1 ∧ 0 < x.2.1}

/-- Hölder-½ increments on every compact box:
`Var(h_ε(z) − h_δ(w)) ≤ L_m ‖(ε,z) − (δ,w)‖` there. -/
def GffIncrementBound : Prop :=
  ∀ m : ℕ, ∃ L : ℝ, ∀ s ∈ box m, ∀ t ∈ box m,
    gffCircleCov s.1 s.2 s.1 s.2 + gffCircleCov t.1 t.2 t.1 t.2 -
      2 * gffCircleCov s.1 s.2 t.1 t.2 ≤ L * ‖s - t‖

/-- A kernel that is PSD on every finite subset of a countable set has a Gram representation by
finitely supported real sequences. -/
def CountableGramRep : Prop :=
  ∀ (T : Type) [Countable T] (K : T → T → ℝ), (∀ F : Finset T, PSDOn F K) →
    ∃ v : T → ℕ → ℝ, (∀ t, ∃ N, ∀ k ≥ N, v t k = 0) ∧
      ∀ s t, (∑' k, v s k * v t k) = K s t

/-- A Gaussian series `t ↦ Σ_k v_t(k) ω_k` over a countable set of (radius, centre) pairs, with
Hölder-½ increments on every box, is almost surely uniformly continuous on every box. -/
def GaussianSeriesLocallyUnifCont : Prop :=
  ∀ (T₀ : Set (ℝ × ℂ)), T₀.Countable → ∀ v : ℝ × ℂ → ℕ → ℝ,
    (∀ t, ∃ N, ∀ k ≥ N, v t k = 0) →
    (∀ m : ℕ, ∃ L : ℝ, ∀ s ∈ T₀, ∀ t ∈ T₀, s ∈ box m → t ∈ box m →
      (∑' k, (v s k - v t k) ^ 2) ≤ L * ‖s - t‖) →
    ∀ᵐ ω ∂(Measure.infinitePi fun _ : ℕ => gaussianReal 0 1),
      ∀ m : ℕ, UniformContinuousOn (fun t => ∑' k, v t k * ω k) (T₀ ∩ box m)

end LQGDimension.Blueprint.Existence
