/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.CONF.L29FKG at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.CONF.L29Approx
import LatticeProb.Bonanno.LQGMetric.Gaussian.AssociationFun
import Mathlib.Probability.Distributions.Gaussian.IsGaussianProcess.Def
import Mathlib.Probability.Moments.Covariance
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# CONF Lemma 2.9: FKG for continuous positively correlated Gaussian functions

Gwynne–Miller, *Confluence of geodesics in Liouville quantum gravity for γ ∈ (0,2)*
(arXiv:1905.00381), Lemma 2.9 (`lem-fkg-cont`), `confluence-final.tex` lines 676–709.

`LQGMetric.CONF.fkg_continuous_gaussian`: let `X` be a locally compact, σ-compact metric space,
`C(X, ℝ)` with the compact-open (= local uniform) topology and a Borel σ-algebra, `f` a measurable
random element of `C(X, ℝ)` which is a Gaussian process with `Cov(f(x), f(y)) ≥ 0`, and `Φ, Ψ`
bounded, measurable, non-decreasing functions on `C(X, ℝ)`, each a.s. continuous at `f`. Then
`Cov(Φ(f), Ψ(f)) ≥ 0`.

Proof (CONF:685–708): the approximations `f^n = Σ_j f(x_j^n) φ_j^n → f` a.s.
(`exists_fin_approx_ae_tendsto`, L29Approx); `Φ(f^n), Ψ(f^n)` are non-decreasing functions of the
Gaussian vector `(f(x_j^n))_j` with nonnegative covariances, so Pitt's theorem
(L. D. Pitt, Ann. Probab. 10 (1982) 496–499; `LQGMetric.Pitt.integral_mul_le_of_monotone`) gives
`E[Φ(f^n)] E[Ψ(f^n)] ≤ E[Φ(f^n) Ψ(f^n)]`; dominated convergence passes to the limit.

Modelling: σ-compactness is CONF's implicit hypothesis (compact exhaustion). "Φ is a.s.
continuous at f" is `∀ᵐ ω, ContinuousAt Φ (f ω)` (topological continuity at the sample).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set

namespace LQGMetric

namespace CONF

variable {X : Type*} [MetricSpace X] [MeasurableSpace C(X, ℝ)] [BorelSpace C(X, ℝ)]
  {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}

/-- The finite-dimensional interpolation `y ↦ Σ_j y_j φ_j` (CONF:693). -/
def l29Interp {t : Finset X} (φ : t → C(X, ℝ)) (y : t → ℝ) : C(X, ℝ) := ∑ j : t, y j • φ j

omit [MeasurableSpace C(X, ℝ)] [BorelSpace C(X, ℝ)] in
lemma continuous_l29Interp {t : Finset X} (φ : t → C(X, ℝ)) : Continuous (l29Interp φ) :=
  continuous_finsetSum _ fun j _ => (continuous_apply j).smul continuous_const

omit [MeasurableSpace C(X, ℝ)] [BorelSpace C(X, ℝ)] in
/-- Increasing one of the values `f(x_j)` can only increase `f^n` (CONF:705). -/
lemma monotone_l29Interp {t : Finset X} {φ : t → C(X, ℝ)} (hφ : ∀ j, 0 ≤ φ j) :
    Monotone (l29Interp φ) := by
  intro y y' hy
  rw [ContinuousMap.le_def]
  intro x
  simp only [l29Interp, ContinuousMap.coe_sum, ContinuousMap.coe_smul, Finset.sum_apply,
    Pi.smul_apply, smul_eq_mul]
  exact Finset.sum_le_sum fun j _ =>
    mul_le_mul_of_nonneg_right (hy j) ((ContinuousMap.le_def.1 (hφ j)) x)

omit [MeasurableSpace C(X, ℝ)] [BorelSpace C(X, ℝ)] in
/-- Passing a covariance inequality to the limit under bounded a.e. convergence. -/
lemma integral_mul_le_of_tendsto [IsFiniteMeasure P] {A B : ℕ → Ω → ℝ} {a b : Ω → ℝ}
    {CA CB : ℝ} (hAm : ∀ n, AEStronglyMeasurable (A n) P)
    (hBm : ∀ n, AEStronglyMeasurable (B n) P) (hAb : ∀ n ω, |A n ω| ≤ CA)
    (hBb : ∀ n ω, |B n ω| ≤ CB) (hA : ∀ᵐ ω ∂P, Tendsto (fun n => A n ω) atTop (𝓝 (a ω)))
    (hB : ∀ᵐ ω ∂P, Tendsto (fun n => B n ω) atTop (𝓝 (b ω)))
    (hn : ∀ n, (∫ ω, A n ω ∂P) * (∫ ω, B n ω ∂P) ≤ ∫ ω, A n ω * B n ω ∂P) :
    (∫ ω, a ω ∂P) * (∫ ω, b ω ∂P) ≤ ∫ ω, a ω * b ω ∂P := by
  have h1 := tendsto_integral_of_dominated_convergence (fun _ => CA) hAm (integrable_const CA)
    (fun n => Eventually.of_forall fun ω => by simpa [Real.norm_eq_abs] using hAb n ω) hA
  have h2 := tendsto_integral_of_dominated_convergence (fun _ => CB) hBm (integrable_const CB)
    (fun n => Eventually.of_forall fun ω => by simpa [Real.norm_eq_abs] using hBb n ω) hB
  have h3 := tendsto_integral_of_dominated_convergence (fun _ => CA * CB)
    (fun n => (hAm n).mul (hBm n)) (integrable_const _)
    (fun n => Eventually.of_forall fun ω => by
      rw [Real.norm_eq_abs, Pi.mul_apply, abs_mul]
      exact mul_le_mul (hAb n ω) (hBb n ω) (abs_nonneg _) ((abs_nonneg _).trans (hAb n ω)))
    (by filter_upwards [hA, hB] with ω ha hb using ha.mul hb)
  exact le_of_tendsto_of_tendsto' (h1.mul h2) h3 hn

variable [LocallyCompactSpace X] [SigmaCompactSpace X]

end CONF

end LQGMetric
