/-
Gaussian laws are closed under almost sure limits.

Mathlib 4.32 has Gaussian measures and their characteristic functions but no
statement that a limit of Gaussians is Gaussian, and that is the one step every
construction of a Gaussian process by an orthogonal series needs: the partial
sums are Gaussian by independence, the limit is not obviously anything.  The
proof is the characteristic function: `|e^{itx}| = 1`, so dominated convergence
carries the almost sure limit inside the integral, and a characteristic function
determines a finite measure on the line.
-/
import Mathlib

noncomputable section

namespace LatticeProb

open MeasureTheory ProbabilityTheory Filter Complex

open scoped ENNReal NNReal Topology

/-- **An almost sure limit of centred Gaussians is a centred Gaussian.**  The
variances need only converge; no uniform integrability is required, because the
characteristic function is bounded by one. -/
theorem map_eq_gaussianReal_of_tendsto_ae {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {X : ℕ → Ω → ℝ} {Y : Ω → ℝ} {σ : ℕ → ℝ≥0} {s : ℝ≥0}
    (hXm : ∀ n, Measurable (X n)) (hYm : Measurable Y)
    (hX : ∀ n, P.map (X n) = gaussianReal 0 (σ n))
    (hae : ∀ᵐ ω ∂P, Tendsto (fun n => X n ω) atTop (𝓝 (Y ω)))
    (hσ : Tendsto (fun n => ((σ n : ℝ≥0) : ℝ)) atTop (𝓝 ((s : ℝ≥0) : ℝ))) :
    P.map Y = gaussianReal 0 s := by
  haveI : IsProbabilityMeasure (P.map Y) := Measure.isProbabilityMeasure_map hYm.aemeasurable
  refine Measure.ext_of_charFun ?_
  funext t
  -- the characteristic function of the limit is the limit of the characteristic functions
  have hnormone : ∀ (u : ℝ) (ω : Ω), ‖Complex.exp ((t : ℂ) * (u : ℂ) * Complex.I)‖ = 1 := by
    intro u ω
    rw [show (t : ℂ) * (u : ℂ) * Complex.I = ((t * u : ℝ) : ℂ) * Complex.I by push_cast; ring]
    exact Complex.norm_exp_ofReal_mul_I _
  have hlim : Tendsto (fun n => ∫ ω, Complex.exp ((t : ℂ) * (X n ω : ℂ) * Complex.I) ∂P)
      atTop (𝓝 (∫ ω, Complex.exp ((t : ℂ) * (Y ω : ℂ) * Complex.I) ∂P)) := by
    refine MeasureTheory.tendsto_integral_of_dominated_convergence (fun _ => 1) ?_
      (integrable_const 1) ?_ ?_
    · intro n
      exact (Complex.measurable_exp.comp
        ((Complex.measurable_ofReal.comp (hXm n)).const_mul _ |>.mul_const _)).aestronglyMeasurable
    · intro n
      exact Filter.Eventually.of_forall fun ω => le_of_eq (hnormone _ ω)
    · filter_upwards [hae] with ω hω
      exact (Complex.continuous_exp.tendsto _).comp
        (((Complex.continuous_ofReal.tendsto _).comp hω).const_mul _ |>.mul_const _)
  -- each term is the characteristic function of a Gaussian
  have hterm : ∀ n, ∫ ω, Complex.exp ((t : ℂ) * (X n ω : ℂ) * Complex.I) ∂P
      = Complex.exp (-((σ n : ℝ) : ℂ) * (t : ℂ) ^ 2 / 2) := by
    intro n
    have h1 : charFun (P.map (X n)) t = ∫ ω, Complex.exp ((t : ℂ) * (X n ω : ℂ) * Complex.I) ∂P := by
      rw [charFun_apply_real, integral_map (hXm n).aemeasurable]
      exact (Complex.measurable_exp.comp
        (Complex.measurable_ofReal.const_mul _ |>.mul_const _)).aestronglyMeasurable
    rw [← h1, hX n, charFun_gaussianReal]
    push_cast
    ring_nf
  have hgoal : ∫ ω, Complex.exp ((t : ℂ) * (Y ω : ℂ) * Complex.I) ∂P
      = Complex.exp (-((s : ℝ) : ℂ) * (t : ℂ) ^ 2 / 2) := by
    refine tendsto_nhds_unique (hlim.congr fun n => (hterm n)) ?_
    have : Tendsto (fun n => Complex.exp (-((σ n : ℝ) : ℂ) * (t : ℂ) ^ 2 / 2)) atTop
        (𝓝 (Complex.exp (-((s : ℝ) : ℂ) * (t : ℂ) ^ 2 / 2))) := by
      refine (Complex.continuous_exp.tendsto _).comp ?_
      exact (((Complex.continuous_ofReal.tendsto _).comp hσ).neg.mul_const _).div_const _
    exact this
  have hfm : AEStronglyMeasurable
      (fun x : ℝ => Complex.exp ((t : ℂ) * (x : ℂ) * Complex.I)) (P.map Y) :=
    (Complex.continuous_exp.comp (by fun_prop)).aestronglyMeasurable
  rw [charFun_apply_real, charFun_gaussianReal, integral_map hYm.aemeasurable hfm, hgoal]
  push_cast
  ring_nf

end LatticeProb

end
