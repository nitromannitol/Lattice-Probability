import LatticeProb.Prob.BrownianContAll

open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace LatticeProb

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}

/-- Coordinate copies of a real Brownian process on the fourfold product space. -/
def brownianFourCopy (B : ℝ≥0 → Ω → ℝ) (i : Fin 4) (t : ℝ≥0) (ω : Fin 4 → Ω) : ℝ :=
  B t (ω i)

/-- Coordinate copies retain the complete Brownian predicate and measurable continuous paths,
and arbitrary finite time blocks are independent across coordinates. -/
theorem brownian_four_copies (B : ℝ≥0 → Ω → ℝ) (hB : IsBrownianReal B P)
    (hm : ∀ t, Measurable (B t)) (hc : ∀ ω, Continuous fun t => B t ω) :
    (∀ i, IsBrownianReal (brownianFourCopy B i) (Measure.pi fun _ : Fin 4 => P)) ∧
    (∀ i t, Measurable (brownianFourCopy B i t)) ∧
    (∀ i ω, Continuous fun t => brownianFourCopy B i t ω) ∧
    (∀ n : ℕ, ∀ times : Fin 4 → Fin n → ℝ≥0,
      iIndepFun (fun i ω j => brownianFourCopy B i (times i j) ω)
        (Measure.pi fun _ : Fin 4 => P)) := by
  haveI : IsProbabilityMeasure P := hB.isGaussianProcess.isProbabilityMeasure
  refine ⟨fun i => isBrownianReal_comp_eval hB i, ?_, ?_, ?_⟩
  · intro i t
    exact (hm t).comp (measurable_pi_apply i)
  · intro i ω
    exact hc (ω i)
  · intro n times
    exact iIndepFun_pi (fun i => (measurable_pi_lambda _ fun j => hm (times i j)).aemeasurable)

/-- The coordinate process has positive variance at any positive time. -/
theorem brownian_four_copy_covariance (B : ℝ≥0 → Ω → ℝ) (hB : IsBrownianReal B P)
    (i : Fin 4) (t : ℝ≥0) :
    cov[brownianFourCopy B i t, brownianFourCopy B i t; Measure.pi fun _ : Fin 4 => P] = t := by
  haveI : IsProbabilityMeasure P := hB.isGaussianProcess.isProbabilityMeasure
  change cov[(fun ω => B t (ω i)), (fun ω => B t (ω i)); Measure.pi fun _ : Fin 4 => P] = t
  simpa only [min_self] using (isBrownianReal_comp_eval (d := 4) hB i).toIsPreBrownianReal.covariance_eval t t

/-- All four copies start at zero simultaneously almost surely. -/
theorem brownian_four_copies_start_zero (B : ℝ≥0 → Ω → ℝ) (hB : IsBrownianReal B P) :
    ∀ᵐ ω ∂(Measure.pi fun _ : Fin 4 => P), ∀ i, brownianFourCopy B i 0 ω = 0 := by
  haveI : IsProbabilityMeasure P := hB.isGaussianProcess.isProbabilityMeasure
  rw [ae_all_iff]
  intro i
  exact (isBrownianReal_comp_eval (d := 4) hB i).toIsPreBrownianReal.eval_zero_ae_eq_zero

end LatticeProb
