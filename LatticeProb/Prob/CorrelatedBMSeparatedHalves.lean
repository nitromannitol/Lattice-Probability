import LatticeProb.Prob.CorrelatedBMConeTimes

/-! # Independent halves of a correlated Brownian pair -/

set_option autoImplicit false

open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace LatticeProb.CorrelatedBM

open MatedCRTHarmonic.MatedCRT

/-- The centered two-coordinate paths on opposite sides of a deterministic time
are independent, regardless of the correlation of the coordinates. -/
theorem indepFun_centered_opposite_halves {γ : ℝ} {μ : Measure Path2}
    (hμ : IsCorrelatedBM2 γ μ) {d : ℝ} (hd : |d| = 1) (c : ℝ) :
    IndepFun (fun ω (p : Fin 2 × ℝ≥0) => coneIncr p.1 (c + -d * (p.2 : ℝ)) c ω)
      (fun ω (p : Fin 2 × ℝ≥0) => coneIncr p.1 (c + d * (p.2 : ℝ)) c ω) μ := by
  refine GaussIndep.indepFun_of_mem_span_of_covariance_eq_zero hμ.isGaussianProcess
    (A := fun p : Fin 2 × ℝ≥0 => coneIncr p.1 (c + -d * (p.2 : ℝ)) c)
    (B := fun p : Fin 2 × ℝ≥0 => coneIncr p.1 (c + d * (p.2 : ℝ)) c)
    (fun p => coneIncr_mem_span _ _ _) (fun p => coneIncr_mem_span _ _ _) fun p q => ?_
  rw [cov_coneIncr hμ]
  have hp := p.2.coe_nonneg
  have hq := q.2.coe_nonneg
  have e1 : |c + -d * (p.2 : ℝ) - c| = p.2 := by
    rw [show c + -d * (p.2 : ℝ) - c = -d * p.2 by ring, abs_mul, abs_neg,
      hd, one_mul, abs_of_nonneg hp]
  have e2 : |c + d * (q.2 : ℝ) - c| = q.2 := by
    rw [show c + d * (q.2 : ℝ) - c = d * q.2 by ring, abs_mul, hd, one_mul,
      abs_of_nonneg hq]
  have e3 : |c + -d * (p.2 : ℝ) - (c + d * q.2)| = p.2 + q.2 := by
    rw [show c + -d * (p.2 : ℝ) - (c + d * q.2) = -d * (p.2 + q.2) by ring,
      abs_mul, abs_neg, hd, one_mul, abs_of_nonneg (add_nonneg hp hq)]
  rw [e1, e2, e3]
  ring

end LatticeProb.CorrelatedBM
