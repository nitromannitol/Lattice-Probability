import LatticeProb.Analysis.ClassicalIntervalGradientCompositionPairing
import LatticeProb.Analysis.IntervalSineHilbertBasis
import LatticeProb.Analysis.WedgeArcSineClosureFourier

/-! # Sine graph of the interval gradient composition -/

set_option autoImplicit false

open MeasureTheory Set

namespace LatticeProb

open LQGMetric.HeatSq

/-- The graph of the closed interval gradient followed by its adjoint lies in
 the closure of the finite diagonal sine graph. -/
theorem classicalIntervalGradient_composition_mem_sineGraph_closure {a b : ℝ}
    (hab : a < b) (u : (classicalIntervalGradient a b).closure.domain)
    (hu : (classicalIntervalGradient a b).closure u ∈
      (classicalIntervalGradient a b).closure.adjoint.domain) :
    ((u : Lp ℂ 2 (volume.restrict (Ioo a b))),
      (classicalIntervalGradient a b).closure.adjoint ⟨_, hu⟩) ∈
      (show (Lp ℂ 2 (volume.restrict (Ioo a b))) →ₗ.[ℂ]
        (Lp ℂ 2 (volume.restrict (Ioo a b))) from
        ⟨_, orthonormalDiagonalCore (intervalSineHilbertBasis hab).orthonormal
          (fun n => (Real.pi * (n + 1 : ℕ) / (b - a)) ^ 2)⟩).graph.topologicalClosure := by
  apply (hilbertBasis_diagonal_graph_closure_iff (intervalSineHilbertBasis hab)
    (fun n => (Real.pi * (n + 1 : ℕ) / (b - a)) ^ 2) _ _).2
  intro n
  have heig : (intervalSineEigenvalueMode_memLp a b n).toLp
      (fun x => ((Real.pi * (n + 1 : ℕ) / (b - a)) ^ 2 : ℝ) *
        intervalSineMode a (b - a) n x) =
      (((Real.pi * (n + 1 : ℕ) / (b - a)) ^ 2 : ℝ) : ℂ) •
        (intervalSineMode_memLp a b n).toLp (intervalSineMode a (b - a) n) := by
    rw [← MemLp.toLp_const_smul]
    congr 1
  have hp := classicalIntervalGradient_closure_adjoint_gradient_sine_pairing hab u hu n
  rw [heig, inner_smul_left, Complex.conj_ofReal] at hp
  rw [intervalSineHilbertBasis_apply, intervalNormalizedSineLp,
    inner_smul_left, inner_smul_left, Complex.conj_ofReal]
  rw [hp]
  ring

end LatticeProb
