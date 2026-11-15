import LatticeProb.Analysis.ClassicalIntervalGradientSineComposition

/-! # Sine pairings for the interval gradient composition -/

set_option autoImplicit false

open MeasureTheory Set

namespace LatticeProb

open LQGMetric.HeatSq

/-- The adjoint-gradient composition satisfies the Dirichlet sine coefficient
identity on its domain. -/
theorem classicalIntervalGradient_closure_adjoint_gradient_sine_pairing {a b : ℝ}
    (hab : a < b) (u : (classicalIntervalGradient a b).closure.domain)
    (hu : (classicalIntervalGradient a b).closure u ∈
      (classicalIntervalGradient a b).closure.adjoint.domain) (n : ℕ) :
    inner ℂ ((intervalSineMode_memLp a b n).toLp (intervalSineMode a (b - a) n))
        ((classicalIntervalGradient a b).closure.adjoint ⟨_, hu⟩) =
      inner ℂ ((intervalSineEigenvalueMode_memLp a b n).toLp
        (fun x => ((Real.pi * (n + 1 : ℕ) / (b - a)) ^ 2 : ℝ) *
          intervalSineMode a (b - a) n x)) (u : _) := by
  let G := (classicalIntervalGradient a b).closure
  obtain ⟨hs, hsval⟩ := classicalIntervalGradient_closure_sine hab n
  obtain ⟨hd, hdval⟩ := classicalIntervalGradient_closure_adjoint_sine hab n
  have hf := LinearPMap.adjoint_isFormalAdjoint (classicalIntervalGradient_closure_dense hab)
  have h1 := hf.symm ⟨_, hs⟩ ⟨G u, hu⟩
  have h2 := hf ⟨_, hd⟩ u
  rw [hsval] at h1
  rw [hdval] at h2
  exact h1.symm.trans h2.symm

end LatticeProb
