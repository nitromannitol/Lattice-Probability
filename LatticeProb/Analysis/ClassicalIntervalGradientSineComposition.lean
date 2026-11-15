import LatticeProb.Analysis.ClassicalIntervalGradientSineAdjoint

/-! # Sine modes of the closed interval gradient and its adjoint -/

set_option autoImplicit false

open MeasureTheory Set

namespace LatticeProb

open LQGMetric.HeatSq

/-- Each sine mode belongs to the closed gradient domain, with its classical
sine derivative as image. -/
theorem classicalIntervalGradient_closure_sine {a b : ℝ} (hab : a < b)
    (n : ℕ) :
    ∃ h : (intervalSineMode_memLp a b n).toLp (intervalSineMode a (b - a) n) ∈
        (classicalIntervalGradient a b).closure.domain,
      (classicalIntervalGradient a b).closure
          ⟨(intervalSineMode_memLp a b n).toLp (intervalSineMode a (b - a) n), h⟩ =
        (intervalSineDerivative_memLp a b n).toLp (intervalSineDerivative a (b - a) n) := by
  let s := (intervalSineMode_memLp a b n).toLp (intervalSineMode a (b - a) n)
  let d := (intervalSineDerivative_memLp a b n).toLp (intervalSineDerivative a (b - a) n)
  have hgraph : (s, d) ∈ (classicalIntervalGradient a b).graph := by
    rw [classicalIntervalGradient_graph]
    refine ⟨intervalSineMode a (b - a) n, intervalSineDerivative a (b - a) n,
      (intervalSineMode_memLp a b n).coeFn_toLp,
      (intervalSineDerivative_memLp a b n).coeFn_toLp, ?_, ?_, ?_, ?_⟩
    · have hc : Continuous (intervalSineMode a (b - a) n) := by
        unfold intervalSineMode sinMode
        fun_prop
      exact hc.continuousOn
    · have h := (sinMode_const_mul_endpoints a (b - a) 1 (n + 1) (by linarith)).1
      simpa [intervalSineMode] using congrArg (fun x : ℝ => (x : ℂ)) h
    · have h := (sinMode_const_mul_endpoints a (b - a) 1 (n + 1) (by linarith)).2
      have he : a + (b - a) = b := by ring
      rw [he] at h
      simpa [intervalSineMode] using congrArg (fun x : ℝ => (x : ℂ)) h
    · intro x hx
      convert (hasDerivAt_const_mul_sinMode a (b - a) 1 (n + 1) x).ofReal_comp using 1 <;>
        simp only [intervalSineDerivative, one_mul]
      funext y
      rfl
  have hclosed : (s, d) ∈ (classicalIntervalGradient a b).closure.graph :=
    LinearPMap.le_graph_of_le (classicalIntervalGradient a b).le_closure hgraph
  have hs : s ∈ (classicalIntervalGradient a b).closure.domain :=
    LinearPMap.mem_domain_of_mem_graph hclosed
  exact ⟨hs, (LinearPMap.image_iff hs).2 hclosed |>.symm⟩

/-- Applying the adjoint after the closed gradient sends a sine mode to its
Dirichlet eigenvalue times that mode. -/
theorem classicalIntervalGradient_closure_adjoint_gradient_sine {a b : ℝ}
    (hab : a < b) (n : ℕ) :
    ∃ hs : (intervalSineMode_memLp a b n).toLp (intervalSineMode a (b - a) n) ∈
        (classicalIntervalGradient a b).closure.domain,
    ∃ hd : (classicalIntervalGradient a b).closure
        ⟨(intervalSineMode_memLp a b n).toLp (intervalSineMode a (b - a) n), hs⟩ ∈
        (classicalIntervalGradient a b).closure.adjoint.domain,
      (classicalIntervalGradient a b).closure.adjoint
        ⟨(classicalIntervalGradient a b).closure
          ⟨(intervalSineMode_memLp a b n).toLp (intervalSineMode a (b - a) n), hs⟩, hd⟩ =
        (intervalSineEigenvalueMode_memLp a b n).toLp
          (fun x => ((Real.pi * (n + 1 : ℕ) / (b - a)) ^ 2 : ℝ) *
            intervalSineMode a (b - a) n x) := by
  obtain ⟨hs, himage⟩ := classicalIntervalGradient_closure_sine hab n
  obtain ⟨hd, hadj⟩ := classicalIntervalGradient_closure_adjoint_sine hab n
  refine ⟨hs, himage ▸ hd, ?_⟩
  simpa only [himage] using hadj

end LatticeProb
