import LatticeProb.Analysis.ClassicalIntervalGradientSineEnergy

/-! # Adjoint of the closed interval gradient on sine derivatives -/

set_option autoImplicit false

open MeasureTheory Set

namespace LatticeProb

open LQGMetric.HeatSq

/-- The closed zero-boundary interval gradient has dense domain. -/
theorem classicalIntervalGradient_closure_dense {a b : ℝ} (hab : a < b) :
    Dense ((classicalIntervalGradient a b).closure.domain : Set
      (Lp ℂ 2 (volume.restrict (Ioo a b)))) := by
  have h : Dense ((classicalIntervalGradient a b).domain : Set
      (Lp ℂ 2 (volume.restrict (Ioo a b)))) := by
    have hc := classicalIntervalGradient_domain_dense hab
    simpa only [Submodule.topologicalClosure_coe, Submodule.top_coe,
      ← dense_iff_closure_eq] using congrArg (fun s : Submodule ℂ (Lp ℂ 2 (volume.restrict (Ioo a b))) =>
        (s : Set (Lp ℂ 2 (volume.restrict (Ioo a b))))) hc
  exact h.mono (classicalIntervalGradient a b).le_closure.1

/-- Each sine derivative belongs to the adjoint domain of the closed gradient,
with value equal to the sine mode times its Dirichlet eigenvalue. -/
theorem classicalIntervalGradient_closure_adjoint_sine {a b : ℝ} (hab : a < b)
    (n : ℕ) :
    ∃ h : (intervalSineDerivative_memLp a b n).toLp
        (intervalSineDerivative a (b - a) n) ∈
          (classicalIntervalGradient a b).closure.adjoint.domain,
      (classicalIntervalGradient a b).closure.adjoint
          ⟨(intervalSineDerivative_memLp a b n).toLp
            (intervalSineDerivative a (b - a) n), h⟩ =
        (intervalSineEigenvalueMode_memLp a b n).toLp
          (fun x => ((Real.pi * (n + 1 : ℕ) / (b - a)) ^ 2 : ℝ) *
            intervalSineMode a (b - a) n x) := by
  let G := (classicalIntervalGradient a b).closure
  let d := (intervalSineDerivative_memLp a b n).toLp
    (intervalSineDerivative a (b - a) n)
  let e := (intervalSineEigenvalueMode_memLp a b n).toLp
    (fun x => ((Real.pi * (n + 1 : ℕ) / (b - a)) ^ 2 : ℝ) *
      intervalSineMode a (b - a) n x)
  have hweak : ∀ v : G.domain, inner ℂ e (v : _) = inner ℂ d (G v) := by
    intro v
    have hv := G.mem_graph v
    rw [← (classicalIntervalGradient_isClosable hab).graph_closure_eq_closure_graph,
      classicalIntervalGradient_graph] at hv
    exact classicalIntervalGradientGraph_closure_sine_energy hab _ hv n
  have hd : d ∈ G.adjoint.domain := LinearPMap.mem_adjoint_domain_of_exists _ ⟨e, hweak⟩
  exact ⟨hd, LinearPMap.adjoint_apply_eq (classicalIntervalGradient_closure_dense hab) _ hweak⟩

end LatticeProb
