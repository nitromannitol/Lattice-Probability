import LatticeProb.Analysis.ClassicalIntervalGradientSineComposition

/-! # Finite sine sums for the closed interval gradient -/

set_option autoImplicit false

open MeasureTheory Set Finset
open scoped BigOperators

namespace LatticeProb

open LQGMetric.HeatSq

/-- Finite complex combinations of sine modes and their derivatives lie in the
respective graphs of the closed interval gradient and its adjoint. -/
theorem classicalIntervalGradient_closure_finite_sines_graph {a b : ℝ} (hab : a < b)
    (s : Finset ℕ) (c : ℕ → ℂ) :
    ((∑ n ∈ s, c n • (intervalSineMode_memLp a b n).toLp
        (intervalSineMode a (b - a) n)),
      (∑ n ∈ s, c n • (intervalSineDerivative_memLp a b n).toLp
        (intervalSineDerivative a (b - a) n))) ∈
      (classicalIntervalGradient a b).closure.graph ∧
    ((∑ n ∈ s, c n • (intervalSineDerivative_memLp a b n).toLp
        (intervalSineDerivative a (b - a) n)),
      (∑ n ∈ s, c n • (intervalSineEigenvalueMode_memLp a b n).toLp
        (fun x => ((Real.pi * (n + 1 : ℕ) / (b - a)) ^ 2 : ℝ) *
          intervalSineMode a (b - a) n x))) ∈
      (classicalIntervalGradient a b).closure.adjoint.graph := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert n s hn ih =>
    obtain ⟨hs, hsval⟩ := classicalIntervalGradient_closure_sine hab n
    obtain ⟨hd, hdval⟩ := classicalIntervalGradient_closure_adjoint_sine hab n
    have hg := ((classicalIntervalGradient a b).closure.mem_graph ⟨_, hs⟩)
    rw [hsval] at hg
    have ha := ((classicalIntervalGradient a b).closure.adjoint.mem_graph ⟨_, hd⟩)
    rw [hdval] at ha
    constructor
    · simpa only [Finset.sum_insert hn, Prod.smul_mk, Prod.mk_add_mk] using
        ((classicalIntervalGradient a b).closure.graph.add_mem
          ((classicalIntervalGradient a b).closure.graph.smul_mem (c n) hg) ih.1)
    · simpa only [Finset.sum_insert hn, Prod.smul_mk, Prod.mk_add_mk] using
        ((classicalIntervalGradient a b).closure.adjoint.graph.add_mem
          ((classicalIntervalGradient a b).closure.adjoint.graph.smul_mem (c n) ha) ih.2)

/-- On every finite sine combination, the adjoint-gradient composition is the
corresponding finite sum of Dirichlet eigenvalue modes. -/
theorem classicalIntervalGradient_closure_adjoint_gradient_finite_sines {a b : ℝ}
    (hab : a < b) (s : Finset ℕ) (c : ℕ → ℂ) :
    ∃ hs : (∑ n ∈ s, c n • (intervalSineMode_memLp a b n).toLp
        (intervalSineMode a (b - a) n)) ∈ (classicalIntervalGradient a b).closure.domain,
    ∃ hd : (classicalIntervalGradient a b).closure ⟨_, hs⟩ ∈
        (classicalIntervalGradient a b).closure.adjoint.domain,
      (classicalIntervalGradient a b).closure.adjoint ⟨_, hd⟩ =
        ∑ n ∈ s, c n • (intervalSineEigenvalueMode_memLp a b n).toLp
          (fun x => ((Real.pi * (n + 1 : ℕ) / (b - a)) ^ 2 : ℝ) *
            intervalSineMode a (b - a) n x) := by
  obtain ⟨hg, ha⟩ := classicalIntervalGradient_closure_finite_sines_graph hab s c
  have hs := LinearPMap.mem_domain_of_mem_graph hg
  have hv := (LinearPMap.image_iff hs).2 hg
  have hd := LinearPMap.mem_domain_of_mem_graph ha
  refine ⟨hs, hv ▸ hd, ?_⟩
  simpa only [← hv] using ((LinearPMap.image_iff hd).2 ha).symm

end LatticeProb
