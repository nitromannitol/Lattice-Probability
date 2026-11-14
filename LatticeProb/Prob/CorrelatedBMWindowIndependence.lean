import LatticeProb.Prob.CorrelatedBMConeTimes

/-!
# Independent increment windows

The coordinate increment processes of a two-sided correlated Brownian pair on
intervals with disjoint interiors are mutually independent.
-/

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Set

namespace LatticeProb.CorrelatedBM

open MatedCRTHarmonic.MatedCRT

/-- Increments over two time-ordered intervals have zero covariance. -/
theorem cov_coneIncr_eq_zero_of_ordered {γ : ℝ} {μ : Measure Path2}
    (hμ : IsCorrelatedBM2 γ μ) (i j : Fin 2) {a x b y : ℝ}
    (hax : a ≤ x) (hxb : x ≤ b) (hby : b ≤ y) :
    cov[coneIncr i x a, coneIncr j y b; μ] = 0 := by
  have : IsProbabilityMeasure μ := hμ.isProbabilityMeasure
  have hL2 (k : Fin 2) (u v : ℝ) : MemLp (coneIncr k u v) 2 μ := by
    exact ((hμ.isGaussianProcess.hasGaussianLaw_eval (k, u)).memLp_two).sub
      ((hμ.isGaussianProcess.hasGaussianLaw_eval (k, v)).memLp_two)
  have hz (u : ℝ) (hu : u ≤ b) :
      cov[coneIncr i u b, coneIncr j y b; μ] = 0 := by
    rw [cov_coneIncr hμ, abs_of_nonpos (sub_nonpos.mpr hu),
      abs_of_nonneg (sub_nonneg.mpr hby), abs_of_nonpos (sub_nonpos.mpr (hu.trans hby))]
    ring
  have heq : coneIncr i x a = fun ω => coneIncr i x b ω - coneIncr i a b ω := by
    funext ω
    simp only [coneIncr]
    ring
  rw [heq, covariance_fun_sub_left (hL2 i x b) (hL2 i a b) (hL2 j y b),
    hz x hxb, hz a (hax.trans hxb), sub_self]

/-- Increment processes indexed by intervals whose interiors are disjoint are
mutually independent, including when endpoints coincide. -/
theorem iIndepFun_increment_windows {ι : Type*} {γ : ℝ} {μ : Measure Path2}
    (hμ : IsCorrelatedBM2 γ μ) (l r : ι → ℝ)
    (hsep : ∀ i j, i ≠ j → r i ≤ l j ∨ r j ≤ l i) :
    iIndepFun (fun i ω (p : Fin 2 × {x : ℝ // x ∈ Icc (l i) (r i)}) =>
      coneIncr p.1 p.2.1 (l i) ω) μ := by
  let X := fun (i : ι) (p : Fin 2 × {x : ℝ // x ∈ Icc (l i) (r i)}) =>
    coneIncr p.1 p.2.1 (l i)
  have hG : IsGaussianProcess (fun p : (i : ι) × (Fin 2 × {x : ℝ // x ∈ Icc (l i) (r i)}) =>
      X p.1 p.2) μ :=
    GaussIndep.isGaussianProcess_of_mem_span hμ.isGaussianProcess
      (fun p => coneIncr_mem_span _ _ _)
  refine IsGaussianProcess.iIndepFun_of_covariance_eq_zero hG
    (fun i p => (hG.aemeasurable ⟨i, p⟩)) ?_
  intro i j hij p q
  rcases hsep i j hij with h | h
  · exact cov_coneIncr_eq_zero_of_ordered hμ p.1 q.1 p.2.2.1
      (p.2.2.2.trans h) q.2.2.1
  · rw [covariance_comm]
    exact cov_coneIncr_eq_zero_of_ordered hμ q.1 p.1 q.2.2.1
      (q.2.2.2.trans h) p.2.2.1

end LatticeProb.CorrelatedBM
