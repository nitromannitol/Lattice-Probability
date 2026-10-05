import Mathlib

/-!
# Pitt's Gaussian association theorem: comparator challenge

Mathlib-only comparator challenge for Pitt's theorem (Pitt, *Ann. Probab.* 10 (1982) 496-499),
`LatticeProb.pitt_gaussian_fkg` in `LatticeProb/Prob/PittFinal.lean`.

Content: let `X t` (`t ∈ T`) be a centred Gaussian family on a probability space, with integrable,
measurable members and integrable pairwise products whose expectations are nonnegative.  Then for any
finitely many indices `q 0, …, q (k-1)` and any bounded Borel coordinatewise nondecreasing functions
`f`, `g` of `k` real variables, with `Y = (X (q i))ᵢ`,
`E f(Y) · E g(Y) ≤ E f(Y) g(Y)`.  Covariance matrices may be singular.

Only Mathlib is imported and no definition is needed (`IsGaussianProcess` is Mathlib's).  The sole
intentional `sorry` is the proof of the final theorem.
-/

open MeasureTheory ProbabilityTheory

namespace LatticeProbAudit

/-- **Pitt's Gaussian association theorem** for Gaussian families on an arbitrary index set. -/
theorem pitt_gaussian_fkg {Ω T : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (X : T → Ω → ℝ) (hG : IsGaussianProcess X P)
    (hm : ∀ t, Measurable (X t))
    (hmean : ∀ t, Integrable (X t) P ∧ ∫ ω, X t ω ∂P = 0)
    (hcov : ∀ s t, Integrable (fun ω => X s ω * X t ω) P ∧ 0 ≤ ∫ ω, X s ω * X t ω ∂P)
    (k : ℕ) (q : Fin k → T) (f g : (Fin k → ℝ) → ℝ) (hf : Monotone f) (hg : Monotone g)
    (hfm : Measurable f) (hgm : Measurable g) (hfb : ∃ M : ℝ, ∀ x, |f x| ≤ M)
    (hgb : ∃ M : ℝ, ∀ x, |g x| ≤ M) :
    (∫ ω, f (fun i => X (q i) ω) ∂P) * (∫ ω, g (fun i => X (q i) ω) ∂P)
      ≤ ∫ ω, f (fun i => X (q i) ω) * g (fun i => X (q i) ω) ∂P := by
  sorry

end LatticeProbAudit
