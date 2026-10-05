import Mathlib
import LatticeProb.Prob.PittFinal

/-!
# Solution: PittGaussianFKG

The challenge module `LatticeProbAudit/PittGaussianFKG/Challenge.lean` imports only Mathlib and states
Pitt's Gaussian association theorem with one intentional `sorry`.  This solution proves the
byte-identical statement by `LatticeProb.pitt_gaussian_fkg`.
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
      ≤ ∫ ω, f (fun i => X (q i) ω) * g (fun i => X (q i) ω) ∂P :=
  LatticeProb.pitt_gaussian_fkg P X hG hm hmean hcov k q f g hf hg hfm hgm hfb hgb

end LatticeProbAudit
