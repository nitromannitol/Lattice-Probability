import Mathlib
import LatticeProb.Prob.PittStatements
import LatticeProb.Prob.PittCovariance
import LatticeProb.Prob.PittSmooth
import LatticeProb.Prob.PittNondegenerate
import LatticeProb.Prob.PittDegenerate
import LatticeProb.Prob.PittGlue

/-!
# Pitt's Gaussian association theorem

Composition of the four stages (`PittCovariance`, `PittSmooth`, `PittNondegenerate`,
`PittDegenerate`) and the passage to Gaussian families on an arbitrary index set (`PittGlue`).
-/

open MeasureTheory ProbabilityTheory

namespace LatticeProb

/-- **Pitt's theorem for Gaussian vectors**: a centred Gaussian vector on `ℝ^k` with positive
semidefinite covariance matrix with nonnegative entries is associated: for bounded Borel
coordinatewise nondecreasing `f`, `g`, `(∫ f)(∫ g) ≤ ∫ f g`. -/
theorem pitt_fullStmt (k : ℕ) : PittFullStmt k :=
  pitt_full k (pitt_nondeg k (pitt_smooth k (pitt_covRep k)))

/-- **Pitt's Gaussian association theorem for Gaussian families** (Pitt, Ann. Probab. 10 (1982),
496-499), in the vocabulary of the frozen `Sandpile.External.PittGaussianFKG`: a centred Gaussian
family `X : T → Ω → ℝ` with nonnegative covariances is positively associated: for any finitely many
indices `q : Fin k → T` and bounded Borel coordinatewise nondecreasing `f`, `g` on `Fin k → ℝ`,
`E f(Y) · E g(Y) ≤ E f(Y) g(Y)` with `Y = (X (q i))_i`. -/
theorem pitt_gaussian_fkg {Ω T : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (X : T → Ω → ℝ) (hG : IsGaussianProcess X P)
    (hm : ∀ t, Measurable (X t))
    (hmean : ∀ t, Integrable (X t) P ∧ ∫ ω, X t ω ∂P = 0)
    (hcov : ∀ s t, Integrable (fun ω => X s ω * X t ω) P ∧ 0 ≤ ∫ ω, X s ω * X t ω ∂P)
    (k : ℕ) (q : Fin k → T) (f g : (Fin k → ℝ) → ℝ) (hf : Monotone f) (hg : Monotone g)
    (hfm : Measurable f) (hgm : Measurable g) (hfb : ∃ M : ℝ, ∀ x, |f x| ≤ M)
    (hgb : ∃ M : ℝ, ∀ x, |g x| ≤ M) :
    (∫ ω, f (fun i => X (q i) ω) ∂P) * (∫ ω, g (fun i => X (q i) ω) ∂P)
      ≤ ∫ ω, f (fun i => X (q i) ω) * g (fun i => X (q i) ω) ∂P :=
  pitt_associated_of_gaussianProcess (fun k => pitt_fullStmt k) P X hG hm hmean hcov k q f g hf hg
    hfm hgm hfb hgb

end LatticeProb
