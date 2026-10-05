import Mathlib
import LatticeProb.Prob.MehlerInterpolation

/-!
# Pitt's Gaussian association theorem: the statements

Pitt (Ann. Probab. 10 (1982), 496-499): a centred Gaussian vector with nonnegative covariances is
associated.  The proof is staged through four propositions, each proved from the previous one:

* `PittCovRep k`: the covariance representation for the standard Gaussian on `ℝ^k` (Mehler/OU
  interpolation with a weight);
* `PittSmoothStmt k`: association for `C²_b` coordinatewise nondecreasing functions, any PSD
  covariance with nonnegative entries;
* `PittNondegStmt k`: association for bounded Borel nondecreasing functions, nondegenerate covariance;
* `PittFullStmt k`: association for bounded Borel nondecreasing functions, any PSD covariance with
  nonnegative entries.
-/

open MeasureTheory ProbabilityTheory
open scoped MatrixOrder

namespace LatticeProb

/-- Coordinatewise nondecreasing. -/
def PittMono {k : ℕ} (f : EuclideanSpace ℝ (Fin k) → ℝ) : Prop :=
  ∀ x y : EuclideanSpace ℝ (Fin k), (∀ i, x i ≤ y i) → f x ≤ f y

/-- Covariance representation for the standard Gaussian `γ` on `ℝ^k`:
`Cov_γ(F, G) = ∫_0^{π/2} sin a · ∑_i E[ ∂_i F(Z) · E_W ∂_i G(cos a Z + sin a W) ] da`
for `F ∈ C¹_b`, `G ∈ C²_b`. -/
def PittCovRep (k : ℕ) : Prop :=
  ∀ F G : EuclideanSpace ℝ (Fin k) → ℝ, mehlerIClassC1b F → mehlerIClassC2b G →
    ∫ z, F z * G z ∂(stdGaussian (EuclideanSpace ℝ (Fin k)))
        - (∫ z, F z ∂(stdGaussian (EuclideanSpace ℝ (Fin k))))
          * (∫ z, G z ∂(stdGaussian (EuclideanSpace ℝ (Fin k))))
      = ∫ a in Set.Ioo 0 (Real.pi / 2), Real.sin a *
          ∑ i : Fin k, ∫ z, fderiv ℝ F z (EuclideanSpace.single i (1 : ℝ)) *
            (∫ w, fderiv ℝ G (Real.cos a • z + Real.sin a • w)
              (EuclideanSpace.single i (1 : ℝ)) ∂(stdGaussian (EuclideanSpace ℝ (Fin k))))
            ∂(stdGaussian (EuclideanSpace ℝ (Fin k)))

/-- Association for smooth bounded nondecreasing functions. -/
def PittSmoothStmt (k : ℕ) : Prop :=
  ∀ S : Matrix (Fin k) (Fin k) ℝ, S.PosSemidef → (∀ i j, 0 ≤ S i j) →
    ∀ f g : EuclideanSpace ℝ (Fin k) → ℝ, mehlerIClassC2b f → mehlerIClassC2b g →
      PittMono f → PittMono g →
      (∫ x, f x ∂(multivariateGaussian (0 : EuclideanSpace ℝ (Fin k)) S))
          * (∫ x, g x ∂(multivariateGaussian (0 : EuclideanSpace ℝ (Fin k)) S))
        ≤ ∫ x, f x * g x ∂(multivariateGaussian (0 : EuclideanSpace ℝ (Fin k)) S)

/-- Association for bounded Borel nondecreasing functions, nondegenerate covariance. -/
def PittNondegStmt (k : ℕ) : Prop :=
  ∀ S : Matrix (Fin k) (Fin k) ℝ, S.PosDef → (∀ i j, 0 ≤ S i j) →
    ∀ f g : EuclideanSpace ℝ (Fin k) → ℝ, Measurable f → Measurable g →
      (∃ M : ℝ, ∀ x, |f x| ≤ M) → (∃ M : ℝ, ∀ x, |g x| ≤ M) → PittMono f → PittMono g →
      (∫ x, f x ∂(multivariateGaussian (0 : EuclideanSpace ℝ (Fin k)) S))
          * (∫ x, g x ∂(multivariateGaussian (0 : EuclideanSpace ℝ (Fin k)) S))
        ≤ ∫ x, f x * g x ∂(multivariateGaussian (0 : EuclideanSpace ℝ (Fin k)) S)

/-- Association for bounded Borel nondecreasing functions, any PSD covariance with nonnegative
entries (Pitt's theorem). -/
def PittFullStmt (k : ℕ) : Prop :=
  ∀ S : Matrix (Fin k) (Fin k) ℝ, S.PosSemidef → (∀ i j, 0 ≤ S i j) →
    ∀ f g : EuclideanSpace ℝ (Fin k) → ℝ, Measurable f → Measurable g →
      (∃ M : ℝ, ∀ x, |f x| ≤ M) → (∃ M : ℝ, ∀ x, |g x| ≤ M) → PittMono f → PittMono g →
      (∫ x, f x ∂(multivariateGaussian (0 : EuclideanSpace ℝ (Fin k)) S))
          * (∫ x, g x ∂(multivariateGaussian (0 : EuclideanSpace ℝ (Fin k)) S))
        ≤ ∫ x, f x * g x ∂(multivariateGaussian (0 : EuclideanSpace ℝ (Fin k)) S)

end LatticeProb
