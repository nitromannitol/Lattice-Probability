import Mathlib
import LatticeProb.Prob.MvbeOrthantBerryEsseen

/-!
# Solution: MultivariateBerryEsseen

The challenge module `LatticeProbAudit/MultivariateBerryEsseen/Challenge.lean` imports only Mathlib and
states the multivariate Berry-Esseen comparison for orthants (dimension factor `m`) with one intentional
`sorry`.  This solution proves the byte-identical statement by
`LatticeProb.mvbe_frozenShape_linear_unconditional`, whose statement is the challenge's after unfolding
`LatticeProb.MvbeFrozenShape`, `LatticeProb.mvbeWhGram`, `LatticeProb.mvbeWhQuadForm` and
`LatticeProb.mvbeWhCoeffNorm`.
-/

open MeasureTheory ProbabilityTheory

namespace LatticeProbAudit

/-- **Multivariate Berry-Esseen comparison for orthants** (dimension factor `m`). -/
theorem multivariate_berry_esseen_orthant :
    ∀ M δ : ℝ, 0 < M → 0 < δ → δ < 1 →
      ∃ C : ℝ, 0 < C ∧
        ∀ (N m : ℕ), 1 ≤ m →
          ∀ ν : Measure ℝ, IsProbabilityMeasure ν →
            ∫ z, z ∂ν = 0 → 0 < variance id ν →
            Integrable (fun z => |z| ^ 3) ν →
            ∫ z, |z| ^ 3 ∂ν ≤ M * variance id ν ^ ((3 : ℝ) / 2) →
            ∀ a : Fin N → Fin m → ℝ,
              (∀ v : Fin m → ℝ,
                (1 - δ) * ∑ j, v j ^ 2 ≤
                    ∑ j, ∑ k, (variance id ν * ∑ i, a i j * a i k) * v j * v k ∧
                  ∑ j, ∑ k, (variance id ν * ∑ i, a i j * a i k) * v j * v k ≤
                    (1 + δ) * ∑ j, v j ^ 2) →
              ∀ h : Fin m → ℝ,
                |((Measure.pi fun _ : Fin N => ν)
                        {ξ | ∀ j, ∑ i, a i j * ξ i ≤ h j}).toReal -
                    (multivariateGaussian (0 : EuclideanSpace ℝ (Fin m))
                        (Matrix.of fun j k => variance id ν * ∑ i, a i j * a i k)
                        {y | ∀ j, y j ≤ h j}).toReal| ≤
                  C * (m : ℝ) * variance id ν ^ ((3 : ℝ) / 2) *
                    ∑ i, Real.sqrt (∑ j, a i j ^ 2) ^ 3 := by
  exact LatticeProb.mvbe_frozenShape_linear_unconditional

end LatticeProbAudit
