import Mathlib

/-!
# Multivariate Berry-Esseen for orthants with the factor `m^{1/4}`: comparator challenge

Mathlib-only comparator challenge for the multivariate Berry-Esseen comparison on orthants with the
dimension factor `m` (Raič, *Bernoulli* 25 (2019), Theorem 1.3 for rounded orthants),
`LatticeProb.mvbe_frozenQuarter_unconditional` in `LatticeProb/Prob/MvbeOrthantPerimeterProved.lean`, textually the frozen `Sandpile.External.MultivariateBerryEsseen`.

Content: for every `M > 0` and `0 < δ < 1` there is `C > 0` such that for every `N`, `m ≥ 1`, every
centred probability law `ν` on `ℝ` with finite third absolute moment at most `M Var(ν)^{3/2}` and
positive variance, and every coefficient array `a : Fin N → Fin m → ℝ` whose covariance matrix
`Σ_{jk} = Var(ν) ∑ᵢ a i j a i k` has quadratic form between `(1-δ)|v|²` and `(1+δ)|v|²`, the law of the
linear forms `Y_j = ∑ᵢ a i j ξᵢ` (i.i.d. `ξᵢ ~ ν`) and the centred Gaussian `N(0, Σ)` assign to every
orthant `{y_j ≤ h_j}` probabilities that differ by at most `C m^{1/4} Var(ν)^{3/2} ∑ᵢ |a i|³`.

Only Mathlib is imported and no definition is needed: the covariance matrix, the quadratic form and
the Euclidean norm of a coefficient vector are written out.  The sole intentional `sorry` is the proof
of the final theorem.

## Presentation deltas

The library names the covariance matrix `mvbeWhGram ν a`, the quadratic form `mvbeWhQuadForm S v` and
the coefficient norm `mvbeWhCoeffNorm a i`; the challenge writes out their bodies.
-/

open MeasureTheory ProbabilityTheory

namespace LatticeProbAudit

/-- **Multivariate Berry-Esseen comparison for orthants** (dimension factor `m^{1/4}`). -/
theorem multivariate_berry_esseen_quarter :
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
                  C * (m : ℝ) ^ ((1 : ℝ) / 4) * variance id ν ^ ((3 : ℝ) / 2) *
                    ∑ i, Real.sqrt (∑ j, a i j ^ 2) ^ 3 := by
  sorry

end LatticeProbAudit
