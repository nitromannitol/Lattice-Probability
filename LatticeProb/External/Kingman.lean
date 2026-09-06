/-
Kingman's subadditive ergodic theorem, as an explicit hypothesis.

Mathlib does not have it and this library does not prove it, so a formalization
that needs it carries `LatticeProb.External.KingmanSubadditive` as a hypothesis
rather than as an axiom.

The statement: let `T` preserve a probability measure and let `g n` be an
integrable family which is subadditive along `T`, in the sense that
`g (m + n) ω ≤ g m ω + g n (T^m ω)`, with the means `(∫ g n) / n` bounded below.
Then `g n / n` converges almost everywhere to an invariant integrable limit.
-/
import Mathlib

open MeasureTheory Filter

namespace LatticeProb.External

-- FROZEN-STATEMENT-BEGIN
/-- **Kingman's subadditive ergodic theorem** (Kingman, 1968).  A subadditive
integrable family along a measure-preserving transformation, with means bounded
below, has `g n / n` converging almost everywhere to an invariant integrable
limit. -/
def KingmanSubadditive : Prop :=
  ∀ (Ω : Type) [MeasurableSpace Ω] (μ : Measure Ω) (_ : IsProbabilityMeasure μ)
    (T : Ω → Ω) (_ : MeasurePreserving T μ μ) (g : ℕ → Ω → ℝ)
    (_ : ∀ n, Integrable (g n) μ)
    (_ : ∀ (m n : ℕ) (ω : Ω), g (m + n) ω ≤ g m ω + g n (T^[m] ω))
    (_ : ∃ M : ℝ, ∀ n : ℕ, 1 ≤ n → M ≤ (∫ ω, g n ω ∂μ) / (n : ℝ)),
    ∃ f : Ω → ℝ, Integrable f μ ∧ (∀ ω, f (T ω) = f ω) ∧
      ∀ᵐ ω ∂μ, Tendsto (fun n : ℕ => g n ω / (n : ℝ)) atTop (nhds (f ω))
-- FROZEN-STATEMENT-END

end LatticeProb.External
