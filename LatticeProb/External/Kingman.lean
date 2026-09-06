/-
Kingman's subadditive ergodic theorem, as an explicit hypothesis.

Mathlib does not have it.  This library now proves the two halves that Kingman's
proof rests on and the pieces that surround them, but not yet the theorem
itself:

- `LatticeProb.ae_tendsto_bLimsup` is Birkhoff's pointwise ergodic theorem,
  proved in `LatticeProb/Prob/Birkhoff.lean` from the maximal ergodic theorem;
- `LatticeProb.tendsto_integral_div` is the mean half, that `(∫ g n)/n`
  converges to its infimum, by Fekete;
- `LatticeProb.le_birkhoffSum_of_subadditiveAlong` and
  `LatticeProb.ae_limsup_div_le` are the upper bound: iterating subadditivity
  dominates `g n` by the `n`-th Birkhoff sum of `g 1`, so the upper limit of
  `g n / n` is at most the Birkhoff limit of `g 1`.

What is left is Steele's block decomposition: for a fixed horizon `N` and a
tolerance `ε`, split `[0, m)` greedily into blocks on which the family already
beats `liminf + ε`, and single steps elsewhere, and let the bad set shrink.
Until that lands the full statement is assumed here.

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
