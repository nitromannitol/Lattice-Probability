/-
# Archived: the Pinelis Doob step for an unrelated process

This file is not part of the built library.  It keeps the text of `PinelisDoobStep`, which was
stated in `LatticeProb/Prob/PinelisReduction.lean` as the open input of the Pinelis reduction.
The statement is false: its left-hand sum sees `S 0` and its right-hand side does not, and even
with `S 0 = 0` added it fails because `S` and `v` are unrelated.  The refutations, with the
statements written out, are `LatticeProb.not_pinelisDoobStep` and
`LatticeProb.not_pinelisDoobStep_of_start_zero` in `LatticeProb/Prob/PinelisDoobStepFalse.lean`.
No theorem of the library depends on it; the cross term is bounded by
`LatticeProb.crossTerm_le_variancePair`.
-/
import LatticeProb.Prob.PinelisReduction

open MeasureTheory ProbabilityTheory

namespace LatticeProb

/-- **The one genuinely open input: the Pinelis Doob/conditional-bound step.**

For a `F`-adapted process `S`, the cumulative separated cross term is controlled by the Rosenthal
quantities.  This is Pinelis's cumulative induction, restated on the process itself (the
strong-measurability and `L^p`/`L^{p/2}` integrability hypotheses are exactly what the transfer
lemmas above supply in the application).  It is the only hypothesis of the reduction below and is
never an axiom. -/
def PinelisDoobStep : Prop :=
  ∀ p : ℝ, 2 ≤ p → ∃ K : ℝ, 0 < K ∧
    ∀ {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ] {m₀}
      (F : Filtration ℕ m₀) (S : ℕ → Ω → ℝ) (v : ℕ → Ω → ℝ),
      (∀ i, StronglyMeasurable[F i] (S i)) →
      (∀ i, MemLp (fun ω => |S i ω| ^ (p - 2)) (ENNReal.ofReal (p / (p - 2))) μ) →
      (∀ i, MemLp (v (i + 1)) (ENNReal.ofReal (p / 2)) μ) →
      (∀ i, Integrable (fun ω => |S i ω| ^ (p - 2) * v (i + 1) ω) μ) →
      ∀ k,
        ∑ i ∈ Finset.range k,
            (∫ ω, |S i ω| ^ p ∂μ) ^ ((p - 2) / p)
              * (∫ ω, v (i + 1) ω ^ (p / 2) ∂μ) ^ (2 / p)
          ≤ K * (∫ ω, (∑ i ∈ Finset.Icc 1 k, v i ω) ^ (p / 2) ∂μ) ^ (2 / p)
              * (∫ ω, |S k ω| ^ p ∂μ) ^ ((p - 2) / p)
            + K * ∑ i ∈ Finset.Icc 1 k, ∫ ω, |S i ω| ^ p ∂μ

end LatticeProb
