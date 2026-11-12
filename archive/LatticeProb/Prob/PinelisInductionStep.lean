/-
# Archived: the Pinelis induction step without `L^p` hypotheses

This file is not part of the built library.  It keeps the text of `PinelisInductionStep`, which
was stated in `LatticeProb/Prob/BernsteinInduction.lean` as the remaining step of the martingale
Rosenthal argument.  The statement is false: it carries no `L^p` hypothesis, so for a mean-zero
`Y ∈ L²` with `Y ∉ L⁴` the Bochner integrals on its right-hand side are the junk value `0` while
the left-hand side is positive.  The refutation, with the statement written out, is
`LatticeProb.not_pinelisInductionStep` in `LatticeProb/Prob/PinelisInductionStepFalse.lean`.
No theorem of the library depends on it; the cross term is bounded by
`LatticeProb.crossTerm_le_variancePair`.
-/
import LatticeProb.Prob.BernsteinInduction

open MeasureTheory ProbabilityTheory

namespace LatticeProb

/-- **The single remaining induction step of Pinelis**, as a named `Prop`.

The cumulative one-step bound `martingaleOneStep_iterate` leaves the cross term
`B = ∑_{i<k} E[|S i|^{p-2} v (i+1)]` to be controlled.  The missing step bounds it by the
Rosenthal quantities `W = (E V_k^{p/2})^{2/p}` and `V = ∑_{i≤k} E|ξ_i|^p`:

  `B ≤ K W (E|S k|^p)^{(p-2)/p} + K V`.

This is Pinelis's cumulative induction; it is the only remaining research-level obligation and is
carried as a hypothesis, never as an axiom.  The companion `rosenthal_of_crossTerm` turns it into
the martingale Rosenthal bound once the one-step iteration has produced `A ≤ C(B + V)`. -/
def PinelisInductionStep : Prop :=
  ∀ p : ℝ, 2 ≤ p → ∃ K : ℝ, 0 < K ∧
    ∀ {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ] {m₀}
      (F : Filtration ℕ m₀) (ξ v : ℕ → Ω → ℝ),
      (∀ i, μ[ξ (i + 1) | F i] =ᵐ[μ] 0) →
      (∀ i, μ[fun ω => ξ (i + 1) ω ^ 2 | F i] =ᵐ[μ] v (i + 1)) →
      (∀ i, Integrable (fun ω => |martingalePartialSum ξ i ω| ^ (p - 2) * v (i + 1) ω) μ) →
      ∀ k,
        ∑ i ∈ Finset.range k,
            (∫ ω, |martingalePartialSum ξ i ω| ^ (p - 2) * v (i + 1) ω ∂μ)
          ≤ K * (∫ ω, (∑ i ∈ Finset.Icc 1 k, v i ω) ^ (p / 2) ∂μ) ^ (2 / p)
              * (∫ ω, |martingalePartialSum ξ k ω| ^ p ∂μ) ^ ((p - 2) / p)
            + K * ∑ i ∈ Finset.Icc 1 k, ∫ ω, |ξ i ω| ^ p ∂μ

end LatticeProb
