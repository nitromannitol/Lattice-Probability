import Mathlib

/-!
# Quadratic covariation of a continuous martingale

The dyadic realized covariation of a real-valued process `M` on `[0, T]` and the predicate
`HasQuadCovar`, which says that these realized covariations converge in probability to a given
matrix-valued random variable. For a continuous square-integrable martingale this limit is the
quadratic covariation at time `T`, the classical characterization of the bracket.
-/

namespace LatticeProb.Process

open MeasureTheory Filter

open scoped NNReal

noncomputable section

variable {Ω I : Type*} [Fintype I]

/-- The dyadic realized covariation `Σ_{k < 2^n} ΔM_k ΔM_kᵀ` of `M` on `[0, T]`, where
`ΔM_k = M_{(k+1)T/2^n} - M_{kT/2^n}`. -/
def realizedCovar (M : ℝ≥0 → Ω → I → ℝ) (T : ℝ≥0) (n : ℕ) (ω : Ω) : I → I → ℝ :=
  fun i j => ∑ k ∈ Finset.range (2 ^ n),
    (M (T * ((k + 1 : ℕ) / 2 ^ n : ℝ≥0)) ω i - M (T * ((k : ℕ) / 2 ^ n : ℝ≥0)) ω i) *
      (M (T * ((k + 1 : ℕ) / 2 ^ n : ℝ≥0)) ω j - M (T * ((k : ℕ) / 2 ^ n : ℝ≥0)) ω j)

/-- The quadratic covariation matrix of `M` at time `T` is `Q`: the dyadic realized covariations
converge to `Q` in probability. -/
def HasQuadCovar [MeasurableSpace Ω] (P : Measure Ω) (M : ℝ≥0 → Ω → I → ℝ) (T : ℝ≥0)
    (Q : Ω → I → I → ℝ) : Prop :=
  TendstoInMeasure P (fun n ω => realizedCovar M T n ω) atTop Q

end

end LatticeProb.Process
