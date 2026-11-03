/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGDimension.Statement.Main at commit 31e7483; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGDimension.Statement.Defs

/-!
# Theorem 1.1

The statement of Theorem 1.1, split into its three assertions.

* `Theorem11_AStar`: the numbers `a_n` are finite, `(a_n)` is subadditive, and
  `0 < a* = lim a_n / n = inf_{n ≥ 1} a_n / n < ∞`.  (Finiteness of `a*` is automatic for a
  real number once every `a_n` is finite; `aStar` is *defined* as the infimum.)
* `Theorem11_Lambda`: equation (1.5), `λ(ξ) / ξ^{4/3} → a* / log 16` as `ξ ↓ 0`, for the LFPP
  exponent `λ(ξ)` (which exists for `ξ` in an interval `(0, ξ₀)` by the literature cited in the
  paper; existence is a hypothesis here).
* `Theorem11_Dimension`: equation (1.6), `(d_γ - 2) / γ^{4/3} → 2^{-1/3} a* / log 16` as
  `γ ↓ 0`.  The LQG dimension `d_γ` enters only through the two facts the paper imports from
  the literature: `d_γ → 2` as `γ ↓ 0` [Ding–Gwynne, Theorem 1.2] and the exponent relation
  (1.1), `λ(γ / d_γ) = 1 - (2 + γ²/2) / d_γ` [Ding–Gwynne, Theorem 1.5; Gwynne–Pfeffer,
  Corollary 1.7].  They are hypotheses on an arbitrary function `d`, required only for small
  `γ`.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set Real

namespace LQGDimension

/-- Theorem 1.1, first assertion. -/
def Theorem11_AStar : Prop :=
  (∀ n : ℕ, aE n ≠ ⊤) ∧
  (∀ n m : ℕ, 1 ≤ n → 1 ≤ m → a (n + m) ≤ a n + a m) ∧
  0 < aStar ∧
  Tendsto (fun n : ℕ => a n / n) atTop (𝓝 aStar)

/-- Theorem 1.1, equation (1.5): for the whole-plane GFF `h` and any function `λ` that is the
LFPP exponent at every `ξ ∈ (0, ξ₀)`, `λ(ξ) / ξ^{4/3} → a* / log 16` as `ξ ↓ 0`. -/
def Theorem11_Lambda : Prop :=
  ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) (h : ℝ → ℂ → Ω → ℝ),
    IsGFFCircleAverage h P →
    ∀ lam : ℝ → ℝ, (∃ ξ₀ > 0, ∀ ξ ∈ Ioo 0 ξ₀, IsLFPPExponent h P ξ (lam ξ)) →
      Tendsto (fun ξ => lam ξ / ξ ^ (4 / 3 : ℝ)) (𝓝[>] 0) (𝓝 (aStar / Real.log 16))

/-- Theorem 1.1, equation (1.6): if `d` satisfies `d_γ → 2` and the exponent relation (1.1)
for small `γ`, then `(d_γ - 2) / γ^{4/3} → 2^{-1/3} a* / log 16` as `γ ↓ 0`. -/
def Theorem11_Dimension : Prop :=
  ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) (h : ℝ → ℂ → Ω → ℝ),
    IsGFFCircleAverage h P →
    ∀ d : ℝ → ℝ, Tendsto d (𝓝[>] 0) (𝓝 2) →
      (∃ γ₀ > 0, ∀ γ ∈ Ioo 0 γ₀,
        IsLFPPExponent h P (γ / d γ) (1 - (2 + γ ^ 2 / 2) / d γ)) →
      Tendsto (fun γ => (d γ - 2) / γ ^ (4 / 3 : ℝ)) (𝓝[>] 0)
        (𝓝 (2 ^ (-1 / 3 : ℝ) * aStar / Real.log 16))

/-- Theorem 1.1. -/
def Theorem11 : Prop :=
  Theorem11_AStar ∧ Theorem11_Lambda ∧ Theorem11_Dimension

end LQGDimension
