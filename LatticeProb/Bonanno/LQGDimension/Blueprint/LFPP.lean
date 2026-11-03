/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGDimension.Blueprint.LFPP at commit 31e7483; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGDimension.Statement.Main

/-!
# Blueprint: the LFPP bounds (Proposition 1.2) and the exponent asymptotics

`Prop12Upper` and `Prop12Lower` are (1.7) and (1.8).  They are stated without assuming that
the exponent exists: for every `η > 0`, for all small `ξ`, *any* exponent at `ξ` obeys the
bound.  When `λ(ξ)` exists for all small `ξ`, this is exactly the `lim sup` / `lim inf` bound
of the paper.

`LambdaAsymptotics` is the corresponding form of (1.5).  Both (1.5) and (1.6), as stated in
`LQGDimension.Statement.Main`, follow from it by real analysis.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set Real

namespace LQGDimension.Blueprint

/-- Proposition 1.2, upper bound (1.7). -/
def Prop12Upper : Prop :=
  ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) (h : ℝ → ℂ → Ω → ℝ),
    IsGFFCircleAverage h P →
    ∃ C : ℝ, ∃ N : ℕ, ∀ n ≥ N, ∀ η > 0, ∀ᶠ ξ in 𝓝[>] 0, ∀ lam : ℝ,
      IsLFPPExponent h P ξ lam →
      lam / ξ ^ (4 / 3 : ℝ) ≤
        (a n + C * (n : ℝ) ^ (3 / 4 : ℝ)) / Real.log (2 * 16 ^ n / 3) + η

/-- Proposition 1.2, lower bound (1.8). -/
def Prop12Lower : Prop :=
  ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) (h : ℝ → ℂ → Ω → ℝ),
    IsGFFCircleAverage h P →
    ∃ C : ℝ, ∃ N : ℕ, ∀ n ≥ N, ∀ η > 0, ∀ᶠ ξ in 𝓝[>] 0, ∀ lam : ℝ,
      IsLFPPExponent h P ξ lam →
      (a n - C * (n : ℝ) ^ (7 / 8 : ℝ)) / Real.log (16 ^ n) - η ≤ lam / ξ ^ (4 / 3 : ℝ)

/-- Equation (1.5), for arbitrary exponents: for every `η > 0` and all small `ξ`, every LFPP
exponent `λ` at `ξ` satisfies `|λ / ξ^{4/3} - a* / log 16| ≤ η`. -/
def LambdaAsymptotics : Prop :=
  ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) (h : ℝ → ℂ → Ω → ℝ),
    IsGFFCircleAverage h P →
    ∀ η > 0, ∀ᶠ ξ in 𝓝[>] 0, ∀ lam : ℝ, IsLFPPExponent h P ξ lam →
      |lam / ξ ^ (4 / 3 : ℝ) - aStar / Real.log 16| ≤ η

end LQGDimension.Blueprint
