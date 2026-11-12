/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Statement.Thm11 at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Statement.LFPP
import LatticeProb.Bonanno.LQGMetric.Statement.Metric
import LatticeProb.Bonanno.LQGMetric.Statement.Dimension

/-!
# Target 1: Theorem 1.1 of Gwynne–Miller (convergence of LFPP)

GM = Gwynne–Miller, *Existence and uniqueness of the Liouville quantum gravity metric for
γ ∈ (0,2)*, arXiv:1905.00383v3, `literature/src/1905.00383/uniqueness-final.tex`, l. 229–231:

> **Theorem 1.1** (Convergence of LFPP). The random metrics 𝔞_ε⁻¹ D_h^ε converge in probability
> w.r.t. the local uniform topology on ℂ × ℂ to a random metric on ℂ which is a.s. determined by h.

Context (GM l. 202–224): γ ∈ (0,2) fixed, ξ = γ/d_γ (1.1), h a whole-plane GFF plus a bounded
continuous function (the class for which D_h^ε is defined, l. 216), ε → 0. Readings: see
`STATEMENT_SPEC.md` (entries `theorem11Shape`, `Theorem11`) and DEVIATIONS §1 (S1–S3).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal

namespace LQGMetric

/-- GM Theorem 1.1 for one value of `γ`: if `γ ∈ (0,2)`, then for every whole-plane GFF plus a
bounded continuous function `h` (on any probability space) there is a random continuous function
`Y` on `ℂ × ℂ` which is a.s. a metric on `ℂ` and a.s. a measurable function of `h`, such that
`𝔞_ε⁻¹ D_h^ε → Y` in probability w.r.t. the local uniform topology as `ε → 0⁺`. -/
def theorem11Shape (γ : ℝ) : Prop :=
  0 < γ → γ < 2 →
  ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] (h : Ω → DistC),
    IsGFFPlusBddCont h P → ∃ Y : Ω → C(ℂ × ℂ, ℝ), (∀ᵐ ω ∂P, IsMetricFn (Y ω)) ∧
      AEDeterminedBy Y h P ∧
      TendstoInProbLU P (fun ε ω => (aEps (xiGamma γ) ε)⁻¹ • lfppDist (xiGamma γ) ε (h ω))
        (𝓝[>] 0) (fun ω => Y ω)

/-- **Theorem 1.1 of Gwynne–Miller** (convergence of LFPP), for every `γ ∈ (0,2)`. -/
def Theorem11 : Prop := ∀ γ : ℝ, theorem11Shape γ

end LQGMetric
