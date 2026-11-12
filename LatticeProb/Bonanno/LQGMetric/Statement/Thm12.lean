/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Statement.Thm12 at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Statement.LQGMetric
import LatticeProb.Bonanno.LQGMetric.Statement.LFPP

/-!
# Target 2: Theorem 1.2 of Gwynne–Miller (existence and uniqueness of the LQG metric)

GM = Gwynne–Miller, arXiv:1905.00383v3, `literature/src/1905.00383/uniqueness-final.tex`,
l. 319–322:

> **Theorem 1.2** (Existence and uniqueness of the LQG metric). Fix γ ∈ (0,2). There is a γ-LQG
> metric D such that the limiting metric of Theorem 1.1 is a.s. equal to D_h whenever h is a
> whole-plane GFF plus a bounded continuous function. Furthermore, the γ-LQG metric is unique in
> the following sense. If D and D̃ are two γ-LQG metrics, then there is a deterministic constant
> C > 0 such that if h is a whole-plane GFF plus a continuous function, then a.s. D_h = C D̃_h.

"γ-LQG metric" = strong γ-LQG metric (GM l. 293–307, `IsStrongLQGMetric`). Readings: see
`STATEMENT_SPEC.md` (entries `theorem12Shape`, `Theorem12`) and DEVIATIONS §1 (S4, S5).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal

namespace LQGMetric

/-- GM Theorem 1.2 for one value of `γ`: if `γ ∈ (0,2)`, then
(existence) there is a strong γ-LQG metric `D` such that for every whole-plane GFF plus a bounded
continuous function `h`, `𝔞_ε⁻¹ D_h^ε → D_h` in probability (local uniform topology, `ε → 0⁺`);
(uniqueness) for any two strong γ-LQG metrics `D, D'` there is a deterministic `C > 0` with
a.s. `D_h = C D'_h` for every whole-plane GFF plus a continuous function `h`. -/
def theorem12Shape (γ : ℝ) : Prop :=
  0 < γ → γ < 2 →
  (∃ D : DistC → ContMetric, IsStrongLQGMetric γ D ∧
    ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] (h : Ω → DistC),
      IsGFFPlusBddCont h P →
      TendstoInProbLU P (fun ε ω => (aEps (xiGamma γ) ε)⁻¹ • lfppDist (xiGamma γ) ε (h ω))
        (𝓝[>] 0) (fun ω => (D (h ω)).1)) ∧
  ∀ D D' : DistC → ContMetric, IsStrongLQGMetric γ D → IsStrongLQGMetric γ D' →
    ∃ C : ℝ, 0 < C ∧ ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      (h : Ω → DistC), IsGFFPlusCont h P →
        ∀ᵐ ω ∂P, ∀ u v : ℂ, (D (h ω)).1 (u, v) = C * (D' (h ω)).1 (u, v)

/-- **Theorem 1.2 of Gwynne–Miller** (existence and uniqueness of the LQG metric), for every
`γ ∈ (0,2)`. -/
def Theorem12 : Prop := ∀ γ : ℝ, theorem12Shape γ

end LQGMetric
