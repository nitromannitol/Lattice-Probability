/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Blueprint.GMWeakUniqueness at commit 31e7483; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Statement.LQGMetric

/-!
# Blueprint: GM Theorem 1.9 (weak uniqueness of weak LQG metrics)

Source: Gwynne–Miller, *Existence and uniqueness of the Liouville quantum gravity metric for
γ ∈ (0,2)*, arXiv:1905.00383v3 (GM), `literature/src/1905.00383/uniqueness-final.tex`,
l. 479–482:

> **Theorem 1.9** (Weak uniqueness of weak LQG metrics). Let γ ∈ (0,2) and let D and D̃ be two
> weak γ-LQG metrics which have the *same* values of 𝔠_r in Axiom V. There is a deterministic
> constant C > 0 such that if h is a whole-plane GFF plus a continuous function, then a.s.
> D_h = C D̃_h.

"Weak γ-LQG metric with scaling constants 𝔠" is `IsWeakLQGMetric γ D c` (statement layer,
GM l. 431–452; GM_A D-3: a weak metric is a predicate on the pair `(D, 𝔠)`), so "the same values
of 𝔠_r" is one `c` shared by both hypotheses. "D_h = C D̃_h" is equality of the two metrics at
every pair of points, as in `theorem12Shape` (GM l. 322). This Prop is proved by GM §§3–6
(milestone M2); until then it is a hypothesis of the M1 assembly (`blueprint/M1.md`) only.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal

namespace LQGMetric.Blueprint

/-- **GM Theorem 1.9** (GM l. 479–482): for `γ ∈ (0,2)`, two weak γ-LQG metrics `D`, `D'` with
the same scaling constants `c` agree up to a deterministic constant `C > 0`: for every whole-plane
GFF plus a continuous function `h`, a.s. `D_h = C D'_h`. -/
def GMWeakUniqueness : Prop :=
  ∀ γ : ℝ, 0 < γ → γ < 2 → ∀ (D D' : DistC → ContMetric) (c : ℝ → ℝ),
    IsWeakLQGMetric γ D c → IsWeakLQGMetric γ D' c →
    ∃ C : ℝ, 0 < C ∧ ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      (h : Ω → DistC), IsGFFPlusCont h P →
        ∀ᵐ ω ∂P, ∀ u v : ℂ, (D (h ω)).1 (u, v) = C * (D' (h ω)).1 (u, v)

end LQGMetric.Blueprint
