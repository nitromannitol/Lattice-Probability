/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.LM.L3_1N2P5 at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.LM.L3_1N2P4
import LatticeProb.Bonanno.LQGMetric.Papers.LM.L3_4N6
import LatticeProb.Bonanno.LQGMetric.Papers.LM.L3_4M6
import LatticeProb.Bonanno.LQGMetric.Papers.LM.L4_1

/-!
# LM Lemma 3.1 (1) with `N = 2` and LM Theorem 1.6 (task P2-LM31N2)

Source: Gwynne–Miller, *Local metrics of the Gaussian free field* (arXiv:1905.00379,
`local-metrics-final.tex`), Lemma 3.1 (l. 573–590), proof l. 723–764, Lemma 3.3 (l. 631–637).

* `lmN2ScaleInput_of_germ : LocGermSplit → LMN2ScaleInput s₁ s₂`: the events are replaced by
  Borel versions `E'_k ∈ σ((h − h_{r_k}(0))|_{A_k}) ∨ n2Sig (r_k) A_k`; with
  `f = P[E'_k | (h − h_{r_k}(0))|_{A_k}]` and `a = {f ≥ 1 − η}`: `P[aᶜ] η ≤ E[1 − f] = P[E'_kᶜ]`
  (Markov), `(1 − η) P[a | ℱ_k] ≤ E[f | ℱ_k] = P[E'_k | ℱ_k]` (step (i)), and
  `P[a | ℱ_k] = P[a | 𝓕_{r_k}]` (step (ii)).
* `lmLem3_1aN2_of_germ_canon`, `lmThm1_6_of_germ_canon`: LM Lemma 3.1 (1) (`N = 2`) and LM
  Theorem 1.6 from `LocGermSplit` (LM l. 534) and the canonical nesting `LMNestCanonLeaf`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Metric
open scoped ENNReal

namespace LQGMetric.LM

open Blueprint GM.Bilip DFGPS.L219

/-- `LMAnnulusIterInputQ` ((3.8) for field events and (3.10)) from the canonical nesting. -/
theorem lmAnnulusIterInputQ_of_canon (hC : ∀ s₁ : ℝ, 0 < s₁ → s₁ < 1 → LMNestCanonLeaf s₁) :
    ∀ s₁ s₂ : ℝ, 0 < s₁ → s₁ < s₂ → s₂ < 1 → LMAnnulusIterInputQ s₁ s₂ :=
  fun s₁ s₂ h1 h2 h3 => lmAnnulusIterInputQ_of MQ.mqLem4_1Gen (h1.trans h2) h3
    (lmGoodScaleLeaf_of_dom (lmScaleDomLeaf_of_incr h1 h2 h3 (lmIncrLeaf_of_nest (h1.trans h2) h3
      (lmNestLeaf_of_core (lmNestCoreLeaf_of_canon (hC s₁ h1 (h2.trans h3)))
        lmHarmCenterLeaf))))

end LQGMetric.LM
