/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DFGPS.L2_17Step4 at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DFGPS.L2_19CI
import Mathlib.Probability.ConditionalExpectation

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# DFGPS Lemma 2.17, Step 4: from independence to conditional independence

DFGPS (arXiv:1905.00380, `lqg-metric-estimates-final.tex`) T:1268–1278: "By (eqn-limit-metric-ind),
`D_h(·,·;W)` is conditionally independent from `(h̊, D_{h−φ𝔥}(·,·;W'))` given `h|_V`. We now argue
that `(h, D_h(·,·;W'))` is a measurable function of `(h̊, D_{h−φ𝔥}(·,·;W'))` and `h|_V`, so that
`D_h(·,·;W)` is conditionally independent from `(h, D_h(·,·;W'))` given `h|_V`."

* `condIndepEv_of_indep_sup`: if `A ∨ G` and `B` are independent, then `A ⟂ B | G`.
* `condIndepEv_of_indep_of_le`: if `A ∨ G ⫫ H`, `A'` is a.s. determined by `A ∨ G` and `B'` by
  `H ∨ G`, then `A' ⟂ B' | G` — the abstract form of Step 4.

Standard facts (e.g. Kallenberg, *Foundations of Modern Probability*, 2nd ed., Prop. 6.6, 6.8);
proofs from mathlib's `condExp_indep_eq` and `L219.condIndepEv_sup_cond`.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter

namespace LQGMetric.DFGPS.L217

open GM.Bilip

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}

/-- if `A ∨ G` and `B` are independent, then `A ⟂ B | G` -/
theorem condIndepEv_of_indep_sup [IsProbabilityMeasure μ] {G A B : MeasurableSpace Ω}
    (hG : G ≤ mΩ) (hA : A ≤ mΩ) (hB : B ≤ mΩ) (h : Indep (A ⊔ G) B μ) :
    CondIndepEv G A B μ := by
  refine (condIndepEv_of_condExp_sup_eq (A := B) (B := A) hG hB hA fun b hb => ?_).symm
  have hsm : StronglyMeasurable[B] (b.indicator fun _ => (1 : ℝ)) :=
    stronglyMeasurable_const.indicator hb
  have h1 := condExp_indep_eq hB (sup_le hA hG) hsm h.symm
  have h2 := condExp_indep_eq hB hG hsm (indep_of_indep_of_le_right h.symm le_sup_right)
  exact h1.trans h2.symm

/-- **Step 4 of the proof of DFGPS Lemma 2.17, abstract form**: if `A ∨ G ⫫ H`, every event of
`A'` is a.s. an event of `A ∨ G` and every event of `B'` is a.s. an event of `H ∨ G`, then
`A' ⟂ B' | G`. -/
theorem condIndepEv_of_indep_of_le [IsProbabilityMeasure μ] {G A H A' B' : MeasurableSpace Ω}
    (hG : G ≤ mΩ) (hA : A ≤ mΩ) (hH : H ≤ mΩ) (h : Indep (A ⊔ G) H μ)
    (hA' : A' ≤ aeClosure μ (A ⊔ G)) (hB' : B' ≤ aeClosure μ (H ⊔ G)) :
    CondIndepEv G A' B' μ :=
  CondIndepEv.of_le_aeClosure
    (L219.condIndepEv_sup_cond hG hA hH (condIndepEv_of_indep_sup hG hA hH h)) hA' hB'

end LQGMetric.DFGPS.L217
