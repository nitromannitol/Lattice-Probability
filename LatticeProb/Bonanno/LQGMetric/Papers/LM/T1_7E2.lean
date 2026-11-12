/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.LM.T1_7E2 at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.LM.C1_8CondBd
import LatticeProb.Bonanno.LQGMetric.Blueprint.LMResults
import LatticeProb.Bonanno.LQGMetric.Field.StandardBorelMetric
import LatticeProb.Bonanno.LQGMetric.Prob.CondLaw

/-!
# LM Theorem 1.7, packet P-ES (DEC-107 §5): conditional laws and the bound (5.11)

Gwynne–Miller, *Local metrics of the Gaussian free field* (arXiv:1905.00379,
`local-metrics-final.tex`), proof of Theorem 1.7, decision D107 (`decisions/DEC-107.md` §3).

* `t17e_law_triple_of_condIndepEv` — conditional independence (event form `CondIndepEv`, as in
  `IsLocalMetric` and LM Lemmas 2.4/5.4) of `f` and `g` given `k`, with standard Borel targets,
  gives the kernel form `law(k, f, g) = law(k) ⊗ (κ_f ×ₖ κ_g)`, `κ_• = condDistrib • k μ`. This is
  how "under the conditional law given `(h, θ)` the internal metrics are independent" (LM Lemma 5.4,
  l. 992–997) is turned into the product kernel of `t17e_es_kernel` (T1_7E1). Mathlib has the same
  statement for its `CondIndepFun` on a standard Borel sample space
  (`condIndepFun_iff_map_prod_eq_prod_condDistrib_prod_condDistrib`); our sample space is
  arbitrary, so we prove it from `condDistrib_ae_eq_condExp` (own bookkeeping).
* `t17e_bilip_of_law` — **LM (5.11)** (l. 1030–1036, and (5.6) l. 968–973 in the proof of
  Lemma 5.3), base-metric form: if `(h', D₁)` and `(h', D₂)` both have the law of `(h, D)`, then
  a.s. `D₂ ≤ C(h')² D₁` everywhere. LM: "Since `(h, D^S) =d (h, D)`, Lemma 5.1 implies that if
  `u, v ∈ U`, then a.s. `D(u,v), D^S(u,v) ∈ [C⁻¹ E[D(u,v)|h], C E[D(u,v)|h]]`. This holds a.s. for
  all rational `u, v` simultaneously, so since [they] are continuous metrics, a.s. `C⁻² D ≤ D^S ≤
  C² D`." We apply Lemma 5.1 (`c18_condBded`) to the base metric `d ↦ d(u,v)` (continuous, no
  length property of `D₂` needed); the internal-metric form `D₂(·,·;V) ≤ C² D₁(·,·;V)` for every
  `V` then follows deterministically (`t17_internal_le_of_le`, packet P-LIM). DEVIATION (proposed):
  LM state (5.11) for the internal metrics on `V` via Lemma 5.1 for `D(·,·;V)`; we use the base
  metrics, which give the internal bound for all `V` at once.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal

namespace LQGMetric.LM

open Blueprint

section Bridge

variable {Ω α β β' : Type*} {mΩ : MeasurableSpace Ω} [mα : MeasurableSpace α]
  [mβ : MeasurableSpace β] [StandardBorelSpace β] [Nonempty β]
  [mβ' : MeasurableSpace β'] [StandardBorelSpace β'] [Nonempty β']
  {μ : Measure Ω} [IsProbabilityMeasure μ]

end Bridge

section Bilip

variable {Ω Ω' : Type} [MeasurableSpace Ω] [MeasurableSpace Ω'] {P : Measure Ω}
  [IsProbabilityMeasure P] {μ' : Measure Ω'}

lemma t17e_measurable_apply (p : ℂ × ℂ) : Measurable fun d : ContMetric => d.1 p :=
  (continuous_eval_const p).measurable.comp measurable_subtype_coe

end Bilip

end LQGMetric.LM
