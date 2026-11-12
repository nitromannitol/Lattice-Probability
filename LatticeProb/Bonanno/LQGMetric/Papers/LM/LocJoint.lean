/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.LM.LocJoint at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.LM.LocEquiv

/-!
# LM Lemma 1.4 (`lem-jointly-local`), `n = 2` (task P2-LMLOC)

Source: Gwynne–Miller, *Local metrics of the Gaussian free field* (arXiv:1905.00379,
`local-metrics-final.tex`), Lemma 1.4, l. 253–256, proof l. 257–274 (case `n = 2`). With
`X = (D₁(·,·;ℂ∖V̄), D₂(·,·;ℂ∖V̄), h|_{ℂ∖V})`, `Y = D₁(·,·;V)`, `Z = D₂(·,·;V)`, everything
conditionally on `h|_V`:
* `condIndepEv_internal_of_local` — `X ⟂ Y | h|_V` (LM l. 264–267: conditional independence of
  `D₁, D₂` given `h` (weak union) and locality of `D₁` in form (2) of LM Lemma 2.3
  (`locForm2_of_isLocal`), combined by contraction);
* `condIndepEv_internal_pair` — `Y ⟂ Z | (X, h|_V)` (LM l. 269);
* `lmLem1_4_of` — the conclusion by SS13 Lemma 3.5 in conditional form
  (`condIndepEv_sup_of_condIndepEv`, LM l. 259, 270–271).

Input: `LocGermSplit` (LM l. 534, "`h` is determined by `h|_V` and `h|_{U∖V}`"), used both for
form (2) of locality and to replace conditioning on `h` by conditioning on `(h|_V, h|_{ℂ∖V})`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal

namespace LQGMetric.LM

open Blueprint GM.Bilip DFGPS.L219

variable {Ω : Type} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

/-- **Metrics determined by the field** (LM l. 233: "if `D` is determined by `h`, then `D` is a
local metric for `h` iff `D(·,·;V)` is determined by `h|_V`"; the case GM l. 905–907 uses): if
`D_j(·,·;V)` is a.s. determined by `h|_V` for every open `V`, then `D₁, D₂` are jointly local.
This is the conclusion of LM Lemma 1.4 in that case, without `LocGermSplit` (the internal metrics
on `V` are `σ(h|_V)`-measurable up to null events, so conditionally independent of everything
given `h|_V`, `GM.Bilip.condIndepEv_of_le_aeClosure`). -/
theorem isJointlyLocal2_of_determined {h : Ω → DistC} {D₁ D₂ : Ω → ContMetric}
    (hm : Measurable h) (hD₁ : Measurable D₁) (hD₂ : Measurable D₂)
    (hlen : ∀ᵐ ω ∂P, (D₁ ω).IsLength ∧ (D₂ ω).IsLength)
    (hdet₁ : ∀ V : TopologicalSpace.Opens ℂ,
      famSigma (internalFam D₁) V ≤ aeClosure P (fieldSigma h V))
    (hdet₂ : ∀ V : TopologicalSpace.Opens ℂ,
      famSigma (internalFam D₂) V ≤ aeClosure P (fieldSigma h V)) :
    IsJointlyLocal2 P h D₁ D₂ := by
  refine ⟨hD₁, hD₂, hlen, fun V => ?_⟩
  have hW : IsOpen (closure (V : Set ℂ))ᶜ := isClosed_closure.isOpen_compl
  refine condIndepEv_of_le_aeClosure (fieldSigma_le hm V) (sup_le (hdet₁ V) (hdet₂ V)) ?_
  refine sup_le (sup_le ((fieldSigmaClosed_le hm _).trans (le_aeClosure _)) ?_) ?_
  · exact (hdet₁ ⟨_, hW⟩).trans (aeClosure_mono (fieldSigma_le hm _))
  · exact (hdet₂ ⟨_, hW⟩).trans (aeClosure_mono (fieldSigma_le hm _))

end LQGMetric.LM
