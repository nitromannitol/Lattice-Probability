/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.LM.T1_7V11 at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.LM.T1_7V7
import LatticeProb.Bonanno.LQGMetric.Papers.LM.C1_8Len
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan

/-!
# LM Lemma 5.3 (restricted): probabilistic tools

Gwynne–Miller, *Local metrics of the Gaussian free field* (arXiv:1905.00379,
`local-metrics-final.tex`), proof of Lemma 5.3 (l. 964–986): "let `D` and `D'` be two conditionally
independent samples from the conditional law … To prove the lemma it suffices to show that a.s.
`D = D'`" (here: the values `F(D) = F(D')` of one functional).

* `t17v_aeDet_comp`: copy criterion for a functional `f ∘ Y` (from `aeDeterminedBy_of_condIndepEv_of_ae_eq`
  and the conditional independence of the copy, Prob/CondCopies.lean).
* `t17v_ae_eq_of_le_of_map_eq`: `U ≤ V` a.s. and `law U = law V` give `U = V` a.s. (through the
  bounded strictly increasing `arctan`); this replaces LM's "Symmetrically" (l. 984) since the two
  samples have the same law. Own elementary argument.
* `t17v_measurable_length_subset`: a measurable set of length metrics of full `ν`-measure
  (`{d | d.IsLength}` is universally measurable, `c18_uMeasurableSet_isLength`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

namespace LQGMetric.LM

/-- copy criterion for a real functional of `Y` -/
theorem t17v_aeDet_comp {Ω α β : Type*} [mΩ : MeasurableSpace Ω] [mα : MeasurableSpace α]
    [mβ : MeasurableSpace β] [StandardBorelSpace β] [Nonempty β] {μ : Measure Ω}
    [IsProbabilityMeasure μ] {X : Ω → α} {Y : Ω → β} (hX : Measurable X) (hY : Measurable Y)
    {f : β → ℝ} (hf : Measurable f)
    (heq : ∀ᵐ q ∂condCopyMeasure Y X μ hX, f (Y q.1) = f q.2) :
    AEDeterminedBy (f ∘ Y) X μ := by
  have hCI := (condIndepEv_condCopy (μ := μ) hX hY).mono
    (show MeasurableSpace.comap (fun q : Ω × β => f (Y q.1)) inferInstance ≤
        mβ.comap (fun q : Ω × β => Y q.1) by
      rw [show (fun q : Ω × β => f (Y q.1)) = f ∘ (fun q : Ω × β => Y q.1) from rfl,
        ← MeasurableSpace.comap_comp]
      exact MeasurableSpace.comap_mono hf.comap_le)
    (show MeasurableSpace.comap (fun q : Ω × β => f q.2) inferInstance ≤
        mβ.comap (Prod.snd : Ω × β → β) by
      rw [show (fun q : Ω × β => f q.2) = f ∘ (Prod.snd : Ω × β → β) from rfl,
        ← MeasurableSpace.comap_comp]
      exact MeasurableSpace.comap_mono hf.comap_le)
  obtain ⟨F, hF, hYF⟩ := aeDeterminedBy_of_condIndepEv_of_ae_eq (hX.comp measurable_fst)
    (D := fun q : Ω × β => f (Y q.1)) (D' := fun q : Ω × β => f q.2)
    (hf.comp (hY.comp measurable_fst)) hCI heq
  refine ⟨F, hF, ?_⟩
  rw [Filter.EventuallyEq, ← condCopyMeasure_fst (Y := Y) (μ := μ) hX,
    ae_map_iff measurable_fst.aemeasurable (measurableSet_eq_fun (hf.comp hY) (hF.comp hX))]
  exact hYF

/-- `U ≤ V` a.s. and equal laws give `U = V` a.s. -/
theorem t17v_ae_eq_of_le_of_map_eq {Ω : Type*} [MeasurableSpace Ω] {Q : Measure Ω}
    [IsFiniteMeasure Q] {U V : Ω → ℝ} (hU : Measurable U) (hV : Measurable V)
    (hle : ∀ᵐ q ∂Q, U q ≤ V q) (hmap : Q.map U = Q.map V) : ∀ᵐ q ∂Q, U q = V q := by
  have hb : ∀ x : ℝ, ‖Real.arctan x‖ ≤ Real.pi / 2 := fun x => by
    rw [Real.norm_eq_abs, abs_le]
    exact ⟨(Real.neg_pi_div_two_lt_arctan x).le, (Real.arctan_lt_pi_div_two x).le⟩
  have hint : ∀ W : Ω → ℝ, Measurable W → Integrable (fun q => Real.arctan (W q)) Q := fun W hW =>
    Integrable.of_bound (Real.continuous_arctan.measurable.comp hW).aestronglyMeasurable
      (Real.pi / 2) (Filter.Eventually.of_forall fun q => hb _)
  have hEq : ∫ q, Real.arctan (U q) ∂Q = ∫ q, Real.arctan (V q) ∂Q := by
    rw [← integral_map (f := Real.arctan) hU.aemeasurable
      Real.continuous_arctan.measurable.aestronglyMeasurable,
      ← integral_map (f := Real.arctan) hV.aemeasurable
      Real.continuous_arctan.measurable.aestronglyMeasurable, hmap]
  have h0 : ∫ q, (Real.arctan (V q) - Real.arctan (U q)) ∂Q = 0 := by
    rw [integral_sub (hint V hV) (hint U hU), hEq, sub_self]
  have hnn : 0 ≤ᵐ[Q] fun q => Real.arctan (V q) - Real.arctan (U q) := by
    filter_upwards [hle] with q hq
    exact sub_nonneg.2 (Real.arctan_strictMono.monotone hq)
  have := (integral_eq_zero_iff_of_nonneg_ae hnn ((hint V hV).sub (hint U hU))).1 h0
  filter_upwards [this] with q hq
  exact (Real.arctan_injective (sub_eq_zero.1 hq)).symm

/-- a measurable set of length metrics of full measure -/
theorem t17v_measurable_length_subset (ν : Measure ContMetric) [IsFiniteMeasure ν]
    (hL : ∀ᵐ d ∂ν, d.IsLength) :
    ∃ M : Set ContMetric, MeasurableSet M ∧ M ⊆ {d | d.IsLength} ∧ ∀ᵐ d ∂ν, d ∈ M := by
  obtain ⟨M, hMS, hM, hMae⟩ :=
    (c18_uMeasurableSet_isLength ν inferInstance).exists_measurable_subset_ae_eq
  obtain ⟨N, hSN, hN, hN0⟩ := exists_measurable_superset_of_null
    (show ν ({d : ContMetric | d.IsLength} \ M) = 0 from ae_le_set.1 hMae.symm.le)
  refine ⟨M, hM, hMS, ?_⟩
  have hN' : ∀ᵐ d ∂ν, d ∉ N := measure_eq_zero_iff_ae_notMem.1 hN0
  filter_upwards [hL, hN'] with d h1 h2
  by_contra h3
  exact h2 (hSN ⟨h1, h3⟩)

end LQGMetric.LM
