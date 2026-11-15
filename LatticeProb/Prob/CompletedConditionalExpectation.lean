import LatticeProb.Prob.CompletedHistoryCondExp
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S4.P412jComp

/-! # Conditional expectation on a completed probability space -/

set_option autoImplicit false

open MeasureTheory Filter
open LQGMetric.GM

namespace LatticeProb

/-- Completing the ambient probability space and the conditioning sigma algebra
preserves the conditional expectation of an integrable real function. -/
theorem condExp_completion_ae_eq {Ω : Type} [m : MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] {F : MeasurableSpace Ω}
    (hF : F ≤ m) {f : Ω → ℝ} (hf : Integrable f P) :
    ((@Measure.completion Ω m P)[f ∘ (@gm_ofNull Ω m P) | eventuallyMeasurableSpace F (ae P)] : Ω → ℝ)
      =ᵐ[P] P[f | F] := by
  have hFm : F ≤ (inferInstance : MeasurableSpace (@NullMeasurableSpace Ω m P)) :=
    hF.trans (@p412j_le_null Ω m P)
  have : IsFiniteMeasure ((@Measure.completion Ω m P).trim hFm) :=
    isFiniteMeasure_trim (μ := (@Measure.completion Ω m P)) hFm
  have hsf : SigmaFinite ((@Measure.completion Ω m P).trim hFm) :=
    IsFiniteMeasure.toSigmaFinite _
  have hfi := (@p412j_integrable_completion Ω m P f).2 hf
  have hraw : ((@Measure.completion Ω m P)[f ∘ (@gm_ofNull Ω m P) | F] : Ω → ℝ) =ᵐ[P]
      P[f | F] := by
    have heq := ae_eq_condExp_of_forall_setIntegral_eq (μ := (@Measure.completion Ω m P)) hFm hfi
      (g := P[f | F]) (fun _ _ _ =>
        ((@p412j_integrable_completion Ω m P (P[f | F])).2
          integrable_condExp).integrableOn)
      (fun s hs _ =>
        (@p412j_setIntegral_completion Ω m P (P[f | F]) s (hF s hs)).trans
          ((setIntegral_condExp hF hf hs).trans
            (@p412j_setIntegral_completion Ω m P f s (hF s hs)).symm))
      stronglyMeasurable_condExp.aestronglyMeasurable
    exact heq.symm
  have hFc : eventuallyMeasurableSpace F (ae P) ≤
      (inferInstance : MeasurableSpace (@NullMeasurableSpace Ω m P)) := by
    intro s hs
    obtain ⟨t, ht, hst⟩ := hs
    exact (hF t ht).nullMeasurableSet.congr hst.symm
  have hrep : AELeSigma (eventuallyMeasurableSpace F (ae P)) F (@Measure.completion Ω m P) := by
    intro s hs
    exact hs
  have hclosed := condExp_ae_eq_of_aeLeSigma
    (μ := (@Measure.completion Ω m P)) (f := f ∘ (@gm_ofNull Ω m P))
    (le_eventuallyMeasurableSpace : F ≤ eventuallyMeasurableSpace F (ae P))
    hFc hrep hfi
  exact hclosed.symm.trans hraw

end LatticeProb
