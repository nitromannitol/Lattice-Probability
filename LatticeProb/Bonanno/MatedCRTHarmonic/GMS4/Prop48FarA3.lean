/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module MatedCRTHarmonic.GMS4.Prop48FarA3 at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.MatedCRTHarmonic.GMS4.Prop48FarProduct

/-!
# Two-field Appendix A.3 and the far-pair product

This combines the translated local A.3 estimate with exterior conditional
expectation and Hölder. Its probabilistic premises are integrability, a
measurable local factor, and exterior measurability of the distant point.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set LQGMetric LQGMetric.Blueprint
open scoped ENNReal

namespace MatedCRTHarmonic.GMS4

/-- The source far-pair estimate (4.35)–(4.36), before Lemma 4.9 substitutes
uniform moment bounds and the exponentially small A.3 term is absorbed. The
center is the conditional expectation given A.3's pair of circle averages. -/
theorem prop48_twoField_far_pair_of_lemmaA3
    {Ω : Type} [m₀ : MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P]
    {h hIG : Ω → DistC}
    (hh : IsNormalizedWPGFF h P) (hhIG : IsNormalizedWPGFF hIG P)
    (hind : IndepFun h hIG P)
    {r : ℝ} (hr : 0 < r) (z : ℂ) (hsmall : r + ‖z‖ < 1)
    {p p₀ s δ q : ℝ} (hp : 1 ≤ p) (hpp₀ : p < p₀) (hs : 0 < s)
    (hδ : 0 < δ) (hδa : δ ≤ GMSAppA.a3aN p p₀ 2)
    (hpq : p.HolderConjugate q)
    {Y Z : Ω → ℝ}
    {f : ((DistOn (ballO z (r * δ)) × DistOn (ballO z (r * δ))) ×
      (ℝ × ℝ)) → ℝ}
    (hf : Measurable f)
    (hYfactor : Y =ᵐ[P] fun ω =>
      f (prop48LocalFieldObservation h hIG (r * δ) r z ω))
    (hYp₀ : ∫⁻ ω, ENNReal.ofReal |Y ω| ^ p₀ ∂P ≠ ⊤)
    (hYi : Integrable Y P)
    (hZi : Integrable (Y * Z) P)
    (hAZi : Integrable ((P[Y | GMSAppA.cSigmaN
        (prop48AffineFieldFamily h hIG r z)]) * Z) P)
    (hZext : StronglyMeasurable[prop48ExteriorSigma h hIG r z] Z) :
    ENNReal.ofReal |∫ ω,
      (Y ω - P[Y | GMSAppA.cSigmaN
        (prop48AffineFieldFamily h hIG r z)] ω) * Z ω ∂P| ≤
      (ENNReal.ofReal (GMSAppA.a3C p p₀) *
        (ENNReal.ofReal (δ ^ (s * p)) *
            ∫⁻ ω, ENNReal.ofReal |Y ω| ^ p ∂P +
          ENNReal.ofReal
              (Real.exp (-(GMSAppA.a3bN p p₀ 2 / δ ^ (1 - s)))) *
            (∫⁻ ω, ENNReal.ofReal |Y ω| ^ p₀ ∂P) ^ (p / p₀))) ^ (1 / p) *
      (∫⁻ ω, ENNReal.ofReal |Z ω| ^ q ∂P) ^ (1 / q) := by
  have hm : prop48ExteriorSigma h hIG r z ≤ m₀ := by
    rw [← prop48_extSigmaN_affine_eq_exteriorSigma h hIG hr z]
    refine iSup_le fun i => GMSAppA.extSigma_le ?_
    fin_cases i
    · change Measurable (fun ω => affineComp r z (h ω))
      exact (hh.1.affineComp hr z).measurable
    · change Measurable (fun ω => affineComp r z (hIG ω))
      exact (hhIG.1.affineComp hr z).measurable
  have hA : AEMeasurable
      (P[Y | GMSAppA.cSigmaN (prop48AffineFieldFamily h hIG r z)]) P := by
    have hc : GMSAppA.cSigmaN (prop48AffineFieldFamily h hIG r z) ≤ m₀ := by
      exact (GMSAppA.measurable_pi_of fun i => by
        fin_cases i
        · change Measurable (fun ω => circleAvg (affineComp r z (h ω)) 1 0)
          simpa only [Function.comp_def] using
            (measurable_circleAvg_left 1 0).comp
              ((measurable_affineComp r z).comp hh.1.measurable)
        · change Measurable (fun ω => circleAvg (affineComp r z (hIG ω)) 1 0)
          simpa only [Function.comp_def] using
            (measurable_circleAvg_left 1 0).comp
              ((measurable_affineComp r z).comp hhIG.1.measurable)).comap_le
    exact (stronglyMeasurable_condExp.mono hc).measurable.aemeasurable
  have hA3 := prop48_twoField_lemmaA3_local hh hhIG hind hr z hsmall
    hp hpp₀ hs hδ hδa hf hYfactor hYp₀
  have hholder := prop48_integral_centered_far_holder
    (P := P) (m := prop48ExteriorSigma h hIG r z) hm hYi hZi hAZi hZext hA hpq
  exact hholder.trans (by gcongr)

end MatedCRTHarmonic.GMS4

