/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module MatedCRTHarmonic.ConeLemmaA10.WholePlaneFieldLaw at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.MatedCRTHarmonic.ConeLemmaA10.AreaBiasNormalization
import LatticeProb.Bonanno.MatedCRTHarmonic.ConeLemmaA10.AreaMassIntegrability
import LatticeProb.Bonanno.MatedCRTHarmonic.ConeLemmaA10.CylinderFieldExtensionality
import LatticeProb.Bonanno.MatedCRTHarmonic.ConeLemmaA10.RampTestExhaustion
import LatticeProb.Bonanno.MatedCRTHarmonic.ConeLemmaA10.RootedFieldProbability
import LatticeProb.Bonanno.MatedCRTHarmonic.ConeLemmaA10.RootedFieldSupportAdapter
import LatticeProb.Bonanno.MatedCRTHarmonic.ConeLemmaA10.RootingCylinderObservable
import LatticeProb.Bonanno.MatedCRTHarmonic.ConeLemmaA10.RootingMeasureIntegral
import LatticeProb.Bonanno.MatedCRTHarmonic.ConeLemmaA10.RootingRawShiftIntegral

/-!
# Whole-plane rooted field law

This file assembles the compact-test Palm identity, exhaustion of the open unit disk, and
finite-cylinder extensionality to prove the field-space part of DMS14 Lemma A.10.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Metric
open scoped ENNReal

namespace MatedCRTHarmonic.ConeLemmaA10

open MatedCRTHarmonic.GMS4.GMSA
open LQGMetric LQGMetric.GFFInv

/-- The Bochner integral formula for a density given only by an a.e. measurable version. -/
theorem integral_withDensity_eq_integral_toReal_smul_of_aemeasurable
    {X E : Type*} [MeasurableSpace X] [NormedAddCommGroup E] [NormedSpace ℝ E]
    {μ : Measure X} {d : X → ℝ≥0∞} (hd : AEMeasurable d μ)
    (hdtop : ∀ᵐ x ∂μ, d x < ⊤) (f : X → E) :
    ∫ x, f x ∂(μ.withDensity d) = ∫ x, (d x).toReal • f x ∂μ := by
  have hmeasure : μ.withDensity d = μ.withDensity (hd.mk d) :=
    withDensity_congr_ae hd.ae_eq_mk
  rw [hmeasure, integral_withDensity_eq_integral_toReal_smul hd.measurable_mk]
  · apply integral_congr_ae
    filter_upwards [hd.ae_eq_mk] with x hx
    rw [hx]
  · filter_upwards [hdtop, hd.ae_eq_mk] with x hxtop hx
    simpa only [← hx] using hxtop

/-- Every bounded continuous finite `ev0` cylinder has the same expectation under the rooted
field law and under the explicitly normalized unit-disk-area-biased field law. -/
theorem WholePlaneRootingFieldLawInputs.integral_cylinder_rooted_eq_areaBiased
    {Ω : Type*} [MeasurableSpace Ω] (D : WholePlaneRootingFieldLawInputs Ω)
    (I : Finset TestC0) (F : (I → ℝ) → ℝ)
    (hF : Continuous F) (hFbounded : ∃ C : ℝ, ∀ x, ‖F x‖ ≤ C) :
    ∫ g, F (I.restrict (GFFLaw.ev0 g)) ∂(D.rootedLaw.map D.field) =
      ∫ g, F (I.restrict (GFFLaw.ev0 g)) ∂
        ((D.unrootedLaw.withDensity
          (fun ω => D.area.unitDiskMass ω / ENNReal.ofReal Real.pi)).map D.field) := by
  obtain ⟨C, hC⟩ := hFbounded
  let B : ℝ := max C 0
  have hB : 0 ≤ B := le_max_right C 0
  have hFB : ∀ x, ‖F x‖ ≤ B := fun x => (hC x).trans (le_max_left C 0)
  let X : Ω → I → ℝ := fun ω => I.restrict (pair0 (D.field ω))
  let G : ℂ → ℝ := rootingCylinderObservable D.unrootedLaw I F D.field D.gamma
  obtain ⟨H, hH, hHm, hArea, hagree⟩ := exists_measurableAreaVersion D.area
  have hXmeas : Measurable X := by
    exact (Finset.measurable_restrict I).comp <|
      measurable_pair0.comp D.normalizedWPGFF.1.measurable
  have hFXmeas : AEStronglyMeasurable (fun ω => F (X ω)) D.unrootedLaw :=
    (hF.measurable.comp hXmeas).aestronglyMeasurable
  have hFXbound : ∀ᵐ ω ∂D.unrootedLaw, ‖F (X ω)‖ ≤ B :=
    ae_of_all _ fun ω => hFB (X ω)
  have hLoc : ∀ᵐ ω ∂D.unrootedLaw,
      IsLocallyFiniteMeasure (D.area.areaMeasure ω) := by
    filter_upwards [hArea] with ω hω
    exact hω.1
  have hMassInt : Integrable
      (fun ω => (D.area.areaMeasure ω (ball (0 : ℂ) 1)).toReal) D.unrootedLaw :=
    integrable_areaMeasure_unitDisk_toReal hH hHm D.gamma_pos D.gamma_lt_two hArea
  have hGmeas : AEStronglyMeasurable G volume :=
    (stronglyMeasurable_rootingCylinderObservable D.normalizedWPGFF I F hF D.gamma).aestronglyMeasurable
  have hGbound : ∀ᵐ z ∂volume, ‖G z‖ ≤ B :=
    ae_of_all _ fun z => norm_rootingCylinderObservable_le
      D.normalizedWPGFF I F hFB D.gamma z
  have hTest : ∀ f : ℂ → ℝ, Continuous f → HasCompactSupport f →
      tsupport f ⊆ ball (0 : ℂ) 1 → (∀ z, 0 ≤ f z) →
      Integrable (fun ω => F (X ω) * ∫ z, f z ∂(D.area.areaMeasure ω)) D.unrootedLaw ∧
        ∫ ω, F (X ω) * ∫ z, f z ∂(D.area.areaMeasure ω) ∂D.unrootedLaw =
          ∫ z, f z * G z := by
    intro f hf hfc hfs hfn
    have hAreaInt := (integral_areaTestIntegral_eq_volume hH hHm D.gamma_pos
      D.gamma_lt_two hArea hf hfs hfn).1
    have hprodInt : Integrable
        (fun ω => F (X ω) * areaTestIntegral (μ := D.area.areaMeasure) f ω)
        D.unrootedLaw := hAreaInt.bdd_mul hFXmeas hFXbound
    have hpalm := compactTest_rootingPalm_identity D.normalizedWPGFF hH hHm hagree
      hArea D.gamma_pos D.gamma_lt_two hf hfs hfn I F hF ⟨C, hC⟩
    letI : IsFiniteMeasure (compactTestRootMeasure f) :=
      isFiniteMeasure_compactTestRootMeasure hf hfc hfn
    have hfubini := integral_rootingCylinderObservable D.normalizedWPGFF I F hF hFB
      D.gamma (ν := compactTestRootMeasure f)
    refine ⟨?_, ?_⟩
    · change Integrable
        (fun ω => F (X ω) * areaTestIntegral (μ := D.area.areaMeasure) f ω)
        D.unrootedLaw
      exact hprodInt
    · change
        (∫ ω, F (X ω) * areaTestIntegral (μ := D.area.areaMeasure) f ω
          ∂D.unrootedLaw) = ∫ z, f z * G z
      calc
        (∫ ω, F (X ω) * areaTestIntegral (μ := D.area.areaMeasure) f ω
          ∂D.unrootedLaw) =
            ∫ ω, F (X ω) * ∫ z, f z ∂(D.area.areaMeasure ω)
              ∂D.unrootedLaw := by rfl
        _ =
            ∫ p : Ω × ℂ, rootingCylinderIntegrand I F D.field D.gamma p
              ∂(D.unrootedLaw.prod (compactTestRootMeasure f)) := by
                simpa only [X, rootingCylinderIntegrand, areaTestIntegral] using hpalm.symm
        _ = ∫ z, G z ∂compactTestRootMeasure f := hfubini.symm
        _ = ∫ z, f z * G z := integral_compactTestRootMeasure_eq hf hfn
  have hweighted := integral_unitDisk_mul_of_test_expectations hLoc hMassInt hFXmeas
    hB hFXbound hGmeas hGbound hTest
  have hroot :
      ∫ g, F (I.restrict (GFFLaw.ev0 g)) ∂(D.rootedLaw.map D.field) =
        Real.pi⁻¹ * ∫ z in ball (0 : ℂ) 1, G z := by
    rw [D.integral_cylinder_rooted_eq_rawShift I F hF]
    calc
      ∫ p : Ω × ℂ,
          F (I.restrict (GFFLaw.ev0 (D.field p.1 + logRootingShift D.gamma p.2)))
          ∂(D.unrootedLaw.prod normalizedLebesgueOnRootingDisk) =
          ∫ p : Ω × ℂ, rootingCylinderIntegrand I F D.field D.gamma p
            ∂(D.unrootedLaw.prod normalizedLebesgueOnRootingDisk) := by
              apply integral_congr_ae
              filter_upwards with p
              change
                F (I.restrict (pair0 (D.field p.1 + logRootingShift D.gamma p.2)))
                  = F (I.restrict (pair0 (D.field p.1 + logRootingShift D.gamma p.2)))
              rfl
      _ = ∫ z, G z ∂normalizedLebesgueOnRootingDisk := by
        symm
        exact integral_rootingCylinderObservable D.normalizedWPGFF I F hF hFB D.gamma
      _ = Real.pi⁻¹ * ∫ z in ball (0 : ℂ) 1, G z :=
        integral_normalizedLebesgueOnRootingDisk G
  have hdensMeas : AEMeasurable
      (fun ω => D.area.unitDiskMass ω / ENNReal.ofReal Real.pi) D.unrootedLaw :=
    D.area.unitDiskMass_aemeasurable.div_const _
  have hdensTop : ∀ᵐ ω ∂D.unrootedLaw,
      D.area.unitDiskMass ω / ENNReal.ofReal Real.pi < ⊤ := by
    filter_upwards [hLoc] with ω hω
    letI : IsLocallyFiniteMeasure (D.area.areaMeasure ω) := hω
    apply ENNReal.div_lt_top
    · rw [D.area.unitDiskMass_eq, rootingDisk]
      exact (measure_ball_lt_top : D.area.areaMeasure ω (ball (0 : ℂ) 1) < ⊤).ne
    · exact ne_of_gt (ENNReal.ofReal_pos.mpr Real.pi_pos)
  have hbiased :
      ∫ g, F (I.restrict (GFFLaw.ev0 g)) ∂
          ((D.unrootedLaw.withDensity
            (fun ω => D.area.unitDiskMass ω / ENNReal.ofReal Real.pi)).map D.field) =
        Real.pi⁻¹ *
          ∫ ω, F (X ω) *
            (D.area.areaMeasure ω (ball (0 : ℂ) 1)).toReal ∂D.unrootedLaw := by
    calc
      _ = ∫ ω, F (I.restrict (GFFLaw.ev0 (D.field ω))) ∂
          (D.unrootedLaw.withDensity
            (fun ω => D.area.unitDiskMass ω / ENNReal.ofReal Real.pi)) :=
        integral_map D.normalizedWPGFF.1.measurable.aemeasurable
          ((hF.measurable.comp ((Finset.measurable_restrict I).comp
            (measurable_pi_iff.2 fun ψ => measurable_pair ψ.1))).aestronglyMeasurable)
      _ = ∫ ω, (D.area.unitDiskMass ω / ENNReal.ofReal Real.pi).toReal •
          F (I.restrict (GFFLaw.ev0 (D.field ω))) ∂D.unrootedLaw :=
        integral_withDensity_eq_integral_toReal_smul_of_aemeasurable
          hdensMeas hdensTop _
      _ = Real.pi⁻¹ *
          ∫ ω, F (X ω) *
            (D.area.areaMeasure ω (ball (0 : ℂ) 1)).toReal ∂D.unrootedLaw := by
        rw [← integral_const_mul]
        apply integral_congr_ae
        filter_upwards with ω
        rw [D.area.unitDiskMass_eq, rootingDisk, ENNReal.toReal_div,
          ENNReal.toReal_ofReal Real.pi_pos.le]
        have hev : GFFLaw.ev0 (D.field ω) = pair0 (D.field ω) := rfl
        rw [hev]
        dsimp only [X]
        simp only [smul_eq_mul]
        field_simp
  rw [hroot, hbiased, hweighted.2]

/-- The rooted normalized whole-plane field law is the unit-disk-area-biased unrooted field
law, with the exact normalization `π`. -/
theorem WholePlaneRootingFieldLawInputs.fieldLaw_eq_areaBiased_holds
    {Ω : Type*} [MeasurableSpace Ω] (D : WholePlaneRootingFieldLawInputs Ω) :
    D.rootedLaw.map D.field =
      (D.unrootedLaw.withDensity
        (fun ω => D.area.unitDiskMass ω / D.expectedUnitDiskMass)).map D.field := by
  rw [D.withDensity_areaBias_eq_div_pi]
  letI : IsProbabilityMeasure (D.rootedLaw.map D.field) := D.rootedFieldLaw_isProbability
  letI : IsProbabilityMeasure
      ((D.unrootedLaw.withDensity
        (fun ω => D.area.unitDiskMass ω / ENNReal.ofReal Real.pi)).map D.field) :=
    (Measure.isProbabilityMeasure_map_iff
      D.normalizedWPGFF.1.measurable.aemeasurable).2 D.withDensity_div_pi_isProbability
  apply measure_eq_of_boundedContinuous_cylinder_integrals_of_circleAvgFieldSupport
  · exact D.integral_cylinder_rooted_eq_areaBiased
  · exact D.rootedFieldLaw_ae_circleAvgFieldSupport
  · exact ae_circleAvgFieldSupport_map_withDensity D.normalizedWPGFF _

end MatedCRTHarmonic.ConeLemmaA10

