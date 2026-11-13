/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module MatedCRTHarmonic.GMSCM.RandomShiftComparison at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.MatedCRTHarmonic.GMSCM.RandomShiftCM
import LatticeProb.Bonanno.MatedCRTHarmonic.GMSCM.RandomMixture

/-!
# Observation of a Gaussian mixture with a random Cameron–Martin shift

The scalar coefficient may be correlated with the exterior harmonic field.
Independence is required only between the complete exterior data and the
zero-boundary GFF. The law comparison and its `L^p` bound survive every
measurable observation.
-/

set_option autoImplicit false
set_option maxHeartbeats 800000

noncomputable section

open MeasureTheory ProbabilityTheory Set TopologicalSpace LQGMetric LQGMetric.MarkovZB
open MatedCRTHarmonic.MoTPort.IG.GFFAbsCont
open scoped ENNReal

namespace MatedCRTHarmonic.GMSCM

/-- A Gaussian-square moment for the random coefficient makes every measurable
observation of its zero-boundary Cameron–Martin mixture absolutely continuous,
with an `L^p` density for some `p > 1`. -/
theorem randomZB_observation_comparison
    {U : Opens ℂ} {A Ω S : Type*}
    [MeasurableSpace A] [MeasurableSpace Ω] [MeasurableSpace S]
    {κ : Measure A} [IsProbabilityMeasure κ]
    {P : Measure Ω} [IsProbabilityMeasure P]
    {Z : Ω → DistOn U} (hZ : IsZeroBoundaryGFF U Z P)
    (hadm : ZBAdmissible U) (hne : (U : Set ℂ).Nonempty)
    (f₀ f₁ : zsSub (U : Set ℂ))
    (c : A → ℝ) (hc : Measurable c) {t : ℝ} (ht : 0 < t)
    (hct : Integrable (fun a => Real.exp (t * (c a) ^ 2)) κ)
    (observe : A × DistOn U → S) (hobserve : Measurable observe) :
    ∃ p : ℝ, 1 < p ∧ p < 2 ∧ ∃ M : S → ℝ≥0∞,
      Measurable M ∧
      (κ.prod (P.map Z)).map (fun x =>
        observe (x.1, randomZBShift f₀ f₁ (c x.1) x.2)) =
        ((κ.prod (P.map Z)).map observe).withDensity M ∧
      ∫⁻ y, M y ^ p ∂((κ.prod (P.map Z)).map observe) < ⊤ := by
  let ν : Measure (DistOn U) := P.map Z
  let : IsProbabilityMeasure ν :=
    (Measure.isProbabilityMeasure_map_iff hZ.measurable.aemeasurable).2 inferInstance
  obtain ⟨p, hp, hp2, hmoment⟩ :=
    exists_randomZBDensity_product_moment hZ hadm f₀ f₁ c hc ht hct
  let pE : ℝ≥0∞ := ENNReal.ofReal p
  have hpE : 1 ≤ pE := by
    dsimp [pE]
    simpa using (ENNReal.ofReal_le_ofReal (by linarith : (1 : ℝ) ≤ p))
  have hpEtop : pE ≠ ⊤ := ENNReal.ofReal_ne_top
  have hpEreal : pE.toReal = p := ENNReal.toReal_ofReal (by linarith : 0 ≤ p)
  have hshift : Measurable (fun x : A × DistOn U =>
      randomZBShift f₀ f₁ (c x.1) x.2) :=
    (measurable_randomZBShift f₀ f₁).comp
      ((hc.comp measurable_fst).prodMk measurable_snd)
  have hρ : Measurable (fun x : A × DistOn U =>
      randomZBDensity f₀ f₁ (c x.1) x.2) :=
    (measurable_randomZBDensity f₀ f₁).comp
      ((hc.comp measurable_fst).prodMk measurable_snd)
  obtain ⟨M, hMm, hLaw, hMp⟩ :=
    mixture_observation_comparison (κ := κ) (ν := ν) hshift hρ
      (fun a => randomZBShift_law hZ hadm hne f₀ f₁ (c a))
      hpE hpEtop (by simpa only [hpEreal] using hmoment) observe hobserve
  exact ⟨p, hp, hp2, M, hMm, hLaw, by simpa only [hpEreal] using hMp⟩

/-- In the orientation of (4.16), the unshifted observed law has an `L^p`
density relative to the randomly shifted observed law. -/
theorem randomZB_observation_comparison_reverse
    {U : Opens ℂ} {A Ω S : Type*}
    [MeasurableSpace A] [MeasurableSpace Ω] [MeasurableSpace S]
    {κ : Measure A} [IsProbabilityMeasure κ]
    {P : Measure Ω} [IsProbabilityMeasure P]
    {Z : Ω → DistOn U} (hZ : IsZeroBoundaryGFF U Z P)
    (hadm : ZBAdmissible U) (hne : (U : Set ℂ).Nonempty)
    (f₀ f₁ : zsSub (U : Set ℂ))
    (c : A → ℝ) (hc : Measurable c) {t : ℝ} (ht : 0 < t)
    (hct : Integrable (fun a => Real.exp (t * (c a) ^ 2)) κ)
    (observe : A × DistOn U → S) (hobserve : Measurable observe) :
    ∃ p : ℝ, 1 < p ∧ p < 2 ∧ ∃ M : S → ℝ≥0∞,
      Measurable M ∧
      (κ.prod (P.map Z)).map observe =
        ((κ.prod (P.map Z)).map (fun x =>
          observe (x.1, randomZBShift f₀ f₁ (c x.1) x.2))).withDensity M ∧
      ∫⁻ y, M y ^ p ∂((κ.prod (P.map Z)).map (fun x =>
        observe (x.1, randomZBShift f₀ f₁ (c x.1) x.2))) < ⊤ := by
  let obsShift : A × DistOn U → S := fun x =>
    observe (x.1, randomZBShift f₀ f₁ (c x.1) x.2)
  have hshift : Measurable (fun x : A × DistOn U =>
      randomZBShift f₀ f₁ (c x.1) x.2) :=
    (measurable_randomZBShift f₀ f₁).comp
      ((hc.comp measurable_fst).prodMk measurable_snd)
  have hobsShift : Measurable obsShift :=
    hobserve.comp (measurable_fst.prodMk hshift)
  obtain ⟨p, hp, hp2, M, hMm, hLaw, hMp⟩ :=
    randomZB_observation_comparison hZ hadm hne (-f₀) (-f₁)
      c hc ht hct obsShift hobsShift
  have hcancel : (fun x : A × DistOn U =>
      obsShift (x.1, randomZBShift (-f₀) (-f₁) (c x.1) x.2)) = observe := by
    funext x
    have e : randomZBShift f₀ f₁ (c x.1)
        (randomZBShift (-f₀) (-f₁) (c x.1) x.2) = x.2 := by
      simp only [randomZBShift, ofFunOn_neg_zsSub, smul_neg]
      abel
    exact congrArg (fun z => observe (x.1, z)) e
  refine ⟨p, hp, hp2, M, hMm, ?_, ?_⟩
  · simpa only [hcancel] using hLaw
  · exact hMp

end MatedCRTHarmonic.GMSCM
