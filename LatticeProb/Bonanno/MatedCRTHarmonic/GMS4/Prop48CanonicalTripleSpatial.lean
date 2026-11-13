/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module MatedCRTHarmonic.GMS4.Prop48CanonicalTripleSpatial at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.MatedCRTHarmonic.GMS4O.Prop48OTripleMean
import LatticeProb.Bonanno.MatedCRTHarmonic.GMS4.Prop48CanonicalRegularitySpatial

/-!
# Spatial comparison for the triple conditional mean

The jointly measurable triple mean is bounded almost everywhere in space on
one probability-one event. Its spatial integral supplies the mean term in
[18] (4.29); the all-visit density supplies the remaining fluctuation.
-/

set_option autoImplicit false
noncomputable section

open MeasureTheory Set Metric Filter
open scoped ENNReal NNReal

namespace MatedCRTHarmonic.GMS4.Canonical

open MatedCRTHarmonic.MatedCRT

variable {γ : ℝ} {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
  {X X₀ hIG₀ : Ω → Field} {B B' B₀ B₀' : ℝ≥0 → Ω → ℝ}
  {U : Ω → ℝ} {ηL η η₀ : Ω → C(ℝ, ℂ)} {bm : Ω → Path2}

theorem ae_ae_condMeanTriple_le
    (D : IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm)
    (hγ : γ ∈ Ioo (0 : ℝ) 2) (ε q ζ ρ A : ℝ)
    (hmean : ∀ z ∈ ball (0 : ℂ) ρ,
      ∀ᵐ ω ∂P, GMS4O.p48oCondMeanTriple D hγ ε q ζ ω z ≤ A) :
    ∀ᵐ ω ∂P, ∀ᵐ z ∂(volume.restrict (ball (0 : ℂ) ρ)),
      GMS4O.p48oCondMeanTriple D hγ ε q ζ ω z ≤ A := by
  let _ := D.isProbabilityMeasure
  have hS : MeasurableSet {p : Ω × ℂ |
      GMS4O.p48oCondMeanTriple D hγ ε q ζ p.1 p.2 ≤ A} :=
    measurableSet_le (GMS4O.measurable_p48oCondMeanTriple D hγ ε q ζ) measurable_const
  have h1 : ∀ᵐ z ∂(volume.restrict (ball (0 : ℂ) ρ)), ∀ᵐ ω ∂P,
      GMS4O.p48oCondMeanTriple D hγ ε q ζ ω z ≤ A := by
    rw [ae_restrict_iff' measurableSet_ball]
    exact Eventually.of_forall fun z hz => hmean z hz
  exact (Measure.ae_ae_comm hS).2 h1

theorem ae_integrable_test_mul_condMeanTriple
    (D : IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm)
    (hγ : γ ∈ Ioo (0 : ℝ) 2) (ε q ζ ρ A : ℝ)
    (hmean : ∀ z ∈ ball (0 : ℂ) ρ,
      ∀ᵐ ω ∂P, GMS4O.p48oCondMeanTriple D hγ ε q ζ ω z ≤ A)
    {domain : Set ℂ} {f : ℂ → ℝ}
    (hadm : GMS4.Prop48TestPairAdmissible ρ domain f) :
    ∀ᵐ ω ∂P, Integrable (fun z => f z * GMS4O.p48oCondMeanTriple D hγ ε q ζ ω z)
      (volume.restrict domain) := by
  filter_upwards [ae_ae_condMeanTriple_le D hγ ε q ζ ρ A hmean] with ω hω
  have hm : Measurable fun z => GMS4O.p48oCondMeanTriple D hγ ε q ζ ω z :=
    (GMS4O.measurable_p48oCondMeanTriple D hγ ε q ζ).comp
      (measurable_const.prodMk measurable_id)
  have hωD : ∀ᵐ z ∂(volume.restrict domain),
      GMS4O.p48oCondMeanTriple D hγ ε q ζ ω z ≤ A :=
    ae_restrict_of_ae_restrict_of_subset hadm.domain_subset_ball hω
  refine IntegrableOn.of_bound (GMS4O.p48o_volume_lt_top_of_admissible hadm) ?_
    (GMS4.prop48TestSupNorm ρ f * |A|) ?_
  · have hext : Measurable fun z => GMS4O.p48oTestExt ρ f z *
        GMS4O.p48oCondMeanTriple D hγ ε q ζ ω z :=
      (GMS4O.measurable_p48oTestExt hadm.test_measurable).mul hm
    refine hext.aestronglyMeasurable.congr ?_
    refine (ae_restrict_iff' hadm.domain_borel).2 (Eventually.of_forall fun z hz => ?_)
    simp only
    rw [GMS4O.p48oTestExt_eq_of_mem (hadm.domain_subset_ball hz)]
  · filter_upwards [hωD, ae_restrict_mem hadm.domain_borel] with z hzA hzD
    have h0 := GMS4O.p48oCondMeanTriple_nonneg D hγ ε q ζ ω z
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg h0]
    exact mul_le_mul (GMS4O.p48o_abs_test_le hadm (hadm.domain_subset_ball hzD))
      (hzA.trans (le_abs_self A)) h0
      ((abs_nonneg _).trans (GMS4O.p48o_abs_test_le hadm (hadm.domain_subset_ball hzD)))

theorem ae_setIntegral_test_mul_condMeanTriple_le
    (D : IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm)
    (hγ : γ ∈ Ioo (0 : ℝ) 2) (ε q ζ ρ A : ℝ)
    (hmean : ∀ z ∈ ball (0 : ℂ) ρ,
      ∀ᵐ ω ∂P, GMS4O.p48oCondMeanTriple D hγ ε q ζ ω z ≤ A)
    {domain : Set ℂ} {f : ℂ → ℝ}
    (hadm : GMS4.Prop48TestPairAdmissible ρ domain f) :
    ∀ᵐ ω ∂P, (∫ z in domain, f z * GMS4O.p48oCondMeanTriple D hγ ε q ζ ω z) ≤
      A * ∫ z in domain, f z := by
  filter_upwards [ae_ae_condMeanTriple_le D hγ ε q ζ ρ A hmean,
    ae_integrable_test_mul_condMeanTriple D hγ ε q ζ ρ A hmean hadm] with ω hω hint
  have hωD : ∀ᵐ z ∂(volume.restrict domain),
      GMS4O.p48oCondMeanTriple D hγ ε q ζ ω z ≤ A :=
    ae_restrict_of_ae_restrict_of_subset hadm.domain_subset_ball hω
  have hfA : IntegrableOn (fun z => f z * A) domain :=
    (GMS4O.p48o_integrableOn_test hadm).mul_const A
  calc
    (∫ z in domain, f z * GMS4O.p48oCondMeanTriple D hγ ε q ζ ω z) ≤
        ∫ z in domain, f z * A := by
          refine setIntegral_mono_ae_restrict hint hfA ?_
          filter_upwards [hωD, ae_restrict_mem hadm.domain_borel] with z hzA hzD
          exact mul_le_mul_of_nonneg_left hzA (GMS4O.p48o_test_nonneg hadm hzD)
    _ = A * ∫ z in domain, f z := by rw [integral_mul_const, mul_comm]

theorem aemeasurable_primedFluctuationTriple
    (D : IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm)
    (hγ : γ ∈ Ioo (0 : ℝ) 2) {ε : ℝ} (hε : 0 ≤ ε) (q ζ : ℝ)
    {ρ : ℝ} {domain : Set ℂ} {f : ℂ → ℝ}
    (hadm : GMS4.Prop48TestPairAdmissible ρ domain f) :
    AEMeasurable (GMS4O.p48oPrimedFluctuationTriple D hγ ε q ζ domain f) P := by
  have hG : Measurable fun p : Ω × ℂ => GMS4O.p48oTestExt ρ f p.2 *
      (GMS4O.p48oMaskedVersion D hγ ε q ζ p.1 p.2 -
        GMS4O.p48oCondMeanTriple D hγ ε q ζ p.1 p.2) :=
    ((GMS4O.measurable_p48oTestExt hadm.test_measurable).comp measurable_snd).mul
      ((GMS4O.measurable_p48oMaskedVersion D hγ hε q ζ).sub
        (GMS4O.measurable_p48oCondMeanTriple D hγ ε q ζ))
  have hsm := hG.stronglyMeasurable.integral_prod_right' (ν := volume.restrict domain)
  refine hsm.measurable.aemeasurable.congr ?_
  filter_upwards [GMS4O.p48o_ae_maskedVersion_eq D hγ ε q ζ,
    GMS4O.p48o_ae_ae_maskedPrime_eq_masked D hγ ε q ζ] with ω h1 h2
  refine integral_congr_ae ?_
  filter_upwards [ae_restrict_of_ae h2, ae_restrict_mem hadm.domain_borel] with z hz hzD
  rw [GMS4O.p48oTestExt_eq_of_mem (hadm.domain_subset_ball hzD), h1 z, hz]

theorem ae_good_integral_comparison_triple
    (D : IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm)
    (hγ : γ ∈ Ioo (0 : ℝ) 2) {ε : ℝ} (hε : 0 ≤ ε)
    {q ζ ρ A Bmean : ℝ}
    (hmeanPair : ∀ z ∈ ball (0 : ℂ) ρ,
      Integrable (maskedUStar D hγ ε q ζ z) P ∧
        ∀ᵐ ω ∂P, conditionalMean D hγ ε q ζ ω z ≤ Bmean)
    (hmeanTriple : ∀ z ∈ ball (0 : ℂ) ρ,
      ∀ᵐ ω ∂P, GMS4O.p48oCondMeanTriple D hγ ε q ζ ω z ≤ A)
    (E : Set Ω)
    (hE : ∀ᵐ ω ∂P, ω ∈ E →
      ∀ᵐ z ∂(volume.restrict (ball (0 : ℂ) ρ)),
        ω ∈ localEvent D hγ ε q ζ z)
    {domain : Set ℂ} {f : ℂ → ℝ}
    (hadm : GMS4.Prop48TestPairAdmissible ρ domain f) :
    ∀ᵐ ω ∂P, ω ∈ E →
      (∫ z in domain, f z * uStar ε η₀ ω z) ≤
        A * (∫ z in domain, f z) +
          GMS4O.p48oPrimedFluctuationTriple D hγ ε q ζ domain f ω := by
  filter_upwards [ae_integral_maskedPrime_eq_masked D hγ ε q ζ domain f,
    GMS4O.p48o_ae_integrable_test_mul_maskedPrime D hγ hε hmeanPair hadm,
    ae_integrable_test_mul_condMeanTriple D hγ ε q ζ ρ A hmeanTriple hadm,
    ae_setIntegral_test_mul_condMeanTriple_le D hγ ε q ζ ρ A hmeanTriple hadm,
    hE] with ω hmask hIntPrime hIntMean hmeanω hlocal hωE
  have hlocalD : ∀ᵐ z ∂(volume.restrict domain),
      ω ∈ localEvent D hγ ε q ζ z :=
    ae_restrict_of_ae_restrict_of_subset hadm.domain_subset_ball (hlocal hωE)
  have hmasked : (∫ z in domain, f z * maskedUStarPrime D hγ ε q ζ z ω) =
      ∫ z in domain, f z * uStar ε η₀ ω z := by
    calc
      _ = ∫ z in domain, f z * maskedUStar D hγ ε q ζ z ω := hmask
      _ = ∫ z in domain, f z * uStar ε η₀ ω z := by
        apply integral_congr_ae
        filter_upwards [hlocalD] with z hz
        change f z * (localEvent D hγ ε q ζ z).indicator
          (fun ω' => uStar ε η₀ ω' z) ω = f z * uStar ε η₀ ω z
        rw [Set.indicator_of_mem hz]
  have hsubtract : GMS4O.p48oPrimedFluctuationTriple D hγ ε q ζ domain f ω =
      (∫ z in domain, f z * maskedUStarPrime D hγ ε q ζ z ω) -
        ∫ z in domain, f z * GMS4O.p48oCondMeanTriple D hγ ε q ζ ω z := by
    change (∫ z, f z * (maskedUStarPrime D hγ ε q ζ z ω -
      GMS4O.p48oCondMeanTriple D hγ ε q ζ ω z) ∂volume.restrict domain) = _
    simp_rw [mul_sub]
    exact integral_sub hIntPrime hIntMean
  rw [hsubtract, hmasked]
  linarith

end MatedCRTHarmonic.GMS4.Canonical

