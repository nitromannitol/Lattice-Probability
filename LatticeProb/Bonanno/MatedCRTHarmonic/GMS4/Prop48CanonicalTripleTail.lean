/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module MatedCRTHarmonic.GMS4.Prop48CanonicalTripleTail at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.MatedCRTHarmonic.GMS4.Prop48CanonicalTripleSpatial

/-!
# Chebyshev bound for the triple-centred Proposition 4.8 fluctuation

The variance premise is [18] (4.38), restricted to the spatial good event.
The zero-test branch is retained as required by the Proposition 4.10 consumer.
-/

set_option autoImplicit false
noncomputable section

open MeasureTheory Set Metric
open scoped ENNReal NNReal

namespace MatedCRTHarmonic.GMS4.Canonical

open MatedCRTHarmonic.MatedCRT

variable {γ : ℝ} {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
  {X X₀ hIG₀ : Ω → Field} {B B' B₀ B₀' : ℝ≥0 → Ω → ℝ}
  {U : Ω → ℝ} {ηL η η₀ : Ω → C(ℝ, ℂ)} {bm : Ω → Path2}

theorem prop48_bad_probability_le_of_spatial_variance_triple
    (D : IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm)
    (hγ : γ ∈ Ioo (0 : ℝ) 2)
    {ε q ζ ρ α A Bmean Creg Cvar : ℝ}
    (hε : 0 < ε) (hCreg : 0 ≤ Creg) (hCvar : 0 ≤ Cvar)
    (hmeanPair : ∀ z ∈ ball (0 : ℂ) ρ,
      Integrable (maskedUStar D hγ ε q ζ z) P ∧
        ∀ᵐ ω ∂P, conditionalMean D hγ ε q ζ ω z ≤ Bmean)
    (hmeanTriple : ∀ z ∈ ball (0 : ℂ) ρ,
      ∀ᵐ ω ∂P, GMS4O.p48oCondMeanTriple D hγ ε q ζ ω z ≤ A)
    {E : Set Ω} (hEm : MeasurableSet E)
    (hEfail : P Eᶜ ≤ ENNReal.ofReal (Creg * ε ^ α))
    (hElocal : ∀ᵐ ω ∂P, ω ∈ E →
      ∀ᵐ z ∂(volume.restrict (ball (0 : ℂ) ρ)),
        ω ∈ localEvent D hγ ε q ζ z)
    {domain : Set ℂ} {f : ℂ → ℝ}
    (hadm : GMS4.Prop48TestPairAdmissible ρ domain f)
    (hvar : (∫⁻ ω in E, ENNReal.ofReal
      (GMS4O.p48oPrimedFluctuationTriple D hγ ε q ζ domain f ω ^ 2) ∂P) ≤
      ENNReal.ofReal (((ε ^ α * GMS4.prop48TestSupNorm ρ f) ^ 2) *
        (Cvar * ε ^ α))) :
    P {ω | A * (∫ z in domain, f z) +
        ε ^ α * GMS4.prop48TestSupNorm ρ f <
          ∫ z in domain, f z * uStar ε η₀ ω z} ≤
      ENNReal.ofReal ((Creg + Cvar) * ε ^ α) := by
  let N := GMS4.prop48TestSupNorm ρ f
  have hNnonneg : 0 ≤ N := by
    dsimp [N, GMS4.prop48TestSupNorm]
    apply le_csSup (GMS4.prop48TestSupNorm_bddAbove hadm.test_bounded)
    exact Set.mem_insert 0 _
  have hpow : 0 < ε ^ α := Real.rpow_pos_of_pos hε _
  by_cases hN : 0 < N
  · have hbound : 0 < ε ^ α * N := mul_pos hpow hN
    have hfluc := GMS4.measure_gt_le_of_lintegral_sq_le (P.restrict E)
      (by
        change AEMeasurable
          (GMS4O.p48oPrimedFluctuationTriple D hγ ε q ζ domain f)
          (P.restrict E)
        exact (aemeasurable_primedFluctuationTriple D hγ hε.le q ζ hadm).mono_measure
          Measure.restrict_le_self)
      hbound hvar
    have hcompare := ae_good_integral_comparison_triple
      D hγ hε.le hmeanPair hmeanTriple E hElocal hadm
    have hsub : {ω | A * (∫ z in domain, f z) + ε ^ α * N <
          ∫ z in domain, f z * uStar ε η₀ ω z} ≤ᵐ[P]
        Eᶜ ∪
          (E ∩ {ω | ε ^ α * N <
            GMS4O.p48oPrimedFluctuationTriple D hγ ε q ζ domain f ω}) := by
      filter_upwards [hcompare] with ω hc hb
      by_cases he : ω ∈ E
      · exact Or.inr ⟨he, (add_lt_add_iff_left
          (A * (∫ z in domain, f z))).mp (lt_of_lt_of_le hb (hc he))⟩
      · exact Or.inl he
    have hεpow : 0 ≤ ε ^ α := hpow.le
    calc
      P {ω | A * (∫ z in domain, f z) +
        ε ^ α * GMS4.prop48TestSupNorm ρ f <
          ∫ z in domain, f z * uStar ε η₀ ω z} ≤
          P (Eᶜ ∪ (E ∩ {ω | ε ^ α * N <
            GMS4O.p48oPrimedFluctuationTriple D hγ ε q ζ domain f ω})) :=
        measure_mono_ae hsub
      _ ≤ P Eᶜ + P (E ∩ {ω | ε ^ α * N <
          GMS4O.p48oPrimedFluctuationTriple D hγ ε q ζ domain f ω}) :=
        measure_union_le _ _
      _ ≤ P Eᶜ + (P.restrict E) {ω | ε ^ α * N <
          GMS4O.p48oPrimedFluctuationTriple D hγ ε q ζ domain f ω} := by
        rw [Measure.restrict_apply' hEm, inter_comm]
      _ ≤ ENNReal.ofReal (Creg * ε ^ α) +
          ENNReal.ofReal (Cvar * ε ^ α) := add_le_add hEfail hfluc
      _ = ENNReal.ofReal ((Creg + Cvar) * ε ^ α) := by
        rw [← ENNReal.ofReal_add
          (mul_nonneg hCreg hεpow) (mul_nonneg hCvar hεpow)]
        congr 1
        ring
  · have hN0 : N = 0 := le_antisymm (le_of_not_gt hN) hNnonneg
    have hfzero : ∀ z ∈ ball (0 : ℂ) ρ, f z = 0 := by
      intro z hz
      have habs := GMS4.abs_le_prop48TestSupNorm hadm.test_bounded hz
      rw [show GMS4.prop48TestSupNorm ρ f = N by rfl, hN0] at habs
      exact abs_eq_zero.mp (le_antisymm habs (abs_nonneg _))
    have htest : (∫ z in domain, f z) = 0 := by
      apply setIntegral_eq_zero_of_forall_eq_zero
      intro z hz
      exact hfzero z (hadm.domain_subset_ball hz)
    have hu : ∀ ω, (∫ z in domain, f z * uStar ε η₀ ω z) = 0 := by
      intro ω
      apply setIntegral_eq_zero_of_forall_eq_zero
      intro z hz
      rw [hfzero z (hadm.domain_subset_ball hz), zero_mul]
    have hbad : {ω | A * (∫ z in domain, f z) +
        ε ^ α * GMS4.prop48TestSupNorm ρ f <
          ∫ z in domain, f z * uStar ε η₀ ω z} = (∅ : Set Ω) := by
      ext ω
      simp [htest, hu ω, show GMS4.prop48TestSupNorm ρ f = 0 from hN0]
    rw [hbad, measure_empty]
    exact bot_le

end MatedCRTHarmonic.GMS4.Canonical

