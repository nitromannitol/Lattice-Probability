/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module MatedCRTHarmonic.GMSCM.DataProcessing at commit fdb5cad; only the module paths of local imports are changed.
   Declarations, examples and checks that the copied results do not use are omitted.
   Changed for Lean v4.35: MemLp is now the bound eLpNorm < ∞ (the measurability argument goes to eLpNorm_lt_top_iff_lintegral_rpow_enorm_lt_top). -/
import Mathlib.MeasureTheory.Function.ConditionalExpectation.RadonNikodym
import Mathlib.MeasureTheory.Function.ConditionalExpectation.Real
import Mathlib.MeasureTheory.Function.LpSeminorm.Basic

/-!
# Restriction of a square-integrable Radon–Nikodym density

A measurable observation preserves the L² class of a Radon–Nikodym density. The density
on the observation space is the conditional expectation of the original density given
the observation. This is the Jensen step needed after a Cameron–Martin change of measure.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory
open scoped ENNReal

namespace MatedCRTHarmonic.GMSCM

variable {Ω S : Type*} [MeasurableSpace Ω] [MeasurableSpace S]
    {μ ν : Measure Ω} [IsFiniteMeasure μ] [IsProbabilityMeasure ν]

/-- Data processing for a finite-measure L² Radon–Nikodym derivative. -/
theorem rnDeriv_map_memLp_two (hμν : μ ≪ ν) {f : Ω → S} (hf : Measurable f)
    (hL2 : MemLp (fun ω => (μ.rnDeriv ν ω).toReal) 2 ν) :
    MemLp (fun x => ((μ.map f).rnDeriv (ν.map f) x).toReal) 2 (ν.map f) := by
  let : IsProbabilityMeasure (ν.map f) :=
    (Measure.isProbabilityMeasure_map_iff hf.aemeasurable).2 inferInstance
  have hcond : MemLp (ν[fun ω => (μ.rnDeriv ν ω).toReal | MeasurableSpace.comap f ‹MeasurableSpace S›]) 2 ν :=
    hL2.condExp (by norm_num)
  have hae := toReal_rnDeriv_map hμν hf
  have hcomp : MemLp
      ((fun x => ((μ.map f).rnDeriv (ν.map f) x).toReal) ∘ f) 2 ν :=
    (memLp_congr_ae hae).2 hcond
  exact (memLp_map_measure_iff
    ((Measure.measurable_rnDeriv (μ.map f) (ν.map f)).ennreal_toReal.aestronglyMeasurable)
    hf.aemeasurable).2 hcomp

/-- An L² Cameron–Martin density retains a finite second moment after restriction. -/
theorem rnDeriv_map_sq_finite (hμν : μ ≪ ν) {f : Ω → S} (hf : Measurable f)
    (hL2 : MemLp (fun ω => (μ.rnDeriv ν ω).toReal) 2 ν) :
    ∫⁻ x, ((μ.map f).rnDeriv (ν.map f) x) ^ (2 : ℝ) ∂(ν.map f) < ⊤ := by
  have hL2' := rnDeriv_map_memLp_two hμν hf hL2
  have hfin := lintegral_rpow_enorm_lt_top_of_eLpNorm_lt_top
    (p := (2 : ℝ≥0∞)) (by norm_num) (by norm_num) hL2'
  have hae : ∀ᵐ x ∂(ν.map f), (μ.map f).rnDeriv (ν.map f) x ≠ ⊤ :=
    Measure.rnDeriv_ne_top (μ.map f) (ν.map f)
  convert hfin using 1
  refine lintegral_congr_ae ?_
  filter_upwards [hae] with x hx
  simp [hx]

omit [IsFiniteMeasure μ] [IsProbabilityMeasure ν] in
/-- A finite second moment of an RN derivative gives its real-valued L² class. -/
theorem rnDeriv_memLp_two_of_sq_finite
    (h2 : ∫⁻ ω, (μ.rnDeriv ν ω) ^ (2 : ℝ) ∂ν < ⊤) :
    MemLp (fun ω => (μ.rnDeriv ν ω).toReal) 2 ν := by
  refine (eLpNorm_lt_top_iff_lintegral_rpow_enorm_lt_top
      (p := (2 : ℝ≥0∞)) (by norm_num) (by norm_num)
      (Measure.measurable_rnDeriv μ ν).ennreal_toReal.aestronglyMeasurable).2 ?_
  calc
    (∫⁻ ω, ‖(μ.rnDeriv ν ω).toReal‖ₑ ^ (2 : ℝ≥0∞).toReal ∂ν) ≤
        ∫⁻ ω, (μ.rnDeriv ν ω) ^ (2 : ℝ) ∂ν := by
          refine lintegral_mono fun ω => ?_
          by_cases hω : μ.rnDeriv ν ω = ⊤
          · simp [hω]
          · simp [hω]
    _ < ⊤ := h2

omit [IsFiniteMeasure μ] in
/-- A finite second moment of an explicit density gives an L² Radon–Nikodym derivative. -/
theorem rnDeriv_memLp_two_of_withDensity {ρ : Ω → ℝ≥0∞} (hρ : Measurable ρ)
    (hμ : μ = ν.withDensity ρ) (hρ2 : ∫⁻ ω, ρ ω ^ (2 : ℝ) ∂ν < ⊤) :
    MemLp (fun ω => (μ.rnDeriv ν ω).toReal) 2 ν := by
  have hρL2 : MemLp (fun ω => (ρ ω).toReal) 2 ν := by
    refine (eLpNorm_lt_top_iff_lintegral_rpow_enorm_lt_top
        (p := (2 : ℝ≥0∞)) (by norm_num) (by norm_num)
        hρ.ennreal_toReal.aestronglyMeasurable).2 ?_
    calc
      (∫⁻ ω, ‖(ρ ω).toReal‖ₑ ^ (2 : ℝ≥0∞).toReal ∂ν) ≤
          ∫⁻ ω, ρ ω ^ (2 : ℝ) ∂ν := by
            refine lintegral_mono fun ω => ?_
            by_cases hω : ρ ω = ⊤
            · simp [hω]
            · simp [hω]
      _ < ⊤ := hρ2
  have hae : μ.rnDeriv ν =ᵐ[ν] ρ := by
    rw [hμ]
    exact Measure.rnDeriv_withDensity ν hρ
  exact (memLp_congr_ae (hae.mono fun ω hω => by rw [hω])).2 hρL2

omit [IsFiniteMeasure μ] in
/-- A strictly positive finite density also gives a reverse comparison. Its
second moment under the tilted law is the negative first moment under the base law. -/
theorem inverse_withDensity_sq_finite {ρ : Ω → ℝ≥0∞} (hρ : Measurable ρ)
    (hρpos : ∀ ω, ρ ω ≠ 0) (hρtop : ∀ ω, ρ ω ≠ ⊤)
    (hμ : μ = ν.withDensity ρ)
    (hneg : ∫⁻ ω, ρ ω ^ (-1 : ℝ) ∂ν < ⊤) :
    ∫⁻ ω, (ν.rnDeriv μ ω) ^ (2 : ℝ) ∂μ < ⊤ := by
  have hae : ν.rnDeriv μ =ᵐ[ν] fun ω => (ρ ω)⁻¹ := by
    rw [hμ]
    have h := Measure.rnDeriv_withDensity_right_of_absolutelyContinuous
      (μ := ν) (ν := ν) Measure.AbsolutelyContinuous.rfl hρ.aemeasurable
      (Filter.Eventually.of_forall hρpos) (Filter.Eventually.of_forall hρtop)
    filter_upwards [h, Measure.rnDeriv_self ν] with ω hω hone
    simpa only [hone, mul_one] using hω
  rw [hμ] at hae ⊢
  rw [lintegral_withDensity_eq_lintegral_mul ν hρ
    ((Measure.measurable_rnDeriv ν (ν.withDensity ρ)).pow_const (2 : ℝ))]
  have heq : (fun ω => ρ ω * (ν.rnDeriv (ν.withDensity ρ) ω) ^ (2 : ℝ)) =ᵐ[ν]
      fun ω => ρ ω ^ (-1 : ℝ) := by
    filter_upwards [hae] with ω hω
    rw [hω]
    have hpos := hρpos ω
    have htop := hρtop ω
    rw [ENNReal.rpow_two, pow_two, ENNReal.rpow_neg_one]
    calc
      ρ ω * ((ρ ω)⁻¹ * (ρ ω)⁻¹) = (ρ ω * (ρ ω)⁻¹) * (ρ ω)⁻¹ := by ring
      _ = (ρ ω)⁻¹ := by rw [ENNReal.mul_inv_cancel hpos htop, one_mul]
  simp only [Pi.mul_apply]
  rw [lintegral_congr_ae heq]
  exact hneg

end MatedCRTHarmonic.GMSCM
