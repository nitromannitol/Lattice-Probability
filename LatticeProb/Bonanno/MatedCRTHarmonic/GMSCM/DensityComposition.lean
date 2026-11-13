/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module MatedCRTHarmonic.GMSCM.DensityComposition at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.MatedCRTHarmonic.GMSCM.AffineRandomComparison

/-!
# Composition of two local density comparisons

An `L²` density followed by an `L^r` density, `r>1`, has a finite
`L^(2r/(r+1))` moment relative to the first law. This is Hölder's inequality
under the intermediate law.
-/

set_option autoImplicit false
set_option maxHeartbeats 800000

noncomputable section

open MeasureTheory
open scoped ENNReal

namespace MatedCRTHarmonic.GMSCM

private theorem rpow_sub_one_mul (a : ℝ≥0∞) {p : ℝ} (hp : 1 < p) :
    a ^ (p - 1) * a = a ^ p := by
  by_cases h0 : a = 0
  · subst a
    simp [show 0 < p - 1 by linarith, show 0 < p by linarith]
  by_cases htop : a = ⊤
  · subst a
    simp [show 0 < p - 1 by linarith, show 0 < p by linarith]
  calc
    a ^ (p - 1) * a = a ^ (p - 1) * a ^ (1 : ℝ) := by rw [ENNReal.rpow_one]
    _ = a ^ ((p - 1) + 1) := (ENNReal.rpow_add _ _ h0 htop).symm
    _ = a ^ p := by congr 1; ring

/-- Composition of a square-integrable density and a density with a finite
moment above one. The exponent loss is explicit. -/
theorem withDensity_compose_moment
    {α : Type*} [MeasurableSpace α]
    (ν : Measure α) (a b : α → ℝ≥0∞)
    (ha : Measurable a) (hb : Measurable b)
    (h2 : ∫⁻ x, a x ^ (2 : ℝ) ∂ν < ⊤)
    {r : ℝ} (hr : 1 < r)
    (hrMom : ∫⁻ x, b x ^ r ∂(ν.withDensity a) < ⊤) :
    let p := 2 * r / (r + 1)
    1 < p ∧
      (ν.withDensity a).withDensity b = ν.withDensity (fun x => a x * b x) ∧
      ∫⁻ x, (a x * b x) ^ p ∂ν < ⊤ := by
  let p : ℝ := 2 * r / (r + 1)
  have hr0 : 0 < r := by linarith
  have hrp : 0 < r + 1 := by linarith
  have hp : 1 < p := by dsimp [p]; apply (one_lt_div hrp).2; nlinarith
  have hpr : p < r := by
    dsimp [p]
    apply (div_lt_iff₀ hrp).2
    nlinarith
  have hqpos : 1 < r / p := by
    apply (one_lt_div (by linarith : 0 < p)).2
    exact hpr
  have hrmp : 0 < r - p := by linarith
  have hc : (r / p).HolderConjugate (r / (r - p)) := by
    apply Real.holderConjugate_iff.mpr
    constructor
    · exact hqpos
    · field_simp
      ring
  have ha1 : ∫⁻ x, a x ∂(ν.withDensity a) < ⊤ := by
    rw [lintegral_withDensity_eq_lintegral_mul ν ha ha]
    convert h2 using 1
    apply lintegral_congr
    intro x
    simp [pow_two]
  have hH := ENNReal.lintegral_mul_le_Lp_mul_Lq (ν.withDensity a) hc
    (hb.pow_const p |>.aemeasurable)
    (ha.pow_const (p - 1) |>.aemeasurable)
  have hB : (∫⁻ x, (b x ^ p) ^ (r / p) ∂(ν.withDensity a)) < ⊤ := by
    simpa only [← ENNReal.rpow_mul, show p * (r / p) = r by field_simp] using hrMom
  have hA : (∫⁻ x, (a x ^ (p - 1)) ^ (r / (r - p)) ∂(ν.withDensity a)) < ⊤ := by
    have hpow : (p - 1) * (r / (r - p)) = 1 := by
      have hrel : (p - 1) * r = r - p := by
        dsimp [p]
        field_simp [hrp.ne']
        ring
      calc
        (p - 1) * (r / (r - p)) = ((p - 1) * r) / (r - p) := by ring
        _ = (r - p) / (r - p) := by rw [hrel]
        _ = 1 := div_self hrmp.ne'
    simpa only [← ENNReal.rpow_mul, hpow,
      ENNReal.rpow_one] using ha1
  have hM : ∫⁻ x, b x ^ p * a x ^ (p - 1) ∂(ν.withDensity a) < ⊤ :=
    lt_of_le_of_lt (by simpa only [Pi.mul_apply] using hH) (ENNReal.mul_lt_top
      (ENNReal.rpow_lt_top_of_nonneg (one_div_nonneg.mpr hc.pos.le) hB.ne)
      (ENNReal.rpow_lt_top_of_nonneg (one_div_nonneg.mpr hc.symm.pos.le) hA.ne))
  have hInt : (∫⁻ x, (a x * b x) ^ p ∂ν) =
      ∫⁻ x, b x ^ p * a x ^ (p - 1) ∂(ν.withDensity a) := by
    calc
      _ = ∫⁻ x, a x * (b x ^ p * a x ^ (p - 1)) ∂ν := by
        refine lintegral_congr fun x => ?_
        rw [ENNReal.mul_rpow_of_nonneg _ _ (by linarith : 0 ≤ p)]
        calc
          a x ^ p * b x ^ p = (a x ^ (p - 1) * a x) * b x ^ p := by
            rw [rpow_sub_one_mul (a x) hp]
          _ = a x * (b x ^ p * a x ^ (p - 1)) := by ac_rfl
      _ = _ := (lintegral_withDensity_eq_lintegral_mul ν ha
        ((hb.pow_const p).mul (ha.pow_const (p - 1)))).symm
  exact ⟨hp, (withDensity_mul ν ha hb).symm, hInt ▸ hM⟩

/-- A finite `L^r` moment on a finite measure space supplies every smaller
nonnegative exponent. -/
theorem density_moment_mono
    {α : Type*} [MeasurableSpace α] (μ : Measure α) [IsFiniteMeasure μ]
    (f : α → ℝ≥0∞) {q r : ℝ}
    (hq : 0 ≤ q) (hqr : q ≤ r)
    (hr : ∫⁻ x, f x ^ r ∂μ < ⊤) :
    ∫⁻ x, f x ^ q ∂μ < ⊤ := by
  have hpoint : ∀ x, f x ^ q ≤ 1 + f x ^ r := by
    intro x
    by_cases hx : f x ≤ 1
    · have hle : f x ^ q ≤ (1 : ℝ≥0∞) := by
        simpa using (ENNReal.rpow_le_rpow_of_exponent_ge hx hq :
          f x ^ q ≤ f x ^ (0 : ℝ))
      exact hle.trans (by simp)
    · have hx1 : 1 ≤ f x := le_of_not_ge hx
      exact (ENNReal.rpow_le_rpow_of_exponent_le hx1 hqr).trans (by simp)
  calc
    ∫⁻ x, f x ^ q ∂μ ≤ ∫⁻ x, (1 + f x ^ r) ∂μ := lintegral_mono hpoint
    _ = μ Set.univ + ∫⁻ x, f x ^ r ∂μ := by
      rw [lintegral_add_left (by fun_prop)]
      simp
    _ < ⊤ := ENNReal.add_lt_top.mpr ⟨measure_lt_top μ _, hr⟩

/-- Independent density changes on the two coordinates retain a common
moment above one. -/
theorem prod_withDensity_moment
    {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (ν₁ : Measure α) (ν₂ : Measure β)
    [IsProbabilityMeasure ν₁] [IsProbabilityMeasure ν₂]
    (a₁ : α → ℝ≥0∞) (a₂ : β → ℝ≥0∞)
    (ha₁ : Measurable a₁) (ha₂ : Measurable a₂)
    {p₁ p₂ : ℝ} (hp₁ : 1 < p₁) (hp₂ : 1 < p₂)
    (h₁ : ∫⁻ x, a₁ x ^ p₁ ∂ν₁ < ⊤)
    (h₂ : ∫⁻ y, a₂ y ^ p₂ ∂ν₂ < ⊤) :
    ∃ r : ℝ, 1 < r ∧
      (ν₁.withDensity a₁).prod (ν₂.withDensity a₂) =
        (ν₁.prod ν₂).withDensity (fun z => a₁ z.1 * a₂ z.2) ∧
      ∫⁻ z, (a₁ z.1 * a₂ z.2) ^ r ∂(ν₁.prod ν₂) < ⊤ := by
  let r := min p₁ p₂
  have hr : 1 < r := lt_min hp₁ hp₂
  have h₁r : ∫⁻ x, a₁ x ^ r ∂ν₁ < ⊤ :=
    density_moment_mono ν₁ a₁ (by linarith) (min_le_left _ _) h₁
  have h₂r : ∫⁻ y, a₂ y ^ r ∂ν₂ < ⊤ :=
    density_moment_mono ν₂ a₂ (by linarith) (min_le_right _ _) h₂
  refine ⟨r, hr, prod_withDensity ha₁ ha₂, ?_⟩
  calc
    (∫⁻ z, (a₁ z.1 * a₂ z.2) ^ r ∂(ν₁.prod ν₂)) =
        ∫⁻ z, a₁ z.1 ^ r * a₂ z.2 ^ r ∂(ν₁.prod ν₂) := by
          apply lintegral_congr
          intro z
          exact ENNReal.mul_rpow_of_nonneg _ _ (by linarith)
    _ = (∫⁻ x, a₁ x ^ r ∂ν₁) * (∫⁻ y, a₂ y ^ r ∂ν₂) := by
      rw [lintegral_prod _ (by fun_prop :
        AEMeasurable (fun z : α × β => a₁ z.1 ^ r * a₂ z.2 ^ r) (ν₁.prod ν₂))]
      simp_rw [lintegral_const_mul _ (ha₂.pow_const r)]
      rw [lintegral_mul_const _ (ha₁.pow_const r)]
    _ < ⊤ := ENNReal.mul_lt_top h₁r h₂r

end MatedCRTHarmonic.GMSCM
