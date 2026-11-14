/-
Copyright (c) 2026. All rights reserved.
-/
import Mathlib
import LatticeProb.Prob.LevyProkhorovLipschitz

/-!
# Integrals of bounded functions against two close probability measures

If two probability measures differ by at most `ε` on every measurable set, then the integrals of a
measurable function bounded by `B` differ by at most `2 B ε`.

* `abs_integral_sub_integral_le_of_abs_measureReal_sub_le`: the bound, by the layer cake formula
  for the nonnegative function `g + B ≤ 2 B`.
-/

set_option autoImplicit false

open MeasureTheory Set

namespace LatticeProb

variable {Ω : Type*} [MeasurableSpace Ω]

/-- **Total variation controls bounded integrals.** Let `μ, ν` be probability measures with
`|μ A - ν A| ≤ ε` for every measurable `A`, and `g` measurable with `|g| ≤ B`.  Then
`|∫ g dμ - ∫ g dν| ≤ 2 B ε`. -/
theorem abs_integral_sub_integral_le_of_abs_measureReal_sub_le (μ ν : Measure Ω)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] {g : Ω → ℝ} (hg : Measurable g) {B ε : ℝ}
    (hB : 0 ≤ B) (hgB : ∀ x, |g x| ≤ B)
    (hTV : ∀ A : Set Ω, MeasurableSet A → |μ.real A - ν.real A| ≤ ε) :
    |∫ x, g x ∂μ - ∫ x, g x ∂ν| ≤ 2 * B * ε := by
  have hε : 0 ≤ ε := by simpa using hTV univ MeasurableSet.univ
  set h : Ω → ℝ := fun x => g x + B with hh
  have hmeas : Measurable h := hg.add_const B
  have hh0 : ∀ x, 0 ≤ h x := fun x => by
    have := neg_abs_le (g x); have := hgB x; simp only [hh]; linarith
  have hhB : ∀ x, h x ≤ 2 * B := fun x => by
    have := le_abs_self (g x); have := hgB x; simp only [hh]; linarith
  have hint : ∀ P : Measure Ω, IsProbabilityMeasure P → Integrable h P := fun P _ =>
    (integrable_const (2 * B)).mono' hmeas.aestronglyMeasurable
      (Filter.Eventually.of_forall fun x => by
        rw [Real.norm_eq_abs, abs_of_nonneg (hh0 x)]; exact hhB x)
  have hlay : ∀ P : Measure Ω, IsProbabilityMeasure P →
      ∫ x, h x ∂P = ∫ t in Ioc 0 (2 * B), P.real {a | t ≤ h a} := fun P hP =>
    Integrable.integral_eq_integral_Ioc_meas_le (hint P hP)
      (Filter.Eventually.of_forall hh0) (Filter.Eventually.of_forall hhB)
  have hgint : ∀ P : Measure Ω, IsProbabilityMeasure P → ∫ x, h x ∂P = ∫ x, g x ∂P + B := by
    intro P hP
    have hgi : Integrable g P := (integrable_const B).mono' hg.aestronglyMeasurable
      (Filter.Eventually.of_forall fun x => by rw [Real.norm_eq_abs]; exact hgB x)
    simp only [hh]
    rw [integral_add hgi (integrable_const B)]
    simp
  have hanti : Antitone (fun t : ℝ => {a | t ≤ h a}) := fun s t hst a ha => le_trans hst ha
  have hsub : ∫ x, g x ∂μ - ∫ x, g x ∂ν
      = ∫ t in Ioc 0 (2 * B), (μ.real {a | t ≤ h a} - ν.real {a | t ≤ h a}) := by
    rw [integral_sub (integrableOn_measureReal_of_antitone μ _ hanti 0 (2 * B))
      (integrableOn_measureReal_of_antitone ν _ hanti 0 (2 * B)),
      ← hlay μ inferInstance, ← hlay ν inferInstance, hgint μ inferInstance,
      hgint ν inferInstance]
    ring
  rw [hsub]
  have hbd := norm_setIntegral_le_of_norm_le_const (μ := volume)
    (s := Ioc (0 : ℝ) (2 * B)) (C := ε) (f := fun t => μ.real {a | t ≤ h a} - ν.real {a | t ≤ h a})
    measure_Ioc_lt_top (fun t _ => by
      rw [Real.norm_eq_abs]
      exact hTV _ (hmeas measurableSet_Ici))
  have hvol : (volume : Measure ℝ).real (Ioc (0 : ℝ) (2 * B)) = 2 * B := by
    rw [Real.volume_real_Ioc_of_le (by linarith)]; ring
  rw [hvol] at hbd
  rw [Real.norm_eq_abs] at hbd
  calc _ ≤ ε * (2 * B) := hbd
    _ = 2 * B * ε := by ring

end LatticeProb
