/-
The exponential-tail Jensen comparison for sparse symmetric laws: an even convex function
tested against a rescaled unit-exponential law is bounded below by a two-point comparison at
the endpoints `±1` and at `0`, uniformly as the rescaling parameter grows.

Moved from Parking-Sharpness.
-/
import Mathlib.Probability.Distributions.Exponential
import Mathlib.Analysis.Convex.Integral

noncomputable section
namespace LatticeProb.ConvexOrder
open MeasureTheory ProbabilityTheory Set Real

/-- The unit exponential law written with its elementary density. -/
theorem expMeasure_one_eq : ProbabilityTheory.expMeasure 1 =
    (volume.restrict (Set.Ici (0 : ℝ))).withDensity (fun x => ENNReal.ofReal (Real.exp (-x))) := by
  have heq : gammaPDF 1 1 = Set.indicator (Set.Ici (0 : ℝ))
      (fun x => ENNReal.ofReal (Real.exp (-x))) := by
    funext x
    change exponentialPDF 1 x = _
    rw [exponentialPDF_eq]
    by_cases hx : 0 ≤ x <;> simp [hx]
  rw [ProbabilityTheory.expMeasure, gammaMeasure, heq,
    withDensity_indicator measurableSet_Ici]

/-- The density formula for a real integral against the unit exponential law. -/
theorem integral_expMeasure_one (f : ℝ → ℝ) :
    ∫ x, f x ∂(ProbabilityTheory.expMeasure 1) =
      ∫ x in Set.Ioi (0 : ℝ), Real.exp (-x) * f x := by
  rw [expMeasure_one_eq]
  rw [integral_withDensity_eq_integral_toReal_smul₀
    (by fun_prop) (ae_of_all _ fun x => ENNReal.ofReal_lt_top) f]
  simp only [ENNReal.toReal_ofReal (Real.exp_pos _).le, smul_eq_mul]
  rw [integral_Ici_eq_integral_Ioi]

/-- Integrability under the unit exponential law is weighted integrability. -/
theorem integrable_expMeasure_one_iff (f : ℝ → ℝ) :
    Integrable f (ProbabilityTheory.expMeasure 1) ↔
      IntegrableOn (fun x => Real.exp (-x) * f x) (Set.Ioi (0 : ℝ)) := by
  rw [expMeasure_one_eq, integrable_withDensity_iff_integrable_smul'
    (by fun_prop) (ae_of_all _ fun x => ENNReal.ofReal_lt_top)]
  simp only [ENNReal.toReal_ofReal (Real.exp_pos _).le, smul_eq_mul]
  exact integrableOn_Ici_iff_integrableOn_Ioi
end LatticeProb.ConvexOrder

namespace LatticeProb.ConvexOrder
open MeasureTheory ProbabilityTheory Set Real

/-- The unit exponential law is supported on the nonnegative half-line. -/
theorem ae_nonneg_expMeasure_one : ∀ᵐ x ∂(ProbabilityTheory.expMeasure 1), 0 ≤ x := by
  rw [expMeasure_one_eq, ← restrict_withDensity measurableSet_Ici]
  exact ae_restrict_mem measurableSet_Ici

/-- Restricting above a nonnegative threshold leaves the exponential density. -/
theorem setIntegral_expMeasure_one_Ioi {t : ℝ} (ht : 0 ≤ t) (f : ℝ → ℝ) :
    ∫ x in Set.Ioi t, f x ∂(ProbabilityTheory.expMeasure 1) =
      ∫ x in Set.Ioi t, Real.exp (-x) * f x := by
  rw [expMeasure_one_eq, restrict_withDensity measurableSet_Ioi,
    Measure.restrict_restrict measurableSet_Ioi]
  have heq : Set.Ioi t ∩ Set.Ici (0 : ℝ) = Set.Ioi t :=
    Set.inter_eq_left.mpr fun x hx => ht.trans hx.le
  rw [heq, integral_withDensity_eq_integral_toReal_smul₀
    (by fun_prop) (ae_of_all _ fun x => ENNReal.ofReal_lt_top) f]
  simp only [ENNReal.toReal_ofReal (Real.exp_pos _).le, smul_eq_mul]

/-- The upper tail of the unit exponential law. -/
theorem expMeasure_one_Ioi_real {t : ℝ} (ht : 0 ≤ t) :
    (ProbabilityTheory.expMeasure 1).real (Set.Ioi t) = Real.exp (-t) := by
  calc (ProbabilityTheory.expMeasure 1).real (Set.Ioi t) =
      ∫ _x in Set.Ioi t, (1 : ℝ) ∂(ProbabilityTheory.expMeasure 1) := by simp
    _ = ∫ x in Set.Ioi t, Real.exp (-x) * 1 := setIntegral_expMeasure_one_Ioi ht _
    _ = Real.exp (-t) := by simpa only [mul_one] using integral_exp_neg_Ioi t

/-- The first exponential moment exists below its rate. -/
theorem integrable_exp_abs_expMeasure_one {θ : ℝ} (hθ : θ < 1) :
    Integrable (fun x : ℝ => Real.exp (θ * |x|)) (ProbabilityTheory.expMeasure 1) := by
  rw [integrable_expMeasure_one_iff]
  have h := integrableOn_exp_mul_Ioi (a := θ - 1) (by linarith) 0
  refine h.congr_fun ?_ measurableSet_Ioi
  intro x hx
  change Real.exp ((θ - 1) * x) = Real.exp (-x) * Real.exp (θ * |x|)
  rw [abs_of_pos hx, ← Real.exp_add]
  congr 1
  ring

/-- The mean of the unit exponential law. -/
theorem integral_id_expMeasure_one : ∫ x, x ∂(ProbabilityTheory.expMeasure 1) = 1 := by
  rw [integral_expMeasure_one]
  have h := Real.Gamma_eq_integral (s := 2) (by norm_num)
  norm_num at h
  exact h.symm

/-- The unit exponential law has an integrable identity function. -/
theorem integrable_id_expMeasure_one : Integrable (fun x : ℝ => x) (ProbabilityTheory.expMeasure 1) := by
  rw [integrable_expMeasure_one_iff]
  have h := Real.GammaIntegral_convergent (s := 2) (by norm_num)
  norm_num at h
  exact h

/-- Translating an integral over an upper half-line. -/
theorem integral_Ioi_translate (f : ℝ → ℝ) (t : ℝ) :
    ∫ x in Set.Ioi t, f x = ∫ x in Set.Ioi (0 : ℝ), f (x + t) := by
  rw [← integral_indicator measurableSet_Ioi, ← integral_indicator measurableSet_Ioi]
  rw [← integral_add_right_eq_self ((Set.Ioi t).indicator f) t]
  apply integral_congr_ae
  exact ae_of_all _ fun x => by
    by_cases hx : 0 < x
    · simp [Set.indicator_of_mem, hx]
    · simp [Set.indicator_of_notMem, hx]
end LatticeProb.ConvexOrder

namespace LatticeProb.ConvexOrder
open MeasureTheory ProbabilityTheory Set Real

/-- The first moment in the exponential upper tail. -/
theorem setIntegral_id_expMeasure_one_Ioi {t : ℝ} (ht : 0 ≤ t) :
    ∫ x in Set.Ioi t, x ∂(ProbabilityTheory.expMeasure 1) = (t + 1) * Real.exp (-t) := by
  rw [setIntegral_expMeasure_one_Ioi ht, integral_Ioi_translate]
  have hi : IntegrableOn (fun x : ℝ => Real.exp (-x) * x) (Set.Ioi 0) :=
    (integrable_expMeasure_one_iff _).mp integrable_id_expMeasure_one
  have he := integrableOn_exp_neg_Ioi (0 : ℝ)
  have heq : (fun x : ℝ => Real.exp (-(x + t)) * (x + t)) =
      fun x => Real.exp (-t) * (Real.exp (-x) * x) +
        (t * Real.exp (-t)) * Real.exp (-x) := by
    funext x
    rw [neg_add, Real.exp_add]
    ring
  rw [heq, integral_add (hi.const_mul _) (he.const_mul _),
    integral_const_mul, integral_const_mul,
    ← integral_expMeasure_one (fun x => x), integral_id_expMeasure_one,
    integral_exp_neg_Ioi_zero]
  ring

/-- An even convex function is minimized at zero. -/
theorem ConvexOn.even_zero_le {f : ℝ → ℝ} (hf : ConvexOn ℝ Set.univ f)
    (heven : ∀ x, f (-x) = f x) (x : ℝ) : f 0 ≤ f x := by
  have h := hf.2 (Set.mem_univ x) (Set.mem_univ (-x))
    (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num : (0 : ℝ) ≤ 1 / 2)
    (by norm_num : (1 / 2 : ℝ) + 1 / 2 = 1)
  simp only [smul_eq_mul, heven, show (1 / 2 : ℝ) * x + 1 / 2 * -x = 0 by ring] at h
  linarith
end LatticeProb.ConvexOrder

namespace LatticeProb.ConvexOrder
open MeasureTheory ProbabilityTheory Set Real

/-- Jensen on an exponential tail, with the complement bounded by the minimum. -/
theorem even_convex_exp_tail_le {f : ℝ → ℝ} (hf : ConvexOn ℝ Set.univ f)
    (hfc : Continuous f) (heven : ∀ x, f (-x) = f x) {t : ℝ} (ht : 0 ≤ t)
    (hfi : Integrable (fun x : ℝ => f ((t + 1)⁻¹ * x)) (ProbabilityTheory.expMeasure 1)) :
    Real.exp (-t) * f 1 + (1 - Real.exp (-t)) * f 0 ≤
      ∫ x, f ((t + 1)⁻¹ * x) ∂(ProbabilityTheory.expMeasure 1) := by
  let μ := ProbabilityTheory.expMeasure 1
  haveI : IsProbabilityMeasure μ := isProbabilityMeasure_expMeasure (by norm_num)
  have ht1 : t + 1 ≠ 0 := by linarith
  have hm : μ.real (Set.Ioi t) = Real.exp (-t) := expMeasure_one_Ioi_real ht
  have hm0 : μ (Set.Ioi t) ≠ 0 := by
    intro hz
    have : μ.real (Set.Ioi t) = 0 := by simp [measureReal_def, hz]
    rw [hm] at this
    exact (Real.exp_ne_zero _) this
  have hj := hf.map_set_average_le hfc.continuousOn isClosed_univ hm0 (measure_ne_top _ _)
    (ae_of_all _ fun _ => Set.mem_univ _)
    ((integrable_id_expMeasure_one.const_mul (t + 1)⁻¹).integrableOn (s := Set.Ioi t))
    (hfi.integrableOn (s := Set.Ioi t))
  have havg : (⨍ x in Set.Ioi t, (t + 1)⁻¹ * x ∂μ) = 1 := by
    rw [setAverage_eq, hm, integral_const_mul, setIntegral_id_expMeasure_one_Ioi ht]
    simp only [smul_eq_mul]
    field_simp
  rw [havg, setAverage_eq, hm, smul_eq_mul] at hj
  have hj' : Real.exp (-t) * f 1 ≤ ∫ x in Set.Ioi t, f ((t + 1)⁻¹ * x) ∂μ := by
    calc Real.exp (-t) * f 1 ≤ Real.exp (-t) *
        ((Real.exp (-t))⁻¹ * ∫ x in Set.Ioi t, f ((t + 1)⁻¹ * x) ∂μ) :=
          mul_le_mul_of_nonneg_left hj (Real.exp_pos _).le
      _ = _ := by field_simp
  have hmin : ∀ x : ℝ, f 0 ≤ f ((t + 1)⁻¹ * x) := fun x => ConvexOn.even_zero_le hf heven _
  have hrest := setIntegral_le_integral (s := Set.Ioi t) (hfi.sub (integrable_const (f 0)))
    (ae_of_all μ fun x => sub_nonneg.mpr (hmin x))
  change (∫ x in Set.Ioi t, f ((t + 1)⁻¹ * x) - f 0 ∂μ) ≤
    ∫ x, f ((t + 1)⁻¹ * x) - f 0 ∂μ at hrest
  rw [integral_sub hfi.integrableOn (integrable_const _), integral_sub hfi (integrable_const _),
    integral_const, integral_const, measureReal_restrict_apply_univ, hm] at hrest
  simp only [smul_eq_mul, probReal_univ, one_mul] at hrest
  linarith

/-- Symmetrization preserves convexity. -/
theorem convexOn_symmetrize {f : ℝ → ℝ} (hf : ConvexOn ℝ Set.univ f) :
    ConvexOn ℝ Set.univ (fun x => (f x + f (-x)) / 2) := by
  refine ⟨convex_univ, fun x _ y _ a b ha hb hab => ?_⟩
  have hp := hf.2 (Set.mem_univ x) (Set.mem_univ y) ha hb hab
  have hn := hf.2 (Set.mem_univ (-x)) (Set.mem_univ (-y)) ha hb hab
  change f (a * x + b * y) ≤ a * f x + b * f y at hp
  change f (a * -x + b * -y) ≤ a * f (-x) + b * f (-y) at hn
  rw [show a * -x + b * -y = -(a * x + b * y) by ring] at hn
  change (f (a * x + b * y) + f (-(a * x + b * y))) / 2 ≤
    a * ((f x + f (-x)) / 2) + b * ((f y + f (-y)) / 2)
  linarith

/-- The one-site convex comparison with a scaled symmetric exponential. -/
theorem convex_exp_tail_le {f : ℝ → ℝ} (hf : ConvexOn ℝ Set.univ f)
    (hfc : Continuous f) {t : ℝ} (ht : 0 ≤ t)
    (hfp : Integrable (fun x : ℝ => f ((t + 1)⁻¹ * x)) (ProbabilityTheory.expMeasure 1))
    (hfn : Integrable (fun x : ℝ => f (-((t + 1)⁻¹ * x))) (ProbabilityTheory.expMeasure 1)) :
    Real.exp (-t) / 2 * f 1 + Real.exp (-t) / 2 * f (-1) +
        (1 - Real.exp (-t)) * f 0 ≤
      (∫ x, f ((t + 1)⁻¹ * x) ∂(ProbabilityTheory.expMeasure 1)) / 2 +
        (∫ x, f (-((t + 1)⁻¹ * x)) ∂(ProbabilityTheory.expMeasure 1)) / 2 := by
  have h := even_convex_exp_tail_le (convexOn_symmetrize hf)
    ((hfc.add (hfc.comp continuous_neg)).div_const 2)
    (fun x => by simp [add_comm]) ht ((hfp.add hfn).div_const 2)
  simp only [neg_zero, add_self_div_two] at h
  rw [integral_div, integral_add hfp hfn] at h
  linarith
end LatticeProb.ConvexOrder
