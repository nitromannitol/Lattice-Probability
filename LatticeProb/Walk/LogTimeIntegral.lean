import Mathlib

/-!
# The planar logarithm as a time integral

In the plane the Gaussian part of the potential kernel is
`π⁻¹ ∫_1^∞ (1 - e^{-r²/t}) t⁻¹ dt`, and this module proves that the integral is
`2 log r + κ + O(r^{-2})` for a constant `κ` (`exists_integral_log_integrand`). The
substitution `t = r²/u` turns it into `∫_0^{r²} (1 - e^{-u}) u⁻¹ du`, whose difference from
`log r²` converges with an exponentially small tail.
-/

open MeasureTheory Filter Topology

noncomputable section

namespace LatticeProb.ContinuousTime

/-- The planar Gaussian integrand `(1 - e^{-r²/t})/t` is integrable on `(1, ∞)`. -/
theorem integrableOn_log_integrand (r : ℝ) :
    IntegrableOn (fun t : ℝ => (1 - Real.exp (-r ^ 2 / t)) / t) (Set.Ioi 1) := by
  rw [IntegrableOn]
  apply Integrable.mono' (g := fun t => r ^ 2 * t ^ (-2 : ℝ))
  · exact (integrableOn_Ioi_rpow_of_lt (by norm_num) zero_lt_one).const_mul (r ^ 2)
  · exact ContinuousOn.aestronglyMeasurable (by
      apply ContinuousOn.div
      · apply ContinuousOn.sub
        · exact continuousOn_const
        · apply Real.continuous_exp.comp_continuousOn
          apply ContinuousOn.div
          · exact continuousOn_const
          · exact continuousOn_id
          · intro t ht
            exact ne_of_gt (lt_trans zero_lt_one ht)
      · exact continuousOn_id
      · intro t ht
        exact ne_of_gt (lt_trans zero_lt_one ht)) measurableSet_Ioi
  · exact ae_restrict_of_forall_mem measurableSet_Ioi (fun t ht => by
      have htpos : 0 < t := lt_trans zero_lt_one ht
      have hnonneg : 0 ≤ 1 - Real.exp (-r ^ 2 / t) := by
        have hle : -r ^ 2 / t ≤ 0 := by
          apply div_nonpos_of_nonpos_of_nonneg
          · nlinarith [sq_nonneg r]
          · exact htpos.le
        linarith [Real.exp_le_one_iff.mpr hle]
      have hub : 1 - Real.exp (-r ^ 2 / t) ≤ r ^ 2 / t := by
        have h := Real.one_sub_le_exp_neg (r ^ 2 / t)
        rw [← neg_div] at h
        linarith
      have hrpow : t ^ (-2 : ℝ) = 1 / t ^ 2 := by
        rw [show (-2 : ℝ) = -(2 : ℝ) by norm_num, Real.rpow_neg htpos.le,
          Real.rpow_two, one_div]
      rw [Real.norm_eq_abs, abs_div, abs_of_pos htpos, abs_of_nonneg hnonneg, hrpow]
      rw [div_le_iff₀ htpos]
      have hmul : r ^ 2 * (1 / t ^ 2) * t = r ^ 2 / t := by
        field_simp
      rw [hmul]
      exact hub)

/-- The function `u ↦ e^{-u}/u` is integrable on `(1, ∞)`. -/
private lemma integrableOn_exp_neg_div_Ioi :
    IntegrableOn (fun u : ℝ => Real.exp (-u) / u) (Set.Ioi 1) := by
  rw [IntegrableOn]
  apply Integrable.mono' (g := fun u : ℝ => Real.exp (-u))
  · exact integrableOn_exp_neg_Ioi 1
  · exact ContinuousOn.aestronglyMeasurable (by
      apply ContinuousOn.div
      · exact Real.continuous_exp.comp_continuousOn (by fun_prop)
      · exact continuousOn_id
      · intro u hu
        exact ne_of_gt (lt_trans zero_lt_one hu)) measurableSet_Ioi
  · exact ae_restrict_of_forall_mem measurableSet_Ioi (fun u hu => by
      have hupos : 0 < u := lt_trans zero_lt_one hu
      rw [Real.norm_eq_abs, abs_div, abs_of_pos hupos,
        abs_of_nonneg (Real.exp_pos _).le, div_le_iff₀ hupos]
      calc Real.exp (-u) = Real.exp (-u) * 1 := by ring
        _ ≤ Real.exp (-u) * u :=
            mul_le_mul_of_nonneg_left (le_of_lt hu) (Real.exp_pos _).le)

/-- The function `u ↦ (1 - e^{-u})/u` is interval integrable on `[0, 1]`. -/
private lemma intervalIntegrable_one_sub_exp_neg_div :
    IntervalIntegrable (fun u : ℝ => (1 - Real.exp (-u)) / u) volume 0 1 := by
  rw [intervalIntegrable_iff, Set.uIoc_of_le zero_le_one]
  apply IntegrableOn.of_bound (by simp)
  · exact ContinuousOn.aestronglyMeasurable (by
      apply ContinuousOn.div
      · apply ContinuousOn.sub
        · exact continuousOn_const
        · exact Real.continuous_exp.comp_continuousOn continuousOn_id.neg
      · exact continuousOn_id
      · intro u hu
        exact ne_of_gt hu.1) measurableSet_Ioc
  · exact ae_restrict_of_forall_mem measurableSet_Ioc (fun u hu => by
      have hupos : 0 < u := hu.1
      have he1 : Real.exp (-u) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith [hupos.le])
      have hnum : 0 ≤ 1 - Real.exp (-u) := by linarith
      have hle : 1 - Real.exp (-u) ≤ u := by linarith [Real.one_sub_le_exp_neg u]
      rw [Real.norm_eq_abs, abs_div, abs_of_pos hupos, abs_of_nonneg hnum]
      calc (1 - Real.exp (-u)) / u ≤ u / u :=
            div_le_div_of_nonneg_right hle hupos.le
        _ = 1 := by field_simp)

/-- The substitution `t = r²/u` rewrites the log integrand over `(1, ∞)` as an integral
over `(0, 1)`. -/
private lemma integral_log_integrand_eq_intervalIntegral (r : ℝ) :
    (∫ t in Set.Ioi 1, (1 - Real.exp (-r ^ 2 / t)) / t)
      = ∫ u in (0:ℝ)..1, (1 - Real.exp (-r ^ 2 * u)) / u := by
  let F : ℝ → ℝ := fun u => (1 - Real.exp (-r ^ 2 * u)) / u
  let g : ℝ → ℝ := (Set.Ioo (0:ℝ) 1).indicator F
  have h := integral_comp_rpow_Ioi g (p := -1) (by norm_num : (-1:ℝ) ≠ 0)
  have hLHS : (∫ x in Set.Ioi 0, (|-1| * x ^ ((-1:ℝ) - 1)) • g (x ^ (-1:ℝ)))
      = ∫ x in Set.Ioi 1, (1 - Real.exp (-r ^ 2 / x)) / x := by
    have hpoint : ∀ x ∈ Set.Ioi (0:ℝ),
        (|-1| * x ^ ((-1:ℝ) - 1)) • g (x ^ (-1:ℝ))
          = (Set.Ioi (1:ℝ)).indicator (fun x => (1 - Real.exp (-r ^ 2 / x)) / x) x := by
      intro x hx
      have hxpos : 0 < x := hx
      have hrpow : x ^ ((-1:ℝ) - 1) = (x ^ 2)⁻¹ := by
        rw [show (-1:ℝ) - 1 = -2 by norm_num, Real.rpow_neg (le_of_lt hxpos) 2,
          Real.rpow_two]
      rw [smul_eq_mul, show |(-1:ℝ)| = 1 by norm_num, one_mul, hrpow,
        Real.rpow_neg_one]
      dsimp only [g]
      by_cases hx1 : 1 < x
      · have hmem : x⁻¹ ∈ Set.Ioo (0:ℝ) 1 :=
          ⟨inv_pos.mpr hxpos, inv_lt_one_of_one_lt₀ hx1⟩
        rw [Set.indicator_of_mem hmem (fun u => (1 - Real.exp (-r ^ 2 * u)) / u),
          Set.indicator_of_mem (show x ∈ Set.Ioi (1:ℝ) from hx1) _]
        field_simp
      · have hmem : x⁻¹ ∉ Set.Ioo (0:ℝ) 1 := by
          intro hmem
          have h1 : (1:ℝ) ≤ x⁻¹ := (one_le_inv₀ hxpos).mpr (not_lt.mp hx1)
          linarith [hmem.2]
        rw [Set.indicator_of_notMem hmem _,
          Set.indicator_of_notMem (show x ∉ Set.Ioi (1:ℝ) from hx1) _]
        ring
    calc ∫ x in Set.Ioi 0, (|-1| * x ^ ((-1:ℝ) - 1)) • g (x ^ (-1:ℝ))
        = ∫ x in Set.Ioi 0,
            (Set.Ioi (1:ℝ)).indicator (fun x => (1 - Real.exp (-r ^ 2 / x)) / x) x :=
          setIntegral_congr_fun measurableSet_Ioi hpoint
      _ = ∫ x in Set.Ioi 0 ∩ Set.Ioi 1, (fun x => (1 - Real.exp (-r ^ 2 / x)) / x) x := by
          rw [setIntegral_indicator measurableSet_Ioi]
      _ = ∫ x in Set.Ioi 1, (1 - Real.exp (-r ^ 2 / x)) / x := by
          rw [Set.inter_eq_right.mpr (Set.Ioi_subset_Ioi (by norm_num : (0:ℝ) ≤ 1))]
  have hRHS : (∫ y in Set.Ioi 0, g y) = ∫ u in (0:ℝ)..1, F u := by
    calc ∫ y in Set.Ioi 0, g y
        = ∫ y in Set.Ioi 0 ∩ Set.Ioo (0:ℝ) 1, F y := by
          rw [setIntegral_indicator measurableSet_Ioo]
      _ = ∫ y in Set.Ioo (0:ℝ) 1, F y := by
          rw [Set.inter_eq_right.mpr (Set.Ioo_subset_Ioi_self)]
      _ = ∫ y in Set.Ioc (0:ℝ) 1, F y := (integral_Ioc_eq_integral_Ioo).symm
      _ = ∫ u in (0:ℝ)..1, F u := (intervalIntegral.integral_of_le zero_le_one).symm
  calc (∫ t in Set.Ioi 1, (1 - Real.exp (-r ^ 2 / t)) / t)
      = ∫ x in Set.Ioi 0, (|-1| * x ^ ((-1:ℝ) - 1)) • g (x ^ (-1:ℝ)) := hLHS.symm
    _ = ∫ y in Set.Ioi 0, g y := h
    _ = ∫ u in (0:ℝ)..1, (1 - Real.exp (-r ^ 2 * u)) / u := hRHS

/-- Scaling `u ↦ r² u` rewrites `∫₀¹ (1 - e^{-r²u})/u` as `∫₀^{r²} (1 - e^{-u})/u`. -/
private lemma intervalIntegral_log_integrand_scale (r : ℝ) (hr : 0 < r) :
    (∫ u in (0:ℝ)..1, (1 - Real.exp (-r ^ 2 * u)) / u)
      = ∫ u in (0:ℝ)..r ^ 2, (1 - Real.exp (-u)) / u := by
  have hK : (∫ u in (0:ℝ)..1, (1 - Real.exp (-r ^ 2 * u)) / u)
      = ∫ u in (0:ℝ)..1, r ^ 2 * ((1 - Real.exp (-(r ^ 2 * u))) / (r ^ 2 * u)) := by
    apply intervalIntegral.integral_congr
    intro u _
    by_cases hu : u = 0
    · subst hu
      simp
    · field_simp
  rw [hK, intervalIntegral.integral_const_mul]
  have hcomp := intervalIntegral.integral_comp_mul_left
    (f := fun y : ℝ => (1 - Real.exp (-y)) / y) (a := 0) (b := 1) (c := r ^ 2)
    (by positivity : r ^ 2 ≠ 0)
  rw [hcomp, mul_zero, mul_one, smul_eq_mul, ← mul_assoc,
    mul_inv_cancel₀ (by positivity : r ^ 2 ≠ 0), one_mul]

/-- The planar logarithm: `∫_1^∞ (1 - e^{-r²/t})/t dt = 2 log r + κ + O(r^{-2})`, by the
substitution `t = r²/u`. -/
theorem exists_integral_log_integrand :
    ∃ κ C : ℝ, ∀ r : ℝ, 1 ≤ r →
      |(∫ t in Set.Ioi 1, (1 - Real.exp (-r ^ 2 / t)) / t) - (2 * Real.log r + κ)|
        ≤ C * r ^ (-2 : ℝ) := by
  let K : ℝ → ℝ := fun u => (1 - Real.exp (-u)) / u
  refine ⟨(∫ u in (0:ℝ)..1, K u) - (∫ u in Set.Ioi 1, Real.exp (-u) / u), 1, ?_⟩
  intro r hr
  have hrpos : 0 < r := lt_of_lt_of_le zero_lt_one hr
  have hr2 : (1:ℝ) ≤ r ^ 2 := by nlinarith
  have hInt1r : IntervalIntegrable K volume 1 (r ^ 2) := by
    apply ContinuousOn.intervalIntegrable
    dsimp only [K]
    apply ContinuousOn.div
    · apply ContinuousOn.sub
      · exact continuousOn_const
      · exact Real.continuous_exp.comp_continuousOn continuousOn_id.neg
    · exact continuousOn_id
    · intro u hu
      rw [Set.uIcc_of_le hr2] at hu
      exact ne_of_gt (lt_of_lt_of_le zero_lt_one hu.1)
  have hsplit : (∫ u in (0:ℝ)..r ^ 2, K u)
      = (∫ u in (0:ℝ)..1, K u) + ∫ u in (1:ℝ)..r ^ 2, K u :=
    (intervalIntegral.integral_add_adjacent_intervals
      intervalIntegrable_one_sub_exp_neg_div hInt1r).symm
  have hInt_inv : IntervalIntegrable (fun u : ℝ => 1 / u) volume 1 (r ^ 2) := by
    apply ContinuousOn.intervalIntegrable
    apply ContinuousOn.div
    · exact continuousOn_const
    · exact continuousOn_id
    · intro u hu
      rw [Set.uIcc_of_le hr2] at hu
      exact ne_of_gt (lt_of_lt_of_le zero_lt_one hu.1)
  have hInt_exp : IntervalIntegrable (fun u : ℝ => Real.exp (-u) / u) volume 1 (r ^ 2) := by
    apply ContinuousOn.intervalIntegrable
    apply ContinuousOn.div
    · exact Real.continuous_exp.comp_continuousOn continuousOn_id.neg
    · exact continuousOn_id
    · intro u hu
      rw [Set.uIcc_of_le hr2] at hu
      exact ne_of_gt (lt_of_lt_of_le zero_lt_one hu.1)
  have hKsub : (∫ u in (1:ℝ)..r ^ 2, K u)
      = (∫ u in (1:ℝ)..r ^ 2, 1 / u)
        - ∫ u in (1:ℝ)..r ^ 2, Real.exp (-u) / u := by
    rw [← intervalIntegral.integral_sub hInt_inv hInt_exp]
    apply intervalIntegral.integral_congr
    intro u hu
    rw [Set.uIcc_of_le hr2] at hu
    have hupos : 0 < u := lt_of_lt_of_le zero_lt_one hu.1
    dsimp only [K]
    field_simp
  have hloginv : (∫ u in (1:ℝ)..r ^ 2, 1 / u) = 2 * Real.log r := by
    have h1 : (∫ u in (1:ℝ)..r ^ 2, 1 / u) = ∫ u in (1:ℝ)..r ^ 2, u⁻¹ := by
      apply intervalIntegral.integral_congr
      intro u _
      rw [one_div]
    rw [h1, integral_inv_of_pos zero_lt_one (by positivity : (0:ℝ) < r ^ 2), div_one,
      Real.log_pow]
    norm_num
  have hI1E : (∫ u in (1:ℝ)..r ^ 2, Real.exp (-u) / u)
      = (∫ u in Set.Ioi 1, Real.exp (-u) / u)
        - ∫ u in Set.Ioi (r ^ 2), Real.exp (-u) / u :=
    (intervalIntegral.integral_Ioi_sub_Ioi integrableOn_exp_neg_div_Ioi hr2).symm
  have hidentity : (∫ t in Set.Ioi 1, (1 - Real.exp (-r ^ 2 / t)) / t)
      = (∫ u in (0:ℝ)..1, K u) + 2 * Real.log r
        - (∫ u in Set.Ioi 1, Real.exp (-u) / u)
        + (∫ u in Set.Ioi (r ^ 2), Real.exp (-u) / u) := by
    rw [integral_log_integrand_eq_intervalIntegral r,
      intervalIntegral_log_integrand_scale r hrpos, hsplit, hKsub, hloginv, hI1E]
    ring
  have hE_nonneg : 0 ≤ ∫ u in Set.Ioi (r ^ 2), Real.exp (-u) / u := by
    apply setIntegral_nonneg measurableSet_Ioi
    intro u hu
    exact div_nonneg (Real.exp_pos _).le
      (le_of_lt (lt_trans (by positivity : (0:ℝ) < r ^ 2) hu))
  have hE_le : (∫ u in Set.Ioi (r ^ 2), Real.exp (-u) / u) ≤ r ^ (-2 : ℝ) := by
    have hmono : (∫ u in Set.Ioi (r ^ 2), Real.exp (-u) / u)
        ≤ Real.exp (-(r ^ 2)) := by
      have h := setIntegral_mono_on
        (integrableOn_exp_neg_div_Ioi.mono_set (Set.Ioi_subset_Ioi hr2))
        (integrableOn_exp_neg_Ioi (r ^ 2)) measurableSet_Ioi (fun u hu => by
          have hu1 : (1:ℝ) ≤ u := le_trans hr2 (le_of_lt hu)
          have hupos : 0 < u := lt_of_lt_of_le zero_lt_one hu1
          rw [div_le_iff₀ hupos]
          calc Real.exp (-u) = Real.exp (-u) * 1 := by ring
            _ ≤ Real.exp (-u) * u :=
                mul_le_mul_of_nonneg_left hu1 (Real.exp_pos _).le)
      rwa [integral_exp_neg_Ioi] at h
    have hexp : Real.exp (-(r ^ 2)) ≤ r ^ (-2 : ℝ) := by
      rw [show r ^ (-2 : ℝ) = (r ^ 2)⁻¹ by
            rw [show (-2 : ℝ) = -(2 : ℝ) by norm_num, Real.rpow_neg hrpos.le,
              Real.rpow_two]]
      rw [Real.exp_neg]
      exact (inv_le_inv₀ (Real.exp_pos (r ^ 2)) (by positivity : (0:ℝ) < r ^ 2)).mpr
        (by linarith [Real.add_one_le_exp (r ^ 2)])
    exact hmono.trans hexp
  rw [hidentity]
  have hsimp : (∫ u in (0:ℝ)..1, K u) + 2 * Real.log r
        - (∫ u in Set.Ioi 1, Real.exp (-u) / u)
        + (∫ u in Set.Ioi (r ^ 2), Real.exp (-u) / u)
        - (2 * Real.log r + ((∫ u in (0:ℝ)..1, K u)
            - ∫ u in Set.Ioi 1, Real.exp (-u) / u))
      = ∫ u in Set.Ioi (r ^ 2), Real.exp (-u) / u := by ring
  rw [hsimp, abs_of_nonneg hE_nonneg, one_mul]
  exact hE_le

end LatticeProb.ContinuousTime
