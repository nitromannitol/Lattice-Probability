import LatticeProb.External.ChenKimKumagaiWang
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.Tactic

/-!
# Explicit Nash rates and inverse profiles

The logarithmic scale gives a decreasing time function and its reciprocal derivative rate.
Its positive inverse satisfies the exact CKKW tail identities, including positive rate scalings.
The explicit logarithmic comparison rate is increasing and comparable with this rate.
-/

namespace LatticeProb

open Set Filter MeasureTheory
open scoped Topology

noncomputable section

/-- The logarithmic time scale. -/
def nashScale (u : ℝ) : ℝ := u / (1 + Real.log (1 + u))

/-- The explicit derivative of the logarithmic time scale. -/
def nashScaleDeriv (u : ℝ) : ℝ :=
  (1 + Real.log (1 + u) - u / (1 + u)) / (1 + Real.log (1 + u)) ^ 2

/-- The decreasing time scale at dimension `d`. -/
def nashTime (d : ℕ) (r : ℝ) : ℝ := nashScale (r ^ (-(2 / (d : ℝ))))

/-- The reciprocal negative derivative rate. -/
def nashRate (d : ℕ) (r : ℝ) : ℝ :=
  ((d : ℝ) / 2) * r ^ (1 + 2 / (d : ℝ)) /
    nashScaleDeriv (r ^ (-(2 / (d : ℝ))))

/-- The logarithmic comparison rate. -/
def nashRateStar (d : ℕ) (r : ℝ) : ℝ :=
  r ^ (1 + 2 / (d : ℝ)) * (1 + Real.log (1 + r ^ (-(2 / (d : ℝ)))))

/-- The inverse of the time scale on the positive half-line. -/
def nashProfile (d : ℕ) (t : ℝ) : ℝ :=
  Function.invFunOn (nashTime d) (Ioi 0) t

/-- The logarithmic denominator is positive on the positive half-line. -/
theorem nashScale_denominator_pos {u : ℝ} (hu : 0 < u) :
    0 < 1 + Real.log (1 + u) := by
  have := Real.log_nonneg (show 1 ≤ 1 + u by linarith)
  linarith

/-- The logarithm dominates the rational term in the derivative. -/
theorem nashScale_log_lower {u : ℝ} (hu : 0 < u) :
    u / (1 + u) ≤ Real.log (1 + u) := by
  have h := Real.one_sub_inv_le_log_of_pos (show 0 < 1 + u by linarith)
  have heq : 1 - (1 + u)⁻¹ = u / (1 + u) := by
    field_simp
    ring
  rwa [heq] at h

/-- Differentiating the explicit scale gives its stated derivative. -/
theorem hasDerivAt_nashScale {u : ℝ} (hu : 0 < u) :
    HasDerivAt nashScale (nashScaleDeriv u) u := by
  have hlog := ((hasDerivAt_id u).const_add 1).log
    (show 1 + u ≠ 0 by linarith)
  convert! (hasDerivAt_id u).div (hlog.const_add 1)
    (ne_of_gt (nashScale_denominator_pos hu)) using 1
  simp only [nashScaleDeriv, one_mul, id_eq, div_eq_mul_inv]

/-- The scale derivative is strictly positive. -/
theorem nashScaleDeriv_pos {u : ℝ} (hu : 0 < u) : 0 < nashScaleDeriv u := by
  have h := nashScale_log_lower hu
  exact div_pos (by linarith) (sq_pos_of_pos (nashScale_denominator_pos hu))

/-- The scale is positive at every positive argument. -/
theorem nashScale_pos {u : ℝ} (hu : 0 < u) : 0 < nashScale u :=
  div_pos hu (nashScale_denominator_pos hu)

/-- The logarithmic scale is bounded above by its argument. -/
theorem nashScale_le {u : ℝ} (hu : 0 < u) : nashScale u ≤ u := by
  apply (div_le_iff₀ (nashScale_denominator_pos hu)).2
  have hlog := Real.log_nonneg (show 1 ≤ 1 + u by linarith)
  nlinarith

/-- The scale divided by its argument is the reciprocal logarithmic denominator. -/
theorem nashScale_div {u : ℝ} (hu : 0 < u) :
    nashScale u / u = (1 + Real.log (1 + u))⁻¹ := by
  unfold nashScale
  field_simp [hu.ne']

/-- The derivative is at most the scale divided by its argument. -/
theorem nashScaleDeriv_le {u : ℝ} (hu : 0 < u) :
    nashScaleDeriv u ≤ nashScale u / u := by
  rw [nashScale_div hu]
  have hden := nashScale_denominator_pos hu
  have hfrac : 0 ≤ u / (1 + u) := le_of_lt (div_pos hu (by linarith))
  unfold nashScaleDeriv
  apply (div_le_iff₀ (sq_pos_of_pos hden)).2
  have heq : (1 + Real.log (1 + u))⁻¹ *
      (1 + Real.log (1 + u)) ^ 2 = 1 + Real.log (1 + u) := by
    field_simp
  rw [heq]
  linarith

/-- The derivative is at least half the scale divided by its argument. -/
theorem nashScaleDeriv_lower {u : ℝ} (hu : 0 < u) :
    nashScale u / (2 * u) ≤ nashScaleDeriv u := by
  have hden := nashScale_denominator_pos hu
  have hlog := nashScale_log_lower hu
  have hlog' := (div_le_iff₀ (show 0 < 1 + u by linarith)).1 hlog
  have hlog0 := Real.log_nonneg (show 1 ≤ 1 + u by linarith)
  have hfrac : 2 * (u / (1 + u)) ≤ 1 + Real.log (1 + u) := by
    rw [← mul_div_assoc]
    apply (div_le_iff₀ (show 0 < 1 + u by linarith)).2
    nlinarith
  have heq : nashScale u / (2 * u) = (1 / 2 : ℝ) / (1 + Real.log (1 + u)) := by
    unfold nashScale
    field_simp [hu.ne', hden.ne']
  rw [heq]
  unfold nashScaleDeriv
  apply (le_div_iff₀ (sq_pos_of_pos hden)).2
  have heq' : (1 / 2 : ℝ) / (1 + Real.log (1 + u)) *
      (1 + Real.log (1 + u)) ^ 2 = (1 + Real.log (1 + u)) / 2 := by
    field_simp [hden.ne']
  rw [heq']
  linarith

/-- The time scale is positive on the positive half-line. -/
theorem nashTime_pos (d : ℕ) {r : ℝ} (hr : 0 < r) : 0 < nashTime d r :=
  nashScale_pos (Real.rpow_pos_of_pos hr _)

/-- The rate is positive in positive dimension. -/
theorem nashRate_pos {d : ℕ} (hd : 1 ≤ d) {r : ℝ} (hr : 0 < r) :
    0 < nashRate d r := by
  have hd' : 0 < (d : ℝ) := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hd)
  exact div_pos (mul_pos (div_pos hd' (by norm_num)) (Real.rpow_pos_of_pos hr _))
    (nashScaleDeriv_pos (Real.rpow_pos_of_pos hr _))

/-- The derivative of the time scale is the negative reciprocal rate. -/
theorem hasDerivAt_nashTime {d : ℕ} (_hd : 1 ≤ d) {r : ℝ} (hr : 0 < r) :
    HasDerivAt (nashTime d) (-(nashRate d r)⁻¹) r := by
  have hpow := Real.hasDerivAt_rpow_const (p := -(2 / (d : ℝ))) (Or.inl hr.ne')
  have hchain := (hasDerivAt_nashScale (u := r ^ (-(2 / (d : ℝ))))
    (Real.rpow_pos_of_pos hr _)).comp r hpow
  convert! hchain using 1
  unfold nashRate
  have he : -(2 / (d : ℝ)) - 1 = -(1 + 2 / (d : ℝ)) := by ring
  rw [he, Real.rpow_neg hr.le (1 + 2 / (d : ℝ))]
  simp only [mul_inv_rev, div_eq_mul_inv, inv_inv]
  ring

/-- The time scale is strictly decreasing on its positive domain. -/
theorem nashTime_strictAntiOn {d : ℕ} (hd : 1 ≤ d) :
    StrictAntiOn (nashTime d) (Ioi 0) := by
  apply strictAntiOn_of_deriv_neg (convex_Ioi 0)
  · intro r hr
    exact (hasDerivAt_nashTime hd hr).continuousAt.continuousWithinAt
  · intro r hr
    have hr' : 0 < r := by simpa only [interior_Ioi, mem_Ioi] using hr
    rw [(hasDerivAt_nashTime hd hr').deriv]
    exact neg_neg_of_pos (inv_pos.mpr (nashRate_pos hd hr'))

/-- The time scale tends to zero at infinity. -/
theorem tendsto_nashTime_atTop {d : ℕ} (hd : 1 ≤ d) :
    Tendsto (nashTime d) atTop (𝓝 0) := by
  have hd' : 0 < (d : ℝ) := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hd)
  have hpow := tendsto_rpow_neg_atTop (div_pos (by norm_num : (0 : ℝ) < 2) hd')
  have hscale : ContinuousAt nashScale 0 := by
    change ContinuousAt (fun u : ℝ ↦ u / (1 + Real.log (1 + u))) 0
    apply continuousAt_id.div
    · exact ((continuousAt_const.add continuousAt_id).log (by norm_num)).const_add 1
    · norm_num
  convert! hscale.tendsto.comp hpow using 1
  norm_num [nashScale]

/-- The logarithmic scale diverges at infinity. -/
theorem tendsto_nashScale_atTop : Tendsto nashScale atTop atTop := by
  have hlog : Tendsto (fun u : ℝ ↦ Real.log (1 + u) / u) atTop (𝓝 0) := by
    have h := (Real.tendsto_pow_log_div_mul_add_atTop 1 (-1) 1 one_ne_zero).comp
      (tendsto_atTop_add_const_left atTop 1 tendsto_id)
    simpa only [Function.comp_def, pow_one, one_mul, id_eq, ← sub_eq_add_neg,
      add_sub_cancel_left] using h
  have hratio : Tendsto (fun u : ℝ ↦ (1 + Real.log (1 + u)) / u) atTop (𝓝 0) := by
    simpa only [add_div, one_div, add_zero] using tendsto_inv_atTop_zero.add hlog
  have hpos : ∀ᶠ u : ℝ in atTop, 0 < (1 + Real.log (1 + u)) / u := by
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with u hu
    exact div_pos (nashScale_denominator_pos hu) hu
  have h := (tendsto_nhdsWithin_iff.mpr ⟨hratio, hpos⟩).inv_tendsto_nhdsGT_zero
  change Tendsto (fun u : ℝ ↦ ((1 + Real.log (1 + u)) / u)⁻¹) atTop atTop at h
  change Tendsto (fun u : ℝ ↦ u / (1 + Real.log (1 + u))) atTop atTop
  simpa only [inv_div] using h

/-- The time scale diverges when its positive argument tends to zero. -/
theorem tendsto_nashTime_zero {d : ℕ} (hd : 1 ≤ d) :
    Tendsto (nashTime d) (𝓝[>] 0) atTop := by
  have hd' : 0 < (d : ℝ) := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hd)
  exact tendsto_nashScale_atTop.comp
    (tendsto_rpow_neg_nhdsGT_zero (neg_neg_of_pos (div_pos (by norm_num) hd')))

/-- The time scale takes every positive value. -/
theorem nashTime_surjOn {d : ℕ} (hd : 1 ≤ d) :
    SurjOn (nashTime d) (Ioi 0) (Ioi 0) := by
  intro t ht
  have hsmall := (tendsto_nashTime_atTop hd).eventually (gt_mem_nhds ht)
  obtain ⟨b, hb, hbt⟩ := (hsmall.and (eventually_gt_atTop (0 : ℝ))).exists
  have hlarge := (tendsto_nashTime_zero hd).eventually (eventually_ge_atTop t)
  obtain ⟨a, hat, ha⟩ := (hlarge.and self_mem_nhdsWithin).exists
  have hc : ContinuousOn (nashTime d) (Ioi 0) := fun r hr ↦
    (hasDerivAt_nashTime hd hr).continuousAt.continuousWithinAt
  exact hc.surjOn_Icc hbt ha ⟨le_of_lt hb, hat⟩

/-- The inverse profile is positive at positive times. -/
theorem nashProfile_pos {d : ℕ} (hd : 1 ≤ d) {t : ℝ} (ht : 0 < t) :
    0 < nashProfile d t :=
  (nashTime_surjOn hd).mapsTo_invFunOn ht

/-- The time scale composed with its profile is the identity at positive times. -/
theorem nashTime_nashProfile {d : ℕ} (hd : 1 ≤ d) {t : ℝ} (ht : 0 < t) :
    nashTime d (nashProfile d t) = t :=
  (nashTime_surjOn hd).rightInvOn_invFunOn ht

/-- The profile composed with the time scale is the identity at positive arguments. -/
theorem nashProfile_nashTime {d : ℕ} (hd : 1 ≤ d) {r : ℝ} (hr : 0 < r) :
    nashProfile d (nashTime d r) = r :=
  (nashTime_strictAntiOn hd).injOn.leftInvOn_invFunOn hr

/-- The scaled reciprocal rate is integrable on every positive tail. -/
theorem integrableOn_inv_nashRate {d : ℕ} (hd : 1 ≤ d) {α r : ℝ}
    (hα : 0 < α) (hr : 0 < r) :
    IntegrableOn (fun s ↦ (α * nashRate d s)⁻¹) (Ioi r) := by
  have hderiv : ∀ s ∈ Ici r, HasDerivAt (fun s ↦ -nashTime d s / α)
      ((α * nashRate d s)⁻¹) s := by
    intro s hs
    convert! ((hasDerivAt_nashTime hd (lt_of_lt_of_le hr hs)).neg).div_const α using 1
    simp only [neg_neg, mul_inv_rev, div_eq_mul_inv]
  have hlim : Tendsto (fun s ↦ -nashTime d s / α) atTop (𝓝 0) := by
    simpa only [neg_zero, zero_div] using (tendsto_nashTime_atTop hd).neg.div_const α
  exact integrableOn_Ioi_deriv_of_nonneg' hderiv
    (fun s hs ↦ le_of_lt (inv_pos.mpr (mul_pos hα (nashRate_pos hd (hr.trans hs))))) hlim

/-- The scaled rate has the exact finite tail prescribed by the time scale. -/
theorem ckkwTail_mul_nashRate {d : ℕ} (hd : 1 ≤ d) {α r : ℝ}
    (hα : 0 < α) (hr : 0 < r) :
    External.ckkwTail (fun s ↦ α * nashRate d s) r =
      ENNReal.ofReal (nashTime d r / α) := by
  have hderiv : ∀ s ∈ Ici r, HasDerivAt (fun s ↦ -nashTime d s / α)
      ((α * nashRate d s)⁻¹) s := by
    intro s hs
    convert! ((hasDerivAt_nashTime hd (lt_of_lt_of_le hr hs)).neg).div_const α using 1
    simp only [neg_neg, mul_inv_rev, div_eq_mul_inv]
  have hlim : Tendsto (fun s ↦ -nashTime d s / α) atTop (𝓝 0) := by
    simpa only [neg_zero, zero_div] using (tendsto_nashTime_atTop hd).neg.div_const α
  have hint := integrableOn_inv_nashRate hd hα hr
  have heq := integral_Ioi_of_hasDerivAt_of_tendsto' hderiv hint hlim
  have hnonneg : 0 ≤ᵐ[volume.restrict (Ioi r)] fun s ↦ (α * nashRate d s)⁻¹ := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
    exact le_of_lt (inv_pos.mpr (mul_pos hα (nashRate_pos hd (hr.trans hs))))
  rw [External.ckkwTail, ← ofReal_integral_eq_lintegral_ofReal hint hnonneg, heq]
  congr 1
  ring

/-- The unscaled rate has tail exactly equal to the explicit time scale. -/
theorem ckkwTail_nashRate {d : ℕ} (hd : 1 ≤ d) {r : ℝ} (hr : 0 < r) :
    External.ckkwTail (nashRate d) r = ENNReal.ofReal (nashTime d r) := by
  simpa only [one_mul, div_one] using ckkwTail_mul_nashRate hd zero_lt_one hr

/-- Scaling the rate scales the time argument of its two-sided inverse profile. -/
theorem ckkwInverseProfile_nashRate {d : ℕ} (hd : 1 ≤ d) {α : ℝ} (hα : 0 < α) :
    External.ckkwInverseProfile (fun r ↦ α * nashRate d r)
      (fun t ↦ nashProfile d (α * t)) := by
  refine ⟨?_, ?_, ?_⟩
  · intro r hr
    refine ⟨mul_pos hα (nashRate_pos hd hr), ?_⟩
    rw [ckkwTail_mul_nashRate hd hα hr]
    exact ENNReal.ofReal_ne_top
  · intro t ht
    have hp := nashProfile_pos hd (mul_pos hα ht)
    refine ⟨hp, ?_⟩
    rw [ckkwTail_mul_nashRate hd hα hp,
      ENNReal.toReal_ofReal (le_of_lt (div_pos (nashTime_pos d hp) hα)),
      nashTime_nashProfile hd (mul_pos hα ht)]
    exact mul_div_cancel_left₀ t hα.ne'
  · intro r hr
    dsimp only
    rw [ckkwTail_mul_nashRate hd hα hr,
      ENNReal.toReal_ofReal (le_of_lt (div_pos (nashTime_pos d hr) hα)),
      mul_div_cancel₀ _ hα.ne']
    exact nashProfile_nashTime hd hr

/-- The comparison rate is argument divided by the time scale. -/
theorem nashRateStar_eq_div (d : ℕ) {r : ℝ} (hr : 0 < r) :
    nashRateStar d r = r / nashTime d r := by
  unfold nashRateStar nashTime nashScale
  rw [Real.rpow_add hr, Real.rpow_one, Real.rpow_neg hr.le]
  field_simp

/-- The comparison rate is strictly positive. -/
theorem nashRateStar_pos (d : ℕ) {r : ℝ} (hr : 0 < r) :
    0 < nashRateStar d r := by
  rw [nashRateStar_eq_div d hr]
  exact div_pos hr (nashTime_pos d hr)

/-- The comparison rate divided by its argument is reciprocal time. -/
theorem nashRateStar_div (d : ℕ) {r : ℝ} (hr : 0 < r) :
    nashRateStar d r / r = (nashTime d r)⁻¹ := by
  rw [nashRateStar_eq_div d hr]
  field_simp

/-- The rate-to-argument ratio is increasing on positive arguments. -/
theorem nashRateStar_div_monotoneOn {d : ℕ} (hd : 1 ≤ d) :
    MonotoneOn (fun r ↦ nashRateStar d r / r) (Ioi 0) := by
  intro r hr s hs hrs
  dsimp only
  rw [nashRateStar_div d hr, nashRateStar_div d hs]
  exact (inv_le_inv₀ (nashTime_pos d hr) (nashTime_pos d hs)).2
    ((nashTime_strictAntiOn hd).antitoneOn hr hs hrs)

/-- The comparison rate is increasing on positive arguments. -/
theorem nashRateStar_monotoneOn {d : ℕ} (hd : 1 ≤ d) :
    MonotoneOn (nashRateStar d) (Ioi 0) := by
  intro r hr s hs hrs
  rw [nashRateStar_eq_div d hr, nashRateStar_eq_div d hs]
  exact div_le_div₀ hs.le hrs (nashTime_pos d hs)
    ((nashTime_strictAntiOn hd).antitoneOn hr hs hrs)

/-- Reciprocal bounds convert derivative comparisons into rate comparisons. -/
private theorem rate_div_bounds {a p L D : ℝ} (ha : 0 ≤ a) (hp : 0 ≤ p)
    (hL : 0 < L) (hD : 0 < D) (hlo : (1 / 2 : ℝ) / L ≤ D)
    (hhi : D ≤ L⁻¹) : a * (p * L) ≤ a * p / D ∧ a * p / D ≤ 2 * a * (p * L) := by
  have hhi' : D * L ≤ 1 := by
    simpa only [one_div] using (le_div_iff₀ hL).1 (by simpa only [one_div] using hhi)
  have hlo' : (1 / 2 : ℝ) ≤ D * L := (div_le_iff₀ hL).1 hlo
  have hap : 0 ≤ a * p := mul_nonneg ha hp
  constructor
  · apply (le_div_iff₀ hD).2
    nlinarith [mul_nonneg hap (sub_nonneg.mpr hhi')]
  · apply (div_le_iff₀ hD).2
    nlinarith [mul_nonneg hap (sub_nonneg.mpr hlo')]

/-- The explicit rate lies between the dimension multiples of the comparison rate. -/
theorem nashRate_comparison {d : ℕ} (hd : 1 ≤ d) {r : ℝ} (hr : 0 < r) :
    (d : ℝ) / 2 * nashRateStar d r ≤ nashRate d r ∧
      nashRate d r ≤ (d : ℝ) * nashRateStar d r := by
  have hu := Real.rpow_pos_of_pos hr (-(2 / (d : ℝ)))
  have hd' : 0 < (d : ℝ) := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hd)
  have hlo := nashScaleDeriv_lower hu
  have hhi := nashScaleDeriv_le hu
  rw [nashScale_div hu] at hhi
  have heq : nashScale (r ^ (-(2 / (d : ℝ)))) /
      (2 * r ^ (-(2 / (d : ℝ)))) =
      (1 / 2 : ℝ) / (1 + Real.log (1 + r ^ (-(2 / (d : ℝ))))) := by
    unfold nashScale
    field_simp
  rw [heq] at hlo
  have h := rate_div_bounds (a := (d : ℝ) / 2)
    (le_of_lt (div_pos hd' (by norm_num)))
    (Real.rpow_nonneg hr.le (1 + 2 / (d : ℝ)))
    (nashScale_denominator_pos hu) (nashScaleDeriv_pos hu) hlo hhi
  unfold nashRate nashRateStar
  constructor
  · exact h.1
  · convert h.2 using 1
    ring

/-- The standard comparison constant controls the explicit rate on both sides. -/
theorem nashRate_comparison_max {d : ℕ} (hd : 1 ≤ d) {r : ℝ} (hr : 0 < r) :
    (max 2 (d : ℝ))⁻¹ * nashRateStar d r ≤ nashRate d r ∧
      nashRate d r ≤ max 2 (d : ℝ) * nashRateStar d r := by
  have hd' : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hstar := (nashRateStar_pos d hr).le
  have hinv : (max 2 (d : ℝ))⁻¹ ≤ (d : ℝ) / 2 := by
    have hmax : (0 : ℝ) < max 2 (d : ℝ) := lt_of_lt_of_le (by norm_num) (le_max_left _ _)
    have hhalf := (inv_le_inv₀ hmax (by norm_num : (0 : ℝ) < 2)).2
      (le_max_left 2 (d : ℝ))
    norm_num at hhalf
    linarith
  obtain ⟨hlo, hhi⟩ := nashRate_comparison hd hr
  exact ⟨(mul_le_mul_of_nonneg_right hinv hstar).trans hlo,
    hhi.trans (mul_le_mul_of_nonneg_right (le_max_right _ _) hstar)⟩

/-- The comparison bounds persist when both rates are multiplied by a positive scalar. -/
theorem nashRate_scaled_comparison {d : ℕ} (hd : 1 ≤ d) {α r : ℝ}
    (hα : 0 < α) (hr : 0 < r) :
    (max 2 (d : ℝ))⁻¹ * (α * nashRateStar d r) ≤ α * nashRate d r ∧
      α * nashRate d r ≤ max 2 (d : ℝ) * (α * nashRateStar d r) := by
  obtain ⟨hlo, hhi⟩ := nashRate_comparison_max hd hr
  constructor
  · simpa only [mul_left_comm α] using mul_le_mul_of_nonneg_left hlo hα.le
  · simpa only [mul_left_comm α] using mul_le_mul_of_nonneg_left hhi hα.le

/-- A positive multiple of the comparison rate is positive. -/
theorem nashRateStar_scaled_pos (d : ℕ) {α r : ℝ} (hα : 0 < α) (hr : 0 < r) :
    0 < α * nashRateStar d r :=
  mul_pos hα (nashRateStar_pos d hr)

/-- A positive multiple of the comparison rate is increasing. -/
theorem nashRateStar_scaled_monotoneOn {d : ℕ} (hd : 1 ≤ d) {α : ℝ} (hα : 0 < α) :
    MonotoneOn (fun r ↦ α * nashRateStar d r) (Ioi 0) := by
  intro r hr s hs hrs
  exact mul_le_mul_of_nonneg_left (nashRateStar_monotoneOn hd hr hs hrs) hα.le

/-- The ratio of a positive scaled comparison rate to its argument is increasing. -/
theorem nashRateStar_scaled_div_monotoneOn {d : ℕ} (hd : 1 ≤ d) {α : ℝ}
    (hα : 0 < α) :
    MonotoneOn (fun r ↦ (α * nashRateStar d r) / r) (Ioi 0) := by
  intro r hr s hs hrs
  dsimp only
  rw [mul_div_assoc, mul_div_assoc]
  exact mul_le_mul_of_nonneg_left (nashRateStar_div_monotoneOn hd hr hs hrs) hα.le

/-- At argument one the time scale is explicitly positive in every dimension. -/
theorem nashTime_one (d : ℕ) : nashTime d 1 = 1 / (1 + Real.log 2) := by
  simp only [nashTime, Real.one_rpow, nashScale, one_add_one_eq_two]

/-- The one-dimensional inverse profile returns one at its explicit positive time. -/
theorem nashProfile_one_time : nashProfile 1 (1 / (1 + Real.log 2)) = 1 := by
  rw [← nashTime_one 1]
  exact nashProfile_nashTime (by norm_num) zero_lt_one

/-- The unscaled one-dimensional functions satisfy the actual CKKW inverse condition. -/
theorem ckkwInverseProfile_nashRate_one :
    External.ckkwInverseProfile (nashRate 1) (nashProfile 1) := by
  simpa only [one_mul] using
    (ckkwInverseProfile_nashRate (d := 1) (by norm_num) (α := 1) zero_lt_one)

/-- The logarithmic time factor is strictly increasing at positive times. -/
theorem nash_log_time_strictMonoOn :
    StrictMonoOn (fun t : ℝ ↦ t * (1 + Real.log (1 + t))) (Ioi 0) := by
  intro t ht u hu htu
  change 0 < t at ht
  change 0 < u at hu
  have hlog := Real.log_le_log (by linarith : 0 < 1 + t) (by linarith : 1 + t ≤ 1 + u)
  exact (mul_lt_mul_of_pos_right htu (nashScale_denominator_pos ht)).trans_le
    (mul_le_mul_of_nonneg_left (by linarith) hu.le)

/-- The critical logarithmic profile is antitone on positive times. -/
theorem nash_critical_antitoneOn (d : ℕ) :
    AntitoneOn (fun t : ℝ ↦
      (t * (1 + Real.log (1 + t))) ^ (-((d : ℝ) / 2))) (Ioi 0) := by
  intro t ht u hu htu
  exact Real.rpow_le_rpow_of_nonpos
    (mul_pos ht (nashScale_denominator_pos ht))
    (nash_log_time_strictMonoOn.monotoneOn ht hu htu)
    (neg_nonpos.mpr (div_nonneg (Nat.cast_nonneg d) (by norm_num)))

/-- Dilation improves the critical profile by at least its power decay. -/
theorem nash_critical_dilation (d : ℕ) {s t : ℝ} (hs : 1 ≤ s) (ht : 0 < t) :
    (s * t * (1 + Real.log (1 + s * t))) ^ (-((d : ℝ) / 2)) ≤
      s ^ (-((d : ℝ) / 2)) *
        (t * (1 + Real.log (1 + t))) ^ (-((d : ℝ) / 2)) := by
  have hs0 : 0 < s := lt_of_lt_of_le zero_lt_one hs
  have hst : t ≤ s * t := by nlinarith
  have hlog := Real.log_le_log (by linarith : 0 < 1 + t)
    (by linarith : 1 + t ≤ 1 + s * t)
  rw [← Real.mul_rpow hs0.le (mul_pos ht (nashScale_denominator_pos ht)).le]
  apply Real.rpow_le_rpow_of_nonpos
    (mul_pos hs0 (mul_pos ht (nashScale_denominator_pos ht))) _
    (neg_nonpos.mpr (div_nonneg (Nat.cast_nonneg d) (by norm_num)))
  nlinarith [mul_nonneg (mul_pos hs0 ht).le (sub_nonneg.mpr hlog)]

/-- The logarithm of one plus a nonnegative argument is bounded by twice its square root. -/
theorem nash_log_le_two_sqrt {u : ℝ} (hu : 0 ≤ u) :
    Real.log (1 + u) ≤ 2 * Real.sqrt u := by
  have hs := Real.sqrt_nonneg u
  have hs2 := Real.sq_sqrt hu
  have hlog := Real.log_le_log (by positivity : 0 < 1 + u)
    (show 1 + u ≤ (1 + Real.sqrt u) ^ 2 by nlinarith)
  rw [Real.log_pow] at hlog
  norm_num only [Nat.cast_ofNat] at hlog
  have h := Real.log_le_sub_one_of_pos (show 0 < 1 + Real.sqrt u by positivity)
  linarith

/-- The logarithm is at most half its positive argument. -/
private theorem log_le_half {x : ℝ} (hx : 0 < x) : Real.log x ≤ x / 2 := by
  have h := Real.log_le_sub_one_of_pos (div_pos hx (by norm_num : (0 : ℝ) < 2))
  rw [Real.log_div hx.ne' (by norm_num)] at h
  have htwo := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
  linarith

/-- Inverting the logarithmic scale changes its logarithmic factor by at most four. -/
theorem nashScale_log_comparison {u : ℝ} (hu : 0 < u) :
    1 + Real.log (1 + u) ≤ 4 * (1 + Real.log (1 + nashScale u)) := by
  have hL := nashScale_denominator_pos hu
  have ht := nashScale_pos hu
  have hL1 : 1 ≤ 1 + Real.log (1 + u) := by
    have := Real.log_nonneg (show 1 ≤ 1 + u by linarith)
    linarith
  have heq : nashScale u * (1 + Real.log (1 + u)) = u :=
    div_mul_cancel₀ u hL.ne'
  have hlog := Real.log_le_log (by linarith : 0 < 1 + u)
    (show 1 + u ≤ (1 + nashScale u) * (1 + Real.log (1 + u)) by nlinarith)
  rw [Real.log_mul (by positivity) hL.ne'] at hlog
  have hh := log_le_half hL
  have hnonneg := Real.log_nonneg (show 1 ≤ 1 + nashScale u by linarith)
  linarith

/-- The negative dimension power cancels the reciprocal dimension power. -/
theorem nash_rpow_cancel {d : ℕ} (hd : 1 ≤ d) {r : ℝ} (hr : 0 < r) :
    (r ^ (-(2 / (d : ℝ)))) ^ (-((d : ℝ) / 2)) = r := by
  have hd0 : (d : ℝ) ≠ 0 := by exact_mod_cast (show d ≠ 0 by omega)
  rw [← Real.rpow_mul hr.le]
  have he : -(2 / (d : ℝ)) * -((d : ℝ) / 2) = 1 := by field_simp
  rw [he, Real.rpow_one]

/-- The inverse Nash profile has the explicit two-sided critical-profile comparison. -/
theorem nashProfile_comparison {d : ℕ} (hd : 1 ≤ d) {t : ℝ} (ht : 0 < t) :
    (2 : ℝ) ^ (-(d : ℝ)) *
        (t * (1 + Real.log (1 + t))) ^ (-((d : ℝ) / 2)) ≤ nashProfile d t ∧
      nashProfile d t ≤
        (t * (1 + Real.log (1 + t))) ^ (-((d : ℝ) / 2)) := by
  let r := nashProfile d t
  let u := r ^ (-(2 / (d : ℝ)))
  have hr : 0 < r := nashProfile_pos hd ht
  have hu : 0 < u := Real.rpow_pos_of_pos hr _
  have htime : nashScale u = t := nashTime_nashProfile hd ht
  have htu : t ≤ u := htime ▸ nashScale_le hu
  have heq : u = t * (1 + Real.log (1 + u)) := by
    rw [← htime]
    exact (div_mul_cancel₀ u (nashScale_denominator_pos hu).ne').symm
  have hlog := Real.log_le_log (by linarith : 0 < 1 + t)
    (by linarith : 1 + t ≤ 1 + u)
  have hlo : t * (1 + Real.log (1 + t)) ≤ u := by
    calc
      t * (1 + Real.log (1 + t)) ≤ t * (1 + Real.log (1 + u)) := by
        gcongr
      _ = u := heq.symm
  have hhi : u ≤ 4 * (t * (1 + Real.log (1 + t))) := by
    have h := nashScale_log_comparison hu
    rw [htime] at h
    calc
      u = t * (1 + Real.log (1 + u)) := heq
      _ ≤ t * (4 * (1 + Real.log (1 + t))) := mul_le_mul_of_nonneg_left h ht.le
      _ = _ := by ring
  have hpow : u ^ (-((d : ℝ) / 2)) = r := nash_rpow_cancel hd hr
  have hbase := mul_pos ht (nashScale_denominator_pos ht)
  constructor
  · have h := Real.rpow_le_rpow_of_nonpos hu hhi
      (show -((d : ℝ) / 2) ≤ 0 from
        neg_nonpos.mpr (div_nonneg (Nat.cast_nonneg d) (by norm_num)))
    rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 4) hbase.le, hpow] at h
    have hfour : (4 : ℝ) ^ (-((d : ℝ) / 2)) = (2 : ℝ) ^ (-(d : ℝ)) := by
      rw [show (4 : ℝ) = 2 ^ (2 : ℝ) by norm_num, ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
      congr 1
      ring
    rwa [hfour] at h
  · change r ≤ _
    rw [← hpow]
    exact Real.rpow_le_rpow_of_nonpos hbase hlo
      (neg_nonpos.mpr (div_nonneg (Nat.cast_nonneg d) (by norm_num)))

/-- The prescribed dilation makes the logarithmic Nash quotient at least the dimension. -/
theorem nash_critical_log_quotient {d : ℕ} (hd : 1 ≤ d) {K r : ℝ}
    (hK : 1 ≤ K) (hr : 0 < r) :
    (d : ℝ) ≤ Real.log (r / (K *
      ((4 * Real.exp 2 * K ^ (2 / (d : ℝ))) * nashTime d r *
        (1 + Real.log (1 + (4 * Real.exp 2 * K ^ (2 / (d : ℝ))) *
          nashTime d r))) ^ (-((d : ℝ) / 2)))) := by
  let s := 4 * Real.exp 2 * K ^ (2 / (d : ℝ))
  let t := nashTime d r
  let p := (s * t * (1 + Real.log (1 + s * t))) ^ (-((d : ℝ) / 2))
  have hd0 : (d : ℝ) ≠ 0 := by exact_mod_cast (show d ≠ 0 by omega)
  have hK0 : 0 < K := lt_of_lt_of_le zero_lt_one hK
  have ht : 0 < t := nashTime_pos d hr
  have hs : 1 ≤ s := by
    have hexp := Real.add_one_le_exp (2 : ℝ)
    have hpow := Real.one_le_rpow hK (show 0 ≤ 2 / (d : ℝ) by positivity)
    dsimp only [s]
    nlinarith
  have hs0 : 0 < s := lt_of_lt_of_le zero_lt_one hs
  have hp : 0 < p := Real.rpow_pos_of_pos
    (mul_pos (mul_pos hs0 ht) (nashScale_denominator_pos (mul_pos hs0 ht))) _
  have hcomp := (nashProfile_comparison hd ht).1
  rw [nashProfile_nashTime hd hr] at hcomp
  have hcritical : (t * (1 + Real.log (1 + t))) ^ (-((d : ℝ) / 2)) ≤
      (2 : ℝ) ^ (d : ℝ) * r := by
    have htwo : (0 : ℝ) < 2 ^ (-(d : ℝ)) := Real.rpow_pos_of_pos (by norm_num) _
    have h : (t * (1 + Real.log (1 + t))) ^ (-((d : ℝ) / 2)) ≤
        r / (2 : ℝ) ^ (-(d : ℝ)) :=
      (le_div_iff₀ htwo).2 (by simpa only [mul_comm] using hcomp)
    simpa only [div_eq_mul_inv, Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2),
      inv_inv, mul_comm] using h
  have hbound : p ≤ s ^ (-((d : ℝ) / 2)) * ((2 : ℝ) ^ (d : ℝ) * r) :=
    (nash_critical_dilation d hs ht).trans
      (mul_le_mul_of_nonneg_left hcritical (Real.rpow_nonneg hs0.le _))
  have hlog := Real.log_le_log hp hbound
  rw [Real.log_mul (Real.rpow_pos_of_pos hs0 _).ne'
      (mul_pos (Real.rpow_pos_of_pos (by norm_num) _) hr).ne',
    Real.log_rpow hs0,
    Real.log_mul (Real.rpow_pos_of_pos (by norm_num : (0 : ℝ) < 2) _).ne' hr.ne',
    Real.log_rpow (by norm_num : (0 : ℝ) < 2)] at hlog
  have hslog : Real.log s = 2 * Real.log 2 + 2 +
      (2 / (d : ℝ)) * Real.log K := by
    dsimp only [s]
    rw [Real.log_mul (mul_pos (by norm_num) (Real.exp_pos _)).ne'
      (Real.rpow_pos_of_pos hK0 _).ne',
      Real.log_mul (by norm_num) (Real.exp_pos _).ne', Real.log_exp,
      Real.log_rpow hK0]
    have hfour : Real.log 4 = 2 * Real.log 2 := by
      simpa only [show (2 : ℝ) ^ (2 : ℕ) = 4 by norm_num, Nat.cast_ofNat] using
        Real.log_pow 2 2
    rw [hfour]
  have hid : Real.log r - (Real.log K +
      (-((d : ℝ) / 2) * Real.log s + ((d : ℝ) * Real.log 2 + Real.log r))) = d := by
    rw [hslog]
    field_simp [hd0]
    ring
  change (d : ℝ) ≤ Real.log (r / (K * p))
  rw [Real.log_div hr.ne' (mul_pos hK0 hp).ne', Real.log_mul hK0.ne' hp.ne']
  linarith

/-- The scaled explicit rate is dominated by the literal CKKW supremum Nash profile. -/
theorem nashRate_le_ckkwNashProfile {d : ℕ} (hd : 1 ≤ d) {K r : ℝ}
    (hK : 1 ≤ K) (hr : 0 < r) :
    ENNReal.ofReal ((4 * Real.exp 2 * K ^ (2 / (d : ℝ)))⁻¹ * nashRate d r) ≤
      External.ckkwNashProfile (fun t ↦ K *
        (t * (1 + Real.log (1 + t))) ^ (-((d : ℝ) / 2))) r := by
  let s := 4 * Real.exp 2 * K ^ (2 / (d : ℝ))
  have hK0 : 0 < K := lt_of_lt_of_le zero_lt_one hK
  have hs : 0 < s := mul_pos (mul_pos (by norm_num) (Real.exp_pos _))
    (Real.rpow_pos_of_pos hK0 _)
  have ht := nashTime_pos d hr
  unfold External.ckkwNashProfile
  apply le_iSup_of_le (⟨s * nashTime d r, mul_pos hs ht⟩ : Ioi (0 : ℝ))
  apply ENNReal.ofReal_le_ofReal
  have hrate := (nashRate_comparison hd hr).2
  rw [nashRateStar_eq_div d hr] at hrate
  have hlog := nash_critical_log_quotient hd hK hr
  calc
    s⁻¹ * nashRate d r ≤ s⁻¹ * ((d : ℝ) * (r / nashTime d r)) :=
      mul_le_mul_of_nonneg_left hrate (inv_pos.mpr hs).le
    _ = r / (s * nashTime d r) * (d : ℝ) := by
      simp only [div_eq_mul_inv, mul_inv_rev]
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hlog (div_pos hr (mul_pos hs ht)).le

/-- At dimension, heat prefactor, and argument one, the dominated rate is strictly positive. -/
theorem nashRate_le_ckkwNashProfile_one :
    0 < ENNReal.ofReal ((4 * Real.exp 2)⁻¹ * nashRate 1 1) ∧
      ENNReal.ofReal ((4 * Real.exp 2)⁻¹ * nashRate 1 1) ≤
        External.ckkwNashProfile (fun t ↦
          (t * (1 + Real.log (1 + t))) ^ (-(1 / 2 : ℝ))) 1 := by
  constructor
  · exact ENNReal.ofReal_pos.mpr
      (mul_pos (inv_pos.mpr (mul_pos (by norm_num) (Real.exp_pos _)))
        (nashRate_pos (by norm_num) zero_lt_one))
  · simpa only [Nat.cast_one, div_one, Real.one_rpow, mul_one, one_mul] using
      (nashRate_le_ckkwNashProfile (d := 1) (by norm_num) (K := 1) (r := 1)
        le_rfl zero_lt_one)

end

end LatticeProb
