import LatticeProb.Prob.FreedmanEventwise
import LatticeProb.Prob.BernsteinLayerCake
import LatticeProb.Prob.BernsteinCrossTerm

/-!
# Bounded-difference moment estimates

Numerical estimates for the good-λ argument for bounded martingale differences.
-/

open MeasureTheory

namespace LatticeProb

/-- At the large levels used in the good-λ argument, the Freedman exponent is at most `-2p`. -/
theorem bernstein_goodLambda_exponent_le {p a L : ℝ} (hp : 2 ≤ p) (ha : 0 < a)
    (hL : 8 * p * a ≤ L) :
    -((L - a) ^ 2) /
      (2 * ((1 / (8 * Real.sqrt p)) ^ 2 * L ^ 2 + a * (L - a) / 3)) ≤ -2 * p := by
  have hp0 : 0 < p := by linarith
  have hs : 0 < Real.sqrt p := Real.sqrt_pos.2 hp0
  have hs2 : (Real.sqrt p) ^ 2 = p := Real.sq_sqrt (le_of_lt hp0)
  have hL0 : 0 < L := by nlinarith
  have haL : a ≤ L / 2 := by nlinarith
  have hdelta : (1 / (8 * Real.sqrt p)) ^ 2 = 1 / (64 * p) := by
    field_simp
    nlinarith
  rw [hdelta]
  have hdiff : 0 < L - a := by linarith
  have hden : 0 < 2 * (1 / (64 * p) * L ^ 2 + a * (L - a) / 3) := by positivity
  apply (div_le_iff₀ hden).2
  have hpa : p * a ≤ L / 8 := by nlinarith
  have hmul : p * a * L ≤ L ^ 2 / 8 := by nlinarith [mul_nonneg (sub_nonneg.mpr hpa) (le_of_lt hL0)]
  field_simp
  nlinarith [sq_nonneg (L - 2 * a)]

/-- The coefficient in the integrated good-λ inequality can be absorbed. -/
theorem bernstein_goodLambda_absorption {p : ℝ} (hp : 2 ≤ p) :
    (2 : ℝ) ^ p * (2 * Real.exp (-2 * p)) < 1 / 2 := by
  have hlog : Real.log 2 ≤ 1 := by
    have h := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 2 by norm_num)
    linarith
  have hexp : Real.exp (-2) < 1 / 4 := by
    have he : (2 : ℝ) < Real.exp 1 := Real.exp_one_gt_two
    have he2 : (4 : ℝ) < Real.exp 2 := by
      rw [show (2 : ℝ) = 1 + 1 by norm_num, Real.exp_add]
      nlinarith
    rw [Real.exp_neg]
    simpa only [one_div] using one_div_lt_one_div_of_lt (by norm_num : (0 : ℝ) < 4) he2
  have harg : Real.log 2 * p + -2 * p ≤ -2 := by
    nlinarith [mul_nonneg (show 0 ≤ p by linarith) (sub_nonneg.mpr hlog)]
  have h := Real.exp_le_exp.mpr harg
  calc
    (2 : ℝ) ^ p * (2 * Real.exp (-2 * p)) =
        2 * Real.exp (Real.log 2 * p + -2 * p) := by
          rw [Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 2), Real.exp_add]
          ring
    _ < 1 / 2 := by nlinarith

/-- A root bound for the absorbed moment inequality. -/
theorem bernstein_absorbed_moment_root {p A B C : ℝ} (hp : 2 ≤ p)
    (hA : 0 ≤ A) (hB : 0 ≤ B) (hC : 0 ≤ C)
    (h : A ≤ 2 * (B ^ p + C ^ p)) :
    A ^ (1 / p) ≤ 2 * (B + C) := by
  have hp0 : 0 < p := by linarith
  have hpow : 0 ≤ B ^ p + C ^ p := by positivity
  have hroot : (2 : ℝ) ^ (1 / p) ≤ 2 := by
    have hle : 1 / p ≤ 1 := (div_le_one hp0).2 (by linarith)
    simpa using Real.rpow_le_rpow_of_exponent_le (show (1 : ℝ) ≤ 2 by norm_num) hle
  calc
    A ^ (1 / p) ≤ (2 * (B ^ p + C ^ p)) ^ (1 / p) :=
      Real.rpow_le_rpow hA h (by positivity)
    _ = (2 : ℝ) ^ (1 / p) * (B ^ p + C ^ p) ^ (1 / p) :=
      Real.mul_rpow (by norm_num) hpow
    _ ≤ 2 * (B + C) := by
      have hsum := Real.rpow_add_rpow_le_add hB hC (show (1 : ℝ) ≤ p by linarith)
      exact mul_le_mul hroot hsum (Real.rpow_nonneg hpow _) (by norm_num)

/-- Absorbing the good-λ coefficient yields the explicit moment constant. -/
theorem bernstein_goodLambda_moment_root {p a A D : ℝ} (hp : 2 ≤ p)
    (ha : 0 ≤ a) (hA : 0 ≤ A) (hD : 0 ≤ D)
    (h : (1 - (2 : ℝ) ^ p * (2 * Real.exp (-2 * p))) * A ≤
      (16 * p * a) ^ p + (16 * Real.sqrt p) ^ p * D) :
    A ^ (1 / p) ≤ 32 * (Real.sqrt p * D ^ (1 / p) + p * a) := by
  have hp0 : 0 < p := by linarith
  have hq := bernstein_goodLambda_absorption hp
  have hB : 0 ≤ 16 * p * a := by positivity
  have hC : 0 ≤ 16 * Real.sqrt p * D ^ (1 / p) := by positivity
  have heq : (16 * Real.sqrt p * D ^ (1 / p)) ^ p =
      (16 * Real.sqrt p) ^ p * D := by
    rw [Real.mul_rpow (by positivity) (by positivity), ← Real.rpow_mul hD]
    rw [show 1 / p * p = 1 by field_simp, Real.rpow_one]
  have h' : A ≤ 2 * ((16 * p * a) ^ p + (16 * Real.sqrt p * D ^ (1 / p)) ^ p) := by
    rw [heq]
    nlinarith
  have hroot := bernstein_absorbed_moment_root hp hA hB hC h'
  nlinarith

/-- The layer-cake identity with strict superlevel sets. -/
theorem integral_rpow_eq_integral_meas_lt {Ω : Type*} {m : MeasurableSpace Ω}
    {μ : @Measure Ω m} {M : Ω → ℝ} {p : ℝ} (hp : 0 < p)
    (hMnn : 0 ≤ᵐ[μ] M) (hMint : Integrable (fun ω => M ω ^ p) μ) :
    ∫ ω, M ω ^ p ∂μ =
      ∫ t in Set.Ioi 0, p * t ^ (p - 1) * (μ {ω | t < M ω}).toReal := by
  rw [integral_rpow_eq_integral_meas_le hp hMnn hMint]
  apply integral_congr_ae
  filter_upwards [meas_le_ae_eq_meas_lt μ (volume.restrict (Set.Ioi 0)) M] with t ht
  rw [ht]

/-- Weighted strict tails of a bounded random variable are integrable. -/
theorem integrableOn_rpow_strictTail_of_bounded {Ω : Type*} {m : MeasurableSpace Ω}
    (μ : @Measure Ω m) [IsProbabilityMeasure μ] (M : Ω → ℝ) {p K : ℝ}
    (hp : 2 ≤ p) (hM : ∀ ω, M ω ≤ K) :
    IntegrableOn (fun t : ℝ => p * t ^ (p - 1) * μ.real {ω | t < M ω}) (Set.Ioi 0) := by
  have hp0 : 0 ≤ p := by linarith
  have hpm : 0 ≤ p - 1 := by linarith
  let g : ℝ → ℝ := fun t => p * t ^ (p - 1) * μ.real {ω | t < M ω}
  have hg : Measurable g := by
    have htail : Measurable (fun t : ℝ => μ.real {ω | t < M ω}) := by
      unfold Measure.real
      exact (show Antitone (fun t : ℝ => μ {ω | t < M ω}) from
        fun _ _ hst => measure_mono (fun _ h => lt_of_le_of_lt hst h)).measurable.ennreal_toReal
    exact (measurable_const.mul (Real.continuous_rpow_const hpm).measurable).mul htail
  let c : ℝ := p * K ^ (p - 1)
  have hind : Integrable ((Set.Ioc (0 : ℝ) K).indicator (fun _ : ℝ => c)) :=
    (integrableOn_const (by simp) : IntegrableOn (fun _ : ℝ => c) (Set.Ioc 0 K)).integrable_indicator measurableSet_Ioc
  apply hind.integrableOn.mono' hg.aestronglyMeasurable
  filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with t ht
  have ht0 : 0 < t := ht
  by_cases htK : t ≤ K
  · have hpow : t ^ (p - 1) ≤ K ^ (p - 1) :=
      Real.rpow_le_rpow (le_of_lt ht0) htK hpm
    have htprob : μ.real {ω | t < M ω} ≤ 1 := measureReal_le_one
    have htprob0 : 0 ≤ μ.real {ω | t < M ω} := measureReal_nonneg
    have hweight : 0 ≤ p * t ^ (p - 1) := mul_nonneg hp0 (Real.rpow_nonneg (le_of_lt ht0) _)
    simp only [g, Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hweight htprob0),
      Set.indicator_of_mem (show t ∈ Set.Ioc (0 : ℝ) K from ⟨ht0, htK⟩)]
    dsimp [c]
    nlinarith
  · have hz : {ω | t < M ω} = ∅ := by
      ext ω
      simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
      exact not_lt_of_ge (le_trans (hM ω) (le_of_not_ge htK))
    have hnot : t ∉ Set.Ioc (0 : ℝ) K := fun ht => htK ht.2
    simp [g, hz, Set.indicator_of_notMem hnot]

/-- Weighted tails remain integrable after a positive rescaling. -/
theorem integrableOn_rpow_scaledTail_of_bounded {Ω : Type*} {m : MeasurableSpace Ω}
    (μ : @Measure Ω m) [IsProbabilityMeasure μ] (M : Ω → ℝ) {p K b : ℝ}
    (hp : 2 ≤ p) (hM : ∀ ω, M ω ≤ K) (hb : 0 < b) :
    IntegrableOn (fun t : ℝ => p * t ^ (p - 1) * μ.real {ω | b * t < M ω})
      (Set.Ioi 0) := by
  have hint := integrableOn_rpow_strictTail_of_bounded μ (fun ω => M ω / b) hp
    (fun ω => div_le_div_of_nonneg_right (hM ω) (le_of_lt hb))
  apply hint.congr_fun
  · intro t _
    have hset : {ω | t < M ω / b} = {ω | b * t < M ω} := by
      ext ω
      change (t < M ω / b) ↔ b * t < M ω
      rw [lt_div_iff₀ hb, mul_comm]
    dsimp only
    rw [hset]
  · exact measurableSet_Ioi

/-- Integral of the layer-cake weight below a positive cutoff. -/
theorem integral_rpow_cutoff {p L : ℝ} (hp : 2 ≤ p) (hL : 0 ≤ L) :
    (∫ t in Set.Ioi 0, (Set.Ioc (0 : ℝ) L).indicator
      (fun t => p * t ^ (p - 1)) t) = L ^ p := by
  rw [setIntegral_indicator measurableSet_Ioc, Set.inter_eq_right.mpr Set.Ioc_subset_Ioi_self,
    ← intervalIntegral.integral_of_le hL, intervalIntegral.integral_const_mul,
    integral_rpow (Or.inl (by linarith : (-1 : ℝ) < p - 1))]
  have hp0 : p ≠ 0 := by linarith
  simp only [sub_add_cancel, Real.zero_rpow hp0, sub_zero]
  field_simp

/-- Scaling the argument of a strict tail in the layer-cake integral. -/
theorem integral_rpow_tail_scale {Ω : Type*} {m : MeasurableSpace Ω}
    (μ : @Measure Ω m) (M : Ω → ℝ) (p : ℝ) {b : ℝ} (hb : 0 < b) :
    (∫ t in Set.Ioi 0, p * t ^ (p - 1) * μ.real {ω | b * t < M ω}) =
      (∫ t in Set.Ioi 0, p * t ^ (p - 1) * μ.real {ω | t < M ω}) / b ^ p := by
  have hbpow : 0 < b ^ p := Real.rpow_pos_of_pos hb _
  apply (eq_div_iff (ne_of_gt hbpow)).2
  have hpoint : ∀ t ∈ Set.Ioi (0 : ℝ),
      b ^ p * (p * t ^ (p - 1) * μ.real {ω | b * t < M ω}) =
        b * (p * (b * t) ^ (p - 1) * μ.real {ω | b * t < M ω}) := by
    intro t ht
    rw [Real.mul_rpow (le_of_lt hb) (le_of_lt ht), Real.rpow_sub_one (ne_of_gt hb)]
    field_simp
  calc
    (∫ t in Set.Ioi 0, p * t ^ (p - 1) * μ.real {ω | b * t < M ω}) * b ^ p =
        ∫ t in Set.Ioi 0, b ^ p * (p * t ^ (p - 1) * μ.real {ω | b * t < M ω}) := by
          rw [integral_const_mul]
          ring
    _ = ∫ t in Set.Ioi 0, b * (p * (b * t) ^ (p - 1) * μ.real {ω | b * t < M ω}) :=
      setIntegral_congr_fun measurableSet_Ioi hpoint
    _ = ∫ t in Set.Ioi 0, p * t ^ (p - 1) * μ.real {ω | t < M ω} := by
      rw [integral_const_mul]
      simpa only [mul_zero, smul_eq_mul] using
        integral_comp_mul_left_Ioi' (fun t : ℝ => p * t ^ (p - 1) * μ.real {ω | t < M ω}) 0 hb

/-- Integrating a good-λ estimate for bounded nonnegative random variables. -/
theorem goodLambda_integrated {Ω : Type*} {m : MeasurableSpace Ω}
    (μ : @Measure Ω m) [IsProbabilityMeasure μ] (X Y : Ω → ℝ)
    {p L d q KX KY : ℝ} (hp : 2 ≤ p) (hL : 0 ≤ L) (hd : 0 < d) (hq : 0 ≤ q)
    (hXbound : ∀ ω, X ω ≤ KX) (hYbound : ∀ ω, Y ω ≤ KY)
    (hXnn : 0 ≤ᵐ[μ] X) (hYnn : 0 ≤ᵐ[μ] Y)
    (hXint : Integrable (fun ω => X ω ^ p) μ)
    (hYint : Integrable (fun ω => Y ω ^ p) μ)
    (htail : ∀ t : ℝ, L < t →
      μ.real {ω | 2 * t < X ω} ≤ μ.real {ω | d * t < Y ω} + q * μ.real {ω | t < X ω}) :
    (∫ ω, X ω ^ p ∂μ) / (2 : ℝ) ^ p ≤
      L ^ p + (∫ ω, Y ω ^ p ∂μ) / d ^ p + q * (∫ ω, X ω ^ p ∂μ) := by
  let weight : ℝ → ℝ := fun t => p * t ^ (p - 1)
  let cutoff : ℝ → ℝ := (Set.Ioc 0 L).indicator weight
  let fx : ℝ → ℝ := fun t => weight t * μ.real {ω | 2 * t < X ω}
  let fy : ℝ → ℝ := fun t => weight t * μ.real {ω | d * t < Y ω}
  let fz : ℝ → ℝ := fun t => weight t * μ.real {ω | t < X ω}
  have hp0 : 0 < p := by linarith
  have hpm : 0 ≤ p - 1 := by linarith
  have hweight : Continuous weight := continuous_const.mul (Real.continuous_rpow_const hpm)
  have hcut : IntegrableOn cutoff (Set.Ioi 0) := by
    have hi : IntegrableOn weight (Set.Ioc 0 L) :=
      (hweight.locallyIntegrable.integrableOn_isCompact isCompact_Icc).mono_set Set.Ioc_subset_Icc_self
    exact (hi.integrable_indicator measurableSet_Ioc).integrableOn
  have hfx : IntegrableOn fx (Set.Ioi 0) :=
    integrableOn_rpow_scaledTail_of_bounded μ X hp hXbound (by norm_num : (0 : ℝ) < 2)
  have hfy : IntegrableOn fy (Set.Ioi 0) :=
    integrableOn_rpow_scaledTail_of_bounded μ Y hp hYbound hd
  have hfz : IntegrableOn fz (Set.Ioi 0) :=
    integrableOn_rpow_strictTail_of_bounded μ X hp hXbound
  have hpoint : ∀ᵐ t ∂volume.restrict (Set.Ioi 0), fx t ≤ cutoff t + (fy t + q * fz t) := by
    filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with t ht
    have hw : 0 ≤ weight t := mul_nonneg (le_of_lt hp0) (Real.rpow_nonneg (le_of_lt ht) _)
    have hx0 : 0 ≤ μ.real {ω | 2 * t < X ω} := measureReal_nonneg
    have hy0 : 0 ≤ μ.real {ω | d * t < Y ω} := measureReal_nonneg
    have hz0 : 0 ≤ μ.real {ω | t < X ω} := measureReal_nonneg
    by_cases htL : t ≤ L
    · have hprob : μ.real {ω | 2 * t < X ω} ≤ 1 := measureReal_le_one
      simp only [cutoff, Set.indicator_of_mem (show t ∈ Set.Ioc 0 L from ⟨ht, htL⟩)]
      dsimp only [fx, fy, fz]
      nlinarith [mul_nonneg hw hy0, mul_nonneg (mul_nonneg hq hw) hz0]
    · have h := mul_le_mul_of_nonneg_left (htail t (lt_of_not_ge htL)) hw
      simp only [cutoff, Set.indicator_of_notMem
        (show t ∉ Set.Ioc (0 : ℝ) L from fun ht' => htL ht'.2), zero_add]
      dsimp only [fx, fy, fz]
      nlinarith
  have h := integral_mono_ae hfx (hcut.add (hfy.add (hfz.const_mul q))) hpoint
  change (∫ t in Set.Ioi 0, fx t) ≤
    ∫ t in Set.Ioi 0, cutoff t + (fy t + q * fz t) at h
  rw [integral_add (f := cutoff) (g := fun t => fy t + q * fz t) hcut
      (hfy.add (hfz.const_mul q)),
    integral_add (f := fy) (g := fun t => q * fz t) hfy (hfz.const_mul q),
    integral_const_mul] at h
  have hc : (∫ t in Set.Ioi 0, cutoff t) = L ^ p := integral_rpow_cutoff hp hL
  have hx : (∫ t in Set.Ioi 0, fx t) = (∫ ω, X ω ^ p ∂μ) / (2 : ℝ) ^ p := by
    rw [integral_rpow_tail_scale μ X p (by norm_num : (0 : ℝ) < 2)]
    congr 1
    exact (integral_rpow_eq_integral_meas_lt hp0 hXnn hXint).symm
  have hy : (∫ t in Set.Ioi 0, fy t) = (∫ ω, Y ω ^ p ∂μ) / d ^ p := by
    rw [integral_rpow_tail_scale μ Y p hd]
    congr 1
    exact (integral_rpow_eq_integral_meas_lt hp0 hYnn hYint).symm
  have hz : (∫ t in Set.Ioi 0, fz t) = (∫ ω, X ω ^ p ∂μ) :=
    (integral_rpow_eq_integral_meas_lt hp0 hXnn hXint).symm
  rw [hc, hx, hy, hz] at h
  simpa only [add_assoc] using h

/-- Positive moments of a bounded nonnegative measurable function are integrable. -/
theorem integrable_rpow_of_bounded_nonneg {Ω : Type*} {m : MeasurableSpace Ω}
    (μ : @Measure Ω m) [IsProbabilityMeasure μ] (W : Ω → ℝ) {p K : ℝ}
    (hp : 0 ≤ p) (hW : Measurable W) (hW0 : ∀ ω, 0 ≤ W ω)
    (hWK : ∀ ω, W ω ≤ K) : Integrable (fun ω => W ω ^ p) μ := by
  refine Integrable.of_bound ((Real.continuous_rpow_const hp).measurable.comp hW).aestronglyMeasurable
    (K ^ p) (Filter.Eventually.of_forall ?_)
  intro ω
  rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (hW0 ω) p)]
  exact Real.rpow_le_rpow (hW0 ω) (hWK ω) hp

/-- The integrated good-λ estimate gives the numerical bounded-moment inequality. -/
theorem goodLambda_moment_bound {Ω : Type*} {m : MeasurableSpace Ω}
    (μ : @Measure Ω m) [IsProbabilityMeasure μ] (X Y : Ω → ℝ)
    {p a KX KY : ℝ} (hp : 2 ≤ p) (ha : 0 < a)
    (hX : Measurable X) (hY : Measurable Y)
    (hX0 : ∀ ω, 0 ≤ X ω) (hY0 : ∀ ω, 0 ≤ Y ω)
    (hXbound : ∀ ω, X ω ≤ KX) (hYbound : ∀ ω, Y ω ≤ KY)
    (htail : ∀ t : ℝ, 8 * p * a < t →
      μ.real {ω | 2 * t < X ω} ≤ μ.real {ω | (1 / (8 * Real.sqrt p)) * t < Y ω} +
        (2 * Real.exp (-2 * p)) * μ.real {ω | t < X ω}) :
    (∫ ω, X ω ^ p ∂μ) ^ (1 / p) ≤ 32 *
      (Real.sqrt p * (∫ ω, Y ω ^ p ∂μ) ^ (1 / p) + p * a) := by
  have hp0 : 0 < p := by linarith
  have hs : 0 < Real.sqrt p := Real.sqrt_pos.2 hp0
  have hd : 0 < 1 / (8 * Real.sqrt p) := by positivity
  have hA : 0 ≤ ∫ ω, X ω ^ p ∂μ := integral_nonneg (fun ω => Real.rpow_nonneg (hX0 ω) p)
  have hD : 0 ≤ ∫ ω, Y ω ^ p ∂μ := integral_nonneg (fun ω => Real.rpow_nonneg (hY0 ω) p)
  have hXint := integrable_rpow_of_bounded_nonneg μ X (le_of_lt hp0) hX hX0 hXbound
  have hYint := integrable_rpow_of_bounded_nonneg μ Y (le_of_lt hp0) hY hY0 hYbound
  have h := goodLambda_integrated μ X Y hp (by positivity : 0 ≤ 8 * p * a) hd
    (by positivity : 0 ≤ 2 * Real.exp (-2 * p)) hXbound hYbound
    (Filter.Eventually.of_forall hX0) (Filter.Eventually.of_forall hY0) hXint hYint htail
  have htwo : 0 < (2 : ℝ) ^ p := Real.rpow_pos_of_pos (by norm_num) _
  have hpow1 : (8 * p * a) ^ p * (2 : ℝ) ^ p = (16 * p * a) ^ p := by
    rw [← Real.mul_rpow (by positivity) (by norm_num)]
    congr 1
    ring
  have hpow2 : (2 : ℝ) ^ p / (1 / (8 * Real.sqrt p)) ^ p = (16 * Real.sqrt p) ^ p := by
    rw [← Real.div_rpow (by norm_num) (le_of_lt hd)]
    congr 1
    field_simp
    norm_num
  have h8 : (1 - (2 : ℝ) ^ p * (2 * Real.exp (-2 * p))) * (∫ ω, X ω ^ p ∂μ) ≤
      (16 * p * a) ^ p + (16 * Real.sqrt p) ^ p * (∫ ω, Y ω ^ p ∂μ) := by
    have hm := (div_le_iff₀ htwo).mp h
    rw [← hpow1, ← hpow2]
    have hdiv : (∫ ω, Y ω ^ p ∂μ) / (1 / (8 * Real.sqrt p)) ^ p * (2 : ℝ) ^ p =
        ((2 : ℝ) ^ p / (1 / (8 * Real.sqrt p)) ^ p) * (∫ ω, Y ω ^ p ∂μ) := by ring
    rw [add_mul, add_mul, hdiv] at hm
    nlinarith
  exact bernstein_goodLambda_moment_root hp (le_of_lt ha) hA hD h8

/-- A running maximum of measurable partial sums is measurable. -/
theorem measurable_crossTermMax {Ω : Type*} {m : MeasurableSpace Ω}
    (F : Filtration ℕ m) (ξ : ℕ → Ω → ℝ) (hξ : ∀ i, Measurable[F i] (ξ i)) (k : ℕ) :
    Measurable (crossTermMax ξ k) := by
  apply Finset.measurable_range_sup''
  intro j _
  apply Measurable.abs
  unfold crossTermPartialSum
  exact Finset.measurable_sum _ (fun i _ => (hξ i).mono (F.le i) le_rfl)

/-- The maximum of bounded partial sums is bounded by the number of increments. -/
theorem crossTermMax_le_of_bounded {Ω : Type*} (ξ : ℕ → Ω → ℝ) (k : ℕ) {a : ℝ}
    (ha : 0 ≤ a) (hξ : ∀ i, 1 ≤ i → i ≤ k → ∀ ω, |ξ i ω| ≤ a) (ω : Ω) :
    crossTermMax ξ k ω ≤ (k + 1 : ℕ) * a := by
  apply Finset.sup'_le
  intro j hj
  have hjk : j ≤ k := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
  have hcard : (Finset.Icc 1 j).card ≤ k + 1 := by
    have hsub : Finset.Icc 1 j ⊆ Finset.range (k + 1) := by
      intro i hi
      simp only [Finset.mem_Icc, Finset.mem_range] at hi ⊢
      omega
    simpa using Finset.card_le_card hsub
  calc
    |crossTermPartialSum ξ j ω| ≤ ∑ i ∈ Finset.Icc 1 j, |ξ i ω| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _i ∈ Finset.Icc 1 j, a := by
      apply Finset.sum_le_sum
      intro i hi
      exact hξ i (Finset.mem_Icc.mp hi).1 (le_trans (Finset.mem_Icc.mp hi).2 hjk) ω
    _ = ((Finset.Icc 1 j).card : ℝ) * a := by simp
    _ ≤ (k + 1 : ℕ) * a := mul_le_mul_of_nonneg_right (by exact_mod_cast hcard) ha

/-- Clipped predictable variance is measurable and globally bounded. -/
theorem measurable_clippedDifferenceVariance {Ω : Type*} {m : MeasurableSpace Ω}
    (μ : @Measure Ω m) (F : Filtration ℕ m) (ξ : ℕ → Ω → ℝ) (a : ℝ) (k : ℕ) :
    Measurable (clippedDifferenceVariance μ F ξ a k) := by
  unfold clippedDifferenceVariance
  apply Finset.measurable_sum
  intro i _
  have hcond : Measurable (μ[fun ω => ξ i ω ^ 2 | F (i - 1)]) :=
    (stronglyMeasurable_condExp.mono (F.le (i - 1))).measurable
  exact measurable_const.min (measurable_const.max hcond)

/-- The clipped predictable variance is bounded by the number of summands times `a²`. -/
theorem clippedDifferenceVariance_bounds {Ω : Type*} {m : MeasurableSpace Ω}
    (μ : @Measure Ω m) (F : Filtration ℕ m) (ξ : ℕ → Ω → ℝ) (a : ℝ) (k : ℕ) (ω : Ω) :
    0 ≤ clippedDifferenceVariance μ F ξ a k ω ∧
      clippedDifferenceVariance μ F ξ a k ω ≤ ((Finset.Icc 1 k).card : ℝ) * a ^ 2 := by
  unfold clippedDifferenceVariance
  constructor
  · exact Finset.sum_nonneg (fun i _ => le_min (sq_nonneg a) (le_max_left _ _))
  · calc
      (∑ i ∈ Finset.Icc 1 k,
        min (a ^ 2) (max 0 (μ[fun ω' => ξ i ω' ^ 2 | F (i - 1)] ω))) ≤
          ∑ _i ∈ Finset.Icc 1 k, a ^ 2 :=
        Finset.sum_le_sum (fun _ _ => min_le_left _ _)
      _ = ((Finset.Icc 1 k).card : ℝ) * a ^ 2 := by simp

/-- The square-root moment of clipped variance equals the original variance moment. -/
theorem clippedDifferenceVariance_sqrt_moment_eq {Ω : Type*} {m : MeasurableSpace Ω}
    (μ : @Measure Ω m) [IsProbabilityMeasure μ] (F : Filtration ℕ m)
    (ξ : ℕ → Ω → ℝ) (k : ℕ) {a p : ℝ}
    (hξ : ∀ i, Measurable[F i] (ξ i))
    (hbound : ∀ i, 1 ≤ i → i ≤ k → ∀ ω, |ξ i ω| ≤ a) :
    (∫ ω, (Real.sqrt (clippedDifferenceVariance μ F ξ a k ω)) ^ p ∂μ) =
      ∫ ω, (∑ i ∈ Finset.Icc 1 k,
        μ[fun ω' => ξ i ω' ^ 2 | F (i - 1)] ω) ^ (p / 2) ∂μ := by
  have hae := clippedDifferenceVariance_ae_eq_condQvar (P := μ) hξ hbound (n := k) le_rfl
  apply integral_congr_ae
  filter_upwards [hae] with ω hω
  have hv := (clippedDifferenceVariance_bounds μ F ξ a k ω).1
  rw [Real.sqrt_eq_rpow, ← Real.rpow_mul hv]
  have hp : (1 / 2 : ℝ) * p = p / 2 := by ring
  rw [hp, hω, condQvar_boundedDifferenceSum μ F ξ k k le_rfl ω]

end LatticeProb
