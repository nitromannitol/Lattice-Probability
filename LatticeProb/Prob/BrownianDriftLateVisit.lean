/-
Copyright (c) 2026. All rights reserved.
-/
import Mathlib
import LatticeProb.Prob.BrownianDriftDoob
import LatticeProb.Prob.BrownianDriftSmallBallBound

/-!
# Late visits of a drifted Brownian motion that stays above a small level

Let `B` be a Brownian motion, `c > 0`, `X t = B t + c t`, and `E δ = {X t > -δ for all t}`, an
event of probability `1 - exp (-2 c δ)`.  For every level `K` and every `ε > 0` there are a time
`T` and a bound `δ₀ > 0` such that for all `0 < δ < δ₀` the conditional probability of `E δ`
that `X` visits `(-∞, K)` after time `T` is at most `ε`:
`P (E δ ∩ {∃ s > T, X s < K}) ≤ ε P (E δ)`.

The proof splits according to the height `X T` at time `T`.  If `X T ≥ L`, Doob's maximal
inequality for the exponential martingale gives the factor `exp (2 c (K - L))`, and the
survival comparison bounds the chance of `E δ`-type events by `1 - exp (-2 c δ)` over
`1 - exp (-2 c L)`.  If `X T < L`, Gaussian freezing across the time `T / 2` and the small-ball
bound at scale one give a factor `C δ (L + 1) / √T`.

## Main results

* `LatticeProb.measureReal_late_visit_le`: the quantitative bound.
* `LatticeProb.exists_late_visit_tail`: the uniform tail estimate.
-/

open MeasureTheory ProbabilityTheory Filter MeasurableSpace Topology
open scoped ENNReal NNReal

namespace LatticeProb

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {B : ℝ≥0 → Ω → ℝ}

/-- **High part.**  Doob's inequality on the event of being above `L` at time `T` and staying
above `-δ` before. -/
theorem measureReal_high_late_le (hB : IsPreBrownianReal B P) (hm : ∀ t, Measurable (B t))
    (hcont : ∀ ω, Continuous fun t => B t ω) {c : ℝ} (hc : 0 < c) (T : ℝ≥0) (δ L K : ℝ) :
    P.real (closedStay B c δ T ∩ {ω | L ≤ B T ω + c * T} ∩
        {ω | ∃ s : ℝ≥0, T ≤ s ∧ B s ω + c * s < K}) ≤
      Real.exp (2 * c * (K - L)) * P.real (closedStay B c δ T ∩ {ω | L ≤ B T ω + c * T}) := by
  have hP : IsProbabilityMeasure P := hB.isGaussianProcess.isProbabilityMeasure
  set G : Set Ω := closedStay B c δ T ∩ {ω | L ≤ B T ω + c * T} with hG
  have hGm : MeasurableSet[brownianFiltration B hm T] G :=
    (measurableSet_closedStay hm hcont c δ T).inter (measurableSet_le_drift hm c L le_rfl)
  have hGm' : MeasurableSet G := (brownianFiltration B hm).le T _ hGm
  have h := measure_inter_exists_ge_drift_lt_le hB hm hcont hc T hGm K
  have hnn : 0 ≤ Real.exp (2 * c * K) * ∫ ω in G, Real.exp (-(2 * c) * (B T ω + c * T)) ∂P :=
    mul_nonneg (Real.exp_nonneg _) (integral_nonneg fun _ => Real.exp_nonneg _)
  have h' := ENNReal.toReal_mono ENNReal.ofReal_ne_top h
  rw [ENNReal.toReal_ofReal hnn] at h'
  have hint : ∫ ω in G, Real.exp (-(2 * c) * (B T ω + c * T)) ∂P ≤
      Real.exp (-(2 * c) * L) * P.real G := by
    have h1 : ∫ ω in G, Real.exp (-(2 * c) * (B T ω + c * T)) ∂P ≤
        ∫ _ in G, Real.exp (-(2 * c) * L) ∂P := by
      refine integral_mono_of_nonneg (Filter.Eventually.of_forall fun _ => Real.exp_nonneg _)
        (integrable_const _) ?_
      refine (ae_restrict_iff' hGm').2 (Filter.Eventually.of_forall fun ω hω => ?_)
      have h2 : L ≤ B T ω + c * T := hω.2
      exact Real.exp_le_exp.2 (by nlinarith [mul_nonneg hc.le (sub_nonneg.2 h2)])
    rw [setIntegral_const, smul_eq_mul] at h1
    exact h1.trans (le_of_eq (mul_comm _ _))
  have e : 2 * c * K + -(2 * c) * L = 2 * c * (K - L) := by ring
  calc _ ≤ Real.exp (2 * c * K) * ∫ ω in G, Real.exp (-(2 * c) * (B T ω + c * T)) ∂P := h'
    _ ≤ Real.exp (2 * c * K) * (Real.exp (-(2 * c) * L) * P.real G) :=
        mul_le_mul_of_nonneg_left hint (Real.exp_nonneg _)
    _ = Real.exp (2 * c * (K - L)) * P.real G := by
        rw [← mul_assoc, ← Real.exp_add, e]

/-- Survival comparison for the event of being above `L` at time `T` after staying above `-δ`. -/
theorem measureReal_closedStay_inter_ge_le (hB : IsPreBrownianReal B P)
    (hm : ∀ t, Measurable (B t)) (hcont : ∀ ω, Continuous fun t => B t ω) {c : ℝ} (hc : 0 < c)
    {δ : ℝ} (hδ : 0 < δ) (T : ℝ≥0) {L : ℝ} (hL : 0 < L) :
    P.real (closedStay B c δ T ∩ {ω | L ≤ B T ω + c * T}) ≤
      (1 - Real.exp (-(2 * c * δ))) / (1 - Real.exp (-(2 * c * L))) := by
  have h := measureReal_closedStay_inter_ge_mul_le hB hm hcont hc hδ T L
  have hw : 0 < 1 - Real.exp (-(2 * c * L)) := by
    have : Real.exp (-(2 * c * L)) < Real.exp 0 :=
      Real.exp_lt_exp.2 (by nlinarith [mul_pos hc hL])
    rw [Real.exp_zero] at this
    linarith
  have hle : 1 - Real.exp (-(2 * c * L)) ≤ 1 - Real.exp (-(2 * c * (δ + L))) := by
    have : Real.exp (-(2 * c * (δ + L))) ≤ Real.exp (-(2 * c * L)) :=
      Real.exp_le_exp.2 (by nlinarith [mul_pos hc hδ])
    linarith
  rw [le_div_iff₀ hw]
  exact (mul_le_mul_of_nonneg_left hle measureReal_nonneg).trans h

/-- **Low part.**  Gaussian freezing across the time `T / 2` for the event of staying above `-δ`
up to time `T` and being below `L` at time `T`. -/
theorem measureReal_closedStay_inter_lt_le (hB : IsPreBrownianReal B P)
    (hm : ∀ t, Measurable (B t)) (hcont : ∀ ω, Continuous fun t => B t ω) {c δ : ℝ} (T : ℝ≥0)
    (hT : 0 < T) {L : ℝ} (hL : -δ ≤ L) :
    P.real (closedStay B c δ T ∩ {ω | B T ω + c * T < L}) ≤
      P.real (closedStay B c δ (T / 2)) *
        ((L - -δ) / √(2 * Real.pi * ((T : ℝ) - ((T / 2 : ℝ≥0) : ℝ)))) := by
  have hP : IsProbabilityMeasure P := hB.isGaussianProcess.isProbabilityMeasure
  have hrs : T / 2 < T := half_lt_self hT
  have hsub : closedStay B c δ T ∩ {ω | B T ω + c * T < L} ⊆
      closedStay B c δ (T / 2) ∩ {ω | B T ω + c * T ∈ Set.Icc (-δ) L} := by
    rintro ω ⟨h1, h2⟩
    exact ⟨closedStay_anti hrs.le h1, h1 T le_rfl, h2.le⟩
  have h := measure_inter_drift_mem_Icc_le hB hm hrs
    (measurableSet_closedStay hm hcont c δ (T / 2)) c hL
  have h' := ENNReal.toReal_mono
    (ENNReal.mul_ne_top (measure_ne_top _ _) ENNReal.ofReal_ne_top) h
  rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (div_nonneg (by linarith) (Real.sqrt_nonneg _))]
    at h'
  exact (measureReal_mono hsub).trans h'

/-- The survival probability `1 - exp (-2 c δ)` is at least `c δ` when `2 c δ ≤ 1`. -/
theorem le_one_sub_exp_neg {c δ : ℝ} (hc : 0 < c) (hδ : 0 < δ) (h : 2 * c * δ ≤ 1) :
    c * δ ≤ 1 - Real.exp (-(2 * c * δ)) := by
  have hx : 0 < 2 * c * δ := by positivity
  have hexp : Real.exp (-(2 * c * δ)) ≤ 1 / (1 + 2 * c * δ) := by
    rw [Real.exp_neg, one_div]
    exact inv_anti₀ (by positivity) (by linarith [Real.add_one_le_exp (2 * c * δ)])
  have h1 : 2 * c * δ / (1 + 2 * c * δ) = 1 - 1 / (1 + 2 * c * δ) := by field_simp; ring
  have h2 : 2 * c * δ / 2 ≤ 2 * c * δ / (1 + 2 * c * δ) := by
    rw [div_le_div_iff₀ (by norm_num) (by positivity)]
    nlinarith
  linarith

/-- **Quantitative late-visit bound.**  Given the small-ball constant `C`, a level `L > 0` and a
time `T ≥ 2`, for `0 < δ ≤ 1/4` with `2 c δ ≤ 1`:
`P (E δ ∩ {∃ s > T, X s < K}) ≤ P (E δ) (exp (2 c (K - L)) / (1 - exp (-2 c L)) +
C (L + 1) / (c √T))`. -/
theorem measureReal_late_visit_le (hB : IsPreBrownianReal B P) (hm : ∀ t, Measurable (B t))
    (hcont : ∀ ω, Continuous fun t => B t ω) {c : ℝ} (hc : 0 < c) {C : ℝ} (hC0 : 0 ≤ C)
    (hC : ∀ δ : ℝ, 0 < δ → δ ≤ 1 / 4 → P.real (closedStay B c δ 1) ≤ C * δ)
    (K : ℝ) {L : ℝ} (hL : 0 < L) (T : ℝ≥0) (hT : 2 ≤ T) {δ : ℝ} (hδ : 0 < δ) (hδ4 : δ ≤ 1 / 4)
    (hδc : 2 * c * δ ≤ 1) :
    P.real ({ω | ∀ t : ℝ≥0, -δ < B t ω + c * t} ∩
        {ω | ∃ s : ℝ≥0, T < s ∧ B s ω + c * s < K}) ≤
      P.real {ω | ∀ t : ℝ≥0, -δ < B t ω + c * t} *
        (Real.exp (2 * c * (K - L)) / (1 - Real.exp (-(2 * c * L))) +
          C * (L + 1) / (c * √(T : ℝ))) := by
  have hP : IsProbabilityMeasure P := hB.isGaussianProcess.isProbabilityMeasure
  have hT0 : (0 : ℝ≥0) < T := lt_of_lt_of_le (by norm_num) hT
  have hTr : (2 : ℝ) ≤ T := by exact_mod_cast hT
  have hTpos : (0 : ℝ) < T := by linarith
  have hsT : 0 < √(T : ℝ) := Real.sqrt_pos.2 hTpos
  set p : ℝ := 1 - Real.exp (-(2 * c * δ)) with hp
  have hE : P.real {ω | ∀ t : ℝ≥0, -δ < B t ω + c * t} = p := by
    rw [measureReal_def, measure_forall_drift_gt hB hm hcont hc hδ,
      ENNReal.toReal_ofReal]
    have : Real.exp (-(2 * c * δ)) ≤ 1 := Real.exp_le_one_iff.2 (by nlinarith [mul_pos hc hδ])
    linarith
  have hpl : c * δ ≤ p := le_one_sub_exp_neg hc hδ hδc
  have hw : 0 < 1 - Real.exp (-(2 * c * L)) := by
    have : Real.exp (-(2 * c * L)) < Real.exp 0 :=
      Real.exp_lt_exp.2 (by nlinarith [mul_pos hc hL])
    rw [Real.exp_zero] at this
    linarith
  rw [hE]
  have hsub : {ω | ∀ t : ℝ≥0, -δ < B t ω + c * t} ∩
      {ω | ∃ s : ℝ≥0, T < s ∧ B s ω + c * s < K} ⊆
      (closedStay B c δ T ∩ {ω | L ≤ B T ω + c * T} ∩
        {ω | ∃ s : ℝ≥0, T ≤ s ∧ B s ω + c * s < K}) ∪
      (closedStay B c δ T ∩ {ω | B T ω + c * T < L}) := by
    rintro ω ⟨hE', s, hs, hX⟩
    have hS : ω ∈ closedStay B c δ T := fun t _ => (hE' t).le
    by_cases h : L ≤ B T ω + c * T
    · exact Or.inl ⟨⟨hS, h⟩, s, hs.le, hX⟩
    · exact Or.inr ⟨hS, not_le.1 h⟩
  -- the high part
  have hb1 : P.real (closedStay B c δ T ∩ {ω | L ≤ B T ω + c * T} ∩
        {ω | ∃ s : ℝ≥0, T ≤ s ∧ B s ω + c * s < K}) ≤
      p * (Real.exp (2 * c * (K - L)) / (1 - Real.exp (-(2 * c * L)))) := by
    calc _ ≤ _ := measureReal_high_late_le hB hm hcont hc T δ L K
      _ ≤ Real.exp (2 * c * (K - L)) * (p / (1 - Real.exp (-(2 * c * L)))) :=
          mul_le_mul_of_nonneg_left (measureReal_closedStay_inter_ge_le hB hm hcont hc hδ T hL)
            (Real.exp_nonneg _)
      _ = _ := by ring
  -- the low part
  have hhalf : (((T / 2 : ℝ≥0)) : ℝ) = (T : ℝ) / 2 := by push_cast; ring
  have hden : (T : ℝ) ≤ 2 * Real.pi * ((T : ℝ) - ((T / 2 : ℝ≥0) : ℝ)) := by
    rw [hhalf]; nlinarith [Real.pi_gt_three]
  have hden' : √(T : ℝ) ≤ √(2 * Real.pi * ((T : ℝ) - ((T / 2 : ℝ≥0) : ℝ))) :=
    Real.sqrt_le_sqrt hden
  have hq0 : 0 ≤ (L + 1) / √(T : ℝ) := by positivity
  have hfac : (L - -δ) / √(2 * Real.pi * ((T : ℝ) - ((T / 2 : ℝ≥0) : ℝ))) ≤
      (L + 1) / √(T : ℝ) := by
    rw [sub_neg_eq_add]
    exact div_le_div₀ (by linarith) (by linarith) hsT hden'
  have h1T : (1 : ℝ≥0) ≤ T / 2 := by
    rw [le_div_iff₀ (by norm_num)]; simpa using hT
  have hsmall : P.real (closedStay B c δ (T / 2)) ≤ C * δ :=
    (measureReal_mono (closedStay_anti h1T)).trans (hC δ hδ hδ4)
  have hb2 : P.real (closedStay B c δ T ∩ {ω | B T ω + c * T < L}) ≤
      p * (C * (L + 1) / (c * √(T : ℝ))) := by
    have h0 := measureReal_closedStay_inter_lt_le (c := c) hB hm hcont T hT0 (show -δ ≤ L by linarith)
    have h3 : P.real (closedStay B c δ (T / 2)) *
        ((L - -δ) / √(2 * Real.pi * ((T : ℝ) - ((T / 2 : ℝ≥0) : ℝ)))) ≤
        C * δ * ((L + 1) / √(T : ℝ)) :=
      mul_le_mul hsmall hfac (div_nonneg (by linarith) (Real.sqrt_nonneg _))
        (mul_nonneg hC0 hδ.le)
    refine h0.trans (h3.trans ?_)
    have e : C * (L + 1) / (c * √(T : ℝ)) = C * ((L + 1) / √(T : ℝ)) / c := by
      field_simp
    rw [e, ← mul_div_assoc p (C * ((L + 1) / √(T : ℝ))) c, le_div_iff₀ hc]
    have := mul_le_mul_of_nonneg_right hpl (mul_nonneg hC0 hq0)
    nlinarith
  calc _ ≤ P.real _ := measureReal_mono hsub
    _ ≤ _ := measureReal_union_le _ _
    _ ≤ _ := by linarith

/-- **Uniform tail of the late visits.**  For every level `K` and `ε > 0` there are a time `T` and
`δ₀ > 0` such that for all `0 < δ < δ₀`,
`P (E δ ∩ {∃ s > T, B s + c s < K}) ≤ ε P (E δ)` where `E δ = {∀ t, -δ < B t + c t}`. -/
theorem exists_late_visit_tail (hB : IsPreBrownianReal B P) (hm : ∀ t, Measurable (B t))
    (hcont : ∀ ω, Continuous fun t => B t ω) {c : ℝ} (hc : 0 < c) (K : ℝ) {ε : ℝ} (hε : 0 < ε) :
    ∃ T : ℝ≥0, ∃ δ₀ : ℝ, 0 < δ₀ ∧ ∀ δ : ℝ, 0 < δ → δ < δ₀ →
      P ({ω | ∀ t : ℝ≥0, -δ < B t ω + c * t} ∩
          {ω | ∃ s : ℝ≥0, T < s ∧ B s ω + c * s < K}) ≤
        ENNReal.ofReal ε * P {ω | ∀ t : ℝ≥0, -δ < B t ω + c * t} := by
  have hP : IsProbabilityMeasure P := hB.isGaussianProcess.isProbabilityMeasure
  obtain ⟨C, hC0, hC⟩ := measureReal_closedStay_one_le hB hm hcont hc
  set κ : ℝ := 1 - Real.exp (-(2 * c)) with hκ
  have hκpos : 0 < κ := by
    have : Real.exp (-(2 * c)) < Real.exp 0 := Real.exp_lt_exp.2 (by linarith)
    rw [Real.exp_zero] at this
    linarith
  have hκε : 0 < κ * ε / 2 := by positivity
  set L : ℝ := max 1 (K - Real.log (κ * ε / 2) / (2 * c)) with hLdef
  have hL1 : 1 ≤ L := le_max_left _ _
  have hL0 : 0 < L := by linarith
  have hexp : Real.exp (2 * c * (K - L)) ≤ κ * ε / 2 := by
    have h1 : K - Real.log (κ * ε / 2) / (2 * c) ≤ L := le_max_right _ _
    have h2 : K - L ≤ Real.log (κ * ε / 2) / (2 * c) := by linarith
    have h3 : (K - L) * (2 * c) ≤ Real.log (κ * ε / 2) := (le_div_iff₀ (by positivity)).1 h2
    calc Real.exp (2 * c * (K - L)) ≤ Real.exp (Real.log (κ * ε / 2)) :=
          Real.exp_le_exp.2 (by linarith)
      _ = κ * ε / 2 := Real.exp_log hκε
  have hw : κ ≤ 1 - Real.exp (-(2 * c * L)) := by
    have : Real.exp (-(2 * c * L)) ≤ Real.exp (-(2 * c)) := Real.exp_le_exp.2 (by nlinarith)
    rw [hκ]
    linarith
  have hwpos : 0 < 1 - Real.exp (-(2 * c * L)) := lt_of_lt_of_le hκpos hw
  have hterm1 : Real.exp (2 * c * (K - L)) / (1 - Real.exp (-(2 * c * L))) ≤ ε / 2 := by
    rw [div_le_iff₀ hwpos]
    have := mul_le_mul_of_nonneg_left hw (by positivity : (0 : ℝ) ≤ ε / 2)
    linarith
  set M : ℝ := 2 * C * (L + 1) / (c * ε) with hM
  have hM0 : 0 ≤ M := by positivity
  set T : ℝ≥0 := Real.toNNReal (max 2 (M ^ 2)) with hTdef
  have hTc : (T : ℝ) = max 2 (M ^ 2) :=
    Real.coe_toNNReal _ (le_trans (by norm_num) (le_max_left _ _))
  have hT2 : 2 ≤ T := by
    rw [← NNReal.coe_le_coe, hTc]
    simp
  have hsT : M ≤ √(T : ℝ) := by
    calc M = √(M ^ 2) := (Real.sqrt_sq hM0).symm
      _ ≤ √(T : ℝ) := Real.sqrt_le_sqrt (by rw [hTc]; exact le_max_right _ _)
  have hTpos : (0 : ℝ) < T := by
    rw [hTc]
    exact lt_of_lt_of_le (by norm_num) (le_max_left _ _)
  have hsTpos : 0 < √(T : ℝ) := Real.sqrt_pos.2 hTpos
  have hterm2 : C * (L + 1) / (c * √(T : ℝ)) ≤ ε / 2 := by
    rw [div_le_iff₀ (by positivity)]
    have e : 2 * C * (L + 1) = M * (c * ε) := by rw [hM]; field_simp
    have := mul_le_mul_of_nonneg_right hsT (by positivity : (0 : ℝ) ≤ c * ε)
    nlinarith
  refine ⟨T, min (1 / 4) (1 / (2 * c)), lt_min (by norm_num) (by positivity), fun δ hδ hδlt => ?_⟩
  have hδ4 : δ ≤ 1 / 4 := (lt_min_iff.1 hδlt).1.le
  have hδc : 2 * c * δ ≤ 1 := by
    have : δ ≤ 1 / (2 * c) := (lt_min_iff.1 hδlt).2.le
    rw [le_div_iff₀ (by positivity)] at this
    linarith
  have hQ := measureReal_late_visit_le hB hm hcont hc hC0 hC K hL0 T hT2 hδ hδ4 hδc
  have hfin : P.real ({ω | ∀ t : ℝ≥0, -δ < B t ω + c * t} ∩
        {ω | ∃ s : ℝ≥0, T < s ∧ B s ω + c * s < K}) ≤
      ε * P.real {ω | ∀ t : ℝ≥0, -δ < B t ω + c * t} := by
    calc _ ≤ _ := hQ
      _ ≤ P.real {ω | ∀ t : ℝ≥0, -δ < B t ω + c * t} * ε :=
          mul_le_mul_of_nonneg_left (by linarith) measureReal_nonneg
      _ = _ := mul_comm _ _
  calc _ = ENNReal.ofReal (P.real _) := (ENNReal.ofReal_toReal (measure_ne_top _ _)).symm
    _ ≤ ENNReal.ofReal (ε * P.real {ω | ∀ t : ℝ≥0, -δ < B t ω + c * t}) :=
        ENNReal.ofReal_le_ofReal hfin
    _ = _ := by
        rw [ENNReal.ofReal_mul hε.le]
        congr 1
        exact ENNReal.ofReal_toReal (measure_ne_top _ _)

end LatticeProb
