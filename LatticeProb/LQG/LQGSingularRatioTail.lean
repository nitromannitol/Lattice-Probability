import LatticeProb.LQG.LQGSingularIntegralMoment

/-!
# Tail of a log-singular weighted mass relative to a concentric ball mass

Let `μ` be the `γ`-Liouville quantum gravity measure of a whole-plane Gaussian free field `h`,
normalized by `h_1(0) = 0`, with `γ ∈ (0, 2)`. For a dyadic radius `r = 2^{-j}/4` consider the
weighted mass `Y = r^{γ²} ∫_{B(0,r)} |x|^{-γ²} dμ(x)` and the ball mass `D = μ(B(0, r/2))`.
There are `q > 0` and `C` such that `P(t D < Y) ≤ C t^{-q}` for every `t ≥ 1`, uniformly in the
scale `j` and in the probability space carrying the field.

This is the estimate at the marked point in the proof of the multiscale ratio bound for the
`γ`-quantum cone (Berestycki and Gwynne, arXiv:2003.10320, Lemma A.2): near the origin the cone
measure is `|x|^{-γ²}` times a whole-plane LQG measure, and only one centred variable per scale
is needed.

* `aemeasurable_setLIntegral`: a random measure whose set evaluations are a.e. measurable has
  a.e. measurable integrals against a fixed measurable function.
* `rpow_mul_norm_rpow`: the algebraic identity behind the scale invariance of `Y`.
* `measure_mul_ball_lt_singular_le_zero`: the tail at unit scale, from the fractional moment of the
  singular integral and the lower tail of `μ(B(0, 1/8))`.
* `measure_mul_ball_lt_singular_le`: every dyadic scale, by the exact dyadic scaling relation.
-/

open MeasureTheory ProbabilityTheory Filter Set Metric
open scoped ENNReal NNReal

namespace LatticeProb.LQG

open LatticeProb.Gauss LatticeProb.LQG.LQGDyadicScaling

namespace LQGSingularRatioTail

/-- A random measure all of whose set evaluations are a.e. measurable has a.e. measurable integrals
against a fixed measurable function on a fixed measurable set (approximation by simple functions). -/
theorem aemeasurable_setLIntegral {Ω α : Type*} [MeasurableSpace Ω] [MeasurableSpace α]
    {P : Measure Ω} {μ : Ω → Measure α}
    (hμ : ∀ A : Set α, MeasurableSet A → AEMeasurable (fun ω => μ ω A) P)
    {f : α → ℝ≥0∞} (hf : Measurable f) {s : Set α} (hs : MeasurableSet s) :
    AEMeasurable (fun ω => ∫⁻ x in s, f x ∂μ ω) P := by
  have hg : Measurable (s.indicator f) := hf.indicator hs
  have heq : (fun ω => ∫⁻ x in s, f x ∂μ ω) =
      fun ω => ⨆ n, (SimpleFunc.eapprox (s.indicator f) n).lintegral (μ ω) := by
    funext ω
    rw [← lintegral_indicator hs, lintegral_eq_iSup_eapprox_lintegral hg]
  rw [heq]
  refine AEMeasurable.iSup fun n => ?_
  simp only [SimpleFunc.lintegral]
  exact Finset.aemeasurable_fun_sum _ fun x _ =>
    (hμ _ (SimpleFunc.measurableSet_preimage _ _)).const_mul x

/-- Scale invariance of the weight: `(s/4)^{γ²} |s y|^{-γ²} = |4 y|^{-γ²}` for `s > 0`. -/
theorem rpow_mul_norm_rpow {s : ℝ} (hs : 0 < s) (γ : ℝ) (y : ℂ) :
    (s * (1 / 4)) ^ (γ ^ 2) * ‖(s : ℂ) * y + 0‖ ^ (-γ ^ 2) = ‖4 * y‖ ^ (-γ ^ 2) := by
  have h4 : ‖(4 : ℂ)‖ = 4 := by simp
  rw [add_zero, norm_mul, norm_mul, Complex.norm_real, Real.norm_of_nonneg hs.le, h4,
    Real.mul_rpow hs.le (norm_nonneg _), Real.mul_rpow (by norm_num) (norm_nonneg _),
    Real.mul_rpow hs.le (by norm_num), Real.rpow_neg hs.le, Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 4),
    one_div, Real.inv_rpow (by norm_num : (0 : ℝ) ≤ 4)]
  have h1 : 0 < s ^ (γ ^ 2) := Real.rpow_pos_of_pos hs _
  field_simp

/-- **Unit scale.** For `γ ∈ (0, 2)` there are `q > 0` and `C` such that for every whole-plane GFF
model and `t ≥ 1`, `P(t μ(B(0, 1/8)) < ∫_{B(0,1/4)} |4y|^{-γ²} dμ(y)) ≤ C t^{-q}`. -/
theorem measure_mul_ball_lt_singular_le_zero.{u} {γ : ℝ} (hγ0 : 0 < γ) (hγ2 : γ < 2) :
    ∃ q : ℝ, 0 < q ∧ ∃ C : ℝ≥0, ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ) (μ : Ω → Measure ℂ),
      IsWholePlaneGFF P hC hcirc → IsLQGMeasure P γ hcirc μ → ∀ t : ℝ, 1 ≤ t →
        P {ω | ENNReal.ofReal t * μ ω (ball 0 (1 / 8)) <
          ∫⁻ y in ball (0 : ℂ) (1 / 4), ENNReal.ofReal (‖4 * y‖ ^ (-γ ^ 2)) ∂μ ω} ≤
          C * ENNReal.ofReal (t ^ (-q)) := by
  obtain ⟨p, hp0, C0, hC0⟩ :=
    LQGSingularIntegralMoment.exists_lintegral_singular_rpow_le.{u} hγ0 hγ2
  have hγ4 : γ ^ 2 < 4 := by nlinarith
  obtain ⟨C1, hC1⟩ := LQGBallMassRatioTail.measure_ball_dyadic_lt_le.{u} hγ0 hγ2 one_pos
    (ballMassNegMoment_of_lt hγ0.ne' hγ4 one_pos) 3
  set q : ℝ := min (1 / 4) (p / 2) with hq
  refine ⟨q, lt_min (by norm_num) (by positivity), C0 + C1, ?_⟩
  intro Ω _ P hC hcirc μ hh hμ t ht
  have ht0 : 0 < t := by linarith
  have hs0 : 0 < Real.sqrt t := Real.sqrt_pos.2 ht0
  set N : Ω → ℝ≥0∞ := fun ω =>
    ∫⁻ y in ball (0 : ℂ) (1 / 4), ENNReal.ofReal (‖4 * y‖ ^ (-γ ^ 2)) ∂μ ω with hN
  have hα : (0 : ℝ) < lqgQ γ := by unfold lqgQ; positivity
  have hmeas : ∀ A : Set ℂ, MeasurableSet A → AEMeasurable (fun ω => μ ω A) P := fun A hA =>
    aemeasurable_lqgMeasure_borel hγ0 hγ2 hα hh (isLQGMeasureOfField_zero hμ)
      (lqgLocality_of_gff P γ 0 hC hcirc) A hA
  have hNm : AEMeasurable N P :=
    aemeasurable_setLIntegral hmeas (by fun_prop) measurableSet_ball
  have h8 : (1 / 8 : ℝ) = dyadicScale 3 := by norm_num [dyadicScale]
  have hst : t * (Real.sqrt t)⁻¹ = Real.sqrt t := by
    rw [eq_comm, ← div_eq_mul_inv, eq_div_iff hs0.ne', Real.mul_self_sqrt ht0.le]
  have hsub : {ω | ENNReal.ofReal t * μ ω (ball 0 (1 / 8)) < N ω} ⊆
      {ω | ENNReal.ofReal (Real.sqrt t) ^ p ≤ N ω ^ p} ∪
        {ω | μ ω (ball 0 (dyadicScale 3)) < ENNReal.ofReal (Real.sqrt t)⁻¹} := by
    intro ω hω
    have hω' : ENNReal.ofReal t * μ ω (ball 0 (1 / 8)) < N ω := hω
    by_contra hc
    rw [Set.mem_union, not_or] at hc
    obtain ⟨h1, h2⟩ := hc
    have h1' : N ω < ENNReal.ofReal (Real.sqrt t) :=
      (ENNReal.rpow_lt_rpow_iff hp0).1 (not_le.1 h1)
    have h2' : ENNReal.ofReal (Real.sqrt t)⁻¹ ≤ μ ω (ball 0 (1 / 8)) := by
      rw [h8]; exact not_lt.1 h2
    have h3 : ENNReal.ofReal (Real.sqrt t) ≤ ENNReal.ofReal t * μ ω (ball 0 (1 / 8)) := by
      calc ENNReal.ofReal (Real.sqrt t) = ENNReal.ofReal t * ENNReal.ofReal (Real.sqrt t)⁻¹ := by
            rw [← ENNReal.ofReal_mul ht0.le, hst]
        _ ≤ _ := mul_le_mul' le_rfl h2'
    exact lt_irrefl _ (h3.trans_lt (hω'.trans h1'))
  have hε : ENNReal.ofReal (Real.sqrt t) ^ p = ENNReal.ofReal (t ^ (p / 2)) := by
    rw [ENNReal.ofReal_rpow_of_pos hs0, Real.sqrt_eq_rpow, ← Real.rpow_mul ht0.le]
    congr 2
    ring
  have hε0 : ENNReal.ofReal (Real.sqrt t) ^ p ≠ 0 :=
    (ENNReal.rpow_pos (ENNReal.ofReal_pos.2 hs0) ENNReal.ofReal_ne_top).ne'
  have hεtop : ENNReal.ofReal (Real.sqrt t) ^ p ≠ ∞ :=
    ENNReal.rpow_ne_top_of_nonneg hp0.le ENNReal.ofReal_ne_top
  have hA1 : P {ω | ENNReal.ofReal (Real.sqrt t) ^ p ≤ N ω ^ p} ≤
      C0 * ENNReal.ofReal (t ^ (-q)) := by
    calc _ ≤ (∫⁻ ω, N ω ^ p ∂P) / ENNReal.ofReal (Real.sqrt t) ^ p :=
          meas_ge_le_lintegral_div (hNm.pow_const p) hε0 hεtop
      _ ≤ C0 / ENNReal.ofReal (t ^ (p / 2)) := by
          rw [hε]; gcongr; exact hC0 Ω P hC hcirc μ hh hμ
      _ = C0 * ENNReal.ofReal (t ^ (-(p / 2))) := by
          rw [div_eq_mul_inv, ← ENNReal.ofReal_inv_of_pos (by positivity),
            ← Real.rpow_neg ht0.le]
      _ ≤ _ := by
          gcongr
          exact min_le_right _ _
  have hs4 : Real.sqrt (Real.sqrt t)⁻¹ ^ (1 : ℝ) = t ^ (-(1 / 4 : ℝ)) := by
    rw [Real.rpow_one, Real.sqrt_inv, Real.sqrt_eq_rpow, Real.sqrt_eq_rpow,
      ← Real.rpow_mul ht0.le, ← Real.rpow_neg ht0.le]
    norm_num
  have hA2 : P {ω | μ ω (ball 0 (dyadicScale 3)) < ENNReal.ofReal (Real.sqrt t)⁻¹} ≤
      C1 * ENNReal.ofReal (t ^ (-q)) := by
    calc _ ≤ C1 * ENNReal.ofReal (Real.sqrt (Real.sqrt t)⁻¹ ^ (1 : ℝ)) :=
          hC1 Ω P hC hcirc μ hh hμ _ (inv_pos.2 hs0)
      _ ≤ _ := by
          rw [hs4]
          gcongr
          exact min_le_left _ _
  calc P {ω | ENNReal.ofReal t * μ ω (ball 0 (1 / 8)) < N ω}
      ≤ P ({ω | ENNReal.ofReal (Real.sqrt t) ^ p ≤ N ω ^ p} ∪
          {ω | μ ω (ball 0 (dyadicScale 3)) < ENNReal.ofReal (Real.sqrt t)⁻¹}) := measure_mono hsub
    _ ≤ _ := measure_union_le _ _
    _ ≤ C0 * ENNReal.ofReal (t ^ (-q)) + C1 * ENNReal.ofReal (t ^ (-q)) := add_le_add hA1 hA2
    _ = _ := by rw [ENNReal.coe_add, add_mul]

/-- **Every dyadic scale.** For `γ ∈ (0, 2)` there are `q > 0` and `C` such that for every
whole-plane GFF model, every `j` and every `t ≥ 1`, with `r = 2^{-j}/4`,
`P(t μ(B(0, r/2)) < r^{γ²} ∫_{B(0,r)} |x|^{-γ²} dμ(x)) ≤ C t^{-q}`. -/
theorem measure_mul_ball_lt_singular_le.{u} {γ : ℝ} (hγ0 : 0 < γ) (hγ2 : γ < 2) :
    ∃ q : ℝ, 0 < q ∧ ∃ C : ℝ≥0, ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ) (μ : Ω → Measure ℂ),
      IsWholePlaneGFF P hC hcirc → IsLQGMeasure P γ hcirc μ → ∀ (j : ℕ) (t : ℝ), 1 ≤ t →
        P {ω | ENNReal.ofReal t * μ ω (ball 0 (dyadicScale j * (1 / 8))) <
          ENNReal.ofReal ((dyadicScale j * (1 / 4)) ^ (γ ^ 2)) *
            ∫⁻ x in ball (0 : ℂ) (dyadicScale j * (1 / 4)), ENNReal.ofReal (‖x‖ ^ (-γ ^ 2)) ∂μ ω} ≤
          C * ENNReal.ofReal (t ^ (-q)) := by
  obtain ⟨q, hq0, C, hC0⟩ := measure_mul_ball_lt_singular_le_zero.{u} hγ0 hγ2
  refine ⟨q, hq0, C, ?_⟩
  intro Ω _ P hC hcirc μ hh hμ j t ht
  obtain ⟨hC', hh'⟩ := isWholePlaneGFF_recentredField hh j 0
  obtain ⟨μ', hμ'⟩ := hh'.exists_isLQGMeasure hγ0 hγ2
  refine le_trans (measure_mono_ae ?_) (hC0 Ω P hC' _ μ' hh' hμ' t ht)
  filter_upwards [ae_eq_smul_map hγ0 hμ j 0 hμ'] with ω hω hbad
  have hr := dyadicScale_pos' j
  set F := dyadicFactor γ j (hcirc ω (dyadicScale j) 0) with hF
  have hF0 : F ≠ 0 := dyadicFactor_ne_zero γ j _
  have hFtop : F ≠ ∞ := dyadicFactor_ne_top γ j _
  have hemb := measurableEmbedding_dilate j 0
  have hpre : ∀ ρ : ℝ, (fun w : ℂ => (dyadicScale j : ℂ) * w + 0) ⁻¹' ball 0 (dyadicScale j * ρ) =
      ball 0 ρ := by
    intro ρ
    ext w
    simp only [mem_preimage, Metric.mem_ball, dist_eq_norm, add_zero, sub_zero, norm_mul,
      Complex.norm_real, Real.norm_of_nonneg hr.le]
    exact mul_lt_mul_iff_right₀ hr
  have hball : μ ω (ball 0 (dyadicScale j * (1 / 8))) = F * μ' ω (ball 0 (1 / 8)) := by
    rw [hω, Measure.smul_apply, Measure.map_apply hemb.measurable measurableSet_ball, hpre,
      smul_eq_mul]
  have hint : ENNReal.ofReal ((dyadicScale j * (1 / 4)) ^ (γ ^ 2)) *
      ∫⁻ x in ball (0 : ℂ) (dyadicScale j * (1 / 4)), ENNReal.ofReal (‖x‖ ^ (-γ ^ 2)) ∂μ ω =
      F * ∫⁻ y in ball (0 : ℂ) (1 / 4), ENNReal.ofReal (‖4 * y‖ ^ (-γ ^ 2)) ∂μ' ω := by
    rw [hω, Measure.restrict_smul, lintegral_smul_measure,
      setLIntegral_map measurableSet_ball (by fun_prop) hemb.measurable, hpre, smul_eq_mul,
      mul_left_comm, ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    congr 1
    refine lintegral_congr fun y => ?_
    rw [← ENNReal.ofReal_mul (by positivity), rpow_mul_norm_rpow hr]
  have hbad' : ENNReal.ofReal t * μ ω (ball 0 (dyadicScale j * (1 / 8))) <
      ENNReal.ofReal ((dyadicScale j * (1 / 4)) ^ (γ ^ 2)) *
        ∫⁻ x in ball (0 : ℂ) (dyadicScale j * (1 / 4)), ENNReal.ofReal (‖x‖ ^ (-γ ^ 2)) ∂μ ω :=
    hbad
  rw [hball, hint, mul_left_comm] at hbad'
  exact (ENNReal.mul_lt_mul_iff_right hF0 hFtop).1 hbad'

end LQGSingularRatioTail

end LatticeProb.LQG
