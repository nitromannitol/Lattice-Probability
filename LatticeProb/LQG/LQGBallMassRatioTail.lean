import LatticeProb.LQG.LQGBallMassLowerTail
import LatticeProb.LQG.LQGBallMassUpperDyadic
import LatticeProb.LQG.LQGMeasureNonatomicMassTail
import LatticeProb.LQG.LQGMassFatou
import LatticeProb.LQG.LQGNegMomentMain

/-!
# The tail of the ratio of two concentric LQG ball masses

Let `μ` be the `γ`-Liouville quantum gravity measure of a whole-plane Gaussian free field `h`,
normalized by `h_1(0) = 0`, with `γ ∈ (0, 2)`. For a radius `c > 0`, the event
`t μ(B(0, c)) < μ(B(0, 1/4))` has probability at most `C t^{-p'}` for every `p'` below the exponent `p`
of a finite positive moment of `μ(B(0, 1/4))`; the constant does not depend on the probability space
carrying the field. This is the one-ball estimate behind the multiscale ratio bound of Berestycki and
Gwynne (arXiv:2003.10320, Lemma A.2): positive moments control the larger ball, and
negative moments of all orders together with the Gaussian circle average control the smaller ball.

* `circle_le_le_exp`: the Chernoff bound for the circle average `h_{2^{-k}}(0)`, a centred Gaussian
  variable of variance `k log 2`.
* `measure_ball_dyadic_lt_le`: the lower tail of `μ(B(0, 2^{-m}))`, from the dyadic scaling
  `μ(B(0, 2^{-m})) = 2^{-m(2+γ²/2)} e^{γ h_{2^{-m}}(0)} μ'(B(0, 1))`, a negative moment of the
  unit-ball mass `μ'(B(0, 1))` of the recentred field, and the Chernoff bound.
* `measure_mul_ball_lt_ball_le`: the ratio tail, from a positive and all negative moments.
* `measure_mul_ball_lt_ball_le_of_lt`: the same with the moments supplied by Gaussian multiplicative
  chaos, for `1 ≤ p < 4/γ²`.
-/

open MeasureTheory ProbabilityTheory Filter Set Metric
open scoped ENNReal NNReal

namespace LatticeProb.LQG

open LatticeProb.Gauss LatticeProb.LQG.LQGDyadicScaling

namespace LQGBallMassRatioTail

/-- **Chernoff bound for a dyadic circle average.** For the whole-plane GFF normalized by
`h_1(0) = 0`, `h_{2^{-k}}(0)` is centred Gaussian with variance `k log 2`, so for `l ≥ 0`,
`P(h_{2^{-k}}(0) ≤ ε) ≤ exp(l ε + k log 2 · l² / 2)`. -/
theorem circle_le_le_exp {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {hC : Ω → (ℂ → ℝ) → ℝ}
    {hcirc : Ω → ℝ → ℂ → ℝ} (hh : IsWholePlaneGFF P hC hcirc) (k : ℕ) {l : ℝ} (hl : 0 ≤ l)
    (ε : ℝ) :
    P {ω | hcirc ω (dyadicScale k) 0 ≤ ε} ≤
      ENNReal.ofReal (Real.exp (l * ε + ((k : ℝ) * Real.log 2) * l ^ 2 / 2)) := by
  have hP := hh.isProbabilityMeasure
  have hr := dyadicScale_pos' k
  have hr1 : dyadicScale k ≤ 1 := dyadicScale_le_one' k
  set X : Ω → ℝ := fun ω => hcirc ω (dyadicScale k) 0 with hX
  have hG : HasGaussianLaw X P := hh.hasGaussianLaw_circle hr 0
  have hmean : ∫ ω, X ω ∂P = 0 := hh.integral_eq_zero (.circle (dyadicScale k) 0) hr
  have hlogr : -Real.log (dyadicScale k) = k * Real.log 2 := by
    rw [dyadicScale, Real.log_pow, Real.log_inv]; ring
  have hvar : Var[X; P] = k * Real.log 2 := by
    rw [← covariance_self hG.aemeasurable]
    have hcov := hh.covariance_eq (.circle (dyadicScale k) 0) (.circle (dyadicScale k) 0) hr hr
    rw [LQGMeasureNonatomicMass.wholePlaneGFFCov_circle_zero_lp hr hr1, hlogr] at hcov
    exact hcov
  set v : NNReal := ((k : ℝ) * Real.log 2).toNNReal with hv_def
  have hv : (v : ℝ) = k * Real.log 2 := Real.coe_toNNReal _ (by positivity)
  have hlaw : HasLaw X (gaussianReal 0 v) P :=
    ⟨hG.aemeasurable, by rw [hG.map_eq_gaussianReal, hmean, hvar]⟩
  have hint : ∀ t : ℝ, Integrable (fun ω => Real.exp (t * X ω)) P := by
    intro t
    have h := integrable_exp_mul_gaussianReal (μ := 0) (v := v) t
    rw [← hlaw.map_eq] at h
    exact (integrable_map_measure (by fun_prop) hG.aemeasurable).1 h
  have hch := measure_le_le_exp_mul_mgf ε (neg_nonpos.2 hl) (hint (-l))
  rw [mgf_gaussianReal hlaw] at hch
  rw [← ofReal_measureReal (measure_ne_top P _)]
  refine ENNReal.ofReal_le_ofReal (hch.trans (le_of_eq ?_))
  rw [← Real.exp_add, hv]
  congr 1
  ring

/-- **Lower tail of a dyadic ball mass at the origin.** Given a negative moment of order `q` of the
unit-ball mass (uniformly over whole-plane GFF models), for every `m` there is `C` with
`P(μ(B(0, 2^{-m})) < s) ≤ C (√s)^q` for all `s > 0`, uniformly over models. -/
theorem measure_ball_dyadic_lt_le.{u} {γ q : ℝ} (hγ0 : 0 < γ) (hγ2 : γ < 2) (hq : 0 < q)
    (hN : BallMassNegMoment.{u} γ q) (m : ℕ) :
    ∃ C : ℝ≥0, ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (hC : Ω → (ℂ → ℝ) → ℝ)
      (hcirc : Ω → ℝ → ℂ → ℝ) (μ : Ω → Measure ℂ),
      IsWholePlaneGFF P hC hcirc → IsLQGMeasure P γ hcirc μ → ∀ s : ℝ, 0 < s →
        P {ω | μ ω (ball 0 (dyadicScale m)) < ENNReal.ofReal s} ≤
          C * ENNReal.ofReal (Real.sqrt s ^ q) := by
  obtain ⟨CN, hCN⟩ := hN
  obtain ⟨K, hK⟩ : ∃ K : ℝ, K = Real.exp (q * (2 + γ ^ 2 / 2) * ((m : ℝ) * Real.log 2) +
      ((m : ℝ) * Real.log 2) * (q * γ) ^ 2 / 2) := ⟨_, rfl⟩
  refine ⟨K.toNNReal + CN, ?_⟩
  intro Ω _ P hC hcirc μ hh hμ s hs
  obtain ⟨hC', hh'⟩ := isWholePlaneGFF_recentredField hh m 0
  obtain ⟨μ', hμ'⟩ := hh'.exists_isLQGMeasure hγ0 hγ2
  have hae := ae_measure_ball_eq hγ0 hμ m 0 hμ'
  have hss : 0 < Real.sqrt s := Real.sqrt_pos.2 hs
  have hY := measure_ball_zero_lt_le hγ0 hγ2 hh' hμ' hq (hCN Ω P hC' _ μ' hh' hμ') hss
  obtain ⟨ε, hε⟩ : ∃ ε : ℝ, ε = (Real.log (Real.sqrt s) + (2 + γ ^ 2 / 2) * ((m : ℝ) * Real.log 2)) / γ :=
    ⟨_, rfl⟩
  have hF := circle_le_le_exp hh m (l := q * γ) (by positivity) ε
  have hr0 := dyadicScale_pos' m
  have hlogr : Real.log (dyadicScale m) = -((m : ℝ) * Real.log 2) := by
    rw [dyadicScale, Real.log_pow, Real.log_inv]; ring
  have hsub : {ω | μ ω (ball 0 (dyadicScale m)) < ENNReal.ofReal s} ≤ᵐ[P]
      ({ω | hcirc ω (dyadicScale m) 0 ≤ ε} ∪
        {ω | μ' ω (ball 0 1) < ENNReal.ofReal (Real.sqrt s)} : Set Ω) := by
    filter_upwards [hae] with ω hω hev
    have h1 := hω 1 one_pos
    rw [mul_one] at h1
    by_contra hnot
    rw [Set.mem_union, not_or] at hnot
    have hA : ε < hcirc ω (dyadicScale m) 0 := lt_of_not_ge hnot.1
    have hB : ENNReal.ofReal (Real.sqrt s) ≤ μ' ω (ball 0 1) := le_of_not_gt hnot.2
    have hFge : ENNReal.ofReal (Real.sqrt s) ≤ dyadicFactor γ m (hcirc ω (dyadicScale m) 0) := by
      unfold dyadicFactor
      apply ENNReal.ofReal_le_ofReal
      rw [Real.rpow_def_of_pos hr0, hlogr, ← Real.exp_add]
      calc Real.sqrt s = Real.exp (Real.log (Real.sqrt s)) := (Real.exp_log hss).symm
        _ ≤ _ := by
          apply Real.exp_le_exp.2
          have h2 := (div_lt_iff₀ hγ0).1 (hε ▸ hA)
          linarith
    have hge : ENNReal.ofReal s ≤ μ ω (ball 0 (dyadicScale m)) := by
      rw [h1, ← Real.mul_self_sqrt hs.le, ENNReal.ofReal_mul (Real.sqrt_nonneg _)]
      exact mul_le_mul' hFge hB
    exact (not_lt.2 hge) hev
  calc P {ω | μ ω (ball 0 (dyadicScale m)) < ENNReal.ofReal s}
      ≤ P ({ω | hcirc ω (dyadicScale m) 0 ≤ ε} ∪
          {ω | μ' ω (ball 0 1) < ENNReal.ofReal (Real.sqrt s)}) := measure_mono_ae hsub
    _ ≤ P {ω | hcirc ω (dyadicScale m) 0 ≤ ε} +
          P {ω | μ' ω (ball 0 1) < ENNReal.ofReal (Real.sqrt s)} := measure_union_le _ _
    _ ≤ ENNReal.ofReal (K * Real.sqrt s ^ q) + CN * ENNReal.ofReal (Real.sqrt s ^ q) := by
        refine add_le_add (hF.trans (le_of_eq ?_)) hY
        congr 1
        rw [hK, Real.rpow_def_of_pos hss, ← Real.exp_add, hε]
        congr 1
        field_simp
        ring
    _ = ((K.toNNReal + CN : ℝ≥0) : ℝ≥0∞) * ENNReal.ofReal (Real.sqrt s ^ q) := by
        rw [ENNReal.ofReal_mul (by rw [hK]; exact (Real.exp_pos _).le), ENNReal.coe_add, add_mul]
        rfl

/-- **The ratio tail of concentric ball masses.** Let `γ ∈ (0, 2)`, `c > 0` and `0 < p' < p`. Given
a positive moment of order `p` of `μ(B(0, 1/4))` and negative moments of all orders of `μ(B(0, 1))`
(each uniform over whole-plane GFF models), there is `C` such that for every model and every `t ≥ 1`,
`P(t μ(B(0, c)) < μ(B(0, 1/4))) ≤ C t^{-p'}`. -/
theorem measure_mul_ball_lt_ball_le.{u} {γ p p' c : ℝ} (hγ0 : 0 < γ) (hγ2 : γ < 2) (hc : 0 < c)
    (hp'0 : 0 < p') (hp' : p' < p) (hP : BallMassPosMoment.{u} γ p)
    (hN : ∀ q : ℝ, 0 < q → BallMassNegMoment.{u} γ q) :
    ∃ C : ℝ≥0, ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (hC : Ω → (ℂ → ℝ) → ℝ)
      (hcirc : Ω → ℝ → ℂ → ℝ) (μ : Ω → Measure ℂ),
      IsWholePlaneGFF P hC hcirc → IsLQGMeasure P γ hcirc μ → ∀ t : ℝ, 1 ≤ t →
        P {ω | ENNReal.ofReal t * μ ω (ball 0 c) < μ ω (ball 0 (1 / 4))} ≤
          C * ENNReal.ofReal (t ^ (-p')) := by
  have hp0 : 0 < p := hp'0.trans hp'
  obtain ⟨θ, hθ⟩ : ∃ θ : ℝ, θ = p' / p := ⟨_, rfl⟩
  have hθ1 : θ < 1 := by rw [hθ, div_lt_one hp0]; exact hp'
  have hθp : θ * p = p' := by rw [hθ]; field_simp
  obtain ⟨q, hq⟩ : ∃ q : ℝ, q = 2 * p' / (1 - θ) := ⟨_, rfl⟩
  have hq0 : 0 < q := by rw [hq]; exact div_pos (by linarith) (by linarith)
  have hqθ : (θ - 1) * q / 2 = -p' := by
    rw [hq]
    have h1 : (1 - θ) ≠ 0 := by linarith
    field_simp
    ring
  obtain ⟨m, hm⟩ : ∃ m : ℕ, dyadicScale m ≤ c := by
    obtain ⟨m, hm⟩ := exists_pow_lt_of_lt_one hc (by norm_num : (2 : ℝ)⁻¹ < 1)
    exact ⟨m, hm.le⟩
  obtain ⟨C1, hC1⟩ := measure_ball_dyadic_lt_le hγ0 hγ2 hq0 (hN q hq0) m
  obtain ⟨CP, hCP⟩ := hP
  refine ⟨CP + C1, ?_⟩
  intro Ω _ P hC hcirc μ hh hμ t ht
  have ht0 : 0 < t := by linarith
  have htθ : t ^ θ = t * t ^ (θ - 1) := by
    have h := Real.rpow_add ht0 1 (θ - 1)
    rw [Real.rpow_one, show (1 : ℝ) + (θ - 1) = θ by ring] at h
    exact h
  have hsub : {ω | ENNReal.ofReal t * μ ω (ball 0 c) < μ ω (ball 0 (1 / 4))} ⊆
      {ω | ENNReal.ofReal (t ^ θ) ≤ μ ω (ball 0 (1 / 4))} ∪
        {ω | μ ω (ball 0 (dyadicScale m)) < ENNReal.ofReal (t ^ (θ - 1))} := by
    intro ω hev
    have hev' : ENNReal.ofReal t * μ ω (ball 0 c) < μ ω (ball 0 (1 / 4)) := hev
    by_contra hnot
    rw [Set.mem_union, not_or] at hnot
    have hA : μ ω (ball 0 (1 / 4)) < ENNReal.ofReal (t ^ θ) := lt_of_not_ge hnot.1
    have hB : ENNReal.ofReal (t ^ (θ - 1)) ≤ μ ω (ball 0 (dyadicScale m)) := le_of_not_gt hnot.2
    have hmono : μ ω (ball 0 (dyadicScale m)) ≤ μ ω (ball 0 c) :=
      measure_mono (ball_subset_ball hm)
    have hkey : ENNReal.ofReal (t ^ θ) ≤ ENNReal.ofReal t * μ ω (ball 0 c) := by
      rw [htθ, ENNReal.ofReal_mul ht0.le]
      exact mul_le_mul' le_rfl (hB.trans hmono)
    exact lt_irrefl _ ((hev'.trans hA).trans_le hkey)
  have hα : (0 : ℝ) < lqgQ γ := by unfold lqgQ; positivity
  have hM : AEMeasurable (fun ω => μ ω (ball 0 (1 / 4))) P :=
    aemeasurable_lqgMeasure_borel hγ0 hγ2 hα hh (isLQGMeasureOfField_zero hμ)
      (lqgLocality_of_gff P γ 0 hC hcirc) _ measurableSet_ball
  have hpos : 0 < t ^ p' := Real.rpow_pos_of_pos ht0 p'
  have hne0 : ENNReal.ofReal (t ^ p') ≠ 0 := (ENNReal.ofReal_pos.2 hpos).ne'
  have hA : P {ω | ENNReal.ofReal (t ^ θ) ≤ μ ω (ball 0 (1 / 4))} ≤
      CP * ENNReal.ofReal (t ^ (-p')) := by
    have hsubA : {ω | ENNReal.ofReal (t ^ θ) ≤ μ ω (ball 0 (1 / 4))} ⊆
        {ω | ENNReal.ofReal (t ^ p') ≤ μ ω (ball 0 (1 / 4)) ^ p} := by
      intro ω hω
      have h1 := ENNReal.rpow_le_rpow (show ENNReal.ofReal (t ^ θ) ≤ μ ω (ball 0 (1 / 4)) from hω)
        hp0.le
      rw [ENNReal.ofReal_rpow_of_nonneg (Real.rpow_nonneg ht0.le θ) hp0.le, ← Real.rpow_mul ht0.le,
        hθp] at h1
      exact h1
    calc P {ω | ENNReal.ofReal (t ^ θ) ≤ μ ω (ball 0 (1 / 4))}
        ≤ P {ω | ENNReal.ofReal (t ^ p') ≤ μ ω (ball 0 (1 / 4)) ^ p} := measure_mono hsubA
      _ ≤ (∫⁻ ω, μ ω (ball 0 (1 / 4)) ^ p ∂P) / ENNReal.ofReal (t ^ p') :=
          meas_ge_le_lintegral_div (hM.pow_const p) hne0 ENNReal.ofReal_ne_top
      _ ≤ CP / ENNReal.ofReal (t ^ p') := by
          gcongr
          exact hCP Ω P hC hcirc μ hh hμ
      _ = CP * ENNReal.ofReal (t ^ (-p')) := by
          rw [div_eq_mul_inv, Real.rpow_neg ht0.le, ENNReal.ofReal_inv_of_pos hpos]
  have hsq : Real.sqrt (t ^ (θ - 1)) ^ q = t ^ (-p') := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_mul (Real.rpow_nonneg ht0.le _), ← Real.rpow_mul ht0.le]
    congr 1
    rw [← hqθ]
    ring
  have hB := hC1 Ω P hC hcirc μ hh hμ (t ^ (θ - 1)) (Real.rpow_pos_of_pos ht0 _)
  rw [hsq] at hB
  calc P {ω | ENNReal.ofReal t * μ ω (ball 0 c) < μ ω (ball 0 (1 / 4))}
      ≤ P ({ω | ENNReal.ofReal (t ^ θ) ≤ μ ω (ball 0 (1 / 4))} ∪
          {ω | μ ω (ball 0 (dyadicScale m)) < ENNReal.ofReal (t ^ (θ - 1))}) := measure_mono hsub
    _ ≤ P {ω | ENNReal.ofReal (t ^ θ) ≤ μ ω (ball 0 (1 / 4))} +
          P {ω | μ ω (ball 0 (dyadicScale m)) < ENNReal.ofReal (t ^ (θ - 1))} :=
        measure_union_le _ _
    _ ≤ CP * ENNReal.ofReal (t ^ (-p')) + C1 * ENNReal.ofReal (t ^ (-p')) := add_le_add hA hB
    _ = ((CP + C1 : ℝ≥0) : ℝ≥0∞) * ENNReal.ofReal (t ^ (-p')) := by
        rw [ENNReal.coe_add, add_mul]

/-- **The ratio tail, with the moments of Gaussian multiplicative chaos.** For `γ ∈ (0, 2)`, `c > 0`,
`1 ≤ p` with `p γ² < 4` and `0 < p' < p`, there is `C` such that for every whole-plane GFF model and
every `t ≥ 1`, `P(t μ(B(0, c)) < μ(B(0, 1/4))) ≤ C t^{-p'}`. -/
theorem measure_mul_ball_lt_ball_le_of_lt.{u} {γ p p' c : ℝ} (hγ0 : 0 < γ) (hγ2 : γ < 2)
    (hc : 0 < c) (hp1 : 1 ≤ p) (hpγ : p * γ ^ 2 < 4) (hp'0 : 0 < p') (hp' : p' < p) :
    ∃ C : ℝ≥0, ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (hC : Ω → (ℂ → ℝ) → ℝ)
      (hcirc : Ω → ℝ → ℂ → ℝ) (μ : Ω → Measure ℂ),
      IsWholePlaneGFF P hC hcirc → IsLQGMeasure P γ hcirc μ → ∀ t : ℝ, 1 ≤ t →
        P {ω | ENNReal.ofReal t * μ ω (ball 0 c) < μ ω (ball 0 (1 / 4))} ≤
          C * ENNReal.ofReal (t ^ (-p')) :=
  measure_mul_ball_lt_ball_le hγ0 hγ2 hc hp'0 hp' (ballMassPosMoment_of_lt hγ0.ne' hp1 hpγ)
    (fun _ hq => ballMassNegMoment_of_lt hγ0.ne' (by nlinarith) hq)

end LQGBallMassRatioTail

end LatticeProb.LQG
