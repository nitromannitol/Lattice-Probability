import LatticeProb.LQG.LQGBallMassRatioTail
import LatticeProb.LQG.GMCCircleLaw
import LatticeProb.LQG.GMCThickPart
import LatticeProb.Analysis.LogKernel
import LatticeProb.Bonanno.QuantumZipper.Proofs.LQG.FractionalMoments

/-!
# A fractional moment of the LQG integral of a log-singular weight

Let `μ` be the `γ`-Liouville quantum gravity measure of a whole-plane Gaussian free field, normalized by
`h_1(0) = 0`, with `γ ∈ (0, 2)`. The weight `|4y|^{-γ²}` on `B(0, 1/4)` is the density that turns `μ` into the
LQG measure of the field with an added `γ`-log singularity at the origin. We show that the weighted mass
`N = ∫_{B(0,1/4)} |4y|^{-γ²} dμ(y)` has a finite moment of some positive order `p`, uniformly over the models:
`E[N^p] ≤ C`.

The proof splits `B(0, 1/4) \ {0}` into dyadic annuli. On the annulus where `2^{-k-2} < |4y| ≤ 2^{-k}`, the
weight is at most `2^{(k+2)γ²}`, so `N ≤ ∑_k 2^{(k+2)γ²} μ(B(0, 2^{-k}/4))`. For `p ≤ 1` the `p`-th power is
subadditive. By the exact dyadic scaling of the field, `μ(B(0, 2^{-k}/4)) = 2^{-k(2+γ²/2)} e^{γ h_{2^{-k}}(0)} M_k`,
where `M_k` is the mass of `B(0, 1/4)` for a recentred whole-plane field and `h_{2^{-k}}(0) ∼ N(0, k log 2)`.
The Cauchy-Schwarz inequality, the Gaussian moment generating function and Jensen's inequality (`2p ≤ 1`) with
the first moment of `M_k` give `E[μ(B(0, 2^{-k}/4))^p] ≤ C 2^{-k(p(2+γ²/2) - p²γ²)}`, and the series converges
once `pγ² < 2 - γ²/2`.

## Main results

* `ofReal_norm_rpow_le_tsum`, `setLIntegral_norm_rpow_le_tsum`: the dyadic annulus bound of the weighted mass.
* `lintegral_measure_ball_dyadic_rpow_le`: the fractional moment of `μ(B(0, 2^{-k}/4))`, uniformly over models.
* `exists_lintegral_singular_rpow_le`: `E[(∫_{B(0,1/4)} |4y|^{-γ²} dμ(y))^p] ≤ C` for some `p > 0`.
-/

open MeasureTheory ProbabilityTheory Filter Set Metric
open scoped ENNReal NNReal

namespace LatticeProb.LQG

open LatticeProb.Gauss LatticeProb.LQG.LQGDyadicScaling

namespace LQGSingularIntegralMoment

/-- The weight of the dyadic annulus with index `k`: `(2^{-(k+2)})^{-γ²}`. -/
noncomputable def annulusWeight (γ : ℝ) (k : ℕ) : ℝ≥0∞ :=
  ENNReal.ofReal (((2 : ℝ)⁻¹ ^ (k + 2)) ^ (-γ ^ 2))

/-- **Dyadic annulus bound.** For `y ∈ B(0, 1/4)`, the weight `|4y|^{-γ²}` is at most the sum over `k` of the
annulus weights of the balls `B(0, 2^{-k}/4)` that contain `y`. -/
theorem ofReal_norm_rpow_le_tsum {γ : ℝ} (hγ : 0 < γ) {y : ℂ} (hy : y ∈ ball (0 : ℂ) (1 / 4)) :
    ENNReal.ofReal (‖4 * y‖ ^ (-γ ^ 2)) ≤
      ∑' k : ℕ, (ball (0 : ℂ) (dyadicScale k * (1 / 4))).indicator (fun _ => annulusWeight γ k) y := by
  rw [mem_ball, dist_zero_right] at hy
  rcases eq_or_ne y 0 with rfl | hy0
  · have hz0 : (0 : ℝ) ^ (-γ ^ 2) = 0 := Real.zero_rpow (neg_ne_zero.2 (pow_ne_zero 2 hγ.ne'))
    rw [mul_zero, norm_zero, hz0, ENNReal.ofReal_zero]
    exact zero_le
  have hnorm : ‖4 * y‖ = 4 * ‖y‖ := by rw [norm_mul]; norm_num
  have hy0' : 0 < ‖y‖ := norm_pos_iff.2 hy0
  have hx0 : 0 < ‖4 * y‖ := by rw [hnorm]; positivity
  have hx1 : ‖4 * y‖ < 1 := by rw [hnorm]; linarith
  obtain ⟨n, hn1, hn2⟩ := exists_nat_pow_near_of_lt_one hx0 hx1.le
    (by norm_num : (0 : ℝ) < 2⁻¹) (by norm_num : (2 : ℝ)⁻¹ < 1)
  have hmem : y ∈ ball (0 : ℂ) (dyadicScale (n - 1) * (1 / 4)) := by
    rw [mem_ball, dist_zero_right, dyadicScale]
    rcases Nat.eq_zero_or_pos n with h0 | hpos
    · subst h0
      rw [Nat.zero_sub, pow_zero]
      linarith
    · have hk : n = (n - 1) + 1 := by omega
      rw [hk, pow_succ, hnorm] at hn2
      have h2 : (0 : ℝ) < (2 : ℝ)⁻¹ ^ (n - 1) := by positivity
      have h3 : (2 : ℝ)⁻¹ ^ (n - 1) * 2⁻¹ = (2 : ℝ)⁻¹ ^ (n - 1) / 2 := by ring
      linarith
  refine le_trans ?_ (ENNReal.le_tsum (n - 1))
  simp only [indicator_of_mem hmem, annulusWeight]
  apply ENNReal.ofReal_le_ofReal
  have hle : (2 : ℝ)⁻¹ ^ (n - 1 + 2) ≤ ‖4 * y‖ := by
    have : (2 : ℝ)⁻¹ ^ (n - 1 + 2) ≤ (2 : ℝ)⁻¹ ^ (n + 1) :=
      pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)
    linarith
  exact Real.rpow_le_rpow_of_nonpos (by positivity) hle (neg_nonpos.2 (sq_nonneg γ))

/-- **Annulus bound of the weighted mass.** For every measure `ν` on `ℂ`,
`∫_{B(0,1/4)} |4y|^{-γ²} dν(y) ≤ ∑_k (2^{-(k+2)})^{-γ²} ν(B(0, 2^{-k}/4))`. -/
theorem setLIntegral_norm_rpow_le_tsum {γ : ℝ} (hγ : 0 < γ) (ν : Measure ℂ) :
    ∫⁻ y in ball (0 : ℂ) (1 / 4), ENNReal.ofReal (‖4 * y‖ ^ (-γ ^ 2)) ∂ν ≤
      ∑' k : ℕ, annulusWeight γ k * ν (ball 0 (dyadicScale k * (1 / 4))) := by
  calc ∫⁻ y in ball (0 : ℂ) (1 / 4), ENNReal.ofReal (‖4 * y‖ ^ (-γ ^ 2)) ∂ν
      ≤ ∫⁻ y in ball (0 : ℂ) (1 / 4), ∑' k : ℕ,
          (ball (0 : ℂ) (dyadicScale k * (1 / 4))).indicator (fun _ => annulusWeight γ k) y ∂ν :=
        setLIntegral_mono' measurableSet_ball fun y hy => ofReal_norm_rpow_le_tsum hγ hy
    _ ≤ ∫⁻ y, ∑' k : ℕ,
          (ball (0 : ℂ) (dyadicScale k * (1 / 4))).indicator (fun _ => annulusWeight γ k) y ∂ν :=
        setLIntegral_le_lintegral _ _
    _ = ∑' k : ℕ, ∫⁻ y,
          (ball (0 : ℂ) (dyadicScale k * (1 / 4))).indicator (fun _ => annulusWeight γ k) y ∂ν :=
        lintegral_tsum fun k => (measurable_const.indicator measurableSet_ball).aemeasurable
    _ = ∑' k : ℕ, annulusWeight γ k * ν (ball 0 (dyadicScale k * (1 / 4))) := by
        congr 1
        funext k
        rw [lintegral_indicator_const measurableSet_ball]

/-- **Fractional moment of a dyadic ball mass at the origin.** For `0 < p` with `2p ≤ 1` there is `C` such that,
for every whole-plane GFF model and every `k`, `E[μ(B(0, 2^{-k}/4))^p] ≤ C (2^{-k})^{p(2+γ²/2) - p²γ²}`. -/
theorem lintegral_measure_ball_dyadic_rpow_le.{u} {γ p : ℝ} (hγ0 : 0 < γ) (hγ2 : γ < 2) (hp0 : 0 < p)
    (hp : 2 * p ≤ 1) :
    ∃ C : ℝ≥0, ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (hC : Ω → (ℂ → ℝ) → ℝ)
      (hcirc : Ω → ℝ → ℂ → ℝ) (μ : Ω → Measure ℂ),
      IsWholePlaneGFF P hC hcirc → IsLQGMeasure P γ hcirc μ → ∀ k : ℕ,
        ∫⁻ ω, μ ω (ball 0 (dyadicScale k * (1 / 4))) ^ p ∂P ≤
          C * ENNReal.ofReal (dyadicScale k ^ (p * (2 + γ ^ 2 / 2) - p ^ 2 * γ ^ 2)) := by
  obtain ⟨C1, hC1⟩ := ballMassPosMoment_of_lt.{u} hγ0.ne' le_rfl (by nlinarith : 1 * γ ^ 2 < 4)
  refine ⟨C1 ^ p, ?_⟩
  intro Ω _ P hC hcirc μ hh hμ k
  have hP := hh.isProbabilityMeasure
  obtain ⟨hC', hh'⟩ := isWholePlaneGFF_recentredField hh k 0
  obtain ⟨μ', hμ'⟩ := hh'.exists_isLQGMeasure hγ0 hγ2
  have hae := ae_measure_ball_eq hγ0 hμ k 0 hμ'
  have hlaw := hh.hasLaw_circle_dyadic k
  set X : Ω → ℝ := fun ω => hcirc ω (dyadicScale k) 0 with hX
  set v : ℝ≥0 := ((k : ℝ) * Real.log 2).toNNReal with hv_def
  have hv : (v : ℝ) = k * Real.log 2 := Real.coe_toNNReal _ (by positivity)
  have hD := dyadicScale_pos' k
  have hlogD : Real.log (dyadicScale k) = -((k : ℝ) * Real.log 2) := by
    rw [dyadicScale, Real.log_pow, Real.log_inv]; ring
  have hα : (0 : ℝ) < lqgQ γ := by unfold lqgQ; positivity
  set M : Ω → ℝ≥0∞ := fun ω => μ' ω (ball 0 (1 / 4)) with hMdef
  have hM : AEMeasurable M P :=
    aemeasurable_lqgMeasure_borel hγ0 hγ2 hα hh' (isLQGMeasureOfField_zero hμ')
      (lqgLocality_of_gff P γ 0 hC' (recentredField hcirc k 0)) _ measurableSet_ball
  set F : Ω → ℝ≥0∞ := fun ω => dyadicFactor γ k (X ω) with hFdef
  have hF : AEMeasurable F P := by
    have hmeas : Measurable fun x : ℝ => dyadicFactor γ k x := by
      unfold dyadicFactor
      exact ENNReal.measurable_ofReal.comp (measurable_const.mul
        (Real.measurable_exp.comp (measurable_const.mul measurable_id)))
    exact hmeas.comp_aemeasurable hlaw.aemeasurable
  -- the scaling identity
  have heq : ∫⁻ ω, μ ω (ball 0 (dyadicScale k * (1 / 4))) ^ p ∂P =
      ∫⁻ ω, ((fun ω => F ω ^ p) * (fun ω => M ω ^ p)) ω ∂P := by
    refine lintegral_congr_ae ?_
    filter_upwards [hae] with ω hω
    rw [hω (1 / 4) (by norm_num), ENNReal.mul_rpow_of_nonneg _ _ hp0.le]
    rfl
  -- Cauchy-Schwarz
  have hpq : (2 : ℝ).HolderConjugate 2 :=
    (Real.holderConjugate_iff_eq_conjExponent one_lt_two).2 (by norm_num)
  have hH := ENNReal.lintegral_mul_le_Lp_mul_Lq P hpq (hF.pow_const p) (hM.pow_const p)
  -- the mass factor: Jensen with `2p ≤ 1` and the first moment
  have hMbound : (∫⁻ ω, (M ω ^ p) ^ (2 : ℝ) ∂P) ^ (1 / (2 : ℝ)) ≤ (C1 : ℝ≥0∞) ^ p := by
    have h1 : ∫⁻ ω, M ω ∂P ≤ C1 := by
      have := hC1 Ω P hC' _ μ' hh' hμ'
      simpa only [ENNReal.rpow_one] using this
    have h2 : ∫⁻ ω, (M ω ^ p) ^ (2 : ℝ) ∂P = ∫⁻ ω, M ω ^ (p * 2) ∂P := by
      congr 1
      funext ω
      rw [← ENNReal.rpow_mul]
    have h3 : ∫⁻ ω, M ω ^ (p * 2) ∂P ≤ (∫⁻ ω, M ω ∂P) ^ (p * 2) :=
      QuantumZipper.FracMom.lintegral_rpow_le_rpow_lintegral hM (by positivity) (by linarith)
    calc (∫⁻ ω, (M ω ^ p) ^ (2 : ℝ) ∂P) ^ (1 / (2 : ℝ))
        ≤ ((C1 : ℝ≥0∞) ^ (p * 2)) ^ (1 / (2 : ℝ)) := by
          rw [h2]
          refine ENNReal.rpow_le_rpow (h3.trans (ENNReal.rpow_le_rpow h1 (by positivity))) (by norm_num)
      _ = (C1 : ℝ≥0∞) ^ p := by
          rw [← ENNReal.rpow_mul]
          congr 1
          ring
  -- the Gaussian factor
  set e : ℝ := p * (2 + γ ^ 2 / 2) - p ^ 2 * γ ^ 2 with he
  have hFbound : (∫⁻ ω, (F ω ^ p) ^ (2 : ℝ) ∂P) ^ (1 / (2 : ℝ)) =
      ENNReal.ofReal (dyadicScale k ^ e) := by
    have h1 : ∀ ω, (F ω ^ p) ^ (2 : ℝ) =
        ENNReal.ofReal (dyadicScale k ^ ((2 + γ ^ 2 / 2) * (p * 2))) *
          ENNReal.ofReal (Real.exp ((p * 2 * γ) * X ω)) := by
      intro ω
      have hA : 0 ≤ dyadicScale k ^ (2 + γ ^ 2 / 2) * Real.exp (γ * X ω) := by positivity
      show (dyadicFactor γ k (X ω) ^ p) ^ (2 : ℝ) = _
      rw [dyadicFactor, ← ENNReal.rpow_mul, ENNReal.ofReal_rpow_of_nonneg hA (by positivity : (0 : ℝ) ≤ p * 2),
        ← ENNReal.ofReal_mul (Real.rpow_nonneg hD.le _)]
      congr 1
      rw [Real.mul_rpow (Real.rpow_nonneg hD.le _) (Real.exp_pos _).le, ← Real.rpow_mul hD.le,
        ← Real.exp_mul, show γ * X ω * (p * 2) = p * 2 * γ * X ω by ring]
    have h2 : ∫⁻ ω, (F ω ^ p) ^ (2 : ℝ) ∂P =
        ENNReal.ofReal (dyadicScale k ^ ((2 + γ ^ 2 / 2) * (p * 2)) *
          Real.exp ((p * 2 * γ) ^ 2 * v / 2)) := by
      simp_rw [h1]
      rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
        LatticeProb.GaussTail.lintegral_ofReal_exp_mul_of_hasLaw hlaw,
        ← ENNReal.ofReal_mul (Real.rpow_nonneg hD.le _)]
    have h3 : dyadicScale k ^ ((2 + γ ^ 2 / 2) * (p * 2)) * Real.exp ((p * 2 * γ) ^ 2 * v / 2) =
        (dyadicScale k ^ e) ^ (2 : ℝ) := by
      rw [Real.rpow_def_of_pos hD, Real.rpow_def_of_pos hD, ← Real.exp_mul, ← Real.exp_add, hlogD, hv]
      congr 1
      rw [he]
      ring
    have hE0 : 0 ≤ (dyadicScale k ^ e) ^ (2 : ℝ) := by positivity
    rw [h2, h3, ENNReal.ofReal_rpow_of_nonneg hE0 (by norm_num : (0 : ℝ) ≤ 1 / 2),
      ← Real.rpow_mul (Real.rpow_nonneg hD.le e)]
    norm_num
  calc ∫⁻ ω, μ ω (ball 0 (dyadicScale k * (1 / 4))) ^ p ∂P
      = ∫⁻ ω, ((fun ω => F ω ^ p) * (fun ω => M ω ^ p)) ω ∂P := heq
    _ ≤ (∫⁻ ω, (F ω ^ p) ^ (2 : ℝ) ∂P) ^ (1 / (2 : ℝ)) *
          (∫⁻ ω, (M ω ^ p) ^ (2 : ℝ) ∂P) ^ (1 / (2 : ℝ)) := hH
    _ ≤ ENNReal.ofReal (dyadicScale k ^ e) * (C1 : ℝ≥0∞) ^ p := by
        rw [hFbound]
        exact mul_le_mul' le_rfl hMbound
    _ = ((C1 ^ p : ℝ≥0) : ℝ≥0∞) * ENNReal.ofReal (dyadicScale k ^ e) := by
        rw [ENNReal.coe_rpow_of_nonneg _ hp0.le, mul_comm]

/-- **Fractional moment of the log-singular weighted mass.** For `γ ∈ (0, 2)` there are `p > 0` and `C` such that
for every whole-plane GFF model, `E[(∫_{B(0,1/4)} |4y|^{-γ²} dμ(y))^p] ≤ C`. -/
theorem exists_lintegral_singular_rpow_le.{u} {γ : ℝ} (hγ0 : 0 < γ) (hγ2 : γ < 2) :
    ∃ p : ℝ, 0 < p ∧ ∃ C : ℝ≥0, ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ) (μ : Ω → Measure ℂ),
      IsWholePlaneGFF P hC hcirc → IsLQGMeasure P γ hcirc μ →
        ∫⁻ ω, (∫⁻ y in ball (0 : ℂ) (1 / 4), ENNReal.ofReal (‖4 * y‖ ^ (-γ ^ 2)) ∂μ ω) ^ p ∂P ≤ C := by
  have hγsq : 0 < γ ^ 2 := by positivity
  have hγ4 : γ ^ 2 < 4 := by nlinarith
  have hγne : γ ≠ 0 := hγ0.ne'
  set p : ℝ := min (1 / 2) ((4 - γ ^ 2) / (4 * γ ^ 2)) with hp
  have hp0 : 0 < p := lt_min (by norm_num) (div_pos (by linarith) (by positivity))
  have hp2 : 2 * p ≤ 1 := by linarith [min_le_left (1 / 2 : ℝ) ((4 - γ ^ 2) / (4 * γ ^ 2))]
  have hp1 : p ≤ 1 := by linarith
  have hpγ : p * γ ^ 2 ≤ (4 - γ ^ 2) / 4 := by
    calc p * γ ^ 2 ≤ (4 - γ ^ 2) / (4 * γ ^ 2) * γ ^ 2 :=
          mul_le_mul_of_nonneg_right (min_le_right _ _) hγsq.le
      _ = (4 - γ ^ 2) / 4 := by field_simp
  set β : ℝ := p * (2 - γ ^ 2 / 2 - p * γ ^ 2) with hβ
  have hβ0 : 0 < β := mul_pos hp0 (by linarith)
  obtain ⟨C0, hC0⟩ := lintegral_measure_ball_dyadic_rpow_le.{u} hγ0 hγ2 hp0 hp2
  set K : ℝ := (C0 : ℝ) * ((4 : ℝ)⁻¹) ^ (-γ ^ 2 * p) with hK
  have hK0 : 0 ≤ K := by positivity
  refine ⟨p, hp0, (K * (1 : ℝ) ^ β * (1 - (1 / 2) ^ β)⁻¹).toNNReal, ?_⟩
  intro Ω _ P hC hcirc μ hh hμ
  have hα : (0 : ℝ) < lqgQ γ := by unfold lqgQ; positivity
  have hX : ∀ k : ℕ, AEMeasurable (fun ω => μ ω (ball 0 (dyadicScale k * (1 / 4)))) P := fun k =>
    aemeasurable_lqgMeasure_borel hγ0 hγ2 hα hh (isLQGMeasureOfField_zero hμ)
      (lqgLocality_of_gff P γ 0 hC hcirc) _ measurableSet_ball
  have hw : ∀ k : ℕ, annulusWeight γ k ^ p * ((C0 : ℝ≥0∞) * ENNReal.ofReal
      (dyadicScale k ^ (p * (2 + γ ^ 2 / 2) - p ^ 2 * γ ^ 2))) =
      ENNReal.ofReal (K * (1 * (1 / 2) ^ k) ^ β) := by
    intro k
    have hDk : (0 : ℝ) < (2 : ℝ)⁻¹ ^ k := by positivity
    have hW0 : (0 : ℝ) ≤ ((2 : ℝ)⁻¹ ^ (k + 2)) ^ (-γ ^ 2) := Real.rpow_nonneg (by positivity) _
    have hreal : (((2 : ℝ)⁻¹ ^ (k + 2)) ^ (-γ ^ 2)) ^ p *
        ((C0 : ℝ) * dyadicScale k ^ (p * (2 + γ ^ 2 / 2) - p ^ 2 * γ ^ 2)) =
        K * (1 * (1 / 2) ^ k) ^ β := by
      have hsplit : (2 : ℝ)⁻¹ ^ (k + 2) = (2 : ℝ)⁻¹ ^ k * (4 : ℝ)⁻¹ := by rw [pow_add]; norm_num
      have hA : ((2 : ℝ)⁻¹ ^ k) ^ (-γ ^ 2 * p) *
          ((2 : ℝ)⁻¹ ^ k) ^ (p * (2 + γ ^ 2 / 2) - p ^ 2 * γ ^ 2) = ((2 : ℝ)⁻¹ ^ k) ^ β := by
        rw [← Real.rpow_add hDk, hβ]
        congr 1
        ring
      rw [hsplit, ← Real.rpow_mul (by positivity : (0 : ℝ) ≤ (2 : ℝ)⁻¹ ^ k * (4 : ℝ)⁻¹),
        Real.mul_rpow hDk.le (by norm_num : (0 : ℝ) ≤ (4 : ℝ)⁻¹), hK, one_mul, one_div, ← hA]
      unfold dyadicScale
      ring
    rw [annulusWeight, ENNReal.ofReal_rpow_of_nonneg hW0 hp0.le, ← ENNReal.ofReal_coe_nnreal,
      ← ENNReal.ofReal_mul (NNReal.coe_nonneg C0), ← ENNReal.ofReal_mul (Real.rpow_nonneg hW0 p), hreal]
  calc ∫⁻ ω, (∫⁻ y in ball (0 : ℂ) (1 / 4), ENNReal.ofReal (‖4 * y‖ ^ (-γ ^ 2)) ∂μ ω) ^ p ∂P
      ≤ ∫⁻ ω, (∑' k : ℕ, annulusWeight γ k * μ ω (ball 0 (dyadicScale k * (1 / 4)))) ^ p ∂P :=
        lintegral_mono fun ω => ENNReal.rpow_le_rpow (setLIntegral_norm_rpow_le_tsum hγ0 (μ ω)) hp0.le
    _ ≤ ∫⁻ ω, ∑' k : ℕ, (annulusWeight γ k * μ ω (ball 0 (dyadicScale k * (1 / 4)))) ^ p ∂P :=
        lintegral_mono fun ω => QuantumZipper.FracMom.rpow_tsum_le_tsum_rpow _ hp0 hp1
    _ = ∑' k : ℕ, ∫⁻ ω, (annulusWeight γ k * μ ω (ball 0 (dyadicScale k * (1 / 4)))) ^ p ∂P :=
        lintegral_tsum fun k => ((hX k).const_mul _).pow_const p
    _ = ∑' k : ℕ, annulusWeight γ k ^ p * ∫⁻ ω, μ ω (ball 0 (dyadicScale k * (1 / 4))) ^ p ∂P := by
        congr 1
        funext k
        simp_rw [ENNReal.mul_rpow_of_nonneg _ _ hp0.le]
        exact lintegral_const_mul' _ _ (ENNReal.rpow_ne_top_of_nonneg hp0.le ENNReal.ofReal_ne_top)
    _ ≤ ∑' k : ℕ, annulusWeight γ k ^ p * (C0 * ENNReal.ofReal
          (dyadicScale k ^ (p * (2 + γ ^ 2 / 2) - p ^ 2 * γ ^ 2))) :=
        ENNReal.tsum_le_tsum fun k => mul_le_mul' le_rfl (hC0 Ω P hC hcirc μ hh hμ k)
    _ = ∑' k : ℕ, ENNReal.ofReal (K * (1 * (1 / 2) ^ k) ^ β) := by
        congr 1
        funext k
        exact hw k
    _ = ENNReal.ofReal (K * (1 : ℝ) ^ β * (1 - (1 / 2) ^ β)⁻¹) :=
        LatticeProb.LogKernel.tsum_ofReal_mul_rpow_half_pow hK0 zero_le_one hβ0
    _ = ((K * (1 : ℝ) ^ β * (1 - (1 / 2) ^ β)⁻¹).toNNReal : ℝ≥0∞) := rfl

end LQGSingularIntegralMoment

end LatticeProb.LQG
