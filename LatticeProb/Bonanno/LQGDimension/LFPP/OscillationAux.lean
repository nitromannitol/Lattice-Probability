/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGDimension.LFPP.OscillationAux at commit 31e7483; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGDimension.LFPP.SegCombLaw
import LatticeProb.Bonanno.LQGDimension.Gaussian.ChainingBox
import LatticeProb.Bonanno.LQGDimension.Gaussian.Concentration
import Mathlib.Analysis.SpecialFunctions.Integrals.PosLogEqCircleAverage

/-!
# Helpers for node `L37` (`Draft.Oscillation37`)

## The circle-average covariance

Write `β(z) = ⨍_{∂B(z,ε)} log max(|y|, 1)` and `A(z, w) = ⨍_{x ∈ ∂B(z,ε)} log⁺ (|w - x| / ε)`.
Using mathlib's `⨍_{∂B(w,ε)} log |y - x| = log ε + log⁺ (|w - x| / ε)` we get
(`gffCircleCov_formula`)

`gffCircleCov ε z ε w = β(z) + β(w) - log ε - A(z, w)`.

Since `A(z, z) = 0` and `A(z, w) ≤ |z - w| / ε`, the increments satisfy
`Var(h_ε(z) - h_ε(w)) ≤ 2 |z - w| / ε` (`gffCircleCov_incr_le`).  For the segment average we use
`gffCircleCov ε z ε w ≤ -log |z - w| + 3 log 2` for `|z|, |w| ≤ 1`, `z ≠ w`, `ε ≤ 1`.

## Probabilistic part

* `measure_preimage_le_of_gram`: through `SegCombLaw`, probabilities of events of finite families
  of point/segment averages are probabilities under `stdGaussian` of the Gram vectors (or `0`
  when the covariance is not PSD, the law then being `δ₀`).
* `std_block_bound`: on a disc `B(g, 10ε)`, chaining (`ChainBox.chainingBox_bound`, with
  `L² = 4/ε`, `a = 20ε`, `d = 2`) plus concentration (`MaxConc.max_sub_tail_le`, `σ² = 20`) give
  `P(max_z |h_ε z - h_ε g| > t) ≤ 2 exp(-2 (t - C₀)² / (20 π²))`, `C₀ = chainConst`.
* `block_event_bound`: the same bound for the supremum over the whole disc (dense sequence,
  continuity of the paths, continuity of measures from below; no measurability needed).
* `osc_prob_le`, `osc_tendsto`: union bound over the grid `ε ℤ²` (`≤ 121 ε⁻²` points).
* `segVar_le`, `segAvg_bounded`: variance bound and Chebyshev for `⟨h_ε, ν_{[0,1]}⟩`.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set Real Metric
open scoped RealInnerProductSpace Classical

namespace LQGDimension

namespace Osc37

/-! ### The circle-average covariance -/

/-- `β(z) = ⨍_{∂B(z,ε)} log max(|y|, 1)`. -/
def betaAvg (ε : ℝ) (z : ℂ) : ℝ := circleAverage (fun y => Real.log (max ‖y‖ 1)) z ε

/-- `A(z, w) = ⨍_{x ∈ ∂B(z,ε)} log⁺ (|w - x| / ε)`. -/
def aAvg (ε : ℝ) (z w : ℂ) : ℝ := circleAverage (fun x => log⁺ (ε⁻¹ * ‖w - x‖)) z ε

lemma continuous_logMaxOne : Continuous fun y : ℂ => Real.log (max ‖y‖ 1) :=
  (continuous_norm.max continuous_const).log fun _ =>
    (lt_of_lt_of_le one_pos (le_max_right _ _)).ne'

lemma circleIntegrable_logMaxOne (c : ℂ) (R : ℝ) :
    CircleIntegrable (fun y : ℂ => Real.log (max ‖y‖ 1)) c R :=
  continuous_logMaxOne.continuousOn.circleIntegrable'

lemma circleIntegrable_posLog (ε : ℝ) (w c : ℂ) (R : ℝ) :
    CircleIntegrable (fun x : ℂ => log⁺ (ε⁻¹ * ‖w - x‖)) c R :=
  (Continuous.continuousOn (by fun_prop)).circleIntegrable'

lemma gffCircleCov_eq_circleAverage (ε δ : ℝ) (z w : ℂ) :
    gffCircleCov ε z δ w =
      circleAverage (fun x => circleAverage (fun y => gffGreen x y) w δ) z ε := by
  simp only [gffCircleCov, circleAverage, smul_eq_mul, circleMap]
  rw [intervalIntegral.integral_const_mul]
  ring

lemma circleAverage_gffGreen {ε : ℝ} (hε : 0 < ε) (x w : ℂ) :
    circleAverage (fun y => gffGreen x y) w ε =
      Real.log (max ‖x‖ 1) + betaAvg ε w - (Real.log ε + log⁺ (ε⁻¹ * ‖w - x‖)) := by
  have e : (fun y => gffGreen x y) =
      fun y => (Real.log (max ‖x‖ 1) + Real.log (max ‖y‖ 1)) - Real.log ‖y - x‖ := by
    funext y
    simp only [gffGreen]
    rw [norm_sub_rev]
    ring
  have h1 : CircleIntegrable (fun y : ℂ => Real.log (max ‖x‖ 1) + Real.log (max ‖y‖ 1)) w ε :=
    (continuous_const.add continuous_logMaxOne).continuousOn.circleIntegrable'
  rw [e, circleAverage_fun_sub h1 (circleIntegrable_log_norm_sub_const _),
    circleAverage_fun_add (circleIntegrable_const _ _ _) (circleIntegrable_logMaxOne _ _),
    circleAverage_const, circleAverage_log_norm_sub_const_eq_log_radius_add_posLog hε.ne']
  rfl

/-- `gffCircleCov ε z ε w = β(z) + β(w) - log ε - A(z, w)`. -/
theorem gffCircleCov_formula {ε : ℝ} (hε : 0 < ε) (z w : ℂ) :
    gffCircleCov ε z ε w = betaAvg ε z + betaAvg ε w - Real.log ε - aAvg ε z w := by
  rw [gffCircleCov_eq_circleAverage]
  have e : (fun x => circleAverage (fun y => gffGreen x y) w ε) =
      fun x => (Real.log (max ‖x‖ 1) + (betaAvg ε w - Real.log ε)) - log⁺ (ε⁻¹ * ‖w - x‖) := by
    funext x
    rw [circleAverage_gffGreen hε]
    ring
  have h1 : CircleIntegrable
      (fun x : ℂ => Real.log (max ‖x‖ 1) + (betaAvg ε w - Real.log ε)) z ε :=
    (continuous_logMaxOne.add continuous_const).continuousOn.circleIntegrable'
  rw [e, circleAverage_fun_sub h1 (circleIntegrable_posLog _ _ _ _),
    circleAverage_fun_add (circleIntegrable_logMaxOne _ _) (circleIntegrable_const _ _ _),
    circleAverage_const]
  simp only [betaAvg, aAvg]
  ring

lemma aAvg_self {ε : ℝ} (hε : 0 < ε) (z : ℂ) : aAvg ε z z = 0 := by
  unfold aAvg
  apply circleAverage_const_on_circle
  intro x hx
  rw [mem_sphere_iff_norm, abs_of_pos hε] at hx
  rw [norm_sub_rev, hx, inv_mul_cancel₀ hε.ne']
  simp [posLog]

lemma aAvg_le {ε : ℝ} (hε : 0 < ε) (z w : ℂ) : aAvg ε z w ≤ ‖z - w‖ / ε := by
  unfold aAvg
  apply circleAverage_mono_on_of_le_circle (circleIntegrable_posLog _ _ _ _)
  intro x hx
  rw [mem_sphere_iff_norm, abs_of_pos hε] at hx
  have h1 : ‖w - x‖ ≤ ‖z - w‖ + ε := by
    calc ‖w - x‖ = ‖(w - z) - (x - z)‖ := by rw [sub_sub_sub_cancel_right]
      _ ≤ ‖w - z‖ + ‖x - z‖ := norm_sub_le _ _
      _ = ‖z - w‖ + ε := by rw [norm_sub_rev w z, hx]
  have hy0 : 0 ≤ ε⁻¹ * ‖w - x‖ := by positivity
  rw [posLog_apply]
  apply max_le (by positivity)
  rcases hy0.eq_or_lt with h | h
  · rw [← h, Real.log_zero]
    positivity
  · calc Real.log (ε⁻¹ * ‖w - x‖) ≤ ε⁻¹ * ‖w - x‖ - 1 := Real.log_le_sub_one_of_pos h
      _ ≤ ε⁻¹ * (‖z - w‖ + ε) - 1 := by gcongr
      _ = ‖z - w‖ / ε := by field_simp; ring

/-- **Increment variance.** `C(z,z) - 2 C(z,w) + C(w,w) ≤ 2 |z - w| / ε`. -/
theorem gffCircleCov_incr_le {ε : ℝ} (hε : 0 < ε) (z w : ℂ) :
    gffCircleCov ε z ε z - 2 * gffCircleCov ε z ε w + gffCircleCov ε w ε w ≤
      2 * ‖z - w‖ / ε := by
  rw [gffCircleCov_formula hε, gffCircleCov_formula hε, gffCircleCov_formula hε, aAvg_self hε,
    aAvg_self hε]
  have h := aAvg_le hε z w
  have e : 2 * ‖z - w‖ / ε = 2 * (‖z - w‖ / ε) := by ring
  rw [e]
  linarith

lemma betaAvg_le {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) {z : ℂ} (hz : ‖z‖ ≤ 1) :
    betaAvg ε z ≤ Real.log 2 := by
  apply circleAverage_mono_on_of_le_circle (circleIntegrable_logMaxOne _ _)
  intro y hy
  rw [mem_sphere_iff_norm, abs_of_pos hε] at hy
  have : ‖y‖ ≤ 2 := by
    calc ‖y‖ = ‖(y - z) + z‖ := by rw [sub_add_cancel]
    _ ≤ ‖y - z‖ + ‖z‖ := norm_add_le _ _
    _ ≤ 2 := by rw [hy]; linarith
  exact Real.log_le_log (lt_of_lt_of_le one_pos (le_max_right _ _)) (max_le this (by norm_num))

lemma aAvg_nonneg (ε : ℝ) (z w : ℂ) : 0 ≤ aAvg ε z w :=
  circleAverage_nonneg_of_nonneg fun _ _ => posLog_nonneg

lemma aAvg_ge {ε : ℝ} (hε : 0 < ε) {z w : ℂ} (h : 2 * ε ≤ ‖z - w‖) :
    Real.log (‖z - w‖ / 2) - Real.log ε ≤ aAvg ε z w := by
  unfold aAvg
  calc Real.log (‖z - w‖ / 2) - Real.log ε
      = circleAverage (fun _ => Real.log (‖z - w‖ / 2) - Real.log ε) z ε :=
        (circleAverage_const _ z ε).symm
    _ ≤ _ := by
      apply circleAverage_mono (circleIntegrable_const _ _ _) (circleIntegrable_posLog _ _ _ _)
      intro x hx
      rw [mem_sphere_iff_norm, abs_of_pos hε] at hx
      have h1 : ‖z - w‖ ≤ ε + ‖w - x‖ := by
        calc ‖z - w‖ = ‖(z - x) + (x - w)‖ := by rw [sub_add_sub_cancel]
          _ ≤ ‖z - x‖ + ‖x - w‖ := norm_add_le _ _
          _ = ε + ‖w - x‖ := by rw [norm_sub_rev z x, hx, norm_sub_rev x w]
      have hd : 0 < ‖z - w‖ / 2 := by linarith
      have h2 : ‖z - w‖ / 2 ≤ ‖w - x‖ := by linarith
      have hwx : 0 < ‖w - x‖ := lt_of_lt_of_le hd h2
      rw [posLog_apply]
      refine le_trans ?_ (le_max_right _ _)
      rw [Real.log_mul (inv_ne_zero hε.ne') hwx.ne', Real.log_inv]
      have := Real.log_le_log hd h2
      linarith

/-- For `|z|, |w| ≤ 1`, `z ≠ w` and `ε ≤ 1`: `C(z, w) ≤ -log |z - w| + 3 log 2`. -/
theorem gffCircleCov_le_log {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) {z w : ℂ} (hz : ‖z‖ ≤ 1)
    (hw : ‖w‖ ≤ 1) (hzw : z ≠ w) :
    gffCircleCov ε z ε w ≤ -Real.log ‖z - w‖ + 3 * Real.log 2 := by
  rw [gffCircleCov_formula hε]
  have hβz := betaAvg_le hε hε1 hz
  have hβw := betaAvg_le hε hε1 hw
  have hd : 0 < ‖z - w‖ := norm_pos_iff.2 (sub_ne_zero.2 hzw)
  have hlog : Real.log (‖z - w‖ / 2) = Real.log ‖z - w‖ - Real.log 2 :=
    Real.log_div hd.ne' two_ne_zero
  have key : -Real.log ε - aAvg ε z w ≤ -Real.log (‖z - w‖ / 2) := by
    rcases le_or_gt (2 * ε) ‖z - w‖ with h | h
    · have := aAvg_ge hε h
      linarith
    · have h0 := aAvg_nonneg ε z w
      have : Real.log (‖z - w‖ / 2) ≤ Real.log ε :=
        Real.log_le_log (by positivity) (by linarith)
      linarith
  rw [hlog] at key
  linarith

/-! ### Transfer of probabilities to the Gram representation -/

open Blueprint.Draft

section Transfer

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}

/-- If `X` has law `gaussVecLaw F C` and `0 ∉ S`, then `P(X ∈ S)` is bounded by any bound on
`P(⟪v, x⟫ ∈ S)` valid for all Gram representations `v` of `C` on `F` (if `C` is not PSD, the
law is `δ₀` and `P(X ∈ S) = 0`). -/
theorem measure_preimage_le_of_gram {ι : Type*} (F : Finset ι) (C : ι → ι → ℝ)
    {X : Ω → (F → ℝ)} (hX : HasLaw X (gaussVecLaw F C) P) {S : Set (F → ℝ)}
    (hS : MeasurableSet S) (h0 : (0 : F → ℝ) ∉ S) (B : ENNReal)
    (hB : ∀ v : ι → EuclideanSpace ℝ F, (∀ i ∈ F, ∀ j ∈ F, ⟪v i, v j⟫ = C i j) →
      stdGaussian (EuclideanSpace ℝ F) {x | (fun i : F => ⟪v i, x⟫) ∈ S} ≤ B) :
    P (X ⁻¹' S) ≤ B := by
  have hmeas : Measurable fun (x : EuclideanSpace ℝ F) (i : F) => x i :=
    (PiLp.continuous_ofLp 2 (fun _ : F => ℝ)).measurable
  rw [← Measure.map_apply_of_aemeasurable hX.aemeasurable hS, hX.map_eq]
  unfold gaussVecLaw
  by_cases hC : PSDOn F C
  · obtain ⟨v, hv⟩ := exists_gram_of_psdOn F C hC
    have hM : (Matrix.of fun i j : F => C i j) = Matrix.of fun i j : F => ⟪v i, v j⟫ := by
      ext i j
      simp [hv i i.2 j j.2]
    rw [hM, ← map_gramMap_stdGaussian F v,
      Measure.map_map hmeas (gramMap F v).continuous.measurable,
      Measure.map_apply (hmeas.comp (gramMap F v).continuous.measurable) hS]
    refine le_trans (le_of_eq ?_) (hB v hv)
    congr 1
  · rw [multivariateGaussian_of_not_posSemidef _ hC, Measure.map_dirac' hmeas,
      Measure.dirac_apply' _ hS]
    have : (fun i : F => (0 : EuclideanSpace ℝ F) i) = 0 := rfl
    rw [this, Set.indicator_of_notMem h0]
    exact zero_le

end Transfer

lemma avg_point (φ : ℂ → ℝ) (z : ℂ) : SegComb.avg φ [((1 : ℝ), z, z)] = φ z := by
  simp [SegComb.avg, segAvg]

lemma circCov_point (ε : ℝ) (z w : ℂ) :
    SegComb.circCov ε [((1 : ℝ), z, z)] [((1 : ℝ), w, w)] = gffCircleCov ε z ε w := by
  simp [SegComb.circCov, segCircCov]

/-! ### Chaining on a block of radius `10 ε` -/

/-- The chaining constant `20 √5 √240`. -/
def chainConst : ℝ := 20 * √5 * √240

lemma chainConst_nonneg : 0 ≤ chainConst := by unfold chainConst; positivity

/-- Coordinates of a complex number, as a vector of `ℝ²` with the sup norm. -/
def coord (z : ℂ) : Fin 2 → ℝ := ![z.re, z.im]

lemma norm_coord_sub_le (z w : ℂ) : ‖coord z - coord w‖ ≤ ‖z - w‖ := by
  refine (pi_norm_le_iff_of_nonneg (norm_nonneg _)).2 fun i => ?_
  fin_cases i
  · simpa [coord, Real.norm_eq_abs] using Complex.abs_re_le_norm (z - w)
  · simpa [coord, Real.norm_eq_abs] using Complex.abs_im_le_norm (z - w)

lemma norm_sub_le_coord (z w : ℂ) : ‖z - w‖ ≤ 2 * ‖coord z - coord w‖ := by
  have h0 : |z.re - w.re| ≤ ‖coord z - coord w‖ := by
    simpa [coord, Real.norm_eq_abs] using norm_le_pi_norm (coord z - coord w) 0
  have h1 : |z.im - w.im| ≤ ‖coord z - coord w‖ := by
    simpa [coord, Real.norm_eq_abs] using norm_le_pi_norm (coord z - coord w) 1
  calc ‖z - w‖ ≤ |(z - w).re| + |(z - w).im| := Complex.norm_le_abs_re_add_abs_im _
    _ ≤ _ := by simp only [Complex.sub_re, Complex.sub_im]; linarith

section Std

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

/-- One-sided tail of the maximal increment on a block (chaining + concentration). -/
theorem std_block_one_sided (F : Finset ℂ) (v : ℂ → E) {g : ℂ} (hgF : g ∈ F) {ε : ℝ}
    (hε : 0 < ε) (hF : ∀ z ∈ F, ‖z - g‖ < 10 * ε)
    (hinc : ∀ i ∈ F, ∀ j ∈ F, ‖v i - v j‖ ^ 2 ≤ 2 * ‖i - j‖ / ε) {t : ℝ}
    (ht : chainConst ≤ t) :
    stdGaussian E {x | ∃ i : F, t < ⟪v i - v g, x⟫} ≤
      ENNReal.ofReal (Real.exp (-2 * (t - chainConst) ^ 2 / (π ^ 2 * 20))) := by
  have hp : ∀ i ∈ F, ∀ j ∈ F, ‖coord i - coord j‖ ≤ 20 * ε := by
    intro i hi j hj
    refine (norm_coord_sub_le i j).trans ?_
    have := hF i hi
    have := hF j hj
    calc ‖i - j‖ = ‖(i - g) - (j - g)‖ := by rw [sub_sub_sub_cancel_right]
      _ ≤ ‖i - g‖ + ‖j - g‖ := norm_sub_le _ _
      _ ≤ 20 * ε := by linarith
  have hv : ∀ i ∈ F, ∀ j ∈ F, ‖v i - v j‖ ^ 2 ≤ √(4 / ε) ^ 2 * ‖coord i - coord j‖ := by
    intro i hi j hj
    rw [Real.sq_sqrt (by positivity)]
    refine (hinc i hi j hj).trans ?_
    have := norm_sub_le_coord i j
    calc 2 * ‖i - j‖ / ε ≤ 2 * (2 * ‖coord i - coord j‖) / ε := by gcongr
      _ = 4 / ε * ‖coord i - coord j‖ := by ring
  have hEM : vecExpectedMax F (fun i => v i - v g) 0 ≤ chainConst := by
    have h := ChainBox.chainingBox_bound F coord v (Real.sqrt_nonneg _) hp hv hgF
    refine h.trans (le_of_eq ?_)
    unfold chainConst
    rw [mul_assoc (20 * √5), ← Real.sqrt_mul (by positivity)]
    congr 2
    field_simp
    norm_num
  have hσ : ∀ i ∈ F, ‖(fun i => v i - v g) i‖ ≤ √20 := by
    intro i hi
    rw [Real.le_sqrt (norm_nonneg _) (by norm_num)]
    refine (hinc i hi g hgF).trans ?_
    rw [div_le_iff₀ hε]
    have := hF i hi
    linarith
  have htail := MaxConc.max_sub_tail_le F (fun i => v i - v g) 0 (σ := √20) (by positivity) hσ
    (s := t - chainConst) (by linarith)
  rw [Real.sq_sqrt (by norm_num)] at htail
  have hsub : {x | ∃ i : F, t < ⟪v i - v g, x⟫} ⊆
      {x | t - chainConst ≤ (⨆ i : F, ⟪v i - v g, x⟫ + (0 : ℂ → ℝ) i) -
        vecExpectedMax F (fun i => v i - v g) 0} := by
    rintro x ⟨i, hi⟩
    have hle := le_ciSup (f := fun j : F => ⟪v j - v g, x⟫ + (0 : ℂ → ℝ) j)
      (Set.finite_range _).bddAbove i
    simp only [Pi.zero_apply, add_zero] at hle
    show t - chainConst ≤ (⨆ j : F, ⟪v j - v g, x⟫ + (0 : ℂ → ℝ) j) -
      vecExpectedMax F (fun i => v i - v g) 0
    simp only [Pi.zero_apply, add_zero]
    linarith
  refine (measure_mono hsub).trans ?_
  rw [← ofReal_measureReal (measure_ne_top _ _)]
  exact ENNReal.ofReal_le_ofReal htail

/-- Two-sided tail of the maximal increment on a block. -/
theorem std_block_bound (F : Finset ℂ) (v : ℂ → E) {g : ℂ} (hgF : g ∈ F) {ε : ℝ}
    (hε : 0 < ε) (hF : ∀ z ∈ F, ‖z - g‖ < 10 * ε)
    (hinc : ∀ i ∈ F, ∀ j ∈ F, ‖v i - v j‖ ^ 2 ≤ 2 * ‖i - j‖ / ε) {t : ℝ}
    (ht : chainConst ≤ t) :
    stdGaussian E {x | ∃ i : F, t < |⟪v i, x⟫ - ⟪v g, x⟫|} ≤
      ENNReal.ofReal (2 * Real.exp (-2 * (t - chainConst) ^ 2 / (π ^ 2 * 20))) := by
  have hinc' : ∀ i ∈ F, ∀ j ∈ F, ‖-v i - -v j‖ ^ 2 ≤ 2 * ‖i - j‖ / ε := by
    intro i hi j hj
    rw [neg_sub_neg, norm_sub_rev]
    exact hinc i hi j hj
  have h1 := std_block_one_sided F v hgF hε hF hinc ht
  have h2 := std_block_one_sided F (fun z => -v z) hgF hε hF hinc' ht
  have hsub : {x | ∃ i : F, t < |⟪v i, x⟫ - ⟪v g, x⟫|} ⊆
      {x | ∃ i : F, t < ⟪v i - v g, x⟫} ∪ {x | ∃ i : F, t < ⟪-v i - -v g, x⟫} := by
    rintro x ⟨i, hi⟩
    rcases lt_abs.1 hi with h | h
    · left
      exact ⟨i, by rwa [inner_sub_left]⟩
    · right
      refine ⟨i, ?_⟩
      rw [inner_sub_left, inner_neg_left, inner_neg_left]
      linarith
  have hexp : 0 ≤ Real.exp (-2 * (t - chainConst) ^ 2 / (π ^ 2 * 20)) := (Real.exp_pos _).le
  calc _ ≤ _ := measure_mono hsub
    _ ≤ _ := measure_union_le _ _
    _ ≤ _ := add_le_add h1 h2
    _ = _ := by rw [← ENNReal.ofReal_add hexp hexp, two_mul]

/-- Chebyshev for `⟪u, x⟫`. -/
lemma std_abs_inner_tail (u : E) {K : ℝ} (hK : 0 < K) :
    stdGaussian E {x | K < |⟪u, x⟫|} ≤ ENNReal.ofReal (‖u‖ ^ 2 / K ^ 2) := by
  have hm := mul_meas_ge_le_integral_of_nonneg (μ := stdGaussian E) (f := fun x => ⟪u, x⟫ ^ 2)
    (ae_of_all _ fun x => sq_nonneg _) (GaussianMax.integrable_inner_sq u) (K ^ 2)
  rw [GaussianMax.integral_inner_sq] at hm
  have hsub : {x | K < |⟪u, x⟫|} ⊆ {x | K ^ 2 ≤ ⟪u, x⟫ ^ 2} := by
    intro x hx
    simp only [Set.mem_ofPred_eq] at hx ⊢
    calc K ^ 2 ≤ |⟪u, x⟫| ^ 2 := pow_le_pow_left₀ hK.le hx.le 2
      _ = ⟪u, x⟫ ^ 2 := sq_abs _
  refine (measure_mono hsub).trans ?_
  rw [← ofReal_measureReal (measure_ne_top _ _)]
  refine ENNReal.ofReal_le_ofReal ?_
  rw [le_div_iff₀ (by positivity)]
  linarith [hm]

end Std

/-! ### The grid of blocks -/

/-- Half-width (in grid steps) of the grid covering the disc of radius `3`. -/
def gridN (ε : ℝ) : ℕ := ⌈3 / ε⌉₊ + 1

/-- The grid `ε ℤ² ∩ [-N ε, N ε]²`. -/
def grid (ε : ℝ) : Finset ℂ :=
  ((Finset.Icc (-(gridN ε : ℤ)) (gridN ε)) ×ˢ (Finset.Icc (-(gridN ε : ℤ)) (gridN ε))).image
    fun mn : ℤ × ℤ => (⟨ε * mn.1, ε * mn.2⟩ : ℂ)

lemma round_mem_Icc {ε : ℝ} (hε : 0 < ε) {x : ℝ} (hx : |x| ≤ 3) :
    round (x / ε) ∈ Finset.Icc (-(gridN ε : ℤ)) (gridN ε) ∧
      |x - ε * round (x / ε)| ≤ ε / 2 := by
  have hr := abs_sub_round (x / ε)
  constructor
  · have hxe : |x / ε| ≤ 3 / ε := by
      rw [abs_div, abs_of_pos hε]
      gcongr
    have hc : 3 / ε ≤ ⌈3 / ε⌉₊ := Nat.le_ceil _
    have hab := abs_sub_abs_le_abs_sub ((round (x / ε) : ℤ) : ℝ) (x / ε)
    rw [abs_sub_comm] at hab
    have h1 : |((round (x / ε) : ℤ) : ℝ)| < gridN ε := by
      unfold gridN
      push_cast
      linarith
    rw [abs_lt] at h1
    rw [Finset.mem_Icc]
    have h1a : -(gridN ε : ℤ) < round (x / ε) := by exact_mod_cast h1.1
    have h1b : round (x / ε) < (gridN ε : ℤ) := by exact_mod_cast h1.2
    exact ⟨h1a.le, h1b.le⟩
  · have e : x - ε * round (x / ε) = ε * (x / ε - round (x / ε)) := by
      field_simp
    rw [e, abs_mul, abs_of_pos hε]
    calc ε * |x / ε - round (x / ε)| ≤ ε * (1 / 2) := by gcongr
      _ = ε / 2 := by ring

lemma exists_grid {ε : ℝ} (hε : 0 < ε) {z : ℂ} (hz : ‖z‖ ≤ 3) :
    ∃ g ∈ grid ε, ‖z - g‖ ≤ ε := by
  obtain ⟨hm, hre⟩ := round_mem_Icc hε ((Complex.abs_re_le_norm z).trans hz)
  obtain ⟨hn, him⟩ := round_mem_Icc hε ((Complex.abs_im_le_norm z).trans hz)
  refine ⟨⟨ε * round (z.re / ε), ε * round (z.im / ε)⟩, ?_, ?_⟩
  · exact Finset.mem_image.2
      ⟨(round (z.re / ε), round (z.im / ε)), Finset.mem_product.2 ⟨hm, hn⟩, rfl⟩
  · refine (Complex.norm_le_abs_re_add_abs_im _).trans ?_
    have e1 : (z - ⟨ε * round (z.re / ε), ε * round (z.im / ε)⟩ : ℂ).re =
        z.re - ε * round (z.re / ε) := rfl
    have e2 : (z - ⟨ε * round (z.re / ε), ε * round (z.im / ε)⟩ : ℂ).im =
        z.im - ε * round (z.im / ε) := rfl
    rw [e1, e2]
    linarith

lemma card_grid_le {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) : ((grid ε).card : ℝ) ≤ 121 / ε ^ 2 := by
  have hcard : (grid ε).card ≤ (2 * gridN ε + 1) ^ 2 := by
    refine Finset.card_image_le.trans ?_
    rw [Finset.card_product, Int.card_Icc]
    have : ((gridN ε : ℤ) + 1 - -(gridN ε : ℤ)).toNat = 2 * gridN ε + 1 := by omega
    rw [this, sq]
  have hN : (gridN ε : ℝ) < 3 / ε + 2 := by
    unfold gridN
    push_cast
    have := Nat.ceil_lt_add_one (show (0 : ℝ) ≤ 3 / ε by positivity)
    linarith
  have h11 : 2 * (gridN ε : ℝ) + 1 ≤ 11 / ε := by
    have h5 : 5 ≤ 5 / ε := by rw [le_div_iff₀ hε]; linarith
    have e : 11 / ε = 2 * (3 / ε) + 5 / ε := by ring
    rw [e]
    linarith
  calc ((grid ε).card : ℝ) ≤ ((2 * gridN ε + 1) ^ 2 : ℕ) := by exact_mod_cast hcard
    _ = (2 * (gridN ε : ℝ) + 1) ^ 2 := by push_cast; ring
    _ ≤ (11 / ε) ^ 2 := by gcongr
    _ = 121 / ε ^ 2 := by ring

/-- If the oscillation exceeds `2t`, some block has an increment exceeding `t`. -/
lemma osc_event {ε : ℝ} (hε : 0 < ε) (φ : ℂ → ℝ) {t : ℝ} (h : 2 * t < osc φ (8 * ε)) :
    ∃ g ∈ grid ε, ∃ u : ℂ, ‖u - g‖ < 10 * ε ∧ t < |φ u - φ g| := by
  unfold osc at h
  have hne : {x | ∃ z w : ℂ, ‖z‖ ≤ 3 ∧ ‖w‖ ≤ 3 ∧ ‖z - w‖ ≤ 8 * ε ∧ x = |φ z - φ w|}.Nonempty :=
    ⟨_, 0, 0, by simp, by simp, by simp only [sub_self, norm_zero]; positivity, rfl⟩
  obtain ⟨x, ⟨z, w, hz, _, hzw, rfl⟩, hlt⟩ := exists_lt_of_lt_csSup hne h
  obtain ⟨g, hg, hzg⟩ := exists_grid hε hz
  refine ⟨g, hg, ?_⟩
  have htri : |φ z - φ w| ≤ |φ z - φ g| + |φ w - φ g| := by
    have := abs_sub_le (φ z) (φ g) (φ w)
    rw [abs_sub_comm (φ g) (φ w)] at this
    exact this
  by_cases h1 : t < |φ z - φ g|
  · exact ⟨z, by linarith, h1⟩
  · refine ⟨w, ?_, by linarith⟩
    calc ‖w - g‖ = ‖(w - z) + (z - g)‖ := by rw [sub_add_sub_cancel]
      _ ≤ ‖w - z‖ + ‖z - g‖ := norm_add_le _ _
      _ < 10 * ε := by rw [norm_sub_rev w z]; linarith

/-! ### The circle-average field -/

section Field

variable {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} {h : ℝ → ℂ → Ω → ℝ}

/-- Block bound for a finite set of points. -/
theorem block_finset_bound (hG : IsGFFCircleAverage h P) {ε : ℝ} (hε : 0 < ε) {g : ℂ}
    (F : Finset ℂ) (hgF : g ∈ F) (hF : ∀ z ∈ F, ‖z - g‖ < 10 * ε) {t : ℝ}
    (ht : chainConst ≤ t) :
    P {ω | ∃ z ∈ F, t < |h ε z ω - h ε g ω|} ≤
      ENNReal.ofReal (2 * Real.exp (-2 * (t - chainConst) ^ 2 / (π ^ 2 * 20))) := by
  have hX := segCombLaw Ω P h hG ε hε ℂ F (fun z => [((1 : ℝ), z, z)])
  obtain ⟨S, hSdef⟩ : ∃ S : Set (F → ℝ), S = {y | ∃ i : F, t < |y i - y ⟨g, hgF⟩|} :=
    ⟨_, rfl⟩
  have hS : MeasurableSet S := by
    rw [hSdef, Set.ofPred_exists]
    exact MeasurableSet.iUnion fun i => (isOpen_lt continuous_const
      (((continuous_apply i).sub (continuous_apply (⟨g, hgF⟩ : F))).abs)).measurableSet
  have h0 : (0 : F → ℝ) ∉ S := by
    rw [hSdef]
    rintro ⟨i, hi⟩
    simp only [Pi.zero_apply, sub_self, abs_zero] at hi
    linarith [chainConst_nonneg]
  have hset : {ω | ∃ z ∈ F, t < |h ε z ω - h ε g ω|} =
      (fun ω (i : F) => SegComb.avg (fun z => h ε z ω) [((1 : ℝ), (i : ℂ), (i : ℂ))]) ⁻¹' S := by
    rw [hSdef]
    ext ω
    constructor
    · rintro ⟨z, hz, hlt⟩
      refine ⟨⟨z, hz⟩, ?_⟩
      simpa [avg_point] using hlt
    · rintro ⟨⟨z, hz⟩, hlt⟩
      exact ⟨z, hz, by simpa [avg_point] using hlt⟩
  rw [hset]
  refine measure_preimage_le_of_gram F _ hX hS h0 _ fun v hv => ?_
  have hv' : ∀ i ∈ F, ∀ j ∈ F, ⟪v i, v j⟫ = gffCircleCov ε i ε j := fun i hi j hj =>
    (hv i hi j hj).trans (circCov_point ε i j)
  have hinc : ∀ i ∈ F, ∀ j ∈ F, ‖v i - v j‖ ^ 2 ≤ 2 * ‖i - j‖ / ε := by
    intro i hi j hj
    rw [norm_sub_sq_real, ← real_inner_self_eq_norm_sq, ← real_inner_self_eq_norm_sq,
      hv' i hi i hi, hv' i hi j hj, hv' j hj j hj]
    exact gffCircleCov_incr_le hε i j
  rw [hSdef]
  exact std_block_bound F v hgF hε hF hinc ht

/-- Block bound for the supremum over the whole open disc `B(g, 10 ε)` (by continuity, through
a dense sequence and continuity of measures from below). -/
theorem block_event_bound (hG : IsGFFCircleAverage h P) {ε : ℝ} (hε : 0 < ε) (g : ℂ) {t : ℝ}
    (ht : chainConst ≤ t) :
    P {ω | ∃ u : ℂ, ‖u - g‖ < 10 * ε ∧ t < |h ε u ω - h ε g ω|} ≤
      ENNReal.ofReal (2 * Real.exp (-2 * (t - chainConst) ^ 2 / (π ^ 2 * 20))) := by
  obtain ⟨u, hu⟩ := TopologicalSpace.exists_dense_seq ℂ
  let Fn : ℕ → Finset ℂ := fun n =>
    insert g (((Finset.range n).image u).filter fun z => ‖z - g‖ < 10 * ε)
  have hFn : ∀ n, ∀ z ∈ Fn n, ‖z - g‖ < 10 * ε := by
    intro n z hz
    rcases Finset.mem_insert.1 hz with rfl | hz
    · rw [sub_self, norm_zero]
      positivity
    · exact (Finset.mem_filter.1 hz).2
  have hmono : Monotone fun n => {ω | ∃ z ∈ Fn n, t < |h ε z ω - h ε g ω|} := by
    rintro m n hmn ω ⟨z, hz, hlt⟩
    refine ⟨z, ?_, hlt⟩
    rcases Finset.mem_insert.1 hz with rfl | hz
    · exact Finset.mem_insert_self _ _
    · refine Finset.mem_insert_of_mem (Finset.mem_filter.2 ⟨?_, (Finset.mem_filter.1 hz).2⟩)
      obtain ⟨k, hk, hkz⟩ := Finset.mem_image.1 (Finset.mem_filter.1 hz).1
      exact Finset.mem_image.2
        ⟨k, Finset.mem_range.2 (lt_of_lt_of_le (Finset.mem_range.1 hk) hmn), hkz⟩
  have hsub : {ω | ∃ u' : ℂ, ‖u' - g‖ < 10 * ε ∧ t < |h ε u' ω - h ε g ω|} ⊆
      ⋃ n, {ω | ∃ z ∈ Fn n, t < |h ε z ω - h ε g ω|} := by
    rintro ω ⟨u₀, hu₀, hlt⟩
    have hc := hG.continuous ε hε ω
    have hO : IsOpen {z : ℂ | ‖z - g‖ < 10 * ε ∧ t < |h ε z ω - h ε g ω|} :=
      (isOpen_lt (continuous_id.sub continuous_const).norm continuous_const).inter
        (isOpen_lt continuous_const ((hc.sub continuous_const).abs))
    obtain ⟨k, hk1, hk2⟩ := hu.exists_mem_open hO ⟨u₀, hu₀, hlt⟩
    refine mem_iUnion.2 ⟨k + 1, u k, ?_, hk2⟩
    exact Finset.mem_insert_of_mem (Finset.mem_filter.2
      ⟨Finset.mem_image.2 ⟨k, Finset.mem_range.2 (Nat.lt_succ_self k), rfl⟩, hk1⟩)
  calc P _ ≤ P (⋃ n, {ω | ∃ z ∈ Fn n, t < |h ε z ω - h ε g ω|}) := measure_mono hsub
    _ = ⨆ n, P {ω | ∃ z ∈ Fn n, t < |h ε z ω - h ε g ω|} := hmono.measure_iUnion
    _ ≤ _ := iSup_le fun n =>
        block_finset_bound hG hε (Fn n) (Finset.mem_insert_self _ _) (hFn n) ht

/-- Union bound over the grid. -/
theorem osc_prob_le (hG : IsGFFCircleAverage h P) {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) {t : ℝ}
    (ht : chainConst ≤ t) :
    P {ω | 2 * t < osc (fun z => h ε z ω) (8 * ε)} ≤
      ENNReal.ofReal (121 / ε ^ 2 *
        (2 * Real.exp (-2 * (t - chainConst) ^ 2 / (π ^ 2 * 20)))) := by
  have hb0 : 0 ≤ 2 * Real.exp (-2 * (t - chainConst) ^ 2 / (π ^ 2 * 20)) := by positivity
  have hsub : {ω | 2 * t < osc (fun z => h ε z ω) (8 * ε)} ⊆
      ⋃ g ∈ grid ε, {ω | ∃ u : ℂ, ‖u - g‖ < 10 * ε ∧ t < |h ε u ω - h ε g ω|} := by
    intro ω hω
    obtain ⟨g, hg, u, hu, hlt⟩ := osc_event hε (fun z => h ε z ω) hω
    exact mem_iUnion₂.2 ⟨g, hg, u, hu, hlt⟩
  calc P _ ≤ P (⋃ g ∈ grid ε, {ω | ∃ u : ℂ, ‖u - g‖ < 10 * ε ∧ t < |h ε u ω - h ε g ω|}) :=
        measure_mono hsub
    _ ≤ ∑ g ∈ grid ε, P {ω | ∃ u : ℂ, ‖u - g‖ < 10 * ε ∧ t < |h ε u ω - h ε g ω|} :=
        measure_biUnion_finset_le _ _
    _ ≤ ∑ _g ∈ grid ε, ENNReal.ofReal (2 * Real.exp (-2 * (t - chainConst) ^ 2 / (π ^ 2 * 20))) :=
        Finset.sum_le_sum fun g _ => block_event_bound hG hε g ht
    _ = ENNReal.ofReal ((grid ε).card *
          (2 * Real.exp (-2 * (t - chainConst) ^ 2 / (π ^ 2 * 20)))) := by
        rw [Finset.sum_const, nsmul_eq_mul, ENNReal.ofReal_mul (Nat.cast_nonneg _),
          ENNReal.ofReal_natCast]
    _ ≤ ENNReal.ofReal (121 / ε ^ 2 *
          (2 * Real.exp (-2 * (t - chainConst) ^ 2 / (π ^ 2 * 20)))) :=
        ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right (card_grid_le hε hε1) hb0)

/-- **Part 1 of (3.7).** `P(κ log(1/ε) < ω_ε) → 0` as `ε ↓ 0`, for every `κ > 0`. -/
theorem osc_tendsto (hG : IsGFFCircleAverage h P) {κ : ℝ} (hκ : 0 < κ) :
    Tendsto (fun ε => P {ω | κ * Real.log (1 / ε) < osc (fun z => h ε z ω) (8 * ε)})
      (𝓝[>] 0) (𝓝 0) := by
  have hchainConst0 : 0 ≤ chainConst := chainConst_nonneg
  set L₁ : ℝ := max (4 * chainConst / κ) (7680 / κ ^ 2) with hL₁
  have hL₁0 : 0 ≤ L₁ := by rw [hL₁]; exact le_max_of_le_right (by positivity)
  set ε₁ := Real.exp (-L₁) with hε₁def
  have hε₁ : 0 < ε₁ := by rw [hε₁def]; exact Real.exp_pos _
  have hε₁1 : ε₁ ≤ 1 := by rw [hε₁def]; exact Real.exp_le_one_iff.2 (by linarith)
  have hbound : ∀ ε ∈ Ioo 0 ε₁,
      P {ω | κ * Real.log (1 / ε) < osc (fun z => h ε z ω) (8 * ε)} ≤
        ENNReal.ofReal (242 * ε) := by
    rintro ε ⟨hε0, hεε₁⟩
    set L := Real.log (1 / ε) with hL
    have hLe : L = -Real.log ε := by rw [hL, one_div, Real.log_inv]
    have hLL₁ : L₁ < L := by
      have := Real.log_lt_log hε0 hεε₁
      rw [hε₁def, Real.log_exp] at this
      linarith
    have hL0 : 0 ≤ L := hL₁0.trans hLL₁.le
    have hL4 : 4 * chainConst / κ ≤ L := by rw [hL₁] at hLL₁; exact (le_max_left _ _).trans hLL₁.le
    have hL7 : 7680 / κ ^ 2 ≤ L := by rw [hL₁] at hLL₁; exact (le_max_right _ _).trans hLL₁.le
    rw [div_le_iff₀ hκ] at hL4
    rw [div_le_iff₀ (by positivity)] at hL7
    have hκL0 : 0 ≤ κ * L := mul_nonneg hκ.le hL0
    have ht : chainConst ≤ κ * L / 2 := by linarith
    have hmain := osc_prob_le hG hε0 (hεε₁.le.trans hε₁1) ht
    have h2t : 2 * (κ * L / 2) = κ * L := by ring
    rw [h2t] at hmain
    refine hmain.trans (ENNReal.ofReal_le_ofReal ?_)
    have hq : (κ * L / 4) ^ 2 ≤ (κ * L / 2 - chainConst) ^ 2 := by
      have h1 : κ * L / 4 ≤ κ * L / 2 - chainConst := by linarith
      have h0 : 0 ≤ κ * L / 4 := by linarith
      exact pow_le_pow_left₀ h0 h1 2
    have hπ : π ^ 2 ≤ 16 := by nlinarith [Real.pi_le_four, Real.pi_pos]
    have key : 3 * L ≤ 2 * (κ * L / 2 - chainConst) ^ 2 / (π ^ 2 * 20) := by
      rw [le_div_iff₀ (by positivity)]
      have a1 : 3 * L * (π ^ 2 * 20) ≤ 3 * L * (16 * 20) :=
        mul_le_mul_of_nonneg_left (by linarith) (by linarith)
      have a2 : 7680 * L ≤ κ ^ 2 * L * L := mul_le_mul_of_nonneg_right (by linarith) hL0
      have a3 : (κ * L / 4) ^ 2 = κ ^ 2 * L * L / 16 := by ring
      linarith
    have hexp : Real.exp (-2 * (κ * L / 2 - chainConst) ^ 2 / (π ^ 2 * 20)) ≤ ε ^ 3 := by
      have e1 : -2 * (κ * L / 2 - chainConst) ^ 2 / (π ^ 2 * 20) =
          -(2 * (κ * L / 2 - chainConst) ^ 2 / (π ^ 2 * 20)) := by ring
      have e2 : ε ^ 3 = Real.exp (3 * Real.log ε) := by
        rw [show (3 : ℝ) * Real.log ε = Real.log (ε ^ 3) by rw [Real.log_pow]; norm_num,
          Real.exp_log (by positivity)]
      rw [e1, e2, Real.exp_le_exp]
      linarith
    calc 121 / ε ^ 2 * (2 * Real.exp (-2 * (κ * L / 2 - chainConst) ^ 2 / (π ^ 2 * 20)))
        ≤ 121 / ε ^ 2 * (2 * ε ^ 3) := by gcongr
      _ = 242 * ε := by
        have hε0' : ε ≠ 0 := hε0.ne'
        field_simp
        ring
  have hlim : Tendsto (fun ε : ℝ => ENNReal.ofReal (242 * ε)) (𝓝[>] 0) (𝓝 0) := by
    have h1 : Tendsto (fun ε : ℝ => 242 * ε) (𝓝 0) (𝓝 0) :=
      (by fun_prop : Continuous fun ε : ℝ => 242 * ε).tendsto' 0 0 (by simp)
    have h2 : Tendsto (fun ε : ℝ => ENNReal.ofReal (242 * ε)) (𝓝[>] 0)
        (𝓝 (ENNReal.ofReal 0)) :=
      (ENNReal.tendsto_ofReal h1).mono_left nhdsWithin_le_nhds
    simpa using h2
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hlim
    (Eventually.of_forall fun _ => zero_le) ?_
  filter_upwards [Ioo_mem_nhdsGT hε₁] with ε hε
  exact hbound ε hε

/-! ### The segment average -/

lemma mul_log_ge {x : ℝ} (hx : 0 ≤ x) : x - 1 ≤ x * Real.log x := by
  rcases hx.eq_or_lt with h | h
  · rw [← h]
    simp
  · have := Real.one_sub_inv_le_log_of_pos h
    calc x - 1 = x * (1 - x⁻¹) := by field_simp
      _ ≤ x * Real.log x := mul_le_mul_of_nonneg_left this h.le

lemma intervalIntegrable_log_sub (s : ℝ) :
    IntervalIntegrable (fun s' => Real.log (s' - s)) volume 0 1 := by
  have := (intervalIntegral.intervalIntegrable_log' (a := 0 - s) (b := 1 - s)).comp_sub_right s
  simpa using this

lemma integral_neg_log_sub_le {s : ℝ} (hs : s ∈ Icc (0 : ℝ) 1) :
    ∫ s' in (0 : ℝ)..1, (-Real.log (s' - s) + 3 * Real.log 2) ≤ 2 + 3 * Real.log 2 := by
  have hneg : IntervalIntegrable (fun s' => -Real.log (s' - s)) volume 0 1 :=
    (intervalIntegrable_log_sub s).neg
  rw [intervalIntegral.integral_add hneg intervalIntegrable_const,
    intervalIntegral.integral_neg,
    intervalIntegral.integral_comp_sub_right (fun u => Real.log u) s, integral_log]
  simp only [intervalIntegral.integral_const, sub_zero, smul_eq_mul, one_mul, zero_sub,
    Real.log_neg_eq_log]
  have h1 := mul_log_ge (x := 1 - s) (by linarith [hs.2])
  have h2 := mul_log_ge (x := s) hs.1
  linarith

/-- The variance of `⟨h_ε, ν_{[0,1]}⟩` is at most `2 + 3 log 2`, for `ε ∈ (0, 1]`. -/
theorem segVar_le (hG : IsGFFCircleAverage h P) {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) :
    SegComb.circCov ε [((1 : ℝ), (0 : ℂ), (1 : ℂ))] [((1 : ℝ), (0 : ℂ), (1 : ℂ))] ≤
      2 + 3 * Real.log 2 := by
  have hc : Continuous fun p : ℝ × ℝ => gffCircleCov ε (p.1 : ℂ) ε (p.2 : ℂ) :=
    (SegLaw.continuous_gffCircleCov hG hε).comp
      (f := fun p : ℝ × ℝ => ((p.1 : ℂ), (p.2 : ℂ))) (by fun_prop)
  have e : SegComb.circCov ε [((1 : ℝ), (0 : ℂ), (1 : ℂ))] [((1 : ℝ), (0 : ℂ), (1 : ℂ))] =
      ∫ s in (0 : ℝ)..1, ∫ s' in (0 : ℝ)..1, gffCircleCov ε (s : ℂ) ε (s' : ℂ) := by
    simp [SegComb.circCov, segCircCov]
  rw [e]
  have hnorm : ∀ s ∈ Icc (0 : ℝ) 1, ‖(s : ℂ)‖ ≤ 1 := by
    intro s hs
    rw [Complex.norm_real, Real.norm_eq_abs, abs_le]
    constructor <;> linarith [hs.1, hs.2]
  have hinner : ∀ s ∈ Icc (0 : ℝ) 1,
      ∫ s' in (0 : ℝ)..1, gffCircleCov ε (s : ℂ) ε (s' : ℂ) ≤ 2 + 3 * Real.log 2 := by
    intro s hs
    have hneg : IntervalIntegrable (fun s' => -Real.log (s' - s)) volume 0 1 :=
      (intervalIntegrable_log_sub s).neg
    have hint : IntervalIntegrable (fun s' => -Real.log (s' - s) + 3 * Real.log 2) volume 0 1 :=
      hneg.add intervalIntegrable_const
    have hf : IntervalIntegrable (fun s' : ℝ => gffCircleCov ε (s : ℂ) ε (s' : ℂ)) volume 0 1 :=
      (hc.comp (Continuous.prodMk_right s)).intervalIntegrable 0 1
    refine le_trans (intervalIntegral.integral_mono_ae_restrict zero_le_one hf hint ?_)
      (integral_neg_log_sub_le hs)
    have hne : ∀ᵐ s' ∂(volume : Measure ℝ), s' ≠ s := by
      rw [ae_iff]
      simp
    filter_upwards [ae_restrict_mem measurableSet_Icc, ae_restrict_of_ae hne] with s' hs' hne'
    have hb := gffCircleCov_le_log hε hε1 (hnorm s hs) (hnorm s' hs')
      (by exact_mod_cast hne'.symm)
    have en : ‖(s : ℂ) - (s' : ℂ)‖ = |s' - s| := by
      rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs, abs_sub_comm]
    rw [en, Real.log_abs] at hb
    exact hb
  calc ∫ s in (0 : ℝ)..1, ∫ s' in (0 : ℝ)..1, gffCircleCov ε (s : ℂ) ε (s' : ℂ)
      ≤ ∫ _s in (0 : ℝ)..1, (2 + 3 * Real.log 2) :=
        intervalIntegral.integral_mono_on zero_le_one
          ((intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
            (μ := volume) (f := fun s s' : ℝ => gffCircleCov ε (s : ℂ) ε (s' : ℂ)) hc 0 1
              ).intervalIntegrable 0 1)
          intervalIntegrable_const hinner
    _ = 2 + 3 * Real.log 2 := by simp

/-- **Part 2 of (3.7).** `⟨h_ε, ν_{[0,1]}⟩ = O_P(1)` uniformly in `ε ∈ (0, 1)`. -/
theorem segAvg_bounded (hG : IsGFFCircleAverage h P) {θ : ℝ} (hθ : 0 < θ) :
    ∃ K : ℝ, ∀ ε ∈ Ioo (0 : ℝ) 1,
      P {ω | K < |segAvg (fun z => h ε z ω) 0 1|} ≤ ENNReal.ofReal θ := by
  obtain ⟨V, hVdef⟩ : ∃ V : ℝ, V = 2 + 3 * Real.log 2 := ⟨_, rfl⟩
  have hV : 0 < V := by
    rw [hVdef]
    have := Real.log_pos one_lt_two
    linarith
  refine ⟨√(V / θ) + 1, fun ε hε => ?_⟩
  obtain ⟨K, hKdef⟩ : ∃ K : ℝ, K = √(V / θ) + 1 := ⟨_, rfl⟩
  rw [← hKdef]
  have hK : 0 < K := by rw [hKdef]; positivity
  have hVK : V / K ^ 2 ≤ θ := by
    rw [div_le_iff₀ (by positivity)]
    have h1 : √(V / θ) ^ 2 = V / θ := Real.sq_sqrt (by positivity)
    have h2 : √(V / θ) ^ 2 ≤ K ^ 2 :=
      pow_le_pow_left₀ (Real.sqrt_nonneg _) (by rw [hKdef]; linarith) 2
    rw [h1, div_le_iff₀ hθ] at h2
    linarith
  have hX := segCombLaw Ω P h hG ε hε.1 Unit Finset.univ
    (fun _ => [((1 : ℝ), (0 : ℂ), (1 : ℂ))])
  obtain ⟨S, hSdef⟩ : ∃ S : Set (↥(Finset.univ : Finset Unit) → ℝ),
      S = {y | K < |y ⟨(), Finset.mem_univ _⟩|} := ⟨_, rfl⟩
  have hS : MeasurableSet S := by
    rw [hSdef]
    exact (isOpen_lt continuous_const (continuous_apply (⟨(), Finset.mem_univ _⟩ : ↥(Finset.univ : Finset Unit))).abs).measurableSet
  have h0 : (0 : ↥(Finset.univ : Finset Unit) → ℝ) ∉ S := by
    rw [hSdef]
    intro hmem
    have : K < |(0 : ↥(Finset.univ : Finset Unit) → ℝ) ⟨(), Finset.mem_univ _⟩| := hmem
    simp only [Pi.zero_apply, abs_zero] at this
    linarith
  have hset : {ω | K < |segAvg (fun z => h ε z ω) 0 1|} =
      (fun ω (_ : (Finset.univ : Finset Unit)) =>
        SegComb.avg (fun z => h ε z ω) [((1 : ℝ), (0 : ℂ), (1 : ℂ))]) ⁻¹' S := by
    rw [hSdef]
    ext ω
    simp [SegComb.avg]
  rw [hset]
  refine measure_preimage_le_of_gram _ _ hX hS h0 _ fun v hv => ?_
  have hvv := hv () (Finset.mem_univ _) () (Finset.mem_univ _)
  have hnorm : ‖v ()‖ ^ 2 ≤ V := by
    rw [← real_inner_self_eq_norm_sq, hvv]
    exact (segVar_le hG hε.1 hε.2.le).trans_eq hVdef.symm
  have hA : {x : EuclideanSpace ℝ (Finset.univ : Finset Unit) |
      (fun i : (Finset.univ : Finset Unit) => ⟪v i, x⟫) ∈ S} = {x | K < |⟪v (), x⟫|} := by
    rw [hSdef]
    rfl
  rw [hA]
  refine (std_abs_inner_tail (v ()) hK).trans (ENNReal.ofReal_le_ofReal (le_trans ?_ hVK))
  gcongr

end Field

end Osc37

end LQGDimension
