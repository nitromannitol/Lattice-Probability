import Mathlib
import LatticeProb.Gauss.GFFIncrementBound
import LatticeProb.Gauss.GFFAffineInvariance

/-!
# Covariance of observables with a small circle average of the whole-plane free field

Limits, as the radius `r → 0+`, of the covariances that appear when the law of the whole-plane Gaussian free
field is tilted by `exp (γ h_r(z))` (the approximate Palm identity of `LatticeProb.LQG.MarkedRootingApprox`):

* the variance of the circle average: `Var h_r(z) + log r → 2 log max(|z|, 1)`, with the quantitative bound
  `|Var h_r(z) + log r - 2 log max(|z|, 1)| ≤ 2 r` for every centre `z`;
* the covariance with a pairing against a test function `φ`:
  `Cov((h, φ), h_r(z)) → ∫ φ(x) wholePlaneCov x z dx`, by dominated convergence (the singularity
  `log |x - z|` is locally integrable);
* the value of this limit: `∫ φ(x) wholePlaneCov x z dx = log max(|z|,1) ∫ φ - ∫ (log |w - z| - log max(1,|w|)) φ(w) dw`.

## Main statements

* `LatticeProb.Gauss.abs_circleAverage_wholePlaneNormalization_sub_le`
* `LatticeProb.Gauss.tendsto_wholePlaneGFFCov_circle_self_add_log`
* `LatticeProb.Gauss.wholePlaneGFFCov_pairing_circle_eq`
* `LatticeProb.Gauss.tendsto_wholePlaneGFFCov_pairing_circle`
* `LatticeProb.Gauss.integral_mul_wholePlaneCov_eq`
-/

open MeasureTheory Metric Filter Topology

namespace LatticeProb.Gauss

/-- `log max(|x|, 1)` is `1`-Lipschitz (one-sided form). -/
theorem wholePlaneNormalization_sub_le (x y : ℂ) :
    wholePlaneNormalization x - wholePlaneNormalization y ≤ ‖x - y‖ := by
  unfold wholePlaneNormalization
  have hb : 1 ≤ max ‖y‖ 1 := le_max_right _ _
  have hbpos : 0 < max ‖y‖ 1 := lt_of_lt_of_le one_pos hb
  have hapos : 0 < max ‖x‖ 1 := lt_of_lt_of_le one_pos (le_max_right _ _)
  have hd : 0 ≤ ‖x - y‖ := norm_nonneg _
  have ha : max ‖x‖ 1 ≤ max ‖y‖ 1 + ‖x - y‖ :=
    max_le (by linarith [norm_sub_norm_le x y, le_max_left ‖y‖ 1]) (by linarith)
  rw [← Real.log_div hapos.ne' hbpos.ne']
  refine (Real.log_le_sub_one_of_pos (div_pos hapos hbpos)).trans ?_
  rw [div_sub_one hbpos.ne', div_le_iff₀ hbpos]
  nlinarith

/-- `log max(|x|, 1)` is `1`-Lipschitz. -/
theorem abs_wholePlaneNormalization_sub_le (x y : ℂ) :
    |wholePlaneNormalization x - wholePlaneNormalization y| ≤ ‖x - y‖ := by
  rw [abs_le]
  refine ⟨?_, wholePlaneNormalization_sub_le x y⟩
  have h := wholePlaneNormalization_sub_le y x
  rw [norm_sub_rev] at h
  linarith

/-- The circle average of `log max(|·|, 1)` over `∂B_r(z)` is within `r` of its value at the centre. -/
theorem abs_circleAverage_wholePlaneNormalization_sub_le {r : ℝ} (hr : 0 < r) (z : ℂ) :
    |Real.circleAverage wholePlaneNormalization z r - wholePlaneNormalization z| ≤ r := by
  have hint : CircleIntegrable wholePlaneNormalization z r :=
    continuous_wholePlaneNormalization.continuousOn.circleIntegrable hr.le
  have hdist : ∀ x ∈ sphere z |r|, ‖x - z‖ = r := fun x hx =>
    (mem_sphere_iff_norm.1 hx).trans (abs_of_pos hr)
  rw [abs_le]
  constructor
  · have h := Real.circleAverage_mono (c := z) (R := r)
      (f₁ := fun _ : ℂ => wholePlaneNormalization z - r) (f₂ := wholePlaneNormalization)
      continuous_const.continuousOn.circleIntegrable' hint (fun x hx => by
        have h1 := abs_wholePlaneNormalization_sub_le x z
        rw [hdist x hx, abs_le] at h1
        show wholePlaneNormalization z - r ≤ wholePlaneNormalization x
        linarith [h1.1])
    rw [Real.circleAverage_const] at h
    linarith
  · have h := Real.circleAverage_mono_on_of_le_circle (c := z) (R := r) (f := wholePlaneNormalization)
      (a := wholePlaneNormalization z + r) hint (fun x hx => by
        have h1 := abs_wholePlaneNormalization_sub_le x z
        rw [hdist x hx, abs_le] at h1
        linarith [h1.2])
    linarith

/-- The variance of the circle average `h_r(z)`, shifted by `log r`, is within `2 r` of `2 log max(|z|, 1)`. -/
theorem abs_wholePlaneGFFCov_circle_self_add_log_sub_le {r : ℝ} (hr : 0 < r) (z : ℂ) :
    |wholePlaneGFFCov (.circle r z) (.circle r z) + Real.log r - 2 * wholePlaneNormalization z| ≤ 2 * r := by
  rw [wholePlaneGFFCov_circle_self_eq_sub_log hr z]
  have h := abs_circleAverage_wholePlaneNormalization_sub_le hr z
  have e : Real.circleAverage logMaxAbs z r = Real.circleAverage wholePlaneNormalization z r := rfl
  rw [e]
  rw [abs_le] at h ⊢
  constructor <;> linarith [h.1, h.2]

/-- `Var h_r(z) + log r → 2 log max(|z|, 1)` as `r → 0+`. -/
theorem tendsto_wholePlaneGFFCov_circle_self_add_log (z : ℂ) :
    Tendsto (fun r : ℝ => wholePlaneGFFCov (.circle r z) (.circle r z) + Real.log r) (𝓝[>] 0)
      (𝓝 (2 * wholePlaneNormalization z)) := by
  rw [tendsto_iff_dist_tendsto_zero]
  refine squeeze_zero' (Eventually.of_forall fun _ => dist_nonneg) ?_ (g := fun r : ℝ => 2 * r) ?_
  · filter_upwards [self_mem_nhdsWithin] with r hr
    rw [Real.dist_eq]
    exact abs_wholePlaneGFFCov_circle_self_add_log_sub_le hr z
  · have h : Tendsto (fun r : ℝ => 2 * r) (𝓝[>] 0) (𝓝 (2 * 0)) :=
      (tendsto_id.const_mul 2).mono_left nhdsWithin_le_nhds
    simpa using h

/-- The covariance of the pairing `(h, φ)` with the circle average `h_r(z)`: the kernel integrated against `φ`
with the circle averaged in the second variable. -/
theorem wholePlaneGFFCov_pairing_circle_eq (φ : ℂ → ℝ) {r : ℝ} (hr : 0 < r) (z : ℂ) :
    wholePlaneGFFCov (.pairing φ) (.circle r z) =
      ∫ x, φ x * (wholePlaneNormalization x + Real.circleAverage wholePlaneNormalization z r -
        Real.log (max r ‖z - x‖)) := by
  show ∫ x, φ x * Real.circleAverage (fun y => wholePlaneCov x y) z r = _
  refine integral_congr_ae (Eventually.of_forall fun x => ?_)
  show φ x * Real.circleAverage (fun y => wholePlaneCov x y) z r = _
  rw [circleAverage_wholePlaneCov_eq hr z x]

/-- Off the diagonal, `wholePlaneCov x z = log max(|x|,1) + log max(|z|,1) - log |z - x|`. -/
theorem wholePlaneCov_eq_normalization_add {x z : ℂ} (h : x ≠ z) :
    wholePlaneCov x z = wholePlaneNormalization x + wholePlaneNormalization z - Real.log ‖z - x‖ := by
  rw [GFFCovSymm.wholePlaneCov_eq_log_sub h, norm_sub_rev]
  rfl

/-- For `0 < r ≤ 1` and `t > 0`: `|log max(r, t)| ≤ |log t|`. -/
theorem abs_log_max_le_abs_log {r t : ℝ} (hr : 0 < r) (hr1 : r ≤ 1) (ht : 0 < t) :
    |Real.log (max r t)| ≤ |Real.log t| := by
  rcases le_total r t with h | h
  · rw [max_eq_right h]
  · rw [max_eq_left h]
    have h1 : Real.log r ≤ 0 := Real.log_nonpos hr.le hr1
    have h2 : Real.log t ≤ Real.log r := Real.log_le_log ht h
    rw [abs_of_nonpos h1, abs_of_nonpos (h2.trans h1)]
    linarith

/-- **Covariance with a small circle average.** For a test function `φ` and a point `z`, the covariance of the
pairing `(h, φ)` with the circle average `h_r(z)` converges, as `r → 0+`, to `∫ φ(x) Cov(h(x), h(z)) dx`. -/
theorem tendsto_wholePlaneGFFCov_pairing_circle {φ : ℂ → ℝ} (hφ : IsTestFunction Set.univ φ) (z : ℂ) :
    Tendsto (fun r : ℝ => wholePlaneGFFCov (.pairing φ) (.circle r z)) (𝓝[>] 0)
      (𝓝 (∫ x, φ x * wholePlaneCov x z)) := by
  have hφc : Continuous φ := hφ.1.continuous
  obtain ⟨R, hR⟩ := (isBounded_iff_subset_closedBall (0 : ℂ)).1 hφ.2.1.isCompact.isBounded
  have hRφ : ∀ x, φ x ≠ 0 → ‖x‖ ≤ R := fun x hx => by
    have := hR (subset_tsupport φ (Function.mem_support.2 hx))
    simpa using this
  have hint1 : Integrable (fun x => φ x * Real.log ‖x - z‖) :=
    LatticeProb.LQG.AffineDerived.integrable_mul_log_norm_sub hφ hRφ z
  have hcs : HasCompactSupport (fun x : ℂ => |φ x|) := hφ.2.1.comp_left (g := abs) abs_zero
  have hint2 : Integrable (fun x => |φ x| * (wholePlaneNormalization x + (wholePlaneNormalization z + 1))) := by
    refine Continuous.integrable_of_hasCompactSupport ?_ (hcs.mul_right)
    exact hφc.abs.mul (continuous_wholePlaneNormalization.add continuous_const)
  have hbound : Integrable (fun x => |φ x| * (wholePlaneNormalization x + (wholePlaneNormalization z + 1)) +
      |φ x * Real.log ‖x - z‖|) := hint2.add hint1.abs
  have hnn : ∀ x, 0 ≤ wholePlaneNormalization x := fun x =>
    Real.log_nonneg (le_max_right _ _)
  set F : ℝ → ℂ → ℝ := fun r x => φ x * (wholePlaneNormalization x +
    Real.circleAverage wholePlaneNormalization z r - Real.log (max r ‖z - x‖)) with hF
  have hmain : Tendsto (fun r : ℝ => ∫ x, F r x) (𝓝[>] 0) (𝓝 (∫ x, φ x * wholePlaneCov x z)) := by
    refine tendsto_integral_filter_of_dominated_convergence _ ?_ ?_ hbound ?_
    · filter_upwards [self_mem_nhdsWithin] with r hr
      have hcont : Continuous (F r) := by
        refine hφc.mul ((continuous_wholePlaneNormalization.add continuous_const).sub ?_)
        exact (continuous_const.max (continuous_const.sub continuous_id).norm).log
          (fun x => (lt_of_lt_of_le hr (le_max_left _ _)).ne')
      exact hcont.aestronglyMeasurable
    · filter_upwards [Ioo_mem_nhdsGT one_pos] with r hr
      filter_upwards [(Set.countable_singleton z).ae_notMem volume] with x hx
      have hxz : x ≠ z := by simpa using hx
      have ht : 0 < ‖z - x‖ := norm_pos_iff.2 (sub_ne_zero.2 hxz.symm)
      have hA := abs_circleAverage_wholePlaneNormalization_sub_le hr.1 z
      have hA' : |Real.circleAverage wholePlaneNormalization z r| ≤ wholePlaneNormalization z + 1 := by
        rw [abs_le] at hA ⊢
        constructor <;> linarith [hA.1, hA.2, hr.2, hnn z]
      have hL := abs_log_max_le_abs_log hr.1 hr.2.le ht
      simp only [hF, Real.norm_eq_abs, abs_mul]
      rw [norm_sub_rev z x] at hL ht ⊢
      have habs : |wholePlaneNormalization x + Real.circleAverage wholePlaneNormalization z r -
          Real.log (max r ‖x - z‖)| ≤ wholePlaneNormalization x + (wholePlaneNormalization z + 1) +
            |Real.log ‖x - z‖| := by
        calc _ ≤ |wholePlaneNormalization x + Real.circleAverage wholePlaneNormalization z r| +
              |Real.log (max r ‖x - z‖)| := abs_sub _ _
          _ ≤ |wholePlaneNormalization x| + |Real.circleAverage wholePlaneNormalization z r| +
              |Real.log (max r ‖x - z‖)| := by gcongr; exact abs_add_le _ _
          _ ≤ _ := by rw [abs_of_nonneg (hnn x)]; linarith
      calc |φ x| * |wholePlaneNormalization x + Real.circleAverage wholePlaneNormalization z r -
            Real.log (max r ‖x - z‖)|
          ≤ |φ x| * (wholePlaneNormalization x + (wholePlaneNormalization z + 1) +
            |Real.log ‖x - z‖|) := by gcongr
        _ = |φ x| * (wholePlaneNormalization x + (wholePlaneNormalization z + 1)) +
            |φ x| * |Real.log ‖x - z‖| := by ring
    · filter_upwards [(Set.countable_singleton z).ae_notMem volume] with x hx
      have hxz : x ≠ z := by simpa using hx
      have ht : 0 < ‖z - x‖ := norm_pos_iff.2 (sub_ne_zero.2 hxz.symm)
      have hA : Tendsto (fun r : ℝ => Real.circleAverage wholePlaneNormalization z r) (𝓝[>] 0)
          (𝓝 (wholePlaneNormalization z)) := by
        rw [tendsto_iff_dist_tendsto_zero]
        refine squeeze_zero' (Eventually.of_forall fun _ => dist_nonneg) ?_ (g := fun r : ℝ => r) ?_
        · filter_upwards [self_mem_nhdsWithin] with r hr
          rw [Real.dist_eq]
          exact abs_circleAverage_wholePlaneNormalization_sub_le hr z
        · exact (tendsto_id (α := ℝ)).mono_left (nhdsWithin_le_nhds (a := (0 : ℝ)) (s := Set.Ioi 0))
      have hM : Tendsto (fun r : ℝ => Real.log (max r ‖z - x‖)) (𝓝[>] 0) (𝓝 (Real.log ‖z - x‖)) := by
        have h0 : Tendsto (fun r : ℝ => max r ‖z - x‖) (𝓝 0) (𝓝 (max 0 ‖z - x‖)) :=
          (continuous_id.max continuous_const).tendsto 0
        rw [max_eq_right ht.le] at h0
        exact (h0.log ht.ne').mono_left nhdsWithin_le_nhds
      have hlim := (tendsto_const_nhds (x := wholePlaneNormalization x)).add hA |>.sub hM
      have hlim2 := hlim.const_mul (φ x)
      have hval : φ x * wholePlaneCov x z = φ x * (wholePlaneNormalization x + wholePlaneNormalization z -
          Real.log ‖z - x‖) := by rw [wholePlaneCov_eq_normalization_add hxz]
      rw [hval]
      exact hlim2
  refine hmain.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with r hr
  exact (wholePlaneGFFCov_pairing_circle_eq φ hr z).symm

/-- **Value of the limit.** For a test function `φ`,
`∫ φ(x) Cov(h(x), h(z)) dx = log max(|z|,1) ∫ φ - ∫ (log |w - z| - log max(1,|w|)) φ(w) dw`;
in particular the two agree up to sign when `∫ φ = 0`. -/
theorem integral_mul_wholePlaneCov_eq {φ : ℂ → ℝ} (hφ : IsTestFunction Set.univ φ) (z : ℂ) :
    ∫ x, φ x * wholePlaneCov x z =
      Real.log (max ‖z‖ 1) * (∫ x, φ x) -
        ∫ w, (Real.log ‖w - z‖ - Real.log (max 1 ‖w‖)) * φ w := by
  have hφc : Continuous φ := hφ.1.continuous
  obtain ⟨R, hR⟩ := (isBounded_iff_subset_closedBall (0 : ℂ)).1 hφ.2.1.isCompact.isBounded
  have hRφ : ∀ x, φ x ≠ 0 → ‖x‖ ≤ R := fun x hx => by
    have := hR (subset_tsupport φ (Function.mem_support.2 hx))
    simpa using this
  have hint1 : Integrable (fun x => φ x * Real.log ‖x - z‖) :=
    LatticeProb.LQG.AffineDerived.integrable_mul_log_norm_sub hφ hRφ z
  have hint0 : Integrable φ := hφc.integrable_of_hasCompactSupport hφ.2.1
  have hintN : Integrable (fun x => φ x * wholePlaneNormalization x) :=
    (hφc.mul continuous_wholePlaneNormalization).integrable_of_hasCompactSupport hφ.2.1.mul_right
  have hae : ∀ᵐ x : ℂ, φ x * wholePlaneCov x z =
      (φ x * wholePlaneNormalization x + wholePlaneNormalization z * φ x) - φ x * Real.log ‖x - z‖ := by
    filter_upwards [(Set.countable_singleton z).ae_notMem volume] with x hx
    have hxz : x ≠ z := by simpa using hx
    rw [wholePlaneCov_eq_normalization_add hxz, norm_sub_rev z x]
    ring
  have h1 : Integrable (fun x => φ x * wholePlaneNormalization x + wholePlaneNormalization z * φ x) :=
    hintN.add (hint0.const_mul _)
  rw [integral_congr_ae hae, integral_sub h1 hint1, integral_add hintN (hint0.const_mul _),
    integral_const_mul]
  have e : ∫ w, (Real.log ‖w - z‖ - Real.log (max 1 ‖w‖)) * φ w =
      (∫ x, φ x * Real.log ‖x - z‖) - ∫ x, φ x * wholePlaneNormalization x := by
    rw [← integral_sub hint1 hintN]
    refine integral_congr_ae (Eventually.of_forall fun w => ?_)
    show _ = φ w * Real.log ‖w - z‖ - φ w * Real.log (max ‖w‖ 1)
    rw [max_comm]
    ring
  have hz : wholePlaneNormalization z = Real.log (max ‖z‖ 1) := rfl
  rw [e, hz]
  ring

end LatticeProb.Gauss
