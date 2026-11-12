import Mathlib

/-!
# Smooth approximation of compactly supported Lipschitz functions on the plane

A locally Lipschitz function `g : ℂ → ℝ` of compact support is globally Lipschitz.
Convolution with a normalized smooth bump function of small radius gives smooth functions of compact
support, with the same Lipschitz constant, uniformly close to `g`, supported in a fixed ball.

* `LatticeProb.exists_lipschitzWith_of_locallyLipschitz`: global Lipschitz bound;
* `LatticeProb.exists_smooth_approx_of_lipschitz`: mollification of a Lipschitz function;
* `LatticeProb.exists_smooth_approx_of_locallyLipschitz`: the gradient of the mollifications is bounded
  by a constant independent of the accuracy, and their supports lie in a fixed closed ball.
-/

namespace LatticeProb

open MeasureTheory Metric Set

/-- A locally Lipschitz function of compact support on the plane is Lipschitz. -/
theorem exists_lipschitzWith_of_locallyLipschitz {g : ℂ → ℝ} (hg : LocallyLipschitz g)
    (hc : HasCompactSupport g) : ∃ K : NNReal, LipschitzWith K g := by
  obtain ⟨R0, hR0⟩ := hc.isCompact.isBounded.subset_closedBall (0 : ℂ)
  obtain ⟨K, hK⟩ := LocallyLipschitzOn.exists_lipschitzOnWith_of_compact
    (isCompact_closedBall (0 : ℂ) (R0 + 1)) hg.locallyLipschitzOn
  obtain ⟨M, hM⟩ := hg.continuous.bounded_above_of_compact_support hc
  have hz : ∀ z : ℂ, R0 < ‖z‖ → g z = 0 := fun z hz =>
    image_eq_zero_of_notMem_tsupport fun h => by
      have := hR0 h
      rw [mem_closedBall_zero_iff] at this
      linarith
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM 0)
  refine ⟨max K (Real.toNNReal (2 * M)), LipschitzWith.of_dist_le_mul fun x y => ?_⟩
  have hK0 : ((max K (Real.toNNReal (2 * M)) : NNReal) : ℝ) = max (K : ℝ) (2 * M) := by
    rw [NNReal.coe_max, Real.coe_toNNReal _ (by linarith)]
  rw [hK0]
  by_cases hxy : 1 ≤ dist x y
  · have h1 : dist (g x) (g y) ≤ 2 * M := by
      rw [Real.dist_eq]
      have := hM x
      have := hM y
      rw [Real.norm_eq_abs] at *
      calc |g x - g y| ≤ |g x| + |g y| := abs_sub _ _
        _ ≤ 2 * M := by linarith
    calc dist (g x) (g y) ≤ 2 * M := h1
      _ ≤ max (K : ℝ) (2 * M) * 1 := by rw [mul_one]; exact le_max_right _ _
      _ ≤ max (K : ℝ) (2 * M) * dist x y :=
        mul_le_mul_of_nonneg_left hxy ((NNReal.coe_nonneg _).trans (le_max_left _ _))
  · rw [not_le] at hxy
    by_cases hx : x ∈ closedBall (0 : ℂ) (R0 + 1)
    · by_cases hy : y ∈ closedBall (0 : ℂ) (R0 + 1)
      · exact (hK.dist_le_mul x hx y hy).trans
          (mul_le_mul_of_nonneg_right (le_max_left _ _) dist_nonneg)
      · have hy' : R0 + 1 < ‖y‖ := by simpa [mem_closedBall_zero_iff] using hy
        have hx' : R0 < ‖x‖ := by
          have := norm_sub_norm_le y x
          rw [dist_eq_norm, norm_sub_rev] at hxy
          linarith
        rw [hz x hx', hz y (by linarith), dist_self]
        exact mul_nonneg ((NNReal.coe_nonneg _).trans (le_max_left _ _)) dist_nonneg
    · have hx' : R0 + 1 < ‖x‖ := by simpa [mem_closedBall_zero_iff] using hx
      have hy' : R0 < ‖y‖ := by
        have := norm_sub_norm_le x y
        rw [dist_eq_norm] at hxy
        linarith
      rw [hz x (by linarith), hz y hy', dist_self]
      exact mul_nonneg ((NNReal.coe_nonneg _).trans (le_max_left _ _)) dist_nonneg


/-- Mollification of a Lipschitz function on the plane: for every `ε > 0` there is a smooth function `h`
with the same Lipschitz constant, uniformly `ε`-close to `g`, vanishing at distance more than one from
the region where `g` vanishes outside. -/
theorem exists_smooth_approx_of_lipschitz {g : ℂ → ℝ} {K : NNReal} (hK : LipschitzWith K g)
    {R0 : ℝ} (hR0 : ∀ z : ℂ, R0 < ‖z‖ → g z = 0) {ε : ℝ} (hε : 0 < ε) :
    ∃ h : ℂ → ℝ, ContDiff ℝ (⊤ : ℕ∞) h ∧ LipschitzWith K h ∧ (∀ z : ℂ, R0 + 1 < ‖z‖ → h z = 0) ∧
      ∀ x, |h x - g x| ≤ ε := by
  set r : ℝ := min 1 (ε / (K + 1)) with hr_def
  have hK1 : (0 : ℝ) < K + 1 := by positivity
  have hr : 0 < r := lt_min one_pos (div_pos hε hK1)
  have hr1 : r ≤ 1 := min_le_left _ _
  let ρ : ContDiffBump (0 : ℂ) := ⟨r / 2, r, half_pos hr, half_lt_self hr⟩
  set ρn : ℂ → ℝ := ρ.normed volume with hρn
  have hρc : Continuous ρn := ρ.continuous_normed
  have hρnn : ∀ t, 0 ≤ ρn t := fun t => ρ.nonneg_normed t
  have hρint : ∫ t, ρn t = 1 := ρ.integral_normed
  have hρi : Integrable ρn := ρ.integrable_normed
  have hρsupp : ∀ t, ρn t ≠ 0 → ‖t‖ < r := fun t ht => by
    have : t ∈ Function.support ρn := ht
    rw [hρn, ρ.support_normed_eq] at this
    simpa using this
  have hgc : Continuous g := hK.continuous
  have hint : ∀ x, Integrable (fun t => ρn t * g (x - t)) := fun x =>
    (hρc.mul (hgc.comp (continuous_const.sub continuous_id))).integrable_of_hasCompactSupport
      (ρ.hasCompactSupport_normed.mul_right)
  let h : ℂ → ℝ := fun x => ∫ t, ρn t * g (x - t)
  have hh : h = MeasureTheory.convolution ρn g (ContinuousLinearMap.mul ℝ ℝ) volume := by
    funext x
    rw [MeasureTheory.convolution_def]
    rfl
  have hsmooth : ContDiff ℝ (⊤ : ℕ∞) h := by
    rw [hh]
    exact ρ.hasCompactSupport_normed.contDiff_convolution_left (ContinuousLinearMap.mul ℝ ℝ)
      ρ.contDiff_normed hgc.locallyIntegrable
  have hdiff : ∀ x y, h x - h y = ∫ t, ρn t * (g (x - t) - g (y - t)) := fun x y => by
    simp only [h]
    rw [← integral_sub (hint x) (hint y)]
    congr 1; ext t; ring
  refine ⟨h, hsmooth, ?_, ?_, ?_⟩
  · refine LipschitzWith.of_dist_le_mul fun x y => ?_
    rw [Real.dist_eq, hdiff]
    have hb : ∀ t, ‖ρn t * (g (x - t) - g (y - t))‖ ≤ ρn t * (K * dist x y) := fun t => by
      rw [norm_mul, Real.norm_of_nonneg (hρnn t), Real.norm_eq_abs]
      refine mul_le_mul_of_nonneg_left ?_ (hρnn t)
      have := hK.dist_le_mul (x - t) (y - t)
      rwa [Real.dist_eq, dist_sub_right] at this
    have := norm_integral_le_of_norm_le (hρi.mul_const ((K : ℝ) * dist x y))
      (Filter.Eventually.of_forall hb)
    rw [integral_mul_const, hρint, one_mul] at this
    simpa [Real.norm_eq_abs] using this
  · intro z hz
    show ∫ t, ρn t * g (z - t) = 0
    have : (fun t => ρn t * g (z - t)) = fun _ => 0 := by
      ext t
      by_cases ht : ρn t = 0
      · simp [ht]
      · have := hρsupp t ht
        have h2 := norm_sub_norm_le z t
        rw [hR0 (z - t) (by linarith), mul_zero]
    rw [this]; simp
  · intro x
    have hgx : g x = ∫ t, ρn t * g x := by rw [integral_mul_const, hρint, one_mul]
    have : h x - g x = ∫ t, ρn t * (g (x - t) - g x) := by
      conv_lhs => rw [hgx]
      simp only [h]
      rw [← integral_sub (hint x) (hρi.mul_const _)]
      congr 1; ext t; ring
    rw [this]
    have hb : ∀ t, ‖ρn t * (g (x - t) - g x)‖ ≤ ρn t * (K * r) := fun t => by
      rw [norm_mul, Real.norm_of_nonneg (hρnn t), Real.norm_eq_abs]
      by_cases ht : ρn t = 0
      · simp [ht]
      · refine mul_le_mul_of_nonneg_left ?_ (hρnn t)
        have := hK.dist_le_mul (x - t) x
        rw [Real.dist_eq, dist_self_sub_left] at this
        have hts := hρsupp t ht
        calc |g (x - t) - g x| ≤ K * ‖t‖ := this
          _ ≤ K * r := mul_le_mul_of_nonneg_left hts.le (NNReal.coe_nonneg _)
    have := norm_integral_le_of_norm_le (hρi.mul_const ((K : ℝ) * r))
      (Filter.Eventually.of_forall hb)
    rw [integral_mul_const, hρint, one_mul] at this
    rw [← Real.norm_eq_abs]
    refine this.trans ?_
    have hrK : r ≤ ε / (K + 1) := min_le_right _ _
    calc (K : ℝ) * r ≤ K * (ε / (K + 1)) :=
          mul_le_mul_of_nonneg_left hrK (NNReal.coe_nonneg _)
      _ ≤ ε := by
          rw [mul_div_assoc', div_le_iff₀ hK1]
          nlinarith [NNReal.coe_nonneg K]

/-- **Smooth approximation of a compactly supported locally Lipschitz function.** There are constants
`K` and `R` such that for every `ε > 0` the function `g` is uniformly within `ε` of a smooth function
`h` of compact support in `closedBall 0 R` whose gradient is bounded by `K`. -/
theorem exists_smooth_approx_of_locallyLipschitz {g : ℂ → ℝ} (hg : LocallyLipschitz g)
    (hc : HasCompactSupport g) :
    ∃ K R : ℝ, ∀ ε : ℝ, 0 < ε → ∃ h : ℂ → ℝ, ContDiff ℝ (⊤ : ℕ∞) h ∧ HasCompactSupport h ∧
      tsupport h ⊆ closedBall 0 R ∧ (∀ x, ‖fderiv ℝ h x‖ ≤ K) ∧ ∀ x, |h x - g x| ≤ ε := by
  obtain ⟨K, hK⟩ := exists_lipschitzWith_of_locallyLipschitz hg hc
  obtain ⟨R0, hR0⟩ := hc.isCompact.isBounded.subset_closedBall (0 : ℂ)
  have hz : ∀ z : ℂ, R0 < ‖z‖ → g z = 0 := fun z hz =>
    image_eq_zero_of_notMem_tsupport fun h => by
      have := hR0 h
      rw [mem_closedBall_zero_iff] at this
      linarith
  refine ⟨K, R0 + 1, fun ε hε => ?_⟩
  obtain ⟨h, hs, hl, hsupp, hclose⟩ := exists_smooth_approx_of_lipschitz hK hz hε
  have hsub : tsupport h ⊆ closedBall 0 (R0 + 1) := by
    refine closure_minimal (fun z hz' => ?_) isClosed_closedBall
    rw [mem_closedBall_zero_iff]
    by_contra hlt
    exact hz' (hsupp z (not_le.1 hlt))
  exact ⟨h, hs, IsCompact.of_isClosed_subset (isCompact_closedBall _ _) (isClosed_tsupport _) hsub,
    hsub, fun x => norm_fderiv_le_of_lipschitz ℝ hl, hclose⟩

end LatticeProb
