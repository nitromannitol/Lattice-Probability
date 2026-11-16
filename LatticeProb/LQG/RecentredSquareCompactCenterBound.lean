import LatticeProb.LQG.RecentredSquareMaximalMoment
import LatticeProb.LQG.RecentredSquareGeometry

/-! # Spatial dependence of recentred square approximations -/

open MeasureTheory Set
open scoped ENNReal
open QuantumZipper
open MatedCRTHarmonic.GMCFacts LQGMetric.DGMC LQGMetric.DGMC.Neg3

namespace LatticeProb.LQG

/-- Recentering multiplies an approximation on a fixed measurable set by the
exponential of the circle average at the center. -/
theorem lqgApprox_recentred_eq_mul {Ω : Type*} (H : ℝ → ℂ → Ω → ℝ)
    (ω : Ω) (γ : ℝ) {ε r : ℝ}
    (z : ℂ) {S : Set ℂ} (hS : MeasurableSet S) :
    lqgApprox γ (fun s w => H (ε * s) w ω - H ε z ω) (r / ε) S =
      ENNReal.ofReal (Real.exp (-γ * H ε z ω)) *
        lqgApprox γ (fun s w => H (ε * s) w ω) (r / ε) S := by
  rw [lqgApprox, lqgApprox, withDensity_apply _ hS, withDensity_apply _ hS]
  rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  apply lintegral_congr
  intro w
  rw [← ENNReal.ofReal_mul (Real.exp_nonneg _)]
  congr 1
  have he : Real.exp (γ * (H (ε * (r / ε)) w ω - H ε z ω)) =
      Real.exp (-γ * H ε z ω) * Real.exp (γ * H (ε * (r / ε)) w ω) := by
    rw [← Real.exp_add]
    congr 1
    ring
  rw [he]
  ring

/-- For each fixed measurable set the recentred approximation is continuous
in the recentering point whenever the circle averages are spatially continuous. -/
theorem continuous_lqgApprox_recentred_fixed_set {Ω : Type*}
    [MeasurableSpace Ω] {P : Measure Ω} {H : ℝ → ℂ → Ω → ℝ}
    (hH : LQGDimension.IsGFFCircleAverage H P) (ω : Ω) (γ : ℝ)
    {ε r : ℝ} (hε : 0 < ε) {S : Set ℂ} (hS : MeasurableSet S)
    (hfinite : lqgApprox γ (fun s w => H (ε * s) w ω) (r / ε) S ≠ ⊤) :
    Continuous (fun z => lqgApprox γ (fun s w => H (ε * s) w ω - H ε z ω)
      (r / ε) S) := by
  simp_rw [lqgApprox_recentred_eq_mul H ω γ _ hS]
  apply (ENNReal.continuous_mul_const hfinite).comp
  exact ENNReal.continuous_ofReal.comp (Real.continuous_exp.comp
    (continuous_const.mul (hH.continuous ε hε ω)))

/-- A bounded set has finite approximation mass for the same field. -/
theorem lqgApprox_rescaled_apply_ne_top_of_isBounded {Ω : Type*}
    [MeasurableSpace Ω] {P : Measure Ω} {H : ℝ → ℂ → Ω → ℝ}
    (hH : LQGDimension.IsGFFCircleAverage H P) (ω : Ω) (γ : ℝ)
    {ε r : ℝ} (hε : 0 < ε) (hr : 0 < r) {S : Set ℂ}
    (hS : Bornology.IsBounded S) :
    lqgApprox γ (fun s w => H (ε * s) w ω) (r / ε) S ≠ ⊤ := by
  have hc : Continuous (fun w => H (ε * (r / ε)) w ω) := by
    rw [mul_div_cancel₀ r hε.ne']
    exact hH.continuous r hr ω
  let : IsLocallyFiniteMeasure (lqgApprox γ (fun s w => H (ε * s) w ω) (r / ε)) := by
    unfold lqgApprox
    exact IsLocallyFiniteMeasure.withDensity_ofReal
      (continuous_const.mul (Real.continuous_exp.comp (continuous_const.mul hc)))
  exact hS.measure_lt_top.ne

/-- The same approximation on a fixed bounded measurable set is continuous
in the recentering point. -/
theorem continuous_lqgApprox_recentred_of_isBounded {Ω : Type*}
    [MeasurableSpace Ω] {P : Measure Ω} {H : ℝ → ℂ → Ω → ℝ}
    (hH : LQGDimension.IsGFFCircleAverage H P) (ω : Ω) (γ : ℝ)
    {ε r : ℝ} (hε : 0 < ε) (hr : 0 < r) {S : Set ℂ}
    (hS : MeasurableSet S) (hbounded : Bornology.IsBounded S) :
    Continuous (fun z => lqgApprox γ (fun s w => H (ε * s) w ω - H ε z ω)
      (r / ε) S) :=
  continuous_lqgApprox_recentred_fixed_set hH ω γ hε hS
    (lqgApprox_rescaled_apply_ne_top_of_isBounded hH ω γ hε hr hbounded)

/-- A set containing a centered square bounds its normalized recentred mass. -/
theorem normalized_recentred_square_mass_le_of_subset {Ω : Type*}
    (H : ℝ → ℂ → Ω → ℝ) (γ : ℝ) (z : ℂ) (m k : ℕ) (ω : Ω)
    {S : Set ℂ} (hS : MeasurableSet S)
    (hsub : sqQ (sqCorner z (radius m)) m ⊆ S) :
    normalizedRecentredSquareMass H γ z m k ω ≤
      ENNReal.ofReal ((2 * radius m)⁻¹ ^ 2) *
        (ENNReal.ofReal (Real.exp (-γ * H (2 * radius m) z ω)) *
          lqgApprox γ (fun s w => H (2 * radius m * s) w ω)
            (radius (m + k) / (2 * radius m)) S) := by
  unfold normalizedRecentredSquareMass
  gcongr
  calc
    _ ≤ lqgApprox γ (fun s w => H (2 * radius m * s) w ω -
        H (2 * radius m) z ω) (radius (m + k) / (2 * radius m)) S := measure_mono hsub
    _ = _ := lqgApprox_recentred_eq_mul H ω γ z hS

/-- On a compact set of centers, every fixed level of the normalized
recentred square approximation is bounded simultaneously. -/
theorem exists_compact_bound_normalized_recentred_square_mass {Ω : Type*}
    [MeasurableSpace Ω] {P : Measure Ω} {H : ℝ → ℂ → Ω → ℝ}
    (hH : LQGDimension.IsGFFCircleAverage H P) (ω : Ω) (γ : ℝ)
    (K : Set ℂ) (hK : IsCompact K) (m k : ℕ) :
    ∃ C : ℝ≥0∞, C < ⊤ ∧ ∀ z ∈ K,
      normalizedRecentredSquareMass H γ z m k ω ≤ C := by
  obtain ⟨R, hR⟩ := Metric.isBounded_iff_subset_ball (0 : ℂ) |>.1 hK.isBounded
  let S : Set ℂ := Metric.closedBall 0 (R + radius m)
  have hS : MeasurableSet S := Metric.isClosed_closedBall.measurableSet
  have hsub : ∀ z ∈ K, sqQ (sqCorner z (radius m)) m ⊆ S := by
    intro z hz w hw
    have hz' : ‖z‖ < R := by simpa [Metric.mem_ball, dist_zero_right] using hR hz
    have hw' := norm_sub_le_of_mem_centred_sqQ z m hw
    show w ∈ Metric.closedBall 0 (R + radius m)
    rw [Metric.mem_closedBall, dist_zero_right]
    calc
      ‖w‖ = ‖(w - z) + z‖ := by rw [sub_add_cancel]
      _ ≤ ‖w - z‖ + ‖z‖ := norm_add_le _ _
      _ ≤ R + radius m := by linarith
  have hε : 0 < 2 * radius m := mul_pos (by norm_num) (radius_pos m)
  have hr : 0 < radius (m + k) := radius_pos _
  obtain ⟨B, hB⟩ := hK.bddAbove_image
    ((Real.continuous_exp.comp (continuous_const.mul (hH.continuous _ hε ω))).continuousOn)
  let M := lqgApprox γ (fun s w => H (2 * radius m * s) w ω)
    (radius (m + k) / (2 * radius m)) S
  have hM : M ≠ ⊤ := lqgApprox_rescaled_apply_ne_top_of_isBounded hH ω γ hε hr
    Metric.isBounded_closedBall
  refine ⟨ENNReal.ofReal ((2 * radius m)⁻¹ ^ 2) * (ENNReal.ofReal B * M),
    lt_top_iff_ne_top.mpr (ENNReal.mul_ne_top ENNReal.ofReal_ne_top
      (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hM)), ?_⟩
  intro z hz
  refine (normalized_recentred_square_mass_le_of_subset H γ z m k ω hS (hsub z hz)).trans ?_
  gcongr
  exact hB ⟨z, hz, rfl⟩

/-- Finitely many levels admit one bound over every center in a compact set. -/
theorem exists_compact_finset_bound_normalized_recentred_square_mass {Ω : Type*}
    [MeasurableSpace Ω] {P : Measure Ω} {H : ℝ → ℂ → Ω → ℝ}
    (hH : LQGDimension.IsGFFCircleAverage H P) (ω : Ω) (γ : ℝ)
    (K : Set ℂ) (hK : IsCompact K) (m : ℕ) (T : Finset ℕ) :
    ∃ C : ℝ≥0∞, C < ⊤ ∧ ∀ z ∈ K, ∀ k ∈ T,
      normalizedRecentredSquareMass H γ z m k ω ≤ C := by
  classical
  choose C hC using fun k => exists_compact_bound_normalized_recentred_square_mass hH ω γ K hK m k
  refine ⟨T.sup C, (Finset.sup_lt_iff bot_lt_top).2 (fun k _ => (hC k).1), ?_⟩
  intro z hz k hk
  exact ((hC k).2 z hz).trans (Finset.le_sup (f := C) hk)

end LatticeProb.LQG
