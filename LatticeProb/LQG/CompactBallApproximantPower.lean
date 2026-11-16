import LatticeProb.LQG.RecentredSquareCompactCenterBound

/-! # Uniform compact-center bounds for approximant ball masses -/

open MeasureTheory Set
open scoped ENNReal
open QuantumZipper
open MatedCRTHarmonic.GMCFacts LQGMetric.DGMC LQGMetric.DGMC.Neg3

namespace LatticeProb.LQG

/-- All dyadic approximations of one field satisfy a common positive-power
ball-mass bound on a compact set of centers. -/
theorem ae_exists_compact_center_ball_approximant_power_bound
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {H : ℝ → ℂ → Ω → ℝ}
    (hH : LQGDimension.IsGFFCircleAverage H P)
    (hHm : ∀ r z, Measurable (H r z)) {γ p q : ℝ}
    (hγ : 0 < γ) (hγ2 : γ < 2) (hp : 1 < p) (hpq : p < q)
    (hq : q < 4 / γ ^ 2) (K : Set ℂ) (hK : IsCompact K) :
    ∃ κ : ℝ, 0 < κ ∧ ∀ᵐ ω ∂P, ∃ C : ℝ≥0∞, C < ⊤ ∧
      ∀ z ∈ K, ∀ r : ℝ, 0 < r → r ≤ 1 → ∀ n,
        lqgApprox γ (fun s w => H s w ω) (radius n) (Metric.ball z r) ≤
          C * ENNReal.ofReal (r ^ κ) := by
  classical
  obtain ⟨R, hR⟩ := Metric.isBounded_iff_subset_ball (0 : ℂ) |>.1 hK.isBounded
  obtain ⟨κ, hκ, hevent⟩ := ae_exists_compact_center_recentred_and_square_scale_power_bounds
    hH hHm hγ hγ2 hp hpq hq (Metric.closedBall 0 (R + 4)) (isCompact_closedBall 0 (R + 4))
  refine ⟨κ, hκ, ?_⟩
  filter_upwards [hevent] with ω hevent
  obtain ⟨_, C, hC, hbound⟩ := hevent
  refine ⟨(corners16.card : ℝ≥0∞) * C * ENNReal.ofReal ((2 : ℝ) ^ κ),
    ENNReal.mul_lt_top (ENNReal.mul_lt_top (by simp) hC) ENNReal.ofReal_lt_top, ?_⟩
  intro z hz r hr hr1 n
  obtain ⟨m, hm1, hm2⟩ := exists_nat_pow_near_of_lt_one hr hr1
    (by norm_num : (0 : ℝ) < 2⁻¹) (by norm_num)
  have hm1' : radius (m + 1) < r := hm1
  have hm2' : r ≤ radius m := hm2
  have hmhalf : radius m ≤ 2 * r := by
    have heq : radius m = 2 * radius (m + 1) := by unfold radius; rw [pow_succ]; ring
    linarith
  have hradius : radius m ≤ 1 := by
    unfold radius
    exact pow_le_one₀ (by norm_num) (by norm_num)
  have hzR : ‖z‖ < R := by simpa [Metric.mem_ball, dist_zero_right] using hR hz
  have hcentre : ∀ c ∈ corners16, (z + radius m • c) + radius m • sqCentre ∈
      Metric.closedBall (0 : ℂ) (R + 4) := by
    intro c hc
    have hsq : sqCentre ∈ unitSq := by
      norm_num [unitSq, sqCentre]
    have hc4 := mem_corners16_bound hc sqCentre hsq
    rw [Metric.mem_closedBall, dist_zero_right]
    have hnorm : ‖radius m • (c + sqCentre)‖ ≤ 4 := by
      rw [norm_smul, Real.norm_of_nonneg (radius_pos m).le]
      nlinarith [mul_nonneg (radius_pos m).le (sub_nonneg.mpr hc4)]
    have heq : z + radius m • c + radius m • sqCentre = z + radius m • (c + sqCentre) := by
      rw [smul_add, add_assoc]
    rw [heq]
    linarith [norm_add_le z (radius m • (c + sqCentre))]
  let μ := lqgApprox γ (fun s w => H s w ω) (radius n)
  have hcover : Metric.ball z r ⊆ ⋃ c ∈ corners16, sqQ (z + radius m • c) m :=
    (Metric.ball_subset_ball (by linarith [radius_pos m])).trans (ball_subset_iUnion_sqQ z m)
  have hscale : ENNReal.ofReal (radius m ^ κ) ≤
      ENNReal.ofReal ((2 : ℝ) ^ κ) * ENNReal.ofReal (r ^ κ) := by
    rw [← ENNReal.ofReal_mul (Real.rpow_nonneg (by norm_num) _),
      ← Real.mul_rpow (by norm_num) hr.le]
    exact ENNReal.ofReal_le_ofReal (Real.rpow_le_rpow (radius_pos m).le hmhalf hκ.le)
  calc
    μ (Metric.ball z r) ≤ ∑ c ∈ corners16, μ (sqQ (z + radius m • c) m) :=
      (measure_mono hcover).trans (measure_biUnion_finset_le corners16 _)
    _ ≤ ∑ _c ∈ corners16, C * ENNReal.ofReal (radius m ^ κ) := by
      apply Finset.sum_le_sum
      intro c hc
      have heq : sqCorner ((z + radius m • c) + radius m • sqCentre) (radius m) =
          z + radius m • c := by simp [sqCorner]
      simpa only [heq] using hbound m _ (hcentre c hc) n
    _ = (corners16.card : ℝ≥0∞) * (C * ENNReal.ofReal (radius m ^ κ)) := by simp
    _ ≤ (corners16.card : ℝ≥0∞) * (C *
        (ENNReal.ofReal ((2 : ℝ) ^ κ) * ENNReal.ofReal (r ^ κ))) := by gcongr
    _ = _ := by ring

end LatticeProb.LQG
