import Mathlib
import LatticeProb.LQG.LengthMetricDerived
import LatticeProb.LQG.InternalMetricOfTriangle

/-!
# Positivity of the Weyl scaling between distinct points

For a Euclidean length metric `D` and a weight `e^{ξ f}` with `f` continuous away from the origin (and arbitrary at the
origin), the Weyl scaling `e^{ξ f} · D` of two distinct points is strictly positive. The weight may degenerate at `0`
(for instance `f(z) = -α log |z|` or `f(z) = α log |z|`), so positivity is proved from the endpoint which is not the
origin: the last stretch of a `D`-length parametrized path inside a small ball around that endpoint has `D`-length at
least the positive `D`-distance from the endpoint to the boundary of the ball, and the weight is bounded below on the ball.
-/

namespace LatticeProb.LQG

open MeasureTheory Set Metric
open scoped ENNReal

/-- Positivity of the Weyl scaling when the right endpoint is not the origin. -/
theorem IsEuclideanLengthMetric.weylScaling_pos_of_ne_zero_right {D : ℂ → ℂ → ℝ}
    (hD : IsEuclideanLengthMetric D) (ξ : ℝ) {f : ℂ → ℝ} (hf : ContinuousOn f {0}ᶜ) {u v : ℂ}
    (huv : u ≠ v) (hv : v ≠ 0) : 0 < weylScaling D ξ f u v := by
  set r : ℝ := min (dist u v) (‖v‖ / 2) with hr_def
  have hr : 0 < r := lt_min (dist_pos.2 huv) (by have := norm_pos_iff.2 hv; positivity)
  have hr_u : r ≤ dist u v := min_le_left _ _
  have hr_v : r ≤ ‖v‖ / 2 := min_le_right _ _
  have hball : closedBall v r ⊆ {0}ᶜ := by
    intro z hz h0
    have h0' : z = 0 := h0
    rw [mem_closedBall, h0', dist_zero_left] at hz
    have := norm_pos_iff.2 hv
    linarith
  have hcont : ContinuousOn (fun z => ξ * f z) (closedBall v r) :=
    continuousOn_const.mul (hf.mono hball)
  obtain ⟨M, hM⟩ := (isCompact_closedBall v r).bddBelow_image hcont
  have hMb : ∀ z ∈ closedBall v r, M ≤ ξ * f z := fun z hz => hM ⟨z, hz, rfl⟩
  obtain ⟨ε, hε, hεball⟩ := (hD.isOpen_iff (ball v r)).1 isOpen_ball v (mem_ball_self hr)
  have hpos : 0 < ENNReal.ofReal (Real.exp M) * ENNReal.ofReal ε :=
    ENNReal.mul_pos (ENNReal.ofReal_pos.2 (Real.exp_pos M)).ne' (ENNReal.ofReal_pos.2 hε).ne'
  refine lt_of_lt_of_le hpos ?_
  unfold weylScaling
  refine le_iInf fun T => le_iInf fun p => le_iInf fun hp => le_iInf fun h0 => le_iInf fun hT => ?_
  obtain ⟨hT0, hpc, hlen⟩ := hp
  set S : Set ℝ := Icc 0 T ∩ p ⁻¹' {z | r ≤ dist z v} with hS_def
  have hSc : IsCompact S :=
    isCompact_Icc.of_isClosed_subset
      (hpc.preimage_isClosed_of_isClosed isClosed_Icc (isClosed_le continuous_const
        (continuous_id.dist continuous_const))) inter_subset_left
  have h0S : (0 : ℝ) ∈ S := ⟨⟨le_rfl, hT0⟩, by simpa [h0] using hr_u⟩
  have hs0S : sSup S ∈ S := hSc.sSup_mem ⟨0, h0S⟩
  set s0 : ℝ := sSup S with hs0_def
  have hs0_mem : s0 ∈ Icc 0 T := hs0S.1
  have hs0_dist : r ≤ dist (p s0) v := hs0S.2
  have hs0T : s0 < T := by
    refine lt_of_le_of_ne hs0_mem.2 fun h => ?_
    rw [h, hT, dist_self] at hs0_dist
    linarith
  have hnear : ∀ t ∈ Ioc s0 T, M ≤ ξ * f (p t) := by
    intro t ht
    refine hMb _ (mem_closedBall.2 ?_)
    by_contra hlt
    have htS : t ∈ S := ⟨⟨hs0_mem.1.trans ht.1.le, ht.2⟩, (not_le.1 hlt).le⟩
    exact absurd (le_csSup hSc.bddAbove htS) (not_le.2 ht.1)
  have hDge : ε ≤ D v (p s0) := by
    by_contra hlt
    have := hεball _ (not_le.1 hlt)
    exact absurd hs0_dist (not_le.2 (by simpa [dist_comm] using mem_ball.1 this))
  have hDle : D v (p s0) ≤ T - s0 := by
    have h1 := ofReal_le_curveLength (E := D) (f := p) (a := s0) (b := T) (s := s0) (t := T)
      ⟨le_rfl, hs0T.le⟩ ⟨hs0T.le, le_rfl⟩ hs0T.le
    rw [hlen s0 T hs0_mem.1 hs0T.le le_rfl, hT] at h1
    exact (ENNReal.ofReal_le_ofReal_iff (by linarith)).1 h1
  calc ENNReal.ofReal (Real.exp M) * ENNReal.ofReal ε
      ≤ ENNReal.ofReal (Real.exp M) * ENNReal.ofReal (T - s0) :=
        mul_le_mul' le_rfl (ENNReal.ofReal_le_ofReal (hDge.trans hDle))
    _ = ∫⁻ _ in Ioc s0 T, ENNReal.ofReal (Real.exp M) := by
        rw [setLIntegral_const, Real.volume_Ioc]
    _ ≤ ∫⁻ t in Ioc s0 T, ENNReal.ofReal (Real.exp (ξ * f (p t))) :=
        setLIntegral_mono' measurableSet_Ioc fun t ht =>
          ENNReal.ofReal_le_ofReal (Real.exp_le_exp.2 (hnear t ht))
    _ ≤ ∫⁻ t in Icc 0 T, ENNReal.ofReal (Real.exp (ξ * f (p t))) :=
        lintegral_mono_set fun t ht => ⟨hs0_mem.1.trans ht.1.le, ht.2⟩

/-- Positivity of the Weyl scaling between distinct points, for a weight continuous away from the origin and arbitrary at
the origin. -/
theorem IsEuclideanLengthMetric.weylScaling_pos_of_ne {D : ℂ → ℂ → ℝ} (hD : IsEuclideanLengthMetric D) (ξ : ℝ)
    {f : ℂ → ℝ} (hf : ContinuousOn f {0}ᶜ) {u v : ℂ} (huv : u ≠ v) : 0 < weylScaling D ξ f u v := by
  by_cases hv : v = 0
  · have hu : u ≠ 0 := fun h => huv (h.trans hv.symm)
    rw [hD.weylScaling_symm]
    exact hD.weylScaling_pos_of_ne_zero_right ξ hf huv.symm hu
  · exact hD.weylScaling_pos_of_ne_zero_right ξ hf huv hv

end LatticeProb.LQG
