/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.B2.DG20Conc.LaneCPolygonSquare at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Conc.LaneCPolygonCarrier
import LatticeProb.Bonanno.LQGMetric.Papers.DDDF.S6DGOsc

 







set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Metric
open scoped ENNReal

namespace SupercriticalLQGUniqueness.B2.DG20Conc

open LQGMetric LQGMetric.LFPP LQGMetric.DDDF
open SupercriticalLQGUniqueness.Exponent.PolygonCofinality

 


theorem laneC_exists_polygon_in_open_square_cost_le
    {ξ : ℝ} {φ : ℂ → ℝ} (hφ : Continuous φ)
    {P : ℝ → ℂ} (hP : ContinuousOn P (Icc (0 : ℝ) 1))
    {A : Set ℂ} (hA : IsOpen A)
    (hPA : ∀ u ∈ Icc (0 : ℝ) 1, P u ∈ A)
    (hPS : ∀ u ∈ Icc (0 : ℝ) 1, P u ∈ (rectAB 1 1).toSet)
    {δ : ℝ} (hδ : 0 < δ) :
    ∃ γ : ℝ → ℂ,
      IsPiecewiseC1Path γ (P 0) (P 1) ∧
      (∀ u ∈ Icc (0 : ℝ) 1, γ u ∈ A) ∧
      (∀ u ∈ Icc (0 : ℝ) 1, γ u ∈ (rectAB 1 1).toSet) ∧
      lfppLen ξ φ γ ≤
        ENNReal.ofReal (1 + δ) * (lfppContMetric ξ φ hφ).len P 0 1 := by
  let K : Set ℂ := P '' Icc (0 : ℝ) 1
  have hK : IsCompact K := isCompact_Icc.image_of_continuousOn hP
  have hKA : K ⊆ A := by
    rintro x ⟨u, hu, rfl⟩
    exact hPA u hu
  obtain ⟨d, hd, hdA⟩ := hK.exists_cthickening_subset_open hA hKA
  obtain ⟨R, hKR⟩ := hK.isBounded.subset_closedBall (0 : ℂ)
  have hR : 0 ≤ R := by
    have h0 := hKR (show P 0 ∈ K from ⟨0, ⟨le_rfl, zero_le_one⟩, rfl⟩)
    exact (dist_nonneg : 0 ≤ dist (P 0) (0 : ℂ)).trans h0
  obtain ⟨N, t, ht0, ht1, htmono, htmem, hstep, hpoly, hcost⟩ :=
    laneC_exists_polygon_cost_le_continuous_length
      (ξ := ξ) hφ hP hR hδ hd (fun u hu => hKR ⟨u, hu, rfl⟩)
  let γ := polygonPath (fun i => P (t i)) N
  refine ⟨γ, hpoly, ?_, ?_, hcost⟩
  · apply laneC_polygon_mem_of_segments
    · simpa only [ht0] using hPA 0 ⟨le_rfl, zero_le_one⟩
    · intro i hi u hu
      have hcenter : P (t i) ∈ K := ⟨t i, htmem i hi.le, rfl⟩
      have hdist : dist (segPath (P (t i)) (P (t (i + 1))) u) (P (t i)) ≤ d := by
        exact (segPath_mem_closedBall _ _ hu).trans (by
          simpa [dist_eq_norm] using hstep i hi)
      exact hdA (Metric.mem_cthickening_of_dist_le _ _ d K hcenter hdist)
  · exact (polygonPath_data (ξ := ξ) (f := φ) S6DG.convex_unit
      (fun i => P (t i)) N
      (fun i hi => hPS (t i) (htmem i hi))).2.1

 


theorem laneC_exists_polygon_in_open_square_cost_lt
    {ξ : ℝ} {φ : ℂ → ℝ} (hφ : Continuous φ)
    {P : ℝ → ℂ} (hP : ContinuousOn P (Icc (0 : ℝ) 1))
    {A : Set ℂ} (hA : IsOpen A)
    (hPA : ∀ u ∈ Icc (0 : ℝ) 1, P u ∈ A)
    (hPS : ∀ u ∈ Icc (0 : ℝ) 1, P u ∈ (rectAB 1 1).toSet)
    {M η : ℝ} (hM : 0 < M) (hη : 0 < η)
    (hlen : (lfppContMetric ξ φ hφ).len P 0 1 < ENNReal.ofReal M) :
    ∃ γ : ℝ → ℂ,
      IsPiecewiseC1Path γ (P 0) (P 1) ∧
      (∀ u ∈ Icc (0 : ℝ) 1, γ u ∈ A) ∧
      (∀ u ∈ Icc (0 : ℝ) 1, γ u ∈ (rectAB 1 1).toSet) ∧
      lfppLen ξ φ γ < ENNReal.ofReal (M + η) := by
  let δ := η / (M + 1)
  have hδ : 0 < δ := div_pos hη (by linarith)
  obtain ⟨γ, hγ, hγA, hγS, hcost⟩ :=
    laneC_exists_polygon_in_open_square_cost_le (ξ := ξ) hφ hP hA hPA hPS hδ
  refine ⟨γ, hγ, hγA, hγS, ?_⟩
  have hmul : (1 + δ) * M < M + η := by
    dsimp [δ]
    have hfrac : η / (M + 1) * M < η := by
      have hratio : M / (M + 1) < 1 :=
        (div_lt_one (by linarith)).2 (by linarith)
      have hscaled := mul_lt_mul_of_pos_left hratio hη
      have hrewrite : η / (M + 1) * M = η * (M / (M + 1)) := by ring
      rw [hrewrite]
      simpa only [mul_one] using hscaled
    nlinarith
  calc
    lfppLen ξ φ γ ≤ ENNReal.ofReal (1 + δ) *
        (lfppContMetric ξ φ hφ).len P 0 1 := hcost
    _ ≤ ENNReal.ofReal (1 + δ) * ENNReal.ofReal M := by gcongr
    _ = ENNReal.ofReal ((1 + δ) * M) := by
      rw [ENNReal.ofReal_mul (by linarith : 0 ≤ 1 + δ)]
    _ < ENNReal.ofReal (M + η) :=
      (ENNReal.ofReal_lt_ofReal_iff (by linarith)).mpr hmul

end SupercriticalLQGUniqueness.B2.DG20Conc
