import LatticeProb.LQG.NormalizedCircleSupremumDyadic

/-! # All-scale circle-average bounds for normalized whole-plane fields -/

open MeasureTheory Filter Set Metric

namespace LatticeProb.LQG

/-- An eventual spatial bound extends to every index, with an additive constant,
when the finitely many early functions are continuous on a compact disk. -/
theorem exists_all_scales_circle_le_of_eventually
    (h : ℕ → ℂ → ℝ) (a : ℕ → ℝ) {r ρ : ℝ} (hrρ : r < ρ)
    (hc : ∀ k, Continuous (h k))
    (htail : ∀ᶠ k : ℕ in atTop, ∀ z ∈ ball (0 : ℂ) ρ, h k z ≤ a k) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ k z, z ∈ ball (0 : ℂ) r → h k z ≤ C + a k := by
  obtain ⟨N, hN⟩ := eventually_atTop.1 htail
  have hb : ∀ k : ℕ, ∃ B : ℝ, ∀ z ∈ closedBall (0 : ℂ) r, h k z - a k ≤ B := by
    intro k
    obtain ⟨B, hB⟩ := (isCompact_closedBall (0 : ℂ) r).bddAbove_image
      ((hc k).sub continuous_const).continuousOn
    exact ⟨B, fun z hz => hB ⟨z, hz, rfl⟩⟩
  choose B hB using hb
  obtain ⟨C, hC⟩ := (Set.finite_range (fun k : Fin N => B k)).bddAbove
  refine ⟨max 0 C, le_max_left _ _, fun k z hz => ?_⟩
  by_cases hk : k < N
  · have hkC : B k ≤ C := hC ⟨⟨k, hk⟩, rfl⟩
    have hz' : z ∈ closedBall (0 : ℂ) r := ball_subset_closedBall hz
    have := hB k z hz'
    linarith [le_max_right (0 : ℝ) C]
  · have hzρ : z ∈ ball (0 : ℂ) ρ := ball_subset_ball (le_of_lt hrρ) hz
    have := hN k (Nat.le_of_not_gt hk) z hzρ
    linarith [le_max_left (0 : ℝ) C]

/-- A selected continuous circle-average version of a normalized whole-plane
GFF admits a common all-dyadic upper bound on a fixed smaller disk. -/
theorem ae_exists_all_dyadic_circle_le_of_normalized_gff
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    {X : Ω → LQGMetric.DistC} (hX : LQGMetric.IsNormalizedWPGFF X P)
    {c : Ω → ℝ → ℂ → ℝ}
    (hc : ∀ ω, ContinuousOn (fun p : ℝ × ℂ => c ω p.1 p.2) (Ioi 0 ×ˢ univ))
    (heq : ∀ r, 0 < r → ∀ z, ∀ᵐ ω ∂P, c ω r z = LQGMetric.circleAvg (X ω) r z)
    {δ r ρ : ℝ} (hδ : 0 < δ) (hρ : ρ ∈ Ioo (0 : ℝ) 1) (hrρ : r < ρ) :
    ∀ᵐ ω ∂P, ∃ C : ℝ, 0 ≤ C ∧ ∀ k z, z ∈ ball (0 : ℂ) r →
      c ω (dyadicScale k) z ≤ C + (2 + δ) * Real.log (dyadicScale k)⁻¹ := by
  filter_upwards [ae_eventually_dyadic_circle_sup_le_of_normalized_gff hX hc heq hδ hρ] with ω hω
  apply exists_all_scales_circle_le_of_eventually
    (fun k z => c ω (dyadicScale k) z)
    (fun k => (2 + δ) * Real.log (dyadicScale k)⁻¹) hrρ
  · intro k
    apply continuousOn_univ.mp
    apply (hc ω).comp (continuous_const.prodMk continuous_id).continuousOn
    intro z hz
    exact ⟨by change 0 < (2⁻¹ : ℝ) ^ k; positivity, mem_univ _⟩
  · filter_upwards [hω] with k hk z hz
    exact (le_abs_self _).trans (hk z hz)

end LatticeProb.LQG
