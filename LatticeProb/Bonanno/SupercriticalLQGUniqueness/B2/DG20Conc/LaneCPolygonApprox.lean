/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.B2.DG20Conc.LaneCPolygonApprox at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Conc.LaneCUniformChord

 







set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Metric Set
open scoped ENNReal

namespace SupercriticalLQGUniqueness.B2.DG20Conc

open LQGMetric LQGMetric.LFPP
open SupercriticalLQGUniqueness.Exponent.PolygonCofinality

 


theorem laneC_exists_polygon_cost_le_continuous_length
    {ξ : ℝ} {φ : ℂ → ℝ} (hφ : Continuous φ)
    {P : ℝ → ℂ} (hP : ContinuousOn P (Icc (0 : ℝ) 1))
    {R δ ρ : ℝ} (hR : 0 ≤ R) (hδ : 0 < δ) (hρ : 0 < ρ)
    (htrace : ∀ u ∈ Icc (0 : ℝ) 1, P u ∈ closedBall (0 : ℂ) R) :
    ∃ N : ℕ, ∃ t : ℕ → ℝ,
      t 0 = 0 ∧ t N = 1 ∧ Monotone t ∧
      (∀ i ≤ N, t i ∈ Icc (0 : ℝ) 1) ∧
      (∀ i < N, ‖P (t (i + 1)) - P (t i)‖ ≤ ρ) ∧
      IsPiecewiseC1Path (polygonPath (fun i => P (t i)) N) (P 0) (P 1) ∧
      lfppLen ξ φ (polygonPath (fun i => P (t i)) N) ≤
        ENNReal.ofReal (1 + δ) * (lfppContMetric ξ φ hφ).len P 0 1 := by
  obtain ⟨η, hη, hratio⟩ :=
    laneC_exists_weight_ratio_radius (ξ := ξ) hφ (by linarith : 0 ≤ R + 1) hδ
  let r : ℝ := min (η / 4) (min 1 ρ)
  have hr : 0 < r := lt_min (by positivity) (lt_min one_pos hρ)
  have hr1 : r ≤ 1 := (min_le_right _ _).trans (min_le_left _ _)
  have hrρ : r ≤ ρ := (min_le_right _ _).trans (min_le_right _ _)
  have h3rη : 3 * r < η := by
    have := min_le_left (η / 4) (min 1 ρ)
    dsimp [r]
    linarith
  obtain ⟨τ, hτ, hτP⟩ := Metric.uniformContinuousOn_iff.1
    (isCompact_Icc.uniformContinuousOn_of_continuous hP) r hr
  obtain ⟨M, hM⟩ := exists_nat_one_div_lt hτ
  let N := M + 1
  let t : ℕ → ℝ := fun i => i / ((M : ℝ) + 1)
  have hM1 : (0 : ℝ) < (M : ℝ) + 1 := by positivity
  have htmono : Monotone t := fun i j hij => by
    simp only [t]
    gcongr
  have htmem : ∀ i ≤ N, t i ∈ Icc (0 : ℝ) 1 := by
    intro i hi
    refine ⟨by positivity, ?_⟩
    rw [div_le_one hM1]
    exact_mod_cast hi
  have ht0 : t 0 = 0 := by simp [t]
  have ht1 : t N = 1 := by
    simp only [t, N]
    push_cast
    exact div_self hM1.ne'
  have htstep : ∀ i < N, ‖P (t (i + 1)) - P (t i)‖ ≤ r := by
    intro i hi
    have hstep : t (i + 1) - t i = 1 / ((M : ℝ) + 1) := by
      simp only [t]
      push_cast
      ring
    have hti := htmem i hi.le
    have hti1 := htmem (i + 1) (by omega : i + 1 ≤ N)
    have hdist : dist (t (i + 1)) (t i) < τ := by
      rw [Real.dist_eq, abs_of_nonneg (by linarith [htmono (Nat.le_succ i)])]
      simpa [hstep] using hM
    have := hτP (t (i + 1)) hti1 (t i) hti hdist
    simpa [dist_eq_norm] using this.le
  obtain ⟨hpoly, hcost⟩ :=
    laneC_sampled_polygon_cost_le_of_short_chords
      (ξ := ξ) (P := P) (δ := δ) hφ t N htmono htmem hr hr1 hδ.le
      (fun i hi => htrace (t i) (htmem i hi))
      htstep (fun x hx y hy hxy => hratio x hx y hy (hxy.trans h3rη))
  refine ⟨N, t, ht0, ht1, htmono, htmem,
    (fun i hi => (htstep i hi).trans hrρ), ?_, hcost⟩
  simpa only [ht0, ht1] using hpoly

end SupercriticalLQGUniqueness.B2.DG20Conc
