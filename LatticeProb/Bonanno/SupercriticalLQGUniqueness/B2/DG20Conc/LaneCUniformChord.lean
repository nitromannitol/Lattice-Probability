/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.B2.DG20Conc.LaneCUniformChord at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Conc.LaneCChordRatio

 






set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Metric Set
open scoped ENNReal

namespace SupercriticalLQGUniqueness.B2.DG20Conc

open LQGMetric LQGMetric.LFPP
open SupercriticalLQGUniqueness.Exponent.PolygonCofinality

 

theorem laneC_exists_weight_ratio_radius
    {ξ : ℝ} {φ : ℂ → ℝ} (hφ : Continuous φ)
    {R δ : ℝ} (hR : 0 ≤ R) (hδ : 0 < δ) :
    ∃ η > 0, ∀ x ∈ closedBall (0 : ℂ) R,
      ∀ y ∈ closedBall (0 : ℂ) R, dist x y < η →
        Real.exp (ξ * φ x) ≤ (1 + δ) * Real.exp (ξ * φ y) := by
  let E : ℂ → ℝ := fun x => Real.exp (ξ * φ x)
  have hE : Continuous E := Real.continuous_exp.comp (continuous_const.mul hφ)
  obtain ⟨m, hm, hmE⟩ :=
    exists_pos_le_exp_on (ξ := ξ) hφ (0 : ℂ) R hR
  obtain ⟨η, hη, hηE⟩ := Metric.uniformContinuousOn_iff.1
    ((isCompact_closedBall (0 : ℂ) R).uniformContinuousOn_of_continuous hE.continuousOn)
    (δ * m) (mul_pos hδ hm)
  refine ⟨η, hη, ?_⟩
  intro x hx y hy hxy
  have hdiff := hηE x hx y hy hxy
  rw [Real.dist_eq, abs_lt] at hdiff
  have hmy := hmE y hy
  dsimp [E] at hdiff
  nlinarith

 


theorem laneC_sampled_polygon_cost_le_of_short_chords
    {ξ : ℝ} {φ : ℂ → ℝ} (hφ : Continuous φ)
    {P : ℝ → ℂ} {a b : ℝ} (t : ℕ → ℝ) (N : ℕ)
    (ht : Monotone t)
    (htmem : ∀ i ≤ N, t i ∈ Icc a b)
    {R r δ : ℝ} (hr : 0 < r)
    (hr1 : r ≤ 1) (hδ : 0 ≤ δ)
    (htrace : ∀ i ≤ N, P (t i) ∈ closedBall (0 : ℂ) R)
    (hstep : ∀ i < N, ‖P (t (i + 1)) - P (t i)‖ ≤ r)
    (hrel : ∀ x ∈ closedBall (0 : ℂ) (R + 1),
      ∀ y ∈ closedBall (0 : ℂ) (R + 1), dist x y < 3 * r →
        Real.exp (ξ * φ x) ≤ (1 + δ) * Real.exp (ξ * φ y)) :
    IsPiecewiseC1Path
      (polygonPath (fun i => P (t i)) N) (P (t 0)) (P (t N)) ∧
    lfppLen ξ φ (polygonPath (fun i => P (t i)) N) ≤
      ENNReal.ofReal (1 + δ) * (lfppContMetric ξ φ hφ).len P a b := by
  refine laneC_sampled_polygon_cost_le (ξ := ξ) (P := P) (δ := δ) hφ t N ht htmem ?_
  intro i hi
  let z := P (t i)
  let w := P (t (i + 1))
  have hz : z ∈ closedBall (0 : ℂ) R := htrace i hi.le
  have hball : closedBall z r ⊆ closedBall (0 : ℂ) (R + 1) := by
    intro x hx
    rw [mem_closedBall] at hx ⊢
    have htri := dist_triangle x z 0
    have hzR : dist z 0 ≤ R := by simpa [dist_comm] using hz
    linarith
  apply laneC_chord_cost_le_of_weight_ratio hφ hr hδ (hstep i hi)
  intro x hx y hy
  apply hrel x (hball hx) y (hball hy)
  have hxy := dist_triangle x z y
  have hxz : dist x z ≤ r := hx
  have hzy : dist z y ≤ r := by simpa [dist_comm] using hy
  linarith

end SupercriticalLQGUniqueness.B2.DG20Conc
