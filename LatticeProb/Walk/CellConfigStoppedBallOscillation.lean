import LatticeProb.Walk.CellConfigExitRadiusSandwich

/-! # Stopped paths with nearby ball exit times -/

set_option autoImplicit false

open Set
open scoped NNReal ENNReal

namespace LatticeProb

/-- Uniformly close paths remain close when stopped at their ball exits, provided
that the reference path has small oscillation between the neighboring-radius
exit times. The outer exit must be finite. -/
theorem dist_stopped_openExitTime_ball_le_of_oscillation
    {Ω E : Type*} [PseudoMetricSpace E] (f g : ℝ≥0 → Ω → E)
    (ω : Ω) (z : E) (R δ η : ℝ)
    (hclose : ∀ t, dist (f t ω) (g t ω) ≤ δ)
    (hfinite : openExitTime f (Metric.ball z (R + δ)) ω ≠ ∞)
    (hosc : ∀ s ∈ Icc (openExitTime f (Metric.ball z (R - δ)) ω).toNNReal
        (openExitTime f (Metric.ball z (R + δ)) ω).toNNReal,
      ∀ t ∈ Icc (openExitTime f (Metric.ball z (R - δ)) ω).toNNReal
        (openExitTime f (Metric.ball z (R + δ)) ω).toNNReal,
      dist (f s ω) (f t ω) ≤ η) (t : ℝ≥0) :
    dist (f (min t (openExitTime f (Metric.ball z R) ω).toNNReal) ω)
      (g (min t (openExitTime g (Metric.ball z R) ω).toNNReal) ω) ≤ δ + η := by
  have hδ : 0 ≤ δ := (dist_nonneg : 0 ≤ dist (f 0 ω) (g 0 ω)).trans (hclose 0)
  have hf := openExitTime_ball_sandwich_of_dist_le f f ω z R δ
    (fun s => by simpa only [dist_self] using hδ)
  have hg := openExitTime_ball_sandwich_of_dist_le f g ω z R δ hclose
  have hff := ne_top_of_le_ne_top hfinite hf.2
  have hgf := ne_top_of_le_ne_top hfinite hg.2
  have hfa := ENNReal.toNNReal_mono hff hf.1
  have hfb := ENNReal.toNNReal_mono hfinite hf.2
  have hga := ENNReal.toNNReal_mono hgf hg.1
  have hgb := ENNReal.toNNReal_mono hfinite hg.2
  have hη : 0 ≤ η := (dist_nonneg : 0 ≤ dist
      (f (openExitTime f (Metric.ball z R) ω).toNNReal ω)
      (f (openExitTime f (Metric.ball z R) ω).toNNReal ω)).trans
    (hosc _ ⟨hfa, hfb⟩ _ ⟨hfa, hfb⟩)
  have hmin : dist
      (f (min t (openExitTime f (Metric.ball z R) ω).toNNReal) ω)
      (f (min t (openExitTime g (Metric.ball z R) ω).toNNReal) ω) ≤ η := by
    by_cases ht : t ≤ (openExitTime f (Metric.ball z (R - δ)) ω).toNNReal
    · simpa only [min_eq_left (ht.trans hfa), min_eq_left (ht.trans hga), dist_self] using hη
    · have ht' := (lt_of_not_ge ht).le
      exact hosc _ ⟨le_min ht' hfa, (min_le_right _ _).trans hfb⟩
        _ ⟨le_min ht' hga, (min_le_right _ _).trans hgb⟩
  have hc := hclose (min t (openExitTime g (Metric.ball z R) ω).toNNReal)
  linarith [dist_triangle
    (f (min t (openExitTime f (Metric.ball z R) ω).toNNReal) ω)
    (f (min t (openExitTime g (Metric.ball z R) ω).toNNReal) ω)
    (g (min t (openExitTime g (Metric.ball z R) ω).toNNReal) ω)]

end LatticeProb

namespace LatticeProb.CellConfigInterpolation

open ReflectedGMS ReflectedGMS.GMS BouRabeeGwynne

/-- The stopped interpolations for nearby representatives are uniformly close
when the reference interpolation has bounded oscillation between neighboring
ball exits. -/
theorem dist_stopped_interpolatedWalk_ball_le_of_oscillation
    (H : CellConfig) (p q : H.cells → Plane) (ω : ℕ → H.cells)
    (hpos : ∀ K, 0 < H.holding K) (hunb : H.JumpTimesUnbounded ω)
    {r : ℝ} (hclose : ∀ K, dist (p K) (q K) ≤ r)
    (ε : ℝ≥0) (z : Plane) (R η : ℝ)
    (hfinite : continuousExitTime (Metric.ball z (R + (ε : ℝ) * r)) 0
      (H.interpolatedWalk p ε ω) ≠ ∞)
    (hosc : ∀ s ∈ Icc
        (continuousExitTime (Metric.ball z (R - (ε : ℝ) * r)) 0
          (H.interpolatedWalk p ε ω)).toNNReal
        (continuousExitTime (Metric.ball z (R + (ε : ℝ) * r)) 0
          (H.interpolatedWalk p ε ω)).toNNReal,
      ∀ t ∈ Icc
        (continuousExitTime (Metric.ball z (R - (ε : ℝ) * r)) 0
          (H.interpolatedWalk p ε ω)).toNNReal
        (continuousExitTime (Metric.ball z (R + (ε : ℝ) * r)) 0
          (H.interpolatedWalk p ε ω)).toNNReal,
      dist ((H.interpolatedWalk p ε ω) s) ((H.interpolatedWalk p ε ω) t) ≤ η)
    (t : ℝ≥0) :
    dist ((H.interpolatedWalk p ε ω) (min t
      (continuousExitTime (Metric.ball z R) 0 (H.interpolatedWalk p ε ω)).toNNReal))
      ((H.interpolatedWalk q ε ω) (min t
      (continuousExitTime (Metric.ball z R) 0 (H.interpolatedWalk q ε ω)).toNNReal)) ≤
      (ε : ℝ) * r + η := by
  have h := dist_stopped_openExitTime_ball_le_of_oscillation
      (fun t (_ : Unit) => (0 : Plane) + H.interpolatedWalk p ε ω t)
      (fun t (_ : Unit) => (0 : Plane) + H.interpolatedWalk q ε ω t) () z R
      ((ε : ℝ) * r) η
      (fun t => by simpa only [zero_add] using
        dist_interpolatedWalk_le_of_dist_representatives_le H p q ω hpos hunb hclose ε t)
      hfinite (fun s hs u hu => by simpa only [zero_add] using hosc s hs u hu) t
  change dist ((0 : Plane) + (H.interpolatedWalk p ε ω) (min t
      (continuousExitTime (Metric.ball z R) 0 (H.interpolatedWalk p ε ω)).toNNReal))
    ((0 : Plane) + (H.interpolatedWalk q ε ω) (min t
      (continuousExitTime (Metric.ball z R) 0 (H.interpolatedWalk q ε ω)).toNNReal)) ≤
      (ε : ℝ) * r + η at h
  simpa only [zero_add] using h

end LatticeProb.CellConfigInterpolation
