/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.B2.DG20Pt.HeatPointAwayZeroRawLower at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Pt.HeatCompactFieldTail
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Pt.HeatAnnulusFieldLower
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Pt.PtDistFixedAnnulus
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Pt.PtDistDyadicLowerTail

 

set_option autoImplicit false
noncomputable section

open MeasureTheory ProbabilityTheory Set Metric
open scoped ENNReal
open LQGMetric LQGMetric.DDDF LQGMetric.LFPP

namespace SupercriticalLQGUniqueness.B2.DG20Pt

theorem dg20_heat_point_away_zero_raw_lower
    (ξ : Ioi (0 : ℝ))
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (h : Ω → DistC)
    (hh : IsNormalizedWholePlaneGFF h P)
    (X : Ioi (0 : ℝ) → Ω → C(ℂ, ℝ))
    (hX : ∀ ε, IsHeatSmoothing P h ε (X ε))
    (ε₁ : ℝ) (hε₁ : 0 < ε₁)
    (U : Set ℂ) (z w : ℂ) (hzw : z ≠ w)
    (ζ : ℝ) (hζ : 0 < ζ) :
    ∃ L : ℝ, 0 < L ∧
      ∀ ε : Ioo (0 : ℝ) 1, ε₁ ≤ (ε : ℝ) →
        P {ω | crossLenIn ξ (X ⟨ε, ε.property.1⟩ ω)
          U {z} {w} < ENNReal.ofReal L} ≤ ENNReal.ofReal ζ := by
  have hdist : 0 < dist z w := dist_pos.mpr hzw
  let d : ℝ := min (dist z w / 2) (1 / 2)
  have hd : 0 < d := by dsimp [d]; positivity
  have hdw : 3 * d / 4 < dist z w := by
    have h := min_le_left (dist z w / 2) (1 / 2)
    dsimp [d] at *
    linarith
  let K : Set ℂ := closedBall z d
  let R : ℝ := dist (0 : ℂ) z + d
  have hKR : K ⊆ closedBall (0 : ℂ) R := by
    intro x hx
    have htriangle := dist_triangle (0 : ℂ) z x
    have hdx : dist z x ≤ d := by
      have hx' : dist x z ≤ d := by simpa only [K, mem_closedBall] using hx
      simpa only [dist_comm] using hx'
    apply mem_closedBall.mpr
    rw [dist_comm]
    dsimp [R]
    linarith
  obtain ⟨M, hM, htail⟩ :=
    dg20_heat_compact_field_tail_away_zero P h hh X hX
      ε₁ R hε₁ K hKR ζ hζ
  let L : ℝ := Real.exp (-(|(ξ : ℝ)| * M)) *
    (3 * d / 4 - d / 16)
  have hL : 0 < L := by
    dsimp [L]
    exact mul_pos (Real.exp_pos _) (by linarith)
  refine ⟨L, hL, ?_⟩
  intro ε hε
  have hsub :
      {ω | crossLenIn ξ (X ⟨ε, ε.property.1⟩ ω)
        U {z} {w} < ENNReal.ofReal L} ⊆
      {ω | ∃ x ∈ K, M < |X ⟨ε, ε.property.1⟩ ω x|} := by
    intro ω hw
    by_contra hn
    change ¬ ∃ x ∈ K, M < |X ⟨ε, ε.property.1⟩ ω x| at hn
    push Not at hn
    have hcross :
        ENNReal.ofReal L ≤
          crossLenIn ξ (X ⟨ε, ε.property.1⟩ ω)
            (closedBall z d) (sphere z (d / 16))
            (sphere z (3 * d / 4)) := by
      exact dg20_annulus_crossing_lower_of_field_bound ξ
        (X ⟨ε, ε.property.1⟩ ω) z (d / 16) (3 * d / 4) d M
        (by linarith) (by simpa only [K] using hn)
    have hsep :
        crossLenIn ξ (X ⟨ε, ε.property.1⟩ ω)
          (closedBall z d) (sphere z (d / 16))
          (sphere z (3 * d / 4)) ≤
        crossLenIn ξ (X ⟨ε, ε.property.1⟩ ω) U {z} {w} := by
      calc
        _ ≤ lfppDOn ξ (X ⟨ε, ε.property.1⟩ ω) univ z w :=
          pt_dist_fixed_annulus_cross_le_point ξ
            (X ⟨ε, ε.property.1⟩ ω) z w
            (d / 16) (3 * d / 4) d
            (by positivity) (by linarith) (by linarith) hdw
        _ ≤ lfppDOn ξ (X ⟨ε, ε.property.1⟩ ω) U z w :=
          pt_dist_univ_le_internal ξ (X ⟨ε, ε.property.1⟩ ω) U z w
        _ = _ := by simp only [LQGMetric.DFGPS.crossLenIn_singleton]
    exact (not_lt_of_ge (hcross.trans hsep)) hw
  exact (measure_mono hsub).trans (htail ε hε)

end SupercriticalLQGUniqueness.B2.DG20Pt
