/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.B2.DG20Pt.HeatPointOpenSmallLower at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Pt.HeatAnnulusTranslatedSmallLower
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Pt.PtDistFixedAnnulus
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Pt.PtDistDyadicLowerTail

 

set_option autoImplicit false
noncomputable section

open MeasureTheory ProbabilityTheory Set Metric
open scoped ENNReal
open LQGMetric LQGMetric.DDDF LQGMetric.LFPP

namespace SupercriticalLQGUniqueness.B2.DG20Pt

theorem dg20_heat_point_open_small_lower_of_perc
    (hPerc : SupercriticalLQGUniqueness.B2.Iface.DG20PercEstimate')
    (ξ : Ioi (0 : ℝ))
    (m : Ioi (0 : ℝ) → Ioi (0 : ℝ))
    (hm : ∀ ε, IsLFPPNormalizer ξ ε (m ε))
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (h : Ω → DistC)
    (hh : IsNormalizedWholePlaneGFF h P)
    (X : Ioi (0 : ℝ) → Ω → C(ℂ, ℝ))
    (hX : ∀ ε, IsHeatSmoothing P h ε (X ε))
    (U : Set ℂ) (z w : ℂ) (hzw : z ≠ w)
    (η : ℝ) (hη : 0 < η) :
    ∃ T ε₀ : ℝ, 0 < T ∧ 0 < ε₀ ∧
      ∀ ε : Ioo (0 : ℝ) 1, (ε : ℝ) < ε₀ →
        P {ω | ENNReal.ofReal (m ⟨ε, ε.property.1⟩ : ℝ)⁻¹ *
          crossLenIn ξ (X ⟨ε, ε.property.1⟩ ω) U {z} {w} <
            ENNReal.ofReal T⁻¹} ≤ ENNReal.ofReal η := by
  have hdist : 0 < dist z w := dist_pos.mpr hzw
  let d : ℝ := min (dist z w / 2) (1 / 2)
  have hd : 0 < d := by dsimp [d]; positivity
  have hd2 : d ≤ 1 / 2 := min_le_right _ _
  have hdw : 3 * d / 4 < dist z w := by
    have h := min_le_left (dist z w / 2) (1 / 2)
    dsimp [d] at *
    linarith
  obtain ⟨T, ε₀, hT, hε₀, htail⟩ :=
    dg20_heat_annulus_translated_small_lower_of_perc
      hPerc ξ m hm P h hh X hX z d hd hd2 η hη
  refine ⟨T, ε₀, hT, hε₀, ?_⟩
  intro ε hε
  have hcross (ω : Ω) :
      crossLenIn ξ (X ⟨ε, ε.property.1⟩ ω)
        (closedBall z d) (sphere z (d / 16))
        (sphere z (3 * d / 4)) ≤
      crossLenIn ξ (X ⟨ε, ε.property.1⟩ ω) U {z} {w} := by
    calc
      _ ≤ lfppDOn ξ (X ⟨ε, ε.property.1⟩ ω) univ z w :=
        pt_dist_fixed_annulus_cross_le_point ξ
          (X ⟨ε, ε.property.1⟩ ω) z w (d / 16) (3 * d / 4) d
          (by positivity) (by linarith) (by linarith) hdw
      _ ≤ lfppDOn ξ (X ⟨ε, ε.property.1⟩ ω) U z w :=
        pt_dist_univ_le_internal ξ (X ⟨ε, ε.property.1⟩ ω) U z w
      _ = _ := by simp only [LQGMetric.DFGPS.crossLenIn_singleton]
  have hsub :
      {ω | ENNReal.ofReal (m ⟨ε, ε.property.1⟩ : ℝ)⁻¹ *
        crossLenIn ξ (X ⟨ε, ε.property.1⟩ ω) U {z} {w} <
          ENNReal.ofReal T⁻¹} ⊆
      {ω | ENNReal.ofReal (m ⟨ε, ε.property.1⟩ : ℝ)⁻¹ *
        crossLenIn ξ (X ⟨ε, ε.property.1⟩ ω)
          (closedBall z d) (sphere z (d / 16))
          (sphere z (3 * d / 4)) < ENNReal.ofReal T⁻¹} := by
    intro ω hω
    exact lt_of_le_of_lt
      (mul_le_mul_of_nonneg_left (hcross ω) bot_le) hω
  exact (measure_mono hsub).trans (htail ε hε)

end SupercriticalLQGUniqueness.B2.DG20Pt
