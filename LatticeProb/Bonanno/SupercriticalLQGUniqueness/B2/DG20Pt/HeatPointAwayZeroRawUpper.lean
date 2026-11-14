/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.B2.DG20Pt.HeatPointAwayZeroRawUpper at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Pt.HeatCompactFieldTail
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Pt.PtDistOpenConnectedFinite
import LatticeProb.Bonanno.LQGMetric.Papers.DDDF.LenBasic

 

set_option autoImplicit false
noncomputable section

open MeasureTheory ProbabilityTheory Set Metric
open scoped ENNReal
open LQGMetric LQGMetric.DDDF LQGMetric.LFPP

namespace SupercriticalLQGUniqueness.B2.DG20Pt

theorem dg20_heat_point_away_zero_raw_upper
    (ξ : Ioi (0 : ℝ))
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (h : Ω → DistC)
    (hh : IsNormalizedWholePlaneGFF h P)
    (X : Ioi (0 : ℝ) → Ω → C(ℂ, ℝ))
    (hX : ∀ ε, IsHeatSmoothing P h ε (X ε))
    (ε₁ : ℝ) (hε₁ : 0 < ε₁)
    (U : Set ℂ) (hU : IsOpen U) (hUc : IsConnected U)
    (z w : ℂ) (hz : z ∈ U) (hw : w ∈ U)
    (ζ : ℝ) (hζ : 0 < ζ) :
    ∃ H : ℝ, 0 < H ∧
      ∀ ε : Ioo (0 : ℝ) 1, ε₁ ≤ (ε : ℝ) →
        P {ω | ENNReal.ofReal H <
          crossLenIn ξ (X ⟨ε, ε.property.1⟩ ω)
            U {z} {w}} ≤ ENNReal.ofReal ζ := by
  obtain ⟨q, hq⟩ := LQGMetric.DG.t15_exists_isDGPath hU hUc hz hw
  have hpath : IsPiecewiseC1Path q z w :=
    ⟨hq.source, hq.target, hq.continuousOn, hq.piecewise_contDiff⟩
  let K : Set ℂ := q '' Icc (0 : ℝ) 1
  have hK : IsCompact K := isCompact_Icc.image_of_continuousOn hq.continuousOn
  obtain ⟨R, hKR⟩ := hK.isBounded.subset_closedBall (0 : ℂ)
  obtain ⟨M, hM, htail⟩ :=
    dg20_heat_compact_field_tail_away_zero P h hh X hX
      ε₁ R hε₁ K hKR ζ hζ
  have hadm : AdmPath K {z} {w} q := by
    refine ⟨z, by simp, w, by simp, hpath, ?_⟩
    intro t ht
    exact ⟨t, ht, rfl⟩
  have hfin : lfppLen ξ (fun _ => 0) q ≠ ∞ :=
    lfppLen_ne_top_of_adm continuous_const hK hadm
  let L₀ : ℝ := (lfppLen ξ (fun _ => 0) q).toReal
  have hL₀ : 0 ≤ L₀ := ENNReal.toReal_nonneg
  have hL₀eq : ENNReal.ofReal L₀ = lfppLen ξ (fun _ => 0) q :=
    ENNReal.ofReal_toReal hfin
  let H : ℝ := Real.exp (|(ξ : ℝ)| * M) * (L₀ + 1)
  have hH : 0 < H := by dsimp [H]; positivity
  refine ⟨H, hH, ?_⟩
  intro ε hε
  have hsub :
      {ω | ENNReal.ofReal H <
        crossLenIn ξ (X ⟨ε, ε.property.1⟩ ω) U {z} {w}} ⊆
      {ω | ∃ x ∈ K, M < |X ⟨ε, ε.property.1⟩ ω x|} := by
    intro ω hw
    by_contra hn
    change ¬ ∃ x ∈ K, M < |X ⟨ε, ε.property.1⟩ ω x| at hn
    push Not at hn
    have hcost :
        crossLenIn ξ (X ⟨ε, ε.property.1⟩ ω) U {z} {w} ≤
          ENNReal.ofReal (Real.exp (|(ξ : ℝ)| * M)) *
            lfppLen ξ (fun _ => 0) q := by
      calc
        _ = lfppDOn ξ (X ⟨ε, ε.property.1⟩ ω) U z w := by
          simp only [LQGMetric.DFGPS.crossLenIn_singleton]
        _ ≤ lfppLen ξ (X ⟨ε, ε.property.1⟩ ω) q :=
          lfppDOn_le hpath hq.mapsTo
        _ ≤ ENNReal.ofReal (Real.exp (|(ξ : ℝ)| * M)) *
              lfppLen ξ (fun _ => 0) q := by
          apply lfppLen_le_of_abs_sub_le
          intro t ht
          have hqt : q t ∈ K := ⟨t, ht, rfl⟩
          simpa only [sub_zero] using hn (q t) hqt
    have hHcost : ENNReal.ofReal (Real.exp (|(ξ : ℝ)| * M)) *
        lfppLen ξ (fun _ => 0) q ≤ ENNReal.ofReal H := by
      rw [← hL₀eq, ← ENNReal.ofReal_mul (Real.exp_pos _).le]
      apply ENNReal.ofReal_le_ofReal
      dsimp [H]
      gcongr
      linarith
    exact (not_lt_of_ge (hcost.trans hHcost)) hw
  exact (measure_mono hsub).trans (htail ε hε)

end SupercriticalLQGUniqueness.B2.DG20Pt
