/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.B2.DG20Pt.HeatNormalizerAwayZero at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Pt.HeatCompactFieldTail
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Pt.HeatCrossingFieldBounds
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Pt.MedianTailWindow

 

set_option autoImplicit false
noncomputable section

open MeasureTheory ProbabilityTheory Set Metric
open scoped ENNReal
open LQGMetric LQGMetric.DFGPS LQGMetric.Blueprint

namespace SupercriticalLQGUniqueness.B2.DG20Pt

theorem dg20_heat_normalizer_bounds_away_zero
    (ξ : Ioi (0 : ℝ))
    (m : Ioi (0 : ℝ) → Ioi (0 : ℝ))
    (hm : ∀ ε, IsLFPPNormalizer ξ ε (m ε))
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (h : Ω → DistC)
    (hh : IsNormalizedWholePlaneGFF h P)
    (X : Ioi (0 : ℝ) → Ω → C(ℂ, ℝ))
    (hX : ∀ ε, IsHeatSmoothing P h ε (X ε))
    (ε₁ : ℝ) (hε₁ : 0 < ε₁) :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧
      ∀ ε : Ioo (0 : ℝ) 1, ε₁ ≤ (ε : ℝ) →
        c ≤ (m ⟨ε, ε.property.1⟩ : ℝ) ∧
        (m ⟨ε, ε.property.1⟩ : ℝ) ≤ C := by
  obtain ⟨M, hM, htail⟩ :=
    dg20_heat_compact_field_tail_away_zero P h hh X hX
      ε₁ 2 hε₁ closedUnitSquare
      LQGMetric.DFGPS.closedUnitSquare_subset_closedBall_two
      (1 / 4) (by norm_num)
  let c : ℝ := Real.exp (-(|(ξ : ℝ)| * M))
  let C : ℝ := Real.exp (|(ξ : ℝ)| * M)
  have hc : 0 < c := Real.exp_pos _
  have hC : 0 < C := Real.exp_pos _
  refine ⟨c, C, hc, hC, ?_⟩
  intro ε hε
  let e : Ioi (0 : ℝ) := ⟨ε, ε.property.1⟩
  let Y : Ω → ℝ≥0∞ := fun ω => lfppCrossingLength ξ (X e ω)
  have hmed : IsMedian P Y (ENNReal.ofReal (m e : ℝ)) :=
    hm e P h hh (X e) (hX e)
  have hbad := htail ε hε
  have hquarter : ENNReal.ofReal (1 / 4 : ℝ) < 2⁻¹ := by
    have hhalf : ENNReal.ofReal (1 / 2 : ℝ) = (2 : ℝ≥0∞)⁻¹ := by
      rw [show (1 / 2 : ℝ) = 2⁻¹ by norm_num,
        ENNReal.ofReal_inv_of_pos (by norm_num)]
      norm_num
    rw [← hhalf]
    exact (ENNReal.ofReal_lt_ofReal_iff (by norm_num)).2 (by norm_num)
  have hlo : P {ω | Y ω < ENNReal.ofReal c} < 2⁻¹ := by
    have hsub : {ω | Y ω < ENNReal.ofReal c} ⊆
        {ω | ∃ x ∈ closedUnitSquare, M < |X e ω x|} := by
      intro ω hw
      by_contra hn
      change ¬ ∃ x ∈ closedUnitSquare, M < |X e ω x| at hn
      push Not at hn
      have hb := (dg20_heat_crossing_bounds_of_square_field ξ (X e ω)
        M (fun x hx => hn x hx)).1
      exact (not_lt_of_ge hb) hw
    exact (measure_mono hsub).trans_lt (hbad.trans_lt hquarter)
  have hhi : P {ω | ENNReal.ofReal C < Y ω} < 2⁻¹ := by
    have hsub : {ω | ENNReal.ofReal C < Y ω} ⊆
        {ω | ∃ x ∈ closedUnitSquare, M < |X e ω x|} := by
      intro ω hw
      by_contra hn
      change ¬ ∃ x ∈ closedUnitSquare, M < |X e ω x| at hn
      push Not at hn
      have hb := (dg20_heat_crossing_bounds_of_square_field ξ (X e ω)
        M (fun x hx => hn x hx)).2
      exact (not_lt_of_ge hb) hw
    exact (measure_mono hsub).trans_lt (hbad.trans_lt hquarter)
  obtain ⟨hloM, hhiM⟩ :=
    dg20_median_between_strict_half_tails P Y
      (ENNReal.ofReal (m e : ℝ)) (ENNReal.ofReal c)
      (ENNReal.ofReal C) hmed hlo hhi
  exact ⟨(ENNReal.ofReal_le_ofReal_iff (m e).property.le).1 hloM,
    (ENNReal.ofReal_le_ofReal_iff hC.le).1 hhiM⟩

end SupercriticalLQGUniqueness.B2.DG20Pt
