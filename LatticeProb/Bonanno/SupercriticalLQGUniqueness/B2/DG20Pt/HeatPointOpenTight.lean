/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.B2.DG20Pt.HeatPointOpenTight at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Pt.HeatPointOpenSmallUpper
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Pt.HeatPointOpenSmallLower
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Pt.HeatPointAwayZeroNormalized
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Pt.PtDistOpenMeasurable
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.PfeAxioms.HeatVersionMeasurable

 

set_option autoImplicit false
noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal
open LQGMetric LQGMetric.DDDF

namespace SupercriticalLQGUniqueness.B2.DG20Pt

theorem dg20_heat_point_open_two_sided_tight_of_inputs
    (hPerc : SupercriticalLQGUniqueness.B2.Iface.DG20PercEstimate')
    (hExp : SupercriticalLQGUniqueness.B2.Iface.DG20ExponentRelation)
    (hPos : SupercriticalLQGUniqueness.B2.Iface.DG20ExponentPositive)
    (ξ : Ioi (0 : ℝ)) (Qexp : ℝ) (hQ : IsLFPPExponent ξ Qexp)
    (m : Ioi (0 : ℝ) → Ioi (0 : ℝ))
    (hm : ∀ ε, IsLFPPNormalizer ξ ε (m ε))
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (h : Ω → DistC)
    (hh : IsNormalizedWholePlaneGFF h P)
    (X : Ioi (0 : ℝ) → Ω → C(ℂ, ℝ))
    (hX : ∀ ε, IsHeatSmoothing P h ε (X ε))
    (U : Set ℂ) (hU : IsOpen U) (hUc : IsConnected U)
    (z w : ℂ) (hz : z ∈ U) (hw : w ∈ U) (hzw : z ≠ w) :
    IsTwoSidedTight P (fun (ε : Ioo (0 : ℝ) 1) ω =>
      ENNReal.ofReal (m ⟨ε, ε.property.1⟩ : ℝ)⁻¹ *
        crossLenIn ξ (X ⟨ε, ε.property.1⟩ ω) U {z} {w}) := by
  constructor
  · intro ε
    exact
      (measurable_const.mul (pt_dist_measurable_crossLenIn_open ξ
        U {z} {w} hU (fun ψ : C(ℂ, ℝ) => ψ.continuous)
        (fun y => (continuous_eval_const y).measurable))).comp_aemeasurable
          (B2.PfeAxioms.aemeasurable_heat_smoothing_version P h hh
            ⟨ε, ε.property.1⟩ (X ⟨ε, ε.property.1⟩)
            (hX ⟨ε, ε.property.1⟩))
  · intro η hη
    obtain ⟨T₁, ε₁, hT₁, hε₁, hsmallHi⟩ :=
      dg20_heat_point_open_small_upper_of_inputs
        hPerc hExp hPos ξ Qexp hQ m hm P h hh X hX
        U hU hUc z w hz hw η hη
    obtain ⟨T₂, ε₂, hT₂, hε₂, hsmallLo⟩ :=
      dg20_heat_point_open_small_lower_of_perc
        hPerc ξ m hm P h hh X hX U z w hzw η hη
    let ε₀ : ℝ := min ε₁ ε₂
    have hε₀ : 0 < ε₀ := lt_min hε₁ hε₂
    obtain ⟨T₃, hT₃, hfar⟩ :=
      dg20_heat_point_away_zero_normalized_tails
        ξ m hm P h hh X hX ε₀ hε₀ U hU hUc
        z w hz hw hzw η hη
    let T : ℝ := max (max T₁ T₂) T₃
    have hT : 0 < T := lt_of_lt_of_le hT₁
      ((le_max_left T₁ T₂).trans (le_max_left (max T₁ T₂) T₃))
    have hT₁le : T₁ ≤ T := (le_max_left T₁ T₂).trans (le_max_left _ _)
    have hT₂le : T₂ ≤ T := (le_max_right T₁ T₂).trans (le_max_left _ _)
    have hT₃le : T₃ ≤ T := le_max_right _ _
    have hInv₂ : T⁻¹ ≤ T₂⁻¹ := inv_anti₀ hT₂ hT₂le
    have hInv₃ : T⁻¹ ≤ T₃⁻¹ := inv_anti₀ hT₃ hT₃le
    refine ⟨T, hT, ?_⟩
    intro ε
    let D : Ω → ℝ≥0∞ := fun ω =>
      ENNReal.ofReal (m ⟨ε, ε.property.1⟩ : ℝ)⁻¹ *
        crossLenIn ξ (X ⟨ε, ε.property.1⟩ ω) U {z} {w}
    by_cases hε : (ε : ℝ) < ε₀
    · have hhi := hsmallHi ε (lt_of_lt_of_le hε (min_le_left _ _))
      have hlo := hsmallLo ε (lt_of_lt_of_le hε (min_le_right _ _))
      constructor
      · calc
          P {ω | ENNReal.ofReal T < D ω} ≤
            P {ω | ENNReal.ofReal T₁ < D ω} := by
              apply measure_mono
              intro ω hw
              exact lt_of_le_of_lt (ENNReal.ofReal_le_ofReal hT₁le) hw
          _ ≤ ENNReal.ofReal η := by simpa only [D] using hhi
      · calc
          P {ω | D ω < ENNReal.ofReal T⁻¹} ≤
            P {ω | D ω < ENNReal.ofReal T₂⁻¹} := by
              apply measure_mono
              intro ω hw
              exact lt_of_lt_of_le hw (ENNReal.ofReal_le_ofReal hInv₂)
          _ ≤ ENNReal.ofReal η := by simpa only [D] using hlo
    · have hε' : ε₀ ≤ (ε : ℝ) := le_of_not_gt hε
      obtain ⟨hhi, hlo⟩ := hfar ε hε'
      constructor
      · calc
          P {ω | ENNReal.ofReal T < D ω} ≤
            P {ω | ENNReal.ofReal T₃ < D ω} := by
              apply measure_mono
              intro ω hw
              exact lt_of_le_of_lt (ENNReal.ofReal_le_ofReal hT₃le) hw
          _ ≤ ENNReal.ofReal η := by simpa only [D] using hhi
      · calc
          P {ω | D ω < ENNReal.ofReal T⁻¹} ≤
            P {ω | D ω < ENNReal.ofReal T₃⁻¹} := by
              apply measure_mono
              intro ω hw
              exact lt_of_lt_of_le hw (ENNReal.ofReal_le_ofReal hInv₃)
          _ ≤ ENNReal.ofReal η := by simpa only [D] using hlo

end SupercriticalLQGUniqueness.B2.DG20Pt
