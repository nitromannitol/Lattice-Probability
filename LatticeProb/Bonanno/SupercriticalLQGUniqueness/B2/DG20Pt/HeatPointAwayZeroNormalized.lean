/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.B2.DG20Pt.HeatPointAwayZeroNormalized at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Pt.HeatPointAwayZeroRawUpper
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Pt.HeatPointAwayZeroRawLower
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Pt.HeatNormalizerAwayZero

 

set_option autoImplicit false
noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal
open LQGMetric LQGMetric.DDDF

namespace SupercriticalLQGUniqueness.B2.DG20Pt

theorem dg20_heat_point_away_zero_normalized_tails
    (ξ : Ioi (0 : ℝ))
    (m : Ioi (0 : ℝ) → Ioi (0 : ℝ))
    (hm : ∀ ε, IsLFPPNormalizer ξ ε (m ε))
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (h : Ω → DistC)
    (hh : IsNormalizedWholePlaneGFF h P)
    (X : Ioi (0 : ℝ) → Ω → C(ℂ, ℝ))
    (hX : ∀ ε, IsHeatSmoothing P h ε (X ε))
    (ε₁ : ℝ) (hε₁ : 0 < ε₁)
    (U : Set ℂ) (hU : IsOpen U) (hUc : IsConnected U)
    (z w : ℂ) (hz : z ∈ U) (hw : w ∈ U) (hzw : z ≠ w)
    (ζ : ℝ) (hζ : 0 < ζ) :
    ∃ T : ℝ, 0 < T ∧
      ∀ ε : Ioo (0 : ℝ) 1, ε₁ ≤ (ε : ℝ) →
        P {ω | ENNReal.ofReal T <
          ENNReal.ofReal (m ⟨ε, ε.property.1⟩ : ℝ)⁻¹ *
            crossLenIn ξ (X ⟨ε, ε.property.1⟩ ω)
              U {z} {w}} ≤ ENNReal.ofReal ζ ∧
        P {ω | ENNReal.ofReal (m ⟨ε, ε.property.1⟩ : ℝ)⁻¹ *
            crossLenIn ξ (X ⟨ε, ε.property.1⟩ ω)
              U {z} {w} < ENNReal.ofReal T⁻¹} ≤ ENNReal.ofReal ζ := by
  obtain ⟨c, C, hc, hC, hmed⟩ :=
    dg20_heat_normalizer_bounds_away_zero ξ m hm P h hh X hX ε₁ hε₁
  obtain ⟨H, hH, hhi⟩ :=
    dg20_heat_point_away_zero_raw_upper ξ P h hh X hX
      ε₁ hε₁ U hU hUc z w hz hw ζ hζ
  obtain ⟨L, hL, hlo⟩ :=
    dg20_heat_point_away_zero_raw_lower ξ P h hh X hX
      ε₁ hε₁ U z w hzw ζ hζ
  let T : ℝ := max (H / c) (C / L) + 1
  have hT : 0 < T := by dsimp [T]; positivity
  have hTH : H / c < T := by dsimp [T]; linarith [le_max_left (H / c) (C / L)]
  have hTL : C / L < T := by dsimp [T]; linarith [le_max_right (H / c) (C / L)]
  have hUpper : ENNReal.ofReal c⁻¹ * ENNReal.ofReal H <
      ENNReal.ofReal T := by
    rw [← ENNReal.ofReal_mul (inv_nonneg.mpr hc.le)]
    exact (ENNReal.ofReal_lt_ofReal_iff hT).2
      (by simpa only [div_eq_mul_inv, mul_comm] using hTH)
  have hLower : ENNReal.ofReal T⁻¹ <
      ENNReal.ofReal C⁻¹ * ENNReal.ofReal L := by
    rw [← ENNReal.ofReal_mul (inv_nonneg.mpr hC.le)]
    apply (ENNReal.ofReal_lt_ofReal_iff (mul_pos (inv_pos.mpr hC) hL)).2
    have hCL : C < T * L := (div_lt_iff₀ hL).1 hTL
    have hh := (div_lt_div_iff₀ hT hC).2 (by nlinarith [hCL] : 1 * C < L * T)
    simpa only [div_eq_mul_inv, one_mul, mul_comm L C⁻¹] using hh
  refine ⟨T, hT, ?_⟩
  intro ε hε
  let e : Ioi (0 : ℝ) := ⟨ε, ε.property.1⟩
  let D : Ω → ℝ≥0∞ := fun ω =>
    crossLenIn ξ (X e ω) U {z} {w}
  have hmb := hmed ε hε
  have hmInvUp : ENNReal.ofReal (m e : ℝ)⁻¹ ≤
      ENNReal.ofReal c⁻¹ := by
    rw [ENNReal.ofReal_inv_of_pos (m e).property,
      ENNReal.ofReal_inv_of_pos hc]
    exact ENNReal.inv_le_inv.mpr
      (ENNReal.ofReal_le_ofReal hmb.1)
  have hmInvLo : ENNReal.ofReal C⁻¹ ≤
      ENNReal.ofReal (m e : ℝ)⁻¹ := by
    rw [ENNReal.ofReal_inv_of_pos hC,
      ENNReal.ofReal_inv_of_pos (m e).property]
    exact ENNReal.inv_le_inv.mpr
      (ENNReal.ofReal_le_ofReal hmb.2)
  constructor
  · have hsub : {ω | ENNReal.ofReal T <
        ENNReal.ofReal (m e : ℝ)⁻¹ * D ω} ⊆
        {ω | ENNReal.ofReal H < D ω} := by
      intro ω hw
      by_contra hn
      have hd : D ω ≤ ENNReal.ofReal H := le_of_not_gt hn
      have hcost :
          ENNReal.ofReal (m e : ℝ)⁻¹ * D ω ≤
            ENNReal.ofReal c⁻¹ * ENNReal.ofReal H :=
        (mul_le_mul_of_nonneg_right hmInvUp bot_le).trans
          (mul_le_mul_of_nonneg_left hd bot_le)
      exact (not_lt_of_ge (hcost.trans hUpper.le)) hw
    exact (measure_mono hsub).trans (by simpa only [D, e] using hhi ε hε)
  · have hsub : {ω | ENNReal.ofReal (m e : ℝ)⁻¹ * D ω <
        ENNReal.ofReal T⁻¹} ⊆
        {ω | D ω < ENNReal.ofReal L} := by
      intro ω hw
      by_contra hn
      have hd : ENNReal.ofReal L ≤ D ω := le_of_not_gt hn
      have hcost :
          ENNReal.ofReal C⁻¹ * ENNReal.ofReal L ≤
            ENNReal.ofReal (m e : ℝ)⁻¹ * D ω :=
        (mul_le_mul_of_nonneg_left hd bot_le).trans
          (mul_le_mul_of_nonneg_right hmInvLo bot_le)
      exact (not_lt_of_ge (hLower.le.trans hcost)) hw
    exact (measure_mono hsub).trans (by simpa only [D, e] using hlo ε hε)

end SupercriticalLQGUniqueness.B2.DG20Pt
