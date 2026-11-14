/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.B2.DG20Pt.HeatScaleIface at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Pt.HeatNormalizerGlobalCompare
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Pt.HeatScaleRatioAlgebra

 

set_option autoImplicit false
noncomputable section

open MeasureTheory ProbabilityTheory Set
open LQGMetric LQGMetric.DDDF LQGMetric.WhiteNoise

namespace SupercriticalLQGUniqueness.B2.DG20Pt

theorem dg20Section4_scale_of_inputs
    (hPerc : SupercriticalLQGUniqueness.B2.Iface.DG20PercEstimate')
    (hExp : SupercriticalLQGUniqueness.B2.Iface.DG20ExponentRelation)
    (ξ : Ioi (0 : ℝ)) (Q : ℝ) (hQ : IsLFPPExponent ξ Q)
    (m : Ioi (0 : ℝ) → Ioi (0 : ℝ))
    (hm : ∀ ε, IsLFPPNormalizer ξ ε (m ε))
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (h : Ω → DistC)
    (hh : IsNormalizedWholePlaneGFF h P)
    (X : Ioi (0 : ℝ) → Ω → C(ℂ, ℝ))
    (hX : ∀ ε, IsHeatSmoothing P h ε (X ε)) :
    (∀ ζ : ℝ, 0 < ζ → ∃ D : ℝ, 0 < D ∧
      ∀ r : Ioo (0 : ℝ) 1, ∀ ε : Ioo (0 : ℝ) (r : ℝ),
        D⁻¹ * (r : ℝ) ^ ((ξ : ℝ) * Q + ζ) ≤
          (r : ℝ) * (m ⟨(ε : ℝ) / (r : ℝ),
            Set.mem_Ioi.mpr (div_pos ε.property.1 r.property.1)⟩ : ℝ) /
            (m ⟨(ε : ℝ), Set.mem_Ioi.mpr ε.property.1⟩ : ℝ) ∧
        (r : ℝ) * (m ⟨(ε : ℝ) / (r : ℝ),
            Set.mem_Ioi.mpr (div_pos ε.property.1 r.property.1)⟩ : ℝ) /
            (m ⟨(ε : ℝ), Set.mem_Ioi.mpr ε.property.1⟩ : ℝ) ≤
          D * (r : ℝ) ^ ((ξ : ℝ) * Q - ζ)) ∧
    (∀ ζ : ℝ, 0 < ζ → ∃ D : ℝ, 0 < D ∧
      ∀ r : Ioi (1 : ℝ), ∀ ε : Ioo (0 : ℝ) 1,
        D⁻¹ * (r : ℝ) ^ ((ξ : ℝ) * Q - ζ) ≤
          (r : ℝ) * (m ⟨(ε : ℝ) / (r : ℝ),
            Set.mem_Ioi.mpr (div_pos ε.property.1 (lt_trans one_pos r.property))⟩ : ℝ) /
            (m ⟨(ε : ℝ), Set.mem_Ioi.mpr ε.property.1⟩ : ℝ) ∧
        (r : ℝ) * (m ⟨(ε : ℝ) / (r : ℝ),
            Set.mem_Ioi.mpr (div_pos ε.property.1 (lt_trans one_pos r.property))⟩ : ℝ) /
            (m ⟨(ε : ℝ), Set.mem_Ioi.mpr ε.property.1⟩ : ℝ) ≤
          D * (r : ℝ) ^ ((ξ : ℝ) * Q + ζ)) := by
  have hscale (ζ : ℝ) (hζ : 0 < ζ) :
      ∃ D : ℝ, 0 < D ∧
        (∀ r : Ioo (0 : ℝ) 1, ∀ ε : Ioo (0 : ℝ) (r : ℝ),
          D⁻¹ * (r : ℝ) ^ ((ξ : ℝ) * Q + ζ) ≤
            (r : ℝ) * (m ⟨(ε : ℝ) / (r : ℝ),
              Set.mem_Ioi.mpr (div_pos ε.property.1 r.property.1)⟩ : ℝ) /
              (m ⟨(ε : ℝ), Set.mem_Ioi.mpr ε.property.1⟩ : ℝ) ∧
          (r : ℝ) * (m ⟨(ε : ℝ) / (r : ℝ),
              Set.mem_Ioi.mpr (div_pos ε.property.1 r.property.1)⟩ : ℝ) /
              (m ⟨(ε : ℝ), Set.mem_Ioi.mpr ε.property.1⟩ : ℝ) ≤
            D * (r : ℝ) ^ ((ξ : ℝ) * Q - ζ)) ∧
        (∀ r : Ioi (1 : ℝ), ∀ ε : Ioo (0 : ℝ) 1,
          D⁻¹ * (r : ℝ) ^ ((ξ : ℝ) * Q - ζ) ≤
            (r : ℝ) * (m ⟨(ε : ℝ) / (r : ℝ),
              Set.mem_Ioi.mpr (div_pos ε.property.1 (lt_trans one_pos r.property))⟩ : ℝ) /
              (m ⟨(ε : ℝ), Set.mem_Ioi.mpr ε.property.1⟩ : ℝ) ∧
          (r : ℝ) * (m ⟨(ε : ℝ) / (r : ℝ),
              Set.mem_Ioi.mpr (div_pos ε.property.1 (lt_trans one_pos r.property))⟩ : ℝ) /
              (m ⟨(ε : ℝ), Set.mem_Ioi.mpr ε.property.1⟩ : ℝ) ≤
            D * (r : ℝ) ^ ((ξ : ℝ) * Q + ζ)) := by
    obtain ⟨G, hG, hcomp⟩ :=
      dg20_heat_median_white_noise_compare_all_scales_of_inputs
        hPerc hExp ξ Q hQ m hm P h hh X hX ζ hζ
    obtain ⟨C, B, hC, hB, hpair⟩ :=
      dg20_lambda_delta_real_pair_of_inputs hPerc hExp ξ Q hQ ζ hζ
    let L : ℝ := B⁻¹ * (C⁻¹ * (2 : ℝ) ^ (-|1 - (ξ : ℝ) * Q + ζ|))
    let U : ℝ := B * (C * (2 : ℝ) ^ |1 - (ξ : ℝ) * Q - ζ|)
    have hL : 0 < L := by dsimp [L]; positivity
    have hU : 0 < U := by dsimp [U]; positivity
    let α : ℝ := L / (G * G)
    let β : ℝ := G * G * U
    have hα : 0 < α := by dsimp [α]; positivity
    have hβ : 0 < β := by dsimp [β]; positivity
    let D : ℝ := max β α⁻¹
    have hD : 0 < D := lt_of_lt_of_le hβ (le_max_left _ _)
    have hDβ : β ≤ D := le_max_left _ _
    have hDα : α⁻¹ ≤ D := le_max_right _ _
    have hDinvβ : D⁻¹ ≤ β⁻¹ := by
      simpa only [one_div] using one_div_le_one_div_of_le hβ hDβ
    have hDinvα : D⁻¹ ≤ α := by
      have h := one_div_le_one_div_of_le (inv_pos.mpr hα) hDα
      simpa only [one_div, inv_inv] using h
    obtain ⟨W, hW⟩ := WhiteNoise.exists_isWhiteNoise
    refine ⟨D, hD, ?_, ?_⟩
    · intro r ε
      let ε₁ : Ioo (0 : ℝ) 1 := ⟨ε, ε.property.1,
        lt_trans ε.property.2 r.property.2⟩
      let ε₂ : Ioo (0 : ℝ) 1 :=
        ⟨(ε : ℝ) / (r : ℝ), div_pos ε.property.1 r.property.1,
          (div_lt_one r.property.1).2 ε.property.2⟩
      have hε₁₂ : (ε₁ : ℝ) < (ε₂ : ℝ) := by
        dsimp [ε₁, ε₂]
        exact (lt_div_iff₀ r.property.1).2
          (mul_lt_of_lt_one_right ε.property.1 r.property.2)
      have hratio : (ε₁ : ℝ) / (ε₂ : ℝ) = (r : ℝ) := by
        dsimp [ε₁, ε₂]
        field_simp [ne_of_gt ε.property.1, ne_of_gt r.property.1]
      have hpair' :
          L * (r : ℝ) ^ (1 - (ξ : ℝ) * Q + ζ) *
              lambdaDelta ξ W LQGDimension.ExistAsm.stdP ε₂ ≤
              lambdaDelta ξ W LQGDimension.ExistAsm.stdP ε₁ ∧
          lambdaDelta ξ W LQGDimension.ExistAsm.stdP ε₁ ≤
            U * (r : ℝ) ^ (1 - (ξ : ℝ) * Q - ζ) *
              lambdaDelta ξ W LQGDimension.ExistAsm.stdP ε₂ := by
        simpa only [L, U, hratio, mul_assoc] using
          hpair LQGDimension.ExistAsm.stdP W hW ε₁ ε₂ hε₁₂
      have htransfer := dg20_scale_pair_transfer hG hL hU r.property.1
        (hcomp ε₁ LQGDimension.ExistAsm.stdP W hW)
        (hcomp ε₂ LQGDimension.ExistAsm.stdP W hW) hpair'
      have hmε : 0 < (m ⟨(ε : ℝ), ε.property.1⟩ : ℝ) :=
        (m ⟨(ε : ℝ), ε.property.1⟩).property
      have hratio' := dg20_scale_ratio_fine_first
        r.property.1 hα hβ hmε htransfer.1 htransfer.2
      constructor
      · exact (mul_le_mul_of_nonneg_right hDinvβ
          (Real.rpow_pos_of_pos r.property.1 _).le).trans hratio'.1
      · exact hratio'.2.trans
          (mul_le_mul_of_nonneg_right hDα
            (Real.rpow_pos_of_pos r.property.1 _).le)
    · intro r ε
      let ε₁ : Ioo (0 : ℝ) 1 :=
        ⟨(ε : ℝ) / (r : ℝ),
          div_pos ε.property.1 (lt_trans one_pos r.property),
          (div_lt_one (lt_trans one_pos r.property)).2
            (lt_trans ε.property.2 r.property)⟩
      let ε₂ : Ioo (0 : ℝ) 1 := ε
      have hε₁₂ : (ε₁ : ℝ) < (ε₂ : ℝ) := by
        dsimp [ε₁, ε₂]
        exact (div_lt_iff₀ (lt_trans one_pos r.property)).2
          (lt_mul_of_one_lt_right ε.property.1 r.property)
      have hratio : (ε₁ : ℝ) / (ε₂ : ℝ) = (r : ℝ)⁻¹ := by
        dsimp [ε₁, ε₂]
        field_simp [ne_of_gt ε.property.1,
          ne_of_gt (show (0 : ℝ) < (r : ℝ) from
            lt_trans one_pos r.property)]
      have hpair' :
          L * (r : ℝ)⁻¹ ^ (1 - (ξ : ℝ) * Q + ζ) *
              lambdaDelta ξ W LQGDimension.ExistAsm.stdP ε₂ ≤
              lambdaDelta ξ W LQGDimension.ExistAsm.stdP ε₁ ∧
          lambdaDelta ξ W LQGDimension.ExistAsm.stdP ε₁ ≤
            U * (r : ℝ)⁻¹ ^ (1 - (ξ : ℝ) * Q - ζ) *
              lambdaDelta ξ W LQGDimension.ExistAsm.stdP ε₂ := by
        simpa only [L, U, hratio, mul_assoc] using
          hpair LQGDimension.ExistAsm.stdP W hW ε₁ ε₂ hε₁₂
      have htransfer := dg20_scale_pair_transfer hG hL hU
        (inv_pos.mpr (lt_trans one_pos r.property))
        (hcomp ε₁ LQGDimension.ExistAsm.stdP W hW)
        (hcomp ε₂ LQGDimension.ExistAsm.stdP W hW) hpair'
      have hmε : 0 < (m ⟨(ε : ℝ), ε.property.1⟩ : ℝ) :=
        (m ⟨(ε : ℝ), ε.property.1⟩).property
      have hratio' := dg20_scale_ratio_coarse_first
        (lt_trans one_pos r.property) hα hβ hmε htransfer.1 htransfer.2
      constructor
      · exact (mul_le_mul_of_nonneg_right hDinvα
          (Real.rpow_pos_of_pos (lt_trans one_pos r.property) _).le).trans
          hratio'.1
      · exact hratio'.2.trans
          (mul_le_mul_of_nonneg_right hDβ
            (Real.rpow_pos_of_pos (lt_trans one_pos r.property) _).le)
  constructor
  · intro ζ hζ
    obtain ⟨D, hD, hsmall, _⟩ := hscale ζ hζ
    exact ⟨D, hD, hsmall⟩
  · intro ζ hζ
    obtain ⟨D, hD, _, hlarge⟩ := hscale ζ hζ
    exact ⟨D, hD, hlarge⟩

end SupercriticalLQGUniqueness.B2.DG20Pt
