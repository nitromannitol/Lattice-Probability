/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.B2.DG20Pt.NonDyadicLowBandBoxAbs at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Pt.NonDyadicLowBandBox

 

set_option autoImplicit false
noncomputable section

open MeasureTheory ProbabilityTheory Set
open LQGMetric LQGMetric.DDDF LQGMetric.WhiteNoise LQGMetric.SupTail

namespace SupercriticalLQGUniqueness.B2.DG20Pt

theorem dg20_low_band_box_abs_tail
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    (W : WNSpace → Ω → ℝ) (hW : IsWhiteNoise P W)
    (x₀ : ℂ) (b : ℝ) (hb : 0 < b)
    (a : ℝ) (ha12 : 1 / 2 ≤ a) (ha1 : a ≤ 1)
    (u : ℝ) (hu : 0 ≤ u) :
    P.real {ω | ferniqueCF * Real.sqrt ((8 * b) * b) + u ≤
      ⨆ v : ferniqueBox x₀ b, |phiVer W P a 1 v ω|} ≤
      2 * Real.exp (-u ^ 2 / 2) := by
  have := hW.isProbabilityMeasure
  have hY := isPhiVersion_phiVer hW (lt_of_lt_of_le (by norm_num) ha12) ha1
  have hplus := dg20_low_band_box_signed_tail P W hW x₀ b hb a ha12 ha1 1
    (by norm_num) u hu
  have hminus := dg20_low_band_box_signed_tail P W hW x₀ b hb a ha12 ha1 (-1)
    (by norm_num) u hu
  simp only [one_mul] at hplus
  simp only [neg_one_mul] at hminus
  let B : Set ℂ := ferniqueBox x₀ b
  have hB : IsCompact B := isCompact_ferniqueBox x₀ b
  letI : Nonempty B := ⟨⟨x₀, mem_ferniqueBox_self hb.le⟩⟩
  have hsub :
      {ω | ferniqueCF * Real.sqrt ((8 * b) * b) + u ≤
        ⨆ v : B, |phiVer W P a 1 v ω|} ⊆
      {ω | ferniqueCF * Real.sqrt ((8 * b) * b) + u ≤
        ⨆ v : B, phiVer W P a 1 v ω} ∪
      {ω | ferniqueCF * Real.sqrt ((8 * b) * b) + u ≤
        ⨆ v : B, -phiVer W P a 1 v ω} := by
    intro ω hω
    have hpos : BddAbove (range fun v : B => phiVer W P a 1 v ω) :=
      (hB.image (hY.cont ω)).bddAbove.mono (by
        rintro _ ⟨v, rfl⟩
        exact ⟨v, v.2, rfl⟩)
    have hneg : BddAbove (range fun v : B => -phiVer W P a 1 v ω) :=
      (hB.image (hY.cont ω).neg).bddAbove.mono (by
        rintro _ ⟨v, rfl⟩
        exact ⟨v, v.2, rfl⟩)
    have hsup : (⨆ v : B, |phiVer W P a 1 v ω|) ≤
        max (⨆ v : B, phiVer W P a 1 v ω)
          (⨆ v : B, -phiVer W P a 1 v ω) := by
      apply ciSup_le
      intro v
      rcases le_total 0 (phiVer W P a 1 v ω) with hp | hn
      · rw [abs_of_nonneg hp]
        exact (le_ciSup hpos v).trans (le_max_left _ _)
      · rw [abs_of_nonpos hn]
        exact (le_ciSup hneg v).trans (le_max_right _ _)
    rcases (le_max_iff.mp (hω.trans hsup)) with h | h
    · exact Or.inl h
    · exact Or.inr h
  calc
    P.real {ω | ferniqueCF * Real.sqrt ((8 * b) * b) + u ≤
        ⨆ v : B, |phiVer W P a 1 v ω|} ≤
      P.real ({ω | ferniqueCF * Real.sqrt ((8 * b) * b) + u ≤
        ⨆ v : B, phiVer W P a 1 v ω} ∪
        {ω | ferniqueCF * Real.sqrt ((8 * b) * b) + u ≤
        ⨆ v : B, -phiVer W P a 1 v ω}) :=
          measureReal_mono hsub (measure_ne_top P _)
    _ ≤ P.real {ω | ferniqueCF * Real.sqrt ((8 * b) * b) + u ≤
          ⨆ v : B, phiVer W P a 1 v ω} +
        P.real {ω | ferniqueCF * Real.sqrt ((8 * b) * b) + u ≤
          ⨆ v : B, -phiVer W P a 1 v ω} := measureReal_union_le _ _
    _ ≤ 2 * Real.exp (-u ^ 2 / 2) := by
      dsimp only [B] at *
      linarith

end SupercriticalLQGUniqueness.B2.DG20Pt
