/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.B2.DG20Pt.HorizontalLower at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Pt.RectangleLower

 

set_option autoImplicit false
noncomputable section

open Set MeasureTheory ProbabilityTheory
open scoped ENNReal
open LQGMetric.DDDF LQGMetric.WhiteNoise

namespace SupercriticalLQGUniqueness.B2.DG20Pt

 


theorem perc_field_horizontal_sides_lower_of_inputs
    (hPerc : SupercriticalLQGUniqueness.B2.Iface.DG20PercEstimate')
    (hExp : SupercriticalLQGUniqueness.B2.Iface.DG20ExponentRelation)
    (ξ : Ioi (0 : ℝ)) (Q : ℝ) (hQ : IsLFPPExponent ξ Q)
    (ζ : ℝ) (hζ : 0 < ζ)
    (x₀ x₃ y₀ y₃ a b : ℝ)
    (hx : x₀ < x₃) (hy : y₀ < y₃)
    (ha₀ : y₀ ≤ a) (ha₃ : a ≤ y₃)
    (hb₀ : y₀ ≤ b) (hb₃ : b ≤ y₃) (hab : a ≠ b) :
    ∃ c₀ c₁ : ℝ, 0 < c₀ ∧ 0 < c₁ ∧
      ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
        [IsProbabilityMeasure P] (W : WNSpace → Ω → ℝ),
        IsWhiteNoise P W → ∀ n k : ℕ, k ≤ n → ∀ T : ℝ, 3 < T →
        let r : ℝ := (2 : ℝ)⁻¹ ^ k
        let F : ℂ → ℂ := fun z => (r : ℂ) * z
        P {ω | crossLenIn (ξ : ℝ) (fun z => phiMN W P 0 n z ω)
            (F '' (Icc x₀ x₃ ×ℂ Icc y₀ y₃))
            (F '' (Icc x₀ x₃ ×ℂ ({a} : Set ℝ)))
            (F '' (Icc x₀ x₃ ×ℂ ({b} : Set ℝ))) <
          ENNReal.ofReal (Real.exp ((ξ : ℝ) * phiMN W P 0 k 0 ω)) *
            ENNReal.ofReal (T⁻¹ *
              ((2 : ℝ) ^ (-((ξ : ℝ) * Q + ζ) * (k : ℝ)) * lambdaN ξ W P n))} ≤
          ENNReal.ofReal (c₀ * Real.exp (-c₁ * (Real.log T) ^ 2)) := by
  have hsub (t : ℝ) (ht₀ : y₀ ≤ t) (ht₃ : t ≤ y₃) :
      Icc x₀ x₃ ×ℂ ({t} : Set ℝ) ⊆ Icc x₀ x₃ ×ℂ Icc y₀ y₃ := by
    intro z hz
    rw [Complex.mem_reProdIm] at hz ⊢
    simp only [mem_singleton_iff] at hz
    exact ⟨hz.1, ⟨by simpa only [hz.2] using ht₀,
      by simpa only [hz.2] using ht₃⟩⟩
  have hgA := horizontal_side_geometry (y := a) hx
  have hgB := horizontal_side_geometry (y := b) hx
  exact perc_field_rectangle_lower_of_inputs hPerc hExp ξ Q hQ ζ hζ
    x₀ x₃ y₀ y₃ hx hy _ _
    (hsub a ha₀ ha₃) (hsub b hb₀ hb₃)
    hgA.1 hgB.1 hgA.2.1 hgB.2.1 hgA.2.2 hgB.2.2
    (horizontal_sides_disjoint x₀ x₃ a b hab)

end SupercriticalLQGUniqueness.B2.DG20Pt
