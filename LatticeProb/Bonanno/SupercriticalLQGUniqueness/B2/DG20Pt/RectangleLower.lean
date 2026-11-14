/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.B2.DG20Pt.RectangleLower at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Pt.GaussianFourSum

 




set_option autoImplicit false
noncomputable section

open Set Metric MeasureTheory ProbabilityTheory TopologicalSpace
open scoped ENNReal
open LQGMetric.DDDF LQGMetric.WhiteNoise

namespace SupercriticalLQGUniqueness.B2.DG20Pt

 


theorem perc_field_rectangle_lower_of_inputs
    (hPerc : SupercriticalLQGUniqueness.B2.Iface.DG20PercEstimate')
    (hExp : SupercriticalLQGUniqueness.B2.Iface.DG20ExponentRelation)
    (ξ : Ioi (0 : ℝ)) (Q : ℝ) (hQ : IsLFPPExponent ξ Q)
    (ζ : ℝ) (hζ : 0 < ζ)
    (x₀ x₃ y₀ y₃ : ℝ) (hx : x₀ < x₃) (hy : y₀ < y₃)
    (A B : Set ℂ)
    (hAK : A ⊆ Icc x₀ x₃ ×ℂ Icc y₀ y₃)
    (hBK : B ⊆ Icc x₀ x₃ ×ℂ Icc y₀ y₃)
    (hA : IsCompact A) (hB : IsCompact B)
    (hconnA : IsConnected A) (hconnB : IsConnected B)
    (hntA : A.Nontrivial) (hntB : B.Nontrivial)
    (hdisj : Disjoint A B) :
    ∃ c₀ c₁ : ℝ, 0 < c₀ ∧ 0 < c₁ ∧
      ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
        [IsProbabilityMeasure P] (W : WNSpace → Ω → ℝ),
        IsWhiteNoise P W → ∀ n k : ℕ, k ≤ n → ∀ T : ℝ, 3 < T →
        let r : ℝ := (2 : ℝ)⁻¹ ^ k
        let F : ℂ → ℂ := fun z => (r : ℂ) * z
        P {ω | crossLenIn (ξ : ℝ) (fun z => phiMN W P 0 n z ω)
            (F '' (Icc x₀ x₃ ×ℂ Icc y₀ y₃)) (F '' A) (F '' B) <
          ENNReal.ofReal (Real.exp ((ξ : ℝ) * phiMN W P 0 k 0 ω)) *
            ENNReal.ofReal (T⁻¹ *
              ((2 : ℝ) ^ (-((ξ : ℝ) * Q + ζ) * (k : ℝ)) * lambdaN ξ W P n))} ≤
          ENNReal.ofReal (c₀ * Real.exp (-c₁ * (Real.log T) ^ 2)) := by
  let U : Opens ℂ := ⟨Ioo (x₀ - 1) (x₃ + 1) ×ℂ
    Ioo (y₀ - 1) (y₃ + 1),
    (open_box_geometry (show x₀ - 1 < x₃ + 1 by linarith)
      (show y₀ - 1 < y₃ + 1 by linarith)).1⟩
  have hgeom := open_box_geometry
    (show x₀ - 1 < x₃ + 1 by linarith)
    (show y₀ - 1 < y₃ + 1 by linarith)
  have hKU : Icc x₀ x₃ ×ℂ Icc y₀ y₃ ⊆ U := by
    intro z hz
    change z ∈ Ioo (x₀ - 1) (x₃ + 1) ×ℂ Ioo (y₀ - 1) (y₃ + 1)
    rw [Complex.mem_reProdIm] at hz ⊢
    exact ⟨⟨by linarith [hz.1.1], by linarith [hz.1.2]⟩,
      ⟨by linarith [hz.2.1], by linarith [hz.2.2]⟩⟩
  exact perc_field_compact_subdomain_lower_of_inputs hPerc hExp ξ Q hQ ζ hζ
    U hgeom.2.1 hgeom.2.2 _ A B hKU hAK hBK hA hB
      hconnA hconnB hntA hntB hdisj

end SupercriticalLQGUniqueness.B2.DG20Pt
