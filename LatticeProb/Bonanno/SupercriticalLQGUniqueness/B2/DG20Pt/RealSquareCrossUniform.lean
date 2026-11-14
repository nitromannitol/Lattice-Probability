/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.B2.DG20Pt.RealSquareCrossUniform at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Pt.RealSquareCrossTails
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Pt.NonDyadicMedianLaw

 

set_option autoImplicit false
noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal
open LQGMetric LQGMetric.DDDF LQGMetric.WhiteNoise

namespace SupercriticalLQGUniqueness.B2.DG20Pt

theorem dg20_real_square_cross_tails_uniform_of_perc
    (hPerc : SupercriticalLQGUniqueness.B2.Iface.DG20PercEstimate')
    (ξ : Ioi (0 : ℝ)) :
    ∃ cU CU cL CL : ℝ,
      0 < cU ∧ 0 < CU ∧ 0 < cL ∧ 0 < CL ∧
      ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
        [IsProbabilityMeasure P] (W : WNSpace → Ω → ℝ),
        IsWhiteNoise P W → ∀ s : ℝ, 2 < s →
        ∀ δ : Ioo (0 : ℝ) 1,
          P {ω | Real.exp s * lambdaDelta ξ W P δ ≤
            lenObs ξ (phiVer W P δ 1) (rectAB 1 1) ω} ≤
            ENNReal.ofReal (CU * Real.exp (-cU * s ^ 2 / Real.log s)) ∧
          P {ω | lenObs ξ (phiVer W P δ 1) (rectAB 1 1) ω ≤
            Real.exp (-s) * lambdaDelta ξ W P δ} ≤
            ENNReal.ofReal (CL * Real.exp (-cL * s ^ 2)) := by
  obtain ⟨W₀, hW₀⟩ := exists_isWhiteNoise
  let P₀ : Measure (ℕ → ℝ) := LQGDimension.ExistAsm.stdP
  obtain ⟨⟨cU, CU, hcU, hCU, hU⟩, ⟨cL, CL, hcL, hCL, hL⟩⟩ :=
    dg20_real_square_cross_tails_of_perc hPerc ξ P₀ W₀ hW₀
  refine ⟨cU, CU, cL, CL, hcU, hCU, hcL, hCL, ?_⟩
  intro Ω _ P _ W hW s hs δ
  have hLam := lambdaDelta_eq_of_whiteNoise hW hW₀
    (ξ : ℝ) (δ : ℝ) δ.property.1 δ.property.2.le
  have hLaw := map_lenObs_phiVer_eq_of_whiteNoise hW hW₀
    (ξ : ℝ) (δ : ℝ) δ.property.1 δ.property.2.le
  have hv := isPhiVersion_phiVer hW δ.property.1 δ.property.2.le
  have hv₀ := isPhiVersion_phiVer hW₀ δ.property.1 δ.property.2.le
  have hm := measurable_lenObs hv.cont hv.meas (rectAB 1 1) (ξ := (ξ : ℝ))
  have hm₀ := measurable_lenObs hv₀.cont hv₀.meas (rectAB 1 1) (ξ := (ξ : ℝ))
  constructor
  · calc
      P {ω | Real.exp s * lambdaDelta ξ W P δ ≤
        lenObs ξ (phiVer W P δ 1) (rectAB 1 1) ω} =
        P.map (lenObs ξ (phiVer W P δ 1) (rectAB 1 1))
          (Ici (Real.exp s * lambdaDelta ξ W P δ)) := by
            rw [Measure.map_apply hm measurableSet_Ici]
            rfl
      _ = P₀.map (lenObs ξ (phiVer W₀ P₀ δ 1) (rectAB 1 1))
          (Ici (Real.exp s * lambdaDelta ξ W P δ)) := by rw [hLaw]
      _ = P₀ {ω | Real.exp s * lambdaDelta ξ W₀ P₀ δ ≤
          lenObs ξ (phiVer W₀ P₀ δ 1) (rectAB 1 1) ω} := by
            rw [Measure.map_apply hm₀ measurableSet_Ici, hLam]
            rfl
      _ ≤ _ := hU s hs δ δ.property.1 δ.property.2
  · calc
      P {ω | lenObs ξ (phiVer W P δ 1) (rectAB 1 1) ω ≤
        Real.exp (-s) * lambdaDelta ξ W P δ} =
        P.map (lenObs ξ (phiVer W P δ 1) (rectAB 1 1))
          (Iic (Real.exp (-s) * lambdaDelta ξ W P δ)) := by
            rw [Measure.map_apply hm measurableSet_Iic]
            rfl
      _ = P₀.map (lenObs ξ (phiVer W₀ P₀ δ 1) (rectAB 1 1))
          (Iic (Real.exp (-s) * lambdaDelta ξ W P δ)) := by rw [hLaw]
      _ = P₀ {ω | lenObs ξ (phiVer W₀ P₀ δ 1) (rectAB 1 1) ω ≤
          Real.exp (-s) * lambdaDelta ξ W₀ P₀ δ} := by
            rw [Measure.map_apply hm₀ measurableSet_Iic, hLam]
            rfl
      _ ≤ _ := hL s hs δ δ.property.1 δ.property.2

end SupercriticalLQGUniqueness.B2.DG20Pt
