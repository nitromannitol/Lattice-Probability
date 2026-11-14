/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.B2.DG20Conc.LaneA2LargeSameP at commit fdb5cad; only the module paths of local imports are changed.
   Imports of copied modules that this file does not need are replaced by their own imports. -/
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Conc.LaneA2ShiftRates
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Conc.LaneA2Large

 

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

open Set Metric MeasureTheory
open scoped ENNReal

namespace SupercriticalLQGUniqueness.B2.DG20Conc

open LQGMetric.DDDF LQGMetric.WhiteNoise LQGMetric.LFPP

universe u

theorem laneA2_large_same_p
    {ξ p : ℝ} (hunit : LaneA2HasUnitTails.{u} ξ p) :
    ∃ R₀ G Cneg cNeg Cpos cPos : ℝ,
      24 ≤ R₀ ∧ 1 ≤ G ∧ 0 < Cneg ∧ 0 < cNeg ∧
      0 < Cpos ∧ 0 < cPos ∧
      ∀ (R : ℝ), R₀ ≤ R →
        ∀ {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω)
          (W : WNSpace → Ω → ℝ) (hW : IsWhiteNoise P W)
          (m : ℕ) (T : ℝ), 3 < T →
            P {ω | crossLenIn ξ (fun z => phiMN W P 0 m z ω)
              {z : ℂ | dist z 0 ∈ Icc R (2 * R)}
              (sphere (0 : ℂ) R) (sphere (0 : ℂ) (2 * R)) <
              ENNReal.ofReal (T⁻¹ * ellN ξ W P m (ENNReal.ofReal p))} ≤
              ENNReal.ofReal ((G * Cneg) * R *
                Real.exp (-cNeg * (Real.log T)^2)) ∧
            P {ω | ENNReal.ofReal ((T * R) *
              (LambdaN ξ W P m (ENNReal.ofReal p) *
                ellN ξ W P m (ENNReal.ofReal p))) <
              (lfppContMetric ξ (fun z => phiMN W P 0 m z ω)
                ((isPhiVersion_phiMN hW (Nat.zero_le m)).cont ω)).aroundDist
                {z : ℂ | R < dist z 0 ∧ dist z 0 < 2 * R}
                (sphere (0 : ℂ) R) (sphere (0 : ℂ) (2 * R))} ≤
              ENNReal.ofReal (laneA_upperConstant G Cpos cPos * R *
                Real.exp (-(cPos / 4) * (Real.log T)^2 /
                  Real.log (Real.log T))) := by
  obtain ⟨Cn, cn, Cp, cp, hCn, hcn, hCp, hcp, ht⟩ := hunit
  obtain ⟨R₀, G, hR₀, hG, hR⟩ := laneB_repairedLargeAnnulusGeometry
  refine ⟨R₀, G, Cn, cn, Cp, cp, hR₀, hG,
    hCn, hcn, hCp, hcp, ?_⟩
  intro R hRR Ω _ P W hW m T hT
  exact laneA_source_tails_of_cover P hW (by linarith [hR₀, hRR]) hG
    (laneA2_cover0_to_old (hR R hRR)) hCp hcp
    (fun m T hT => (ht P W hW m T hT).1)
    (fun m T hT => (ht P W hW m T hT).2) m T hT

end SupercriticalLQGUniqueness.B2.DG20Conc
