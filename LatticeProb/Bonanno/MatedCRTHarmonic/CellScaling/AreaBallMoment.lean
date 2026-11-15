/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module MatedCRTHarmonic.CellScaling.Model at commit fdb5cad17d11550228cf8dbaf6216e69fc3d2d82, lines 142–144. -/
import LatticeProb.Bonanno.MatedCRTHarmonic.CellScaling.Model

/-! # Moments of the cone area of the unit ball -/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set Metric
open scoped ENNReal NNReal

namespace MatedCRTHarmonic.CellScaling

def AreaBallMoment {γ : ℝ} {M : MesoModel.MatedCRTUnitMesoModel γ} (D : ConeRealization M) : Prop :=
  AEMeasurable (fun ω => D.area ω (ball 0 1)) M.coupled.family.P ∧
    ∀ p : ℝ, 0 < p → p < 4 / γ ^ 2 - 1 → ∫⁻ ω, D.area ω (ball 0 1) ^ p ∂M.coupled.family.P < ⊤

end MatedCRTHarmonic.CellScaling
