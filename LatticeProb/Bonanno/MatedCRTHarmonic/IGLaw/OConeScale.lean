/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module MatedCRTHarmonic.IGLaw.OConeZero at commit fdb5cad;
   selected declaration, with local imports adapted. -/
import LatticeProb.Bonanno.MatedCRTHarmonic.CellScaling.ConeDefs
import LatticeProb.Bonanno.MatedCRTHarmonic.ConeScaling.LastLevel

set_option autoImplicit false

noncomputable section

open scoped NNReal

namespace MatedCRTHarmonic.IGLaw

/-- The cone scale `R_b` of the α-cone is `exp (L_y)` of its radial path, `y = γ⁻¹ log b`. -/
theorem coneScale_eq_exp_lastLevel_alpha (γ α b₀ : ℝ) {b b' : NNReal → ℝ} {w : C(ℝ, ℝ)}
    (hw : ∀ t, w t = CellScaling.coneRadial γ α b b' t) :
    CellScaling.coneScale γ α b b' b₀ =
      Real.exp (ConeScaling.lastLevel (CellScaling.lqgQ γ) (γ⁻¹ * Real.log b₀) w) := by
  unfold CellScaling.coneScale ConeScaling.lastLevel CellScaling.coneLogRadial
  simp only [hw]

end MatedCRTHarmonic.IGLaw
