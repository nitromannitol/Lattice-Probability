/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DFGPS.P4_1Xi at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DG.BallMass
import LatticeProb.Bonanno.LQGMetric.Papers.DG.XiQBound

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# DFGPS Proposition 4.1: `ξ < 1`

DFGPS T:2531 uses "`ξ < 2/d_2 < 1`, so `1 + 2ξ² < 2 + ξ²`" (via DG Prop 1.7 monotonicity and the
value `d_2`). Here `ξ < 1` is derived from GM's `ξQ − 1 − ξ²/2 < 0` (`Blueprint.GMXiQBound`, GM
U:1056 = DFGPS T:2453, the bound DFGPS state right after Prop 4.1 from Ang Thm 1.9) together with
the proved `χ ≤ 2` (`DG.chiLeTwo`, so `d_γ ≥ 1` and `ξ ≤ γ < 2`): the quadratic
`ξ²/2 − Qξ + 1 > 0` with `Q ≥ 2` forces `ξ < 1` on `(0, 2)`. Own elementary argument (route to the
same fact as DFGPS's; proposed deviation DEV-P41-1).
-/

noncomputable section

namespace LQGMetric.DFGPS.P41

/-- `ξ = γ/d_γ < 1` for `γ ∈ (0,2)` -/
theorem xiGamma_lt_one (hXQ : Blueprint.GMXiQBound) {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) :
    xiGamma γ < 1 := by
  have hd := DG.one_le_dGamma DG.chiLeTwo hγ hγ2
  have hξγ : xiGamma γ ≤ γ := div_le_self hγ.le hd
  have hξ0 : 0 < xiGamma γ := DG.xiGamma_pos hγ
  have hQ : 2 ≤ Q γ := by
    rw [Q]
    have : 2 / γ + γ / 2 - 2 = (γ - 2) ^ 2 / (2 * γ) := by field_simp; ring
    have : 0 ≤ (γ - 2) ^ 2 / (2 * γ) := by positivity
    linarith
  have hB := hXQ γ hγ hγ2
  by_contra hcon
  push Not at hcon
  have h1 : 2 * xiGamma γ ≤ xiGamma γ * Q γ := by nlinarith
  have h2 : (xiGamma γ - 2) ^ 2 ≤ 1 := by nlinarith
  nlinarith

end LQGMetric.DFGPS.P41
