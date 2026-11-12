/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DZZ.S2Bridge at commit fdb5cad; only the module paths of local imports are changed.
   Declarations, examples and checks that the copied results do not use are omitted.
   Imports of copied modules that this file does not need are replaced by their own imports. -/
import LatticeProb.Bonanno.LQGMetric.Field.KilledHeatScale
import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.S2L7Trunc
import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.S2L5Kernel

/-!
# The bridge shell bound (DZZ L2.5, `η` half; decision D62 route (1); task P2-DZZPRE2)

`bridgeShellBound_256 : BridgeShellBound 256`: the radial maximum `M_t = max_{s ≤ t} |X_s|` of the
planar Brownian bridge of length `t` satisfies `P(r − d ≤ M_t < r) ≤ 256 d/√t`.

Ding–Zeitouni–Zhang (arXiv:1807.00422, `LBM_LGDarXiv.tex` l. 459–461) only say "similar
argument"; no published proof of this bounded-density statement was found (see D62). Own
argument (D62 route (1)), all analytic:

1. the shell probability is `q_{B(0,r)}(t; 0, 0) − q_{B(0,r−d)}(t; 0, 0)`, and by Brownian scaling
   (`bridgeStay_ball_scale`) `q_{B(0,ρ)}(t; 0, 0) = G(t/ρ²)`, `G(τ) = q_{B(0,1)}(τ; 0, 0)`;
2. `G(τ) = 2πτ K(τ)` with `K(τ) = p_{B(0,1)}(τ; 0, 0)`, which is log-convex in `τ`
   (`killedHeat_sq_le_real`: Chapman–Kolmogorov + Cauchy–Schwarz);
3. a discrete log-convexity estimate (`logConvex_sub_le`: if `ψ_{j+1}² ≤ ψ_j ψ_{j+2}` then
   `ψ_n − ψ_{n+1} ≤ ψ_0/n`) along the progression `τ/2 ≤ x₀ < x₀ + s < … < τ + s` gives
   `K(τ) − K(τ + s) ≤ (4s/τ) sup_{x ≥ τ/2} K(x)`;
4. `K(x) ≤ min((2πx)⁻¹, 1/(πx²))` (`killedHeat_le_heatKernel`, `killedHeat_le_rpow`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal

namespace LQGMetric
namespace DZZ

open KilledHeat

/-! ### Discrete log-convexity -/

/-! ### The killed heat kernel of the unit disc at its centre -/

/-- `K(x) = p_{B(0,1)}(x; 0, 0)`. -/
def unitDiscK (x : ℝ) : ℝ := killedHeat (Metric.ball 0 1) x.toNNReal 0 0

/-- `G(x) = q_{B(0,1)}(x; 0, 0)`. -/
def unitDiscG (x : ℝ) : ℝ := bridgeStay (Metric.ball 0 1) x.toNNReal 0 0

lemma unitDiscK_nonneg (x : ℝ) : 0 ≤ unitDiscK x := killedHeat_nonneg _ _ _ _

lemma unitDiscG_eq {x : ℝ} (hx : 0 < x) : unitDiscG x = 2 * Real.pi * x * unitDiscK x := by
  unfold unitDiscG unitDiscK killedHeat heatKernel
  rw [Real.coe_toNNReal _ hx.le]
  simp only [sub_self, norm_zero]
  have := Real.pi_pos
  field_simp
  simp

lemma unitDiscK_le_inv {x : ℝ} (hx : 0 < x) : unitDiscK x ≤ (2 * Real.pi * x)⁻¹ := by
  have h := (killedHeat_le_heatKernel (Metric.ball (0 : ℂ) 1) x.toNNReal 0 0).trans
    (heatKernel_le_inv _ (NNReal.coe_nonneg _) 0 0)
  rwa [Real.coe_toNNReal _ hx.le] at h

/-- Scaling: `q_{B(0,ρ)}(t; 0, 0) = G(t/ρ²)`. -/
lemma bridgeStay_ball_eq_unitDiscG {t : ℝ≥0} (ht : t ≠ 0) {ρ : ℝ} (hρ : 0 < ρ) :
    bridgeStay (Metric.ball 0 ρ) t 0 0 = unitDiscG ((t : ℝ) / ρ ^ 2) := by
  have ht' : (0 : ℝ) < t := lt_of_le_of_ne (NNReal.coe_nonneg t) (Ne.symm (by exact_mod_cast ht))
  have hτ : ((t : ℝ) / ρ ^ 2).toNNReal ≠ 0 := by
    simpa using (by positivity : (0 : ℝ) < (t : ℝ) / ρ ^ 2)
  rw [bridgeStay_ball_scale ht, unitDiscG, bridgeStay_ball_scale hτ,
    Real.coe_toNNReal _ (by positivity), Real.sqrt_div' _ (by positivity),
    Real.sqrt_sq hρ.le, one_div_div]

/-! ### The shell bound -/

end DZZ
end LQGMetric
