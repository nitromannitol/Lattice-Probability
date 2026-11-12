/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module QuantumZipper.Proofs.LQG.GoodMeasurableReg at commit fdb5cad; only the module paths of local imports are changed.
   Declarations, examples and checks that the copied results do not use are omitted. -/
import LatticeProb.Bonanno.QuantumZipper.Proofs.LQG.GoodSample
import Mathlib.Probability.Kernel.MeasurableIntegral

/-!
# M4-R5(a), part 1: regularity is a measurable property of field samples

We prove `MeasurableSet {x : FieldSample | IsRegularSample x}` by characterizing regularity
through countably many conditions on measurable functions of `x`
(`isRegularSample_iff_cert`):

* `C1`: at each dyadic radius `2^{-k}`, the raw values `x (fc(d, 2^{-k}))` at dyadic centres
  `d ∈ Hbar` are uniformly continuous on bounded sets (so `avgReg x k` is their continuous
  extension to `Hbar`);
* `C2`: the smoothings `Φ_i(q) = ∫ avgReg x i d(fc q)` are uniformly Cauchy on the countable dense
  set of dyadic points `qpt j` of each box (hence converge locally uniformly on `Hbar × (0,∞)`
  to the canonical witness `canon x q = evalReg x (fc q)`);
* `C3`: `canon x (d, 2^{-k}) = x (fc(d, 2^{-k}))` at dyadic centres;
* `C4`: clause (ii) of regularity at dyadic smoothing radii and dyadic points.

The tool for `C4` is the joint measurability of `(x, u) ↦ evalReg x (fc(u, ρ))`
(`measurable_evalReg_fc_joint`), from the circle kernel.
-/

noncomputable section

open MeasureTheory Filter Set ProbabilityTheory
open scoped Topology

namespace QuantumZipper

namespace GoodMeas

open RegClosure (tendsto_dyadicRoundC fc_ae_mem_Hbar continuousOn_slice tluo_comp_tendsto
  tendsto_radius_nhdsGT continuousOn_integral_fc)
open CircleCont (lpt dyadicRoundC_eq_lpt abs_dyadicRound_sub_le)

/-! ## Measurability tools -/

/-! ## Dyadic points -/

theorem tendsto_dyadicRound' (r : ℝ) : Tendsto (fun n => dyadicRound n r) atTop (𝓝 r) := by
  rw [tendsto_iff_norm_sub_tendsto_zero]
  refine squeeze_zero (g := fun n : ℕ => 1 / (2 : ℝ) ^ n) (fun n => norm_nonneg _) (fun n => by
    rw [Real.norm_eq_abs]; exact abs_dyadicRound_sub_le n r) ?_
  have : Tendsto (fun n : ℕ => (1 / 2 : ℝ) ^ n) atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
  simpa [one_div, inv_pow] using this

/-! ## The countable certificate -/

/-! ### Measurability of the certificate -/

/-! ### Regular samples satisfy the certificate -/

/-! ### The certificate implies regularity -/

/-! ## Main result of part 1 -/

end GoodMeas

end QuantumZipper
