/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DG.S3D105Sc2 at commit fdb5cad; only the module paths of local imports are changed.
   Declarations, examples and checks that the copied results do not use are omitted.
   Imports of copied modules that this file does not need are replaced by their own imports. -/
import LatticeProb.Bonanno.QuantumZipper.Proofs.Analysis.Pushforward
import LatticeProb.Bonanno.LQGMetric.Field.WhiteNoise
import LatticeProb.Bonanno.LQGMetric.Field.KilledHeatScale
import LatticeProb.Bonanno.LQGMetric.Dimension.GMCIdent2Circ
import LatticeProb.Bonanno.LQGMetric.Papers.DG.L3_1B3
import LatticeProb.Bonanno.LQGMetric.Papers.DG.L3_1
import LatticeProb.Bonanno.LQGMetric.Papers.DG.AppAShell
import LatticeProb.Bonanno.LQGMetric.Papers.DG.S3L3
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.MeasureTheory.Measure.Lebesgue.Complex
import Mathlib.LinearAlgebra.Complex.FiniteDimensional

/-!
Ding–Gwynne arXiv:1807.01072 (`metric-comparison-final.tex`): `ĥ = √π ∫_0^1 ∫ p_{s/2}(·, w)
W(dw, ds)` (DG (3.1), DG:907–917), `ĥ_t = √π ∫_{t²}^1 …` (DG:907), and the scale invariance
DG:1010 ("`(ĥ − ĥ_δ)(δ·+b)` has the same law as `ĥ`") made pathwise (DEC-105 §1 item 3, §2):

* `heatKernel_affineC`: `p_{δ²t}(δx+b, δy+b) = δ⁻² p_t(x, y)` (explicit Gaussian formula).
* `scFun_hatMeasKerI`: the kernel identity `U_{δ,b}(K^I_μ) = K^{δ²I}_{(δ·+b)_*μ}` for the time-cut
  kernels `K^I_μ(s,w) = ∫ 1_I(s) p_{s/2}(y, w) μ(dy)` (change of variables `s = δ²s'`,
  `w = δw' + b`).
* `memLp_hatMeasKerI`: the coarse kernel `K^{(c,1]}_ν` is square integrable for every finite `ν`
  (`ĥ_δ` is a regular field).
* `wnScale_hatMeasKerL2`: `U_{δ,b}(K^{(0,1]}_μ) = K^{(0,1]}_ν − K^{(δ²,1]}_ν`, `ν = (δ·+b)_*μ`.
* **`dgHat_wnScale`**: for `0 < δ ≤ 1`, pathwise a.s.
  `ĥ[W ∘ U_{δ,b}](σ_{z,r}) = ĥ[W](σ_{δz+b, δr}) − ĥ_δ[W](σ_{δz+b, δr})`, i.e. the circle averages of
  `(ĥ − ĥ_δ)(δ·+b)` are those of the `ĥ` of the white noise `W ∘ U_{δ,b}` (`isWhiteNoise_comp`).

Own elementary argument (DG state it as a "basic property of `ĥ`"; DV-D105-2).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal

namespace LQGMetric
namespace DG

open WhiteNoise QuantumZipper KilledHeat DZZ GMCIdent SupTail

/-- the affine map `y ↦ δy + b` as a measurable equivalence -/
def affineEquivC {δ : ℝ} (hδ : 0 < δ) (b : ℂ) : ℂ ≃ᵐ ℂ :=
  ((Homeomorph.mulLeft₀ (δ : ℂ) (by exact_mod_cast hδ.ne')).trans
    (Homeomorph.addRight b)).toMeasurableEquiv

end DG
end LQGMetric
