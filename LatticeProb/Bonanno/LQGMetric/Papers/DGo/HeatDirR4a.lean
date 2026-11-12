/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DGo.HeatDirR4a at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DGo.HeatDirR3b
import LatticeProb.Bonanno.LQGMetric.Papers.DGo.HeatDirR2c
import LatticeProb.Bonanno.LQGMetric.Papers.DGo.CouplingTail
import LatticeProb.Bonanno.LQGMetric.Papers.DGo.Smoothness
import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.S2L7Cont
import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.S2ContBox

/-!
# A continuous version of `ĥ^D_δ` on a box (task P2-HEAT3, packet R4)

Ding–Goswami, arXiv:1610.09998, `Watabiki_final.tex`, proof of Prop. 3.3 (DGo:549–556, 702–704):
the field `ĥ^𝒰_δ(v) = √π W(K^𝒰_{δ,v})` (DGo (3.1)), `𝒰 = D = (a, a+L)²`, has a continuous version
on a box `V = ferniqueBox y b` all of whose points are at distance `> ε` from `∂D`, `δ < ε/4`.

* `dgo_hat_cont_version`: the field `x ↦ √π W(K_{δ, c(x)})`, `c` the nearest-point map onto `V`
  (`DZZ.boxClamp`, 1-Lipschitz), has a version continuous on `ℂ` for every `ω`; it agrees a.s.
  with `√π W(K_{δ,v})` at every `v ∈ V`. Proof: (3.9) (`dgo_incr_bound_all`) gives
  `‖K_{c(x)} − K_{c(x')}‖² ≤ (A/(πδ)) ‖x − x'‖`, and the `1/2`-Hölder-kernel Kolmogorov lemma
  `DZZ.exists_continuous_modification_of_kernel_half` (QZ `KolmN`, sixth Gaussian moments).
* An a.e. version of a Gaussian process is a Gaussian process: mathlib
  `ProbabilityTheory.IsGaussianProcess.congr` (used in `isGaussianProcess_hatVer`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Real Set Function Filter Topology Metric
open scoped ENNReal NNReal RealInnerProductSpace

namespace LQGMetric
namespace DGo
namespace HeatDir

open WhiteNoise SupTail

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {W : WNSpace → Ω → ℝ}

/-- the clamped Dirichlet circle kernel `x ↦ K^D_{δ, c(x)}`, `c` the nearest point of `V` -/
def clampKer (a L δ : ℝ) (y : ℂ) (b : ℝ) (x : ℂ) : WNSpace :=
  dirCircKernel a L δ (DZZ.boxClamp y b x)

lemma clampKer_of_mem {a L δ : ℝ} {y : ℂ} {b : ℝ} {v : ℂ} (hv : v ∈ ferniqueBox y b) :
    clampKer a L δ y b v = dirCircKernel a L δ v := by
  unfold clampKer; rw [DZZ.boxClamp_of_mem hv]

end HeatDir
end DGo
end LQGMetric
