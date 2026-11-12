/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DGo.HeatDirCoupling at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DGo.HeatDirGreen
import LatticeProb.Bonanno.LQGMetric.Papers.DDDF.S6P29WN3

/-!
# DGo Lemma 3.1 on a square, coupling form: `ĥ^D_δ(v)` is the circle average of `h^D = zbX W`
(task P2-HEAT1, packet R1)

Ding–Goswami, arXiv:1610.09998, Lemma 3.1 (DGo:495–515) and (3.1)–(3.2) (DGo:491–494): with
`h^D(ρ) = √π W(zbKer ρ)` the white-noise zero-boundary GFF (DDDF DD:1514, `DDDF.P29WN.zbKerL2`),
the field `ĥ^D_δ(v) = √π W(dirCircKernel δ v)` is the circle average of the *same* field:

* `zbKerFun_heatCirc` — `zbKer(heatCirc_{v,ε})(s, z) = 1_{s>0} 1_D(z) circFn_{v, ε + s/2}(z)`
  (Chapman–Kolmogorov `integral_sqDirKernel_mul_circFn`): the white-noise kernel of the
  heat-regularized circle measure is the circle kernel shifted in time.
* `tendsto_zbKerL2_heatCirc` — `zbKer(heatCirc_{v,ε}) → dirCircKernel v` in `L²(ℝ × ℂ)` as `ε → 0⁺`
  (the three inner products are `∫_{2ε}^∞`, `∫_ε^∞`, `∫_0^∞` of `circPair_{v,v}`).
* `zbXSq a L hL W`, `isZBGFFProcessExt_zbXSq` — DDDF's white-noise zero-boundary GFF on any square
  (generalizes `DDDF.P29WN.zbX`, `isZBGFFProcessExt_zbX` from `(−1, 2)²`).
* **`dgo_lemma31_coupling`** — `Var(h^D(heatCirc_{v,ε}) − ĥ^D_δ(v)) → 0`, i.e.
  `ĥ^D_δ(v) = h^D_δ(v)` (`L²(P)` limit) for the zero-boundary GFF `h^D = zbXSq W`;
  `dgo_lemma31_coupling_S` is DG's `𝕊(1) = (−1, 2)²` (DG:1104) with `zbX`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Real Set Function Filter Topology Metric
open scoped ENNReal RealInnerProductSpace

namespace LQGMetric
namespace DGo
namespace HeatDir

open HeatSq DDDF.P29WN

variable {a L δ : ℝ} {v : ℂ}

/-- DDDF's white-noise zero-boundary GFF on a general square `(a, a+L)²`:
`h^D(ρ) = √π W(zbKer ρ)` (DD:1514; `DDDF.P29WN.zbX` is the case `(−1, 2)²`). -/
def zbXSq (a L : ℝ) (hL : 0 < L) {Ω : Type*} (W : WhiteNoise.WNSpace → Ω → ℝ)
    (ρ : BddOn (sqOpen a L)) : Ω → ℝ :=
  W (Real.sqrt π • zbKerL2 a L hL ρ)

/-- `zbXSq` is the zero-boundary GFF on `(a, a+L)²` (the proof of `isZBGFFProcessExt_zbX`, with the
general-square heat form `HeatSq.zeroGFFTestCov_sqOpen_eq_heat_gen`). -/
theorem isZBGFFProcessExt_zbXSq (hL : 0 < L) {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {W : WhiteNoise.WNSpace → Ω → ℝ} (hW : WhiteNoise.IsWhiteNoise P W) :
    IsZBGFFProcessExt (sqOpens a L) (zbXSq a L hL W) P where
  measurable ρ := hW.measurable _
  gaussian := hW.isGaussianProcess_comp _
  centered ρ := QuantumZipper.GFFExist.gs_integral_eq_zero (hW.hasLaw_single _)
  covariance_eq ρ σ := by
    show cov[W (Real.sqrt π • zbKerL2 a L hL ρ), W (Real.sqrt π • zbKerL2 a L hL σ); P] = _
    rw [hW.cov_eq, real_inner_smul_left, real_inner_smul_right, ← mul_assoc,
      Real.mul_self_sqrt Real.pi_pos.le]
    exact (congrArg (π * ·) (inner_zbKerL2 hL ρ σ)).trans
      (zeroGFFTestCov_sqOpen_eq_heat_gen hL ρ σ).symm

end HeatDir
end DGo
end LQGMetric
