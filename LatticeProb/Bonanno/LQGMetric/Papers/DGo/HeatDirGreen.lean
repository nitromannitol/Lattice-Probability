/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DGo.HeatDirGreen at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DGo.HeatDirCK
import LatticeProb.Bonanno.LQGMetric.Field.GreenSquare2
import LatticeProb.Bonanno.LQGMetric.Field.ZeroBoundaryExt

/-!
# DGo Lemma 3.1 on a square: `ĥ^D_δ` has the covariance of the circle averages of a zero-boundary
GFF (task P2-HEAT1, packet R1)

Ding–Goswami, arXiv:1610.09998, `Watabiki_final.tex`, Lemma 3.1 (DGo:495–515): the field
`ĥ^𝒰_δ(v) = √π W(dirCircKernel δ v)` of (3.1) has the law of the circle-average process
`h^𝒰_δ(v)` of a zero-boundary GFF on `𝒰`. DGo's proof compares covariances: both are
`π∫_0^∞ (2π)⁻²∫∫ p^𝒰_s(x_θ, x'_θ') ds` by Chapman–Kolmogorov and `G_𝒰 = π∫_0^∞ p^𝒰_s ds`
(DGo (eq:Green_fxn), DGo:479–486). Here `𝒰 = D = (a, a+L)²`.

* `inner_dirCircKernel` — `⟪K_v, K_v'⟫ = ∫_0^∞ circPair_{v,v'}(s) ds` (Fubini + square CK).
* `heatCirc a L δ v ε hL : BddOn D` — `1_D · (2π)⁻¹∫ p^D_ε(v + δe^{iθ}, ·) dθ`, the Dirichlet heat
  regularization at time `ε` of the uniform measure on `∂B_δ(v)` (a bounded test density).
* `zeroGFFTestCov_heatCirc` — `Cov_D(heatCirc_{v,ε}, heatCirc_{v',ε'}) = π ∫_{ε+ε'}^∞ circPair`,
  from the heat form of the zero-boundary covariance `HeatSq.zeroGFFTestCov_sqOpen_eq_heat_gen`
  (which is `G_D = π∫_0^∞ p^D_s ds` tested against bounded densities, proved spectrally).
* **`dgo_lemma31_sq`** — for every zero-boundary GFF `X` on `D` (`IsZBGFFProcessExt`) and
  `closedBall v δ, closedBall v' δ ⊆ D`:
  `Cov(X(heatCirc_{v,ε}), X(heatCirc_{v',ε'})) → π⟪dirCircKernel v, dirCircKernel v'⟫` as
  `ε, ε' → 0⁺`. The left side is the covariance of the (heat-regularized) circle averages
  `h^D_{δ,ε}(v)`; their `L²(P)` limit is the circle average `h^D_δ(v)` (`tendsto_sq_sub_heatCirc`
  gives the Cauchy property), so `Cov(h^D_δ(v), h^D_δ(v')) = π⟪K_v, K_v'⟫ = Cov(ĥ^D_δ(v), ĥ^D_δ(v'))`.

Reading (proposed DEVIATIONS HEAT1-2): the zero-boundary GFF of this library is a process indexed by
bounded densities (DEC-ZB / D39); the circle average `h^D_δ(v)` is the `L²` limit of its pairings with
the heat-regularized circle measures `heatCirc_{v,ε}` (the standard extension of the GFF to measures of
finite energy, Berestycki–Powell §1.2), rather than a pairing with the circle measure itself.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Real Set Function Filter Topology Metric
open scoped ENNReal RealInnerProductSpace

namespace LQGMetric
namespace DGo
namespace HeatDir

open HeatSq

variable {a L δ : ℝ} {v v' : ℂ}

lemma dirCircFun_of_pos {s : ℝ} (hs : 0 < s) (z : ℂ) :
    dirCircFun a L δ v (s, z) = (sqOpen a L).indicator (circFn a L δ v (s / 2)) z := by
  unfold dirCircFun circFn
  by_cases hz : z ∈ sqOpen a L
  · rw [indicator_of_mem (show ((s, z) : ℝ × ℂ) ∈ Ioi 0 ×ˢ sqOpen a L from ⟨hs, hz⟩),
      indicator_of_mem hz, intervalIntegral.integral_of_le (by positivity)]
  · rw [indicator_of_notMem (show ((s, z) : ℝ × ℂ) ∉ Ioi 0 ×ˢ sqOpen a L from fun h => hz h.2),
      indicator_of_notMem hz]

lemma dirCircFun_of_nonpos {s : ℝ} (hs : s ≤ 0) (z : ℂ) : dirCircFun a L δ v (s, z) = 0 := by
  unfold dirCircFun
  exact indicator_of_notMem (fun h => (not_lt.2 hs) h.1) _

lemma integral_dirCircFun_mul (hL : 0 < L) (s : ℝ) :
    ∫ z, dirCircFun a L δ v (s, z) * dirCircFun a L δ v' (s, z) =
      (Ioi 0).indicator (circPair a L δ v v') s := by
  by_cases hs : 0 < s
  · rw [indicator_of_mem (show s ∈ Ioi (0 : ℝ) from hs)]
    have e : (fun z => dirCircFun a L δ v (s, z) * dirCircFun a L δ v' (s, z)) =
        (sqOpen a L).indicator fun z => circFn a L δ v (s / 2) z * circFn a L δ v' (s / 2) z := by
      funext z
      rw [dirCircFun_of_pos hs, dirCircFun_of_pos hs]
      by_cases hz : z ∈ sqOpen a L
      · simp only [indicator_of_mem hz]
      · simp only [indicator_of_notMem hz, zero_mul]
    rw [e, integral_indicator (measurableSet_sqOpen a L),
      integral_circFn_mul_circFn hL (half_pos hs) (half_pos hs), add_halves]
  · rw [indicator_of_notMem (show s ∉ Ioi (0 : ℝ) from hs)]
    simp only [dirCircFun_of_nonpos (not_lt.1 hs), zero_mul, integral_zero]

/-- **`⟪K_v, K_v'⟫ = ∫_0^∞ circPair_{v,v'}(s) ds`**, and `circPair` is integrable on `(0, ∞)`. -/
theorem inner_dirCircKernel (hL : 0 < L) (hδ : 0 < δ) (hB : closedBall v δ ⊆ sqOpen a L)
    (hB' : closedBall v' δ ⊆ sqOpen a L) :
    IntegrableOn (circPair a L δ v v') (Ioi 0) ∧
      ⟪dirCircKernel a L δ v, dirCircKernel a L δ v'⟫ = ∫ s in Ioi 0, circPair a L δ v v' s := by
  have hf := memLp_dirCircFun hL hδ hB
  have hg := memLp_dirCircFun hL hδ hB'
  have hint := hf.integrable_mul hg
  rw [Measure.volume_eq_prod] at hint
  have hI : Integrable ((Ioi (0 : ℝ)).indicator (circPair a L δ v v')) :=
    hint.integral_prod_left.congr (Eventually.of_forall fun s => integral_dirCircFun_mul hL s)
  refine ⟨(integrable_indicator_iff measurableSet_Ioi).1 hI, ?_⟩
  rw [L2.inner_def]
  have h1 : ∫ q, ⟪(dirCircKernel a L δ v : ℝ × ℂ → ℝ) q, (dirCircKernel a L δ v' : ℝ × ℂ → ℝ) q⟫ =
      ∫ q, dirCircFun a L δ v q * dirCircFun a L δ v' q := by
    refine integral_congr_ae ?_
    filter_upwards [coeFn_dirCircKernel hL hδ hB, coeFn_dirCircKernel hL hδ hB'] with q h1 h2
    simp only [h1, h2, RCLike.inner_apply, conj_trivial,
      RCLike.re_to_real]
    ring
  rw [h1, Measure.volume_eq_prod, integral_prod (fun q => dirCircFun a L δ v q *
    dirCircFun a L δ v' q) hint]
  simp_rw [integral_dirCircFun_mul hL]
  rw [integral_indicator measurableSet_Ioi]

end HeatDir
end DGo
end LQGMetric
