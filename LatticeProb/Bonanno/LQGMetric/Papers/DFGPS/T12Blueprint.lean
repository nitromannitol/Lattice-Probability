/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DFGPS.T12Blueprint at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DFGPS.T12Final
import LatticeProb.Bonanno.LQGMetric.Papers.DFGPS.T12P7A

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# DFGPS Theorem 1.2 (`AsmExistence`): locality of `patchT` and the final assembly

Source: DFGPS arXiv:1905.00380, `lqg-metric-estimates-final.tex` ("T"), proof of Theorem 1.2,
Step 2 (T:1358–1374, Axiom II). For open `U` and a GFF plus continuous `h`, a.s. for `z, w`:
`D_h(z,w;U) = inf_{W ∈ 𝒲, cl W ⊆ U} D_h(z,w;W)` (`internal_eq_iInf_dyadicC`, "letting `O'`
increase to `O`"), `D_h(·,·;W) = tChainInf W (truncLim W h)` (`ae_internal_eq_tChainInf`), and the
resulting functional `locF` of `h` is measurable and factors through `h|_U`
(`exists_locF_factor`).

* `t12Locality` — the node `T12Locality`;
* `dfgps_existence_of_blueprint` — **DFGPS Theorem 1.2** in the form `AsmExistence`.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set Metric
open scoped ENNReal

namespace LQGMetric.DFGPS.T12

open Blueprint

/-- **Axiom II (locality) for the glued metric `patchT`** (T:1358–1374) -/
theorem t12Locality (HG : Lem2_1GffApprox.{0}) (h12 : Lem2_12) {γ : ℝ} (hγ : 0 < γ)
    (hγ2 : γ < 2) (εs : ℕ → ℝ) (hεs : ∀ k, 0 < εs k) (hε0 : Tendsto εs atTop (𝓝 0))
    (hG : T12Good γ εs hεs) : T12Locality γ εs hεs := by
  intro Ω _ P _ h hh U
  obtain ⟨F, hF, hFe⟩ := exists_locF_factor (ξ := xiGamma γ) (hεs := hεs) hε0 U
  refine ⟨F, hF, ?_⟩
  filter_upwards [ae_internal_eq_tChainInf HG h12 hγ hγ2 hε0 hG hh] with ω hω z _ w _
  rw [← hFe, L217.internal_eq_iInf_dyadicC _ U.isOpen]
  unfold locF
  exact iInf_congr fun W => iInf_congr fun _ => hω W z w

end LQGMetric.DFGPS.T12
