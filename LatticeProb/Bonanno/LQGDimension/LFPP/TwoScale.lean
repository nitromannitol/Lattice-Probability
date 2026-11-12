/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGDimension.LFPP.TwoScale at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGDimension.LFPP.TwoScaleAux4

/-!
# Node `L31`: Lemma 3.1, the two-scale covariance bound (3.1)

We prove `Blueprint.Draft.TwoScaleCovBound` with the explicit constant `C = 256`:
for probability segment combinations `μR, νR` with growth `L min(1, s/R)` coupled within `u`,
and `μr, νr` coupled within `v`,
`|logCov(μR - νR, μr - νr)| ≤ C L √(uv) / R`, and the same for `circCov ε` for every `ε`.

Proof outline (files `TwoScaleAux1`–`TwoScaleAux4`).

1. **Kernel bounds** (`kt_four_point`): for the Gaussian kernel `kt t x = e^{-|x|²/(4t²)}`, the
   mixed difference over displacements `|e| ≤ u`, `|f| ≤ v` is at most
   `4 min(1, uv/t²)` times a sum of four wider Gaussians `e^{-|·|²/(16t²)}`.
2. **Growth integral** (`integral_gauss_le_of_growth`, layer cake):
   `∫ e^{-|w-z|²/a} dμ(z) ≤ 2 L √a / R`.
3. **Couplings** (`dbl_coupling_bound`, `gaussPair_bound`): integrating the four-point bound
   against both couplings, `|gaussPair t (μr - νr) (μR - νR)| ≤ 128 (L/R) t min(1, uv/t²)`.
4. **Heat representation** (node `HK`, `HeatKernel.gaussPair_heatRep`) and
   `∫_0^∞ min(1, uv/t²) dt = 2√(uv)` give the log-kernel bound (`logCov_twoScale_bound`);
   growth excludes atoms, so the coarse side is nondegenerate, and `logCov` is symmetric.
5. **Circle averages** (`circCov_eq_avg`): `circCov ε` is the average of `logCov` over
   translates of the two combinations; translations preserve all hypotheses
   (`circCov_twoScale_bound`).

No blueprint hypotheses are needed: the heat-kernel representation is imported from the proved
node `HK` (`LQGDimension.LFPP.HeatKernel`).
-/

namespace LQGDimension

open Blueprint.Draft

/-- **Node `L31`** (`Blueprint.Draft.TwoScaleCovBound`, Lemma 3.1, (3.1)). -/
theorem twoScaleCovBound : Blueprint.Draft.TwoScaleCovBound := by
  refine ⟨256, fun μR νR μr νr L R u v hμR hνR hμr hνr hR hu hv hGμ hGν hcR hcr => ⟨?_, ?_⟩⟩
  · exact TwoScale.logCov_twoScale_bound hμR hνR hμr hνr hR hu hv hGμ hGν hcR hcr
  · intro ε _
    exact TwoScale.circCov_twoScale_bound hμR hνR hμr hνr hR hu hv hGμ hGν hcR hcr ε

end LQGDimension
