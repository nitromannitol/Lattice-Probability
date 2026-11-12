/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DG.S3P18S6 at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DG.S3P18S5
import LatticeProb.Bonanno.LQGMetric.Papers.DG.S3T15

/-!
# DG Props 3.18 / 3.17 on squares and DG Thm 1.5: composites (task P2-DG105s)

Source: Ding–Gwynne arXiv:1807.01072, `metric-comparison-final.tex`, DG:1774–1777 (P3.18 from
P3.22) and DG:1593–1595 (P3.17 on squares). Wiring of the proved steps:

* `r18P322_of_lem37` — `R18P322` from `Blueprint.DGLem3_7` (D118, on `𝕊(1/2)`): the side facts of
  `r18P322_of` are the version clause of `IsDGCoupling` (`p18Half_eq_sqHalf`);
* **`dgProp3_18Sq_of_lem37`** — `DGProp3_18Sq` from `Blueprint.DGLem3_7` and the `𝕍`-scale
  L3.11 / L3.19 inputs of `dg_prop322_sqOne_muHat` for every white noise;
* `dgProp3_21_of_lem37` — `Blueprint.DGProp3_21` from the same hypotheses;
* **`dgProp3_17SqRef_of`**, **`dgProp3_17Sq_of`** — from `DGProp3_16` and `DGP317Show` for every
  white noise (the hypothesis of `dgProp3_17_of`);
* `dgThm1_5_of_inputs` — `DGThm1_5` from all of the above.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set Metric
open scoped ENNReal

namespace LQGMetric.DG

open Blueprint WhiteNoise SupTail

/-- **`DGProp3_17SqRef`** (DG:1593–1595) from `DGProp3_16` and `DGP317Show` -/
theorem dgProp3_17SqRef_of (h316 : DGProp3_16)
    (hshow : ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) (W : WNSpace → Ω → ℝ),
      IsWhiteNoise P W → ∀ γ : ℝ, 0 < γ → γ < 2 → DGP317Show P W γ) : DGProp3_17SqRef :=
  dgProp3_17SqRef_of_unit (r17_unit (dgProp3_17_of h316 hshow))

/-- **`DGProp3_17Sq`** (DG:1593–1595) from `DGProp3_16` and `DGP317Show` -/
theorem dgProp3_17Sq_of (h316 : DGProp3_16)
    (hshow : ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) (W : WNSpace → Ω → ℝ),
      IsWhiteNoise P W → ∀ γ : ℝ, 0 < γ → γ < 2 → DGP317Show P W γ) : DGProp3_17Sq :=
  dgProp3_17Sq_of_ref (dgProp3_17SqRef_of h316 hshow)

end LQGMetric.DG
