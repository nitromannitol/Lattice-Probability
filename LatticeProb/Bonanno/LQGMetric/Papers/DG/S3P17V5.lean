/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DG.S3P17V5 at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DG.S3P17V3
import LatticeProb.Bonanno.LQGMetric.Papers.DG.S3P17V4
import LatticeProb.Bonanno.LQGMetric.Papers.DG.S3P17S5

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# DG Proposition 3.17: (eqn-lfpp-lower-show) from the `𝕍`-scale inputs (P2-DG317V, D121)

Source: Ding–Gwynne arXiv:1807.01072, `metric-comparison-final.tex`, proof of Prop 3.17,
DG:1523–1591. `dgP317Show_of_V` proves `DGP317Show P W γ` (Papers/DG/S3P17.lean, unchanged) for
every white noise `W` from DG Lemmas 3.11 / 3.19 transported by (3.7) **at `𝕍`-scale** — i.e. for
the rescaled white noise `W' = p17vW W` and a measure `μ` on `𝕍` (DG's `μ_ĥ`), on the boxes
`[1/6,5/6]²` / `[1/12,11/12]²` exactly as `dg_prop322_sqOne_muHat` takes them. The proof re-runs
P2-DG317S's `dgP317Show_of` (DG Steps 1–3, `p17s_good`) with
* the measure `μ' = (T⁻¹)_* μ` and `Q = [−1/6,7/6]² = T⁻¹[1/6,5/6]²`, `T z = z/2 + (1+i)/4`;
* Step 1's rectangle bounds from Lemma 3.13 at `𝕍`-scale (`p17v_lemma313`, `p17v_lemma313V`),
  with the field `φ_t = ĥ_{2^{-m-1}}[W'] ∘ T` (`m = m_δ + 1`); the field control `|φ_t − ĥ_δ[W]|
  ≤ η' log δ⁻¹` on `𝕊` from Lemma 3.6 for `W` and the smooth window
  `ĥ_{2^{-m-1}}[W'] ∘ T − ĥ_{2^{-m}}[W] = φ_{1,2}[W]` (`ae_phiVer_p17vW`, `p17v_window`);
* the lower bound of Step 3 from Lemma 3.21 at `𝕍`-scale (`p17v_lb`).
`dgP317Show_of_muHat`: the composite with `μ = μ_ĥ` (`muHat`) for every white noise, the input
form of `dgProp3_17_of`.
-/

noncomputable section

open MeasureTheory Set Metric
open scoped ENNReal

namespace LQGMetric.DG

open Blueprint WhiteNoise

variable {Ω : Type} [MeasurableSpace Ω]

lemma p17v_two_p39d (M : ℕ) : 2 * p39d (M + 1 + 1) = (2 : ℝ)⁻¹ ^ (M + 1) := by
  rw [p39d, pow_succ (2 : ℝ)⁻¹ (M + 1)]; ring

end LQGMetric.DG
