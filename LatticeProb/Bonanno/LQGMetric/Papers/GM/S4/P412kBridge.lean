/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.GM.S4.P412kBridge at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S4.P412jAsm
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S4.Iterate6Main
import LatticeProb.Bonanno.LQGMetric.Papers.CONF.L2_4S2

/-!
# The D76 bridge `P412jBridge` (GM Prop 4.12 input)

Source: CONF = Gwynne–Miller arXiv:1905.00381, `confluence-final.tex`, proof of Lemma 2.4,
l. 557–558 ("By Lemma 2.3, no `D_h`-geodesic from 0 to `y` can cross any of the `P_{q_n^-}`'s.
It follows that each such geodesic lies to the right of `P_y^-`"), with CONF Lemma 2.2
(a.s. uniqueness of geodesics to rational points); decision DEC-76.

`p412k_bridge`: for a weak LQG metric, a.s. every point hit by a one-sided-limit leftmost geodesic
(GM's `Conf_k = confPts`, Blueprint `IsLeftmostGeod`) is hit by a DEC-D leftmost geodesic
(`hitSetDD`), via `CONF.isLeftmost_of_side`. Hence `P412jBridge D`.

`gm_P4_12_of'`: `gm_P4_12_of` with the inputs `hC24` (now `CONF.confLem2_4`) and `hbr` discharged.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Filter
open LQGMetric.Blueprint

namespace LQGMetric.GM

/-- a.s., for all `s, t`: `confPts(s, t) ⊆ hitSetDD(s, t)` (CONF L2.4 proof, l. 557–558) -/
theorem p412k_confPts_subset (h38 : DFGPSLem3_8) {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2)
    {D : DistC → ContMetric} {c : ℝ → ℝ} (hD : IsWeakLQGMetric γ D c) {Ω : Type}
    [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] (h : Ω → DistC)
    (hh : IsWholePlaneGFF h P) (𝕫 : ℂ) :
    ∀ᵐ ω ∂P, ∀ s t : ℝ, confPts (D (h ω)) 𝕫 s t ⊆ hitSetDD (D (h ω)) 𝕫 s t := by
  filter_upwards [gm_S1_1_bcpt h38 hγ hγ2 hD P h hh, gm_S1_1 h38 hγ hγ2 hD P h hh,
    CONF.confLem2_2 h38 γ hγ hγ2 D c hD P h hh 𝕫] with ω hc hg hq s t
  rintro x ⟨hx, y, Q, hQ, u, hu, hQu⟩
  exact ⟨hx, y, Q, CONF.isLeftmost_of_side hc hg hq hQ, u, hu, hQu⟩

/-- **the D76 bridge** `P412jBridge D` for every weak LQG metric (input `hbr` of
`gm_P4_12_of`) -/
theorem p412k_bridge (h38 : DFGPSLem3_8) {γ : ℝ} {D : DistC → ContMetric} {c : ℝ → ℝ}
    (hγ : 0 < γ) (hγ2 : γ < 2) (hD : IsWeakLQGMetric γ D c) : P412jBridge D := by
  intro Ω _ P _ h hh 𝕫 ℓ 𝕣 ε β k
  filter_upwards [p412k_confPts_subset h38 hγ hγ2 hD P h hh 𝕫] with ω hω
  exact hω _ _

end LQGMetric.GM
