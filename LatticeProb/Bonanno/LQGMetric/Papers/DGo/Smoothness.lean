/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DGo.Smoothness at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.S2Hat
import LatticeProb.Bonanno.LQGMetric.Field.WhiteNoiseCont

/-!
# Ding–Goswami: the white-noise field `η_δ` (task P2-DGO, WP-105)

Source: Ding–Goswami, arXiv:1610.09998, `Watabiki_final.tex` (cited `DGo:`), §3.
DGo's field (DGo:521) `η_δ^{δ'}(v) = √π ∫_{ℝ² × [δ², δ'²]} p(s/2; v, w) W(dw, ds)` is our
`WhiteNoise.phi W δ δ' v` (decision D35; DG:906–911 call it `ĥ_δ^{δ'}`, DDDF calls it `φ_{δ,δ'}`).

* `dgo_variance_eta` — (3.3) (DGo:526): `Var η_δ(v) = log δ⁻¹`.
* `dgo_lemma32` — **DGo Lemma 3.2** (`lem:smoothness`, DGo:528–546; Lemma 3.1 in the published
  numbering cited by DG:912, DG:1051): `Var(η_δ(v) − η_δ(w)) ≤ |v − w|²/δ²`. The computation
  of DGo:539–543 is `DZZ.dzz_variance_hat_sub_le` (the same estimate, DZZ (eq-hat-h-continuity)).
* `dgo_eta_continuous_version` — DGo:547–548 ("by Kolmogorov–Centsov … a version of `η_δ` with
  continuous sample paths"), from `WhiteNoise.exists_continuous_modification_phi`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory

namespace LQGMetric
namespace DGo

open WhiteNoise

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {W : WNSpace → Ω → ℝ}

/-- **DGo Lemma 3.2** (`lem:smoothness`, DGo:528–546; "Lemma 3.1" in DG:912, DG:1051):
`Var(η_δ^{δ'}(v) − η_δ^{δ'}(w)) ≤ |v − w|²/δ²` for `0 < δ ≤ δ'` (DGo state `δ' = 1`). -/
theorem dgo_lemma32 (hW : IsWhiteNoise P W) {δ δ' : ℝ} (hδ : 0 < δ) (hδδ' : δ ≤ δ') (v w : ℂ) :
    Var[fun ω => phi W δ δ' v ω - phi W δ δ' w ω; P] ≤ ‖v - w‖ ^ 2 / δ ^ 2 :=
  DZZ.dzz_variance_hat_sub_le hW hδ hδδ' v w

end DGo
end LQGMetric
