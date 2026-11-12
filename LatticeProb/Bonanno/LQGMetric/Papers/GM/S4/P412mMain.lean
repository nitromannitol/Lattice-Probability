/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.GM.S4.P412mMain at commit fdb5cad; only the module paths of local imports are changed.
   Changed: docstring wording of the module, P412OfL36AE0 and gm_P4_12S. -/
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S4.P412iCond
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S4.P412mQk
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S4.P412S
import LatticeProb.Bonanno.LQGMetric.Field.HarmLocD

/-!
# GM Proposition 4.12 without the sure-boundary leaf `P412jCentres` (decision D106, part 4)

Source: GM (arXiv:1905.00383v3, `uniqueness-final.tex`) proof of Lemma 4.15 Step 3–4
(l. 2155–2199) and of Proposition 4.12 (l. 2212–2276); decision D106.

* `p412m_P4_12AtC`: the proof of `p412j_P4_12AtC` (P412jMain.lean) with CONF L3.6 in its a.s. form
  `CONFLem3_6AtAE` (`p412m_step_k`) and the a.s. guard centres `p412m_centres` (proved, P-Qk) in
  place of the open input `P412jCentres`; the a.s. good set `G₀` also records `x_{k,j} ω ∈ ∂𝓑^•_{t_k}`;
* `p412m_P4_12At`: all probability spaces (D70 completion transfer `p412j_P4_12At_of_complete`);
* **`gm_P4_12S`**: `GMP4_12S` from `CONFSection3` and the Blueprint inputs (replaces
  `gm_P4_12S_of`, P412S.lean). Since D110 P1, `CONFSection3` carries CONF L3.6 modulo additive
  constants, `CONFLem3_6AtAE0`. Until D110 P5/P6 rewire the chain
  (`CONFLem3_6AtAENE`, `confLem3_6AtAENE_of_AE0`, `GM.FilledBallLocalSet`, normalization
  `normIn h ψ₀` and `η → 0`), the missing step was the node **`P412OfL36AE0`**: Prop 4.12 at
  parameters satisfying L3.6 modulo constants and Thm 3.9. It is now proved, on the final route, by
  `GM.p412n_P412OfL36AE0'` (Papers/GM/S4/P412pMain.lean).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Filter Metric Topology
open scoped ENNReal
open LQGMetric.Blueprint

namespace LQGMetric.GM

/-- **Open node (D110 P5 + P6)**: GM Proposition 4.12 (`GMP4_12At`) at CONF parameters satisfying
CONF Lemma 3.6 modulo additive constants, `CONFLem3_6AtAE0`, and CONF Theorem 3.9, for
constant-invariant geodesic selections. DEC-110 §2.3 gives the proof (inside normalization
`normIn h ψ₀`, `CONFLem3_6AtAENE`, `GM.FilledBallLocalSet` = CONF Lemma 2.1, `η → 0`). -/
def P412OfL36AE0 : Prop :=
  DFGPSLem3_8 → CONFLem2_7 → CONFThm1_4 →
  ∀ {γ : ℝ}, 0 < γ → γ < 2 → ∀ {D : DistC → ContMetric} {c : ℝ → ℝ}, IsWeakLQGMetric γ D c →
  ∀ {cp : CONFParams}, CONFLem3_6AtAE0 γ D c cp → ∀ {χ χ' : ℝ}, 0 < χ → χ < χ' →
  CONFThm3_9At γ D c cp χ → ∀ sel : ℂ → ℂ → DistC → C(unitInterval, ℂ),
  (∀ (a b : ℂ) (g : DistC) (c : ℝ), sel a b (addConst g c) = sel a b g) →
  GMP4_12At γ D c cp χ χ' sel

/-- **GM Proposition 4.12 at the CONF §3 parameters** (`GMP4_12S`, D104) from the CONF §3 package
(with CONF L3.6 modulo additive constants, D110), the Blueprint inputs and the node `P412OfL36AE0`
(D110 P5/P6; proved by `GM.p412n_P412OfL36AE0'`) -/
theorem gm_P4_12S (h38 : DFGPSLem3_8) (hC27 : CONFLem2_7) (hC14 : CONFThm1_4)
    (hC3 : CONFSection3) (hN : P412OfL36AE0) : GMP4_12S := by
  intro γ D c hγ hγ2 hD
  obtain ⟨cp, hcp, h35, h36, H39⟩ := hC3 γ hγ hγ2 D c hD
  refine ⟨cp, hcp, h35, ?_⟩
  intro χ χ' hχ hχQ hχ' sel hsel
  have hξ := xiGamma_pos hγ
  have hχχ' : χ < χ' := by nlinarith
  exact hN h38 hC27 hC14 hγ hγ2 hD h36 hχ hχχ' (H39 χ ⟨hχ, hχQ⟩).2 sel hsel

end LQGMetric.GM
