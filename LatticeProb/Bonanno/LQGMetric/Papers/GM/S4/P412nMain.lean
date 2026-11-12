/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.GM.S4.P412nMain at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S4.P412nCov
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S4.P412mMain

/-!
# GM Proposition 4.12 from the true CONF Lemma 3.6 (D110 P6, part 6)

Source: GM (arXiv:1905.00383v3, `uniqueness-final.tex`) proof of Lemma 4.15 Step 3–4
(l. 2155–2199) and of Proposition 4.12 (l. 2212–2276); GM l. 214 (the additive constant);
decision DEC-110 §2.3.

`p412n_P4_12AtC`: the proof of `p412m_P4_12AtC` (P412mMain.lean) with CONF L3.6 in the on-event
form `CONFLem3_6AtAENE`. For each `q`, the filtration and the CONF L3.6 events are those of the
field `g = h − h(ψ_q)` normalized at the bump `ψ_q = bumpTest q 𝕫` (`p412n_step_k`, on
`E_q = {supp ψ_q ⊆ int 𝓑^•_{t_0}(g)}`), while the events `𝒵^E_k ≠ ∅` and `ℰ_𝕣` are those of `h`;
the two are linked on an a.s. event by Weyl scaling for constants (`D_g = e^{−ξh(ψ_q)} D_h`:
`P412nScale`, `P412nCov`) and by the open node **`ConfRKAddConst`** (the radius `R^ε_𝕣` of CONF
(3.16) does not see an additive constant). This gives `P[bad] ≤ 2ε^M + P[F_qᶜ]`,
`F_q = {B̄_{2^{-q}}(𝕫) ⊆ int 𝓑^•_{t_0}(h)}`, and `q → ∞` (continuity from above, own routine glue,
DEV DV-D110 2).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Filter Metric Topology
open scoped ENNReal
open LQGMetric.Blueprint

namespace LQGMetric.GM

/-- **Open node (D110 P6)**: the radius `R^ε_𝕣(K)` of CONF (3.16) (`confRK`) is a.s. unchanged
when a random additive constant is added to the field, for all `K` simultaneously (GM l. 214;
CONF C:1154 "viewed modulo additive constant"). It reduces to the covariance
`𝔥^U_{h+c} = 𝔥^U_h + c` of the harmonic parts (`CONF.isHarmPart0_addConst_iff`, with the
existence of harmonic parts, DEC-110 P3, and their a.s. uniqueness), `h_r(z) ↦ h_r(z) + c`, and
Weyl scaling `D_{h+c} = e^{ξc} D_h`, on the countably many `(r, z, U)` entering `confRK`. -/
def ConfRKAddConst : Prop :=
  ∀ {γ : ℝ}, 0 < γ → γ < 2 → ∀ {D : DistC → ContMetric} {c : ℝ → ℝ}, IsWeakLQGMetric γ D c →
  ∀ (p : CONFParams) {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (h : Ω → DistC), IsWholePlaneGFF h P → ∀ a : Ω → ℝ, Measurable a →
  ∀ R ε : ℝ, 0 < R → ε ∈ Ioo (0 : ℝ) 1 →
    ∀ᵐ ω ∂P, ∀ K : Set ℂ, confRK (xiGamma γ) c D P (fun ω => addConst (h ω) (a ω)) p R ε K ω =
      confRK (xiGamma γ) c D P h p R ε K ω

end LQGMetric.GM
