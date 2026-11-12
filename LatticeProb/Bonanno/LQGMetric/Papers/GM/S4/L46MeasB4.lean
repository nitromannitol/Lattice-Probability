/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.GM.S4.L46MeasB4 at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S4.L46MeasB2
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S4.L46MeasB3

/-!
# GM Lemma 4.6 (b): `Stab_{k,r}(z)` is a.s. determined by `h|_{ℂ∖B_ρ(z)}` (task P2-E3b)

Source: GM = Gwynne–Miller, arXiv:1905.00383v3, `literature/src/1905.00383/uniqueness-final.tex`,
Lemma 4.6, first claim, and its proof l. 1705–1708 ("By Axiom II (locality), it then follows that
`Stab_{k,r}(z)` is determined by `h|_{ℂ∖B_r(z)}`").

`gm_L4_6b_of_uMeas`: the glue `gm_aeEventIn_of_local` (Axiom II + Lusin separation) applied to the
deterministic locality `gm_stab_of_internal_eq`. The only remaining input is the universal
measurability (D30) of the event on `lenSet` (hypothesis `hUM`, see `handoff/P2-E3b.md`): GM do not
discuss it; the event quantifies over leftmost geodesics (`confPts`, `arcOf`) and over all
`D(·,·;ℂ∖cl B_r(z))`-geodesics, so it is not covered by the analytic/coanalytic tools of D30.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Filter Topology Set Metric
open scoped ENNReal
open LQGMetric.Blueprint

namespace LQGMetric.GM
open LocalEvent

/-- `s_k = τ_{ℓ𝕣} (1 + kε^β)` -/
theorem gm_s4S_eq {Ω : Type} [MeasurableSpace Ω] (D : DistC → ContMetric) (h : Ω → DistC)
    (𝕫 : ℂ) (ℓ 𝕣 ε β : ℝ) (k : ℕ) (ω : Ω) :
    s4S D h 𝕫 ℓ 𝕣 ε β k ω = tauD (D (h ω)) 𝕫 (ℓ * 𝕣) * (1 + k * ε ^ β) := by
  simp only [s4S, s4Unit, gm_tauR_eq_tauD]

end LQGMetric.GM
