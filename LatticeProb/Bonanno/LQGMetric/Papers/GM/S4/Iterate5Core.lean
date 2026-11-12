/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.GM.S4.Iterate5Core at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S4.Iterate5Meas
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S4.Iterate4PairOneA
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S4.Iterate4L420F
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S4.Iterate3L420
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S4.Iterate2Ae

/-!
# `T4_2PairOne` at a fixed scale (DEC-89, packet C): Prop 4.17 + Lemma 4.7 + Lemma 4.20

Source: GM = `literature/src/1905.00383/uniqueness-final.tex`, proof of Proposition 4.17
(l. 2404–2433), Lemma 4.21 (l. 2361–2398) and the end of the proof of Thm 4.2 (l. 2437–2441).

`gm_T42_fixed`: on a complete probability space, with the far normalization `h(ψ₀) = 0`, for a
regularity event `Reg` with (a.s. on `Reg`) `Reg ⊆ F_k` (Lemma 4.19), `𝓑^•_{t_k}` inside
`B_{ρ'}(𝕫)` and away from `𝕨` (`gm_regEvent_WG`), and with the bound `δ₁` of Proposition 4.12,
the bound (4.19) `δ` of Lemma 4.8, and the rate condition `ε^{2ν+ζ/2} ≤ κ/2 − e ≤ 1`, the
probability that `Reg` holds and the pair `(𝕫, 𝕨)` has no witness is at most
`δ₁ + (K+1)√δ + 2ε^M`. The threshold `ε₀` is that of `gm_P4_17_ae`: it depends only on
`b, β, θ, ν, ζ, M`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory MeasurableSpace Set Filter Metric
open LQGMetric.Blueprint
open scoped ENNReal

namespace LQGMetric.GM

theorem gm_aeEventIn_mono' {Ω : Type} {m0 m m' : MeasurableSpace Ω} {P : Measure[m0] Ω}
    (hmm' : m ≤ m') {E : Set Ω} (hE : @AEEventIn Ω m0 P m E) : @AEEventIn Ω m0 P m' E := by
  obtain ⟨F, hF, hEF⟩ := hE
  exact ⟨F, hmm' _ hF, hEF⟩

end LQGMetric.GM
