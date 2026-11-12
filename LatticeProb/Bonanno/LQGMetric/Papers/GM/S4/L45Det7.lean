/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.GM.S4.L45Det7 at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S4.L45Det6

/-!
# GM Lemma 4.5: `GMConfPtSel` from the null-measurability of the prefix events (task P2-E2R)

GM, arXiv:1905.00383, `uniqueness-final.tex` l. 1674–1675. The code events `gmConfEv` (a point
of `Conf_k` in a rational half-plane whose arc has a prescribed finite hit prefix) are invariant
under the locality data at `t_k` (`GMLocData.confPts_eq`, `GMLocData.arcOf_eq`), hence a.s.
`σ(𝓑^•_{t_k}, h|)`-events given their null-measurability (`gm_aeEventIn_Kt`); the decoder `gmXi`
of their code recovers the point (`gm_conf_decode`, `gm_conf_hitPattern_injOn`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Filter Topology Set Metric
open LQGMetric.Blueprint

namespace LQGMetric.GM

lemma gm_ereal_iSup_rat' {r : ℝ} {Q : ℚ → Prop} [∀ a, Decidable (Q a)]
    (hQ : ∀ a, Q a ↔ ((a : ℝ)) < r) :
    (⨆ a : ℚ, if Q a then (((a : ℝ)) : EReal) else ⊥) = (r : EReal) := by
  classical
  rw [← gm_ereal_iSup_rat r]
  congr 1
  funext a
  by_cases hq : Q a
  · simp [hq, (hQ a).1 hq]
  · simp [hq, mt (hQ a).2 hq]

end LQGMetric.GM
