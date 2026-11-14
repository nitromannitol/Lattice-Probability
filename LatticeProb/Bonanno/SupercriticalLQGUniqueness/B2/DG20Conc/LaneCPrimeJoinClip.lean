/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.B2.DG20Conc.LaneCPrimeJoinClip at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Conc.LaneCPrimePrefix

 

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set

namespace SupercriticalLQGUniqueness.B2.DG20Conc

open LQGMetric LQGMetric.LFPP LQGMetric.DDDF

theorem laneC_prime_join_clip (side : Fin 4) (i : Fin 4)
    {δ : ℝ → ℂ}
    (hδ : AdmPath (laneCPrimeJoinRect side i).toSet
      (laneCPrimeJoinRect side i).side₁
      (laneCPrimeJoinRect side i).side₂ δ) :
    ∃ a b : ℝ, 0 ≤ a ∧ a < b ∧ b ≤ 1 ∧
      AdmPath (laneCPrimeJoinMidRect side i).toSet
        (laneCPrimeJoinMidRect side i).side₁
        (laneCPrimeJoinMidRect side i).side₂ (subPath δ a b) := by
  let t : ℝ := -3 / 16 + ((i.val : ℝ) + 1) / 4
  fin_cases side
  · convert (laneC_prime_vertical_connector_middle (x := t) (y := 1) hδ) using 1 <;>
      norm_num [laneCPrimeJoinRect, laneCPrimeJoinMidRect,
      laneCPrimeVerticalConnector, laneCPrimeVerticalConnectorMid,
      t, add_assoc]
  · convert (laneC_prime_vertical_connector_middle (x := t) (y := -1 / 4) hδ) using 1 <;>
      norm_num [laneCPrimeJoinRect, laneCPrimeJoinMidRect,
      laneCPrimeVerticalConnector, laneCPrimeVerticalConnectorMid,
      t, add_assoc]
  · convert (laneC_prime_horizontal_connector_middle (x := -1 / 4) (y := t) hδ) using 1 <;>
      norm_num [laneCPrimeJoinRect, laneCPrimeJoinMidRect,
      laneCPrimeHorizontalConnector, laneCPrimeHorizontalConnectorMid,
      t, add_assoc]
  · convert (laneC_prime_horizontal_connector_middle (x := 1) (y := t) hδ) using 1 <;>
      norm_num [laneCPrimeJoinRect, laneCPrimeJoinMidRect,
      laneCPrimeHorizontalConnector, laneCPrimeHorizontalConnectorMid,
      t, add_assoc]

end SupercriticalLQGUniqueness.B2.DG20Conc
