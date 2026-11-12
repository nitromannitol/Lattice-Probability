/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.CONF.S3T39K8f at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.CONF.S3T39K8e

/-!
# CONF Theorem 3.9, packet J6d, node O2: hit events of the centre set

Gwynne–Miller, *Confluence of geodesics in LQG* (arXiv:1905.00381), `confluence-final.tex`,
C:1586. **`k8CtrHit_iff`**: for `K` closed, bounded, with Jordan frontier and `J ⊆ ∂K`, the
centre set `t39jCtrSet K J r` (closure of the centres `c ∈ ∂K` with `B̄_r(c)` disconnecting `J`
from `∞`) meets the open set `U` iff the countable condition `k8CtrHit K J r U` holds: some
rational closed ball `B̄_ρ(p) ⊆ U` contains limits of rational centres `c'` within `1/(j+1)` of
`∂K` with `B̄_{r + 1/(j+1)}(c')` disconnecting. Own elementary argument.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Metric Filter Topology

namespace LQGMetric.CONF

/-- the countable form of the hit event of the centre set -/
def k8CtrHit (K J : Set ℂ) (r : ℝ) (U : Set ℂ) : Prop :=
  ∃ p : ℚ × ℚ, ∃ ρ : ℚ, (0 : ℝ) < ρ ∧ closedBall (k8Q p) ρ ⊆ U ∧ ∀ j : ℕ, ∃ c' : ℚ × ℚ,
    dist (k8Q c') (k8Q p) < ρ + 1 / ((j : ℝ) + 1) ∧
      k8FrHit K (ball (k8Q c') (1 / ((j : ℝ) + 1))) ∧ k8Disc K J (k8Q c') (r + 1 / ((j : ℝ) + 1))

theorem k8_one_div_pos (j : ℕ) : (0 : ℝ) < 1 / ((j : ℝ) + 1) := by positivity

end LQGMetric.CONF
