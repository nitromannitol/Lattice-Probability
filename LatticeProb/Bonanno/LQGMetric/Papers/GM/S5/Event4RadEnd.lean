/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.GM.S5.Event4RadEnd at commit fdb5cad; only the module paths of local imports are changed. -/
import Mathlib.Analysis.Complex.Basic

/-!
# GM Lemma 5.8: radial ends of the paths `L̂_x`, `L̂_y` (the predicate) (task P2-M2M7)

`RadEnd` (moved here from `Geom58T3`, P2-M2M4, so that `L58Paths` in `Geom58Paths` can use it):
near `x` the set `P` is the segment `{x − te : t ∈ [0, M]}` (GM Lemma 5.8, Step 2, l. 3080–3086;
decision D83 (c)).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open Set

namespace LQGMetric.GM

/-- near `x` the set `P` is the segment `{x − te : t ∈ [0, M]}` (within distance `R`) -/
def RadEnd (P : Set ℂ) (x : ℂ) (M R : ℝ) : Prop :=
  ∃ e : ℂ, ‖e‖ = 1 ∧ (∀ t ∈ Icc (0 : ℝ) M, x - (t : ℂ) * e ∈ P) ∧
    ∀ p ∈ P, dist p x < R → ∃ t ∈ Icc (0 : ℝ) M, p = x - (t : ℂ) * e

end LQGMetric.GM
