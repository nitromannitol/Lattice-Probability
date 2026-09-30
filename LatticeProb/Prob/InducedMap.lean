import LatticeProb.Prob.InducedMap.RetTimeMeasurability
import LatticeProb.Prob.InducedMap.TowerComputation
import LatticeProb.Prob.InducedMap.MeasurePreservation
import LatticeProb.Prob.InducedMap.Ergodicity
import LatticeProb.Prob.InducedMap.Iterates
import LatticeProb.Prob.InducedMap.MainTheorem

/-!
# The first-return (induced) map

For `T` preserving a finite measure `μ` and a measurable `A`, `retTime T A x` is the first
`n > 0` with `T^[n] x ∈ A` (and `0` if there is none) and `inducedMap T A x = T^[retTime T A x] x`
is the first-return map (`LatticeProb.Prob.ReturnTime`).  The main theorem `induced_map` gives

* Poincare recurrence: `retTime T A x > 0` for a.e. `x ∈ A`;
* `inducedMap T A` preserves `μ.restrict A` (no hypothesis `μ A > 0`);
* `inducedMap T A` is ergodic for `μ.restrict A` when `T` is ergodic for `μ`.

This file only imports its children, one per proof stage, under `LatticeProb/Prob/InducedMap/`.

## Route

* Return-time measurability (`RetTimeMeasurability`): `retTime T A x = n` is characterised by an
  explicit membership and avoidance condition on `T^[n] x`, which makes each level set of
  `retTime` measurable, hence `retTime T A` and `inducedMap T A` measurable.
* The tower computation (`TowerComputation`): the tower / Kakutani skyscraper recursion. For
  `B ⊆ A` put `F n B = {x | T^[n] x ∈ B ∧ ∀ j, 0 < j → j < n → T^[j] x ∉ A}` (`retSet`) and
  `H n B = {x | T^[n] x ∈ B ∧ ∀ j < n, T^[j] x ∉ A}` (`avoidSet`, `H 0 B = B`).  Splitting
  `T⁻¹ (H n B)` according to `x ∈ A` gives `T⁻¹ (H n B) = (A ∩ F (n+1) B) ∪ H (n+1) B`, disjoint,
  so `μ (H n B) = μ (A ∩ F (n+1) B) + μ (H (n+1) B)` and by induction
  `μ B = ∑_{k<n} μ (A ∩ F (k+1) B) + μ (H n B)`.  The `H n B` are pairwise disjoint, so
  `μ (H n B) → 0` and `μ B = ∑' k, μ (A ∩ F (k+1) B)`.
* Measure preservation (`MeasurePreservation`): `A ∩ inducedMap⁻¹ B` is the disjoint union of the
  `A ∩ F (k+1) B` and the null set `A ∩ {retTime = 0} ∩ B`, giving Poincaré recurrence and
  invariance of `μ.restrict A` under `inducedMap T A`.
* Ergodicity (`Ergodicity`): for `E` with `inducedMap⁻¹ E = E`, the first-entrance set
  `entSet T A E = {x | ∃ n, T^[n] x ∈ A ∧ (∀ j < n, T^[j] x ∉ A) ∧ T^[n] x ∈ E}` satisfies
  `T⁻¹ entSet =ᵐ[μ] entSet` (exact off `A ∩ {retTime = 0}`), and `entSet ∩ A = E ∩ A`; apply
  Mathlib's `QuasiErgodic.aeconst_set₀` to `entSet` and restrict to `A`.
* Iterates (`Iterates`): the iterates of the induced map are iterates of `T` along the Birkhoff
  sums of the return time (`inducedMap_iterate`), which `LatticeProb.Prob.KingmanLinear` uses.
* Main theorem (`MainTheorem`): assembles the three parts into `induced_map`.

The proof was written by the library's proof fleet from a statement-owned decomposition and
verified by the library gates.
-/
