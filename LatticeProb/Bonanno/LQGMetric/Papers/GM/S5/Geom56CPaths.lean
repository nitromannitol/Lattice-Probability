/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.GM.S5.Geom56CPaths at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S5.Defs

/-!
# GM Lemma 5.6: the Euclidean paths `π₋`, `π₊`, as a statement (task P2-M2L56b)

GM = Gwynne–Miller, arXiv:1905.00383, `literature/src/1905.00383/uniqueness-final.tex`, proof of
Lemma 5.6, l. 2963–2966: "let `v' := (3/2)(v − z) + z`, `L₋` the segment from `z` to `u`, `L₊` the
segment from `v` to `v'`. We can choose a path `π₋` from `z − 2r` to `z` and a path `π₊` from `v'`
to `z + 2r` in `B_{2r}(z)` such that the Euclidean distances from `π₋ ∪ π₊` to `H_r(z)` and from
`π₋ ∪ L₋` to `π₊ ∪ L₊` are each at least `b r`."

`L56Paths` is this sentence, the planar (grid-free) part of the construction of `V_r(z)`, with
`π±` preconnected sets in the closed ball `cl B_{2r}(z)` (as in D69, condition (1) of `L56GeomN`
uses the closed ball) and a constant `b > 0` depending only on `α` (GM take `b = 1 − α`; only
`b > 0` is used). Open node, analogous to `L58Paths` (Geom58Paths.lean); the grid assembly
`L56Paths → L56ConstrN` is described in `handoff/P2-M2L56.md`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Metric

namespace LQGMetric.GM

/-- GM l. 2963–2966: the paths `π₋` (`Pm`) and `π₊` (`Pp`); see the module docstring -/
def L56Paths : Prop := ∀ α : ℝ, 3 / 4 ≤ α → α < 1 → ∃ b : ℝ, 0 < b ∧
  ∀ (z : ℂ) (r : ℝ), 0 < r → ∀ H : Set ℂ, IsHalfAnnulus H z (α * r) r →
  ∀ u ∈ sphere z (α * r), ∀ v ∈ sphere z r, u ∈ closure H → v ∈ closure H →
  ∃ Pm Pp : Set ℂ, IsPreconnected Pm ∧ IsPreconnected Pp ∧
    Pm ⊆ closedBall z (2 * r) ∧ Pp ⊆ closedBall z (2 * r) ∧
    z - 2 * r ∈ Pm ∧ z ∈ Pm ∧ z + (3 / 2 : ℂ) * (v - z) ∈ Pp ∧ z + 2 * r ∈ Pp ∧
    (∀ p ∈ Pm ∪ Pp, ∀ h ∈ closure H, b * r ≤ dist p h) ∧
    (∀ p ∈ Pm ∪ segment ℝ z u, ∀ q ∈ Pp ∪ segment ℝ v (z + (3 / 2 : ℂ) * (v - z)),
      b * r ≤ dist p q)

end LQGMetric.GM
