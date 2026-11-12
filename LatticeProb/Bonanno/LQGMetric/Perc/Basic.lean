/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Perc.Basic at commit fdb5cad; only the module paths of local imports are changed.
   Declarations, examples and checks that the copied results do not use are omitted. -/
import Mathlib.Logic.Relation
import Mathlib.Data.Int.Interval
import Mathlib.Data.Finset.Prod

/-!
Sites are points of `ℤ × ℤ` (the boxes of a grid of boxes). This file fixes the notions used by
the percolation tools of `LQGMetric.Perc.*`:

* `PercAdj4 x y`: `x, y` share an edge (nearest neighbours, `|x - y|₁ = 1`);
* `PercAdjK x y`: `x ≠ y` share an edge or a corner (`*`-adjacency, "chess king" moves,
  `|x - y|_∞ = 1`);
* `percInGrid K L x`: `x ∈ [0, K) × [0, L)`, the `K × L` rectangle of boxes (`K` columns,
  `L` rows; first coordinate = column, second = row);
* `PercGoodLR K L good`: a left–right crossing of the rectangle by `4`-connected good sites
  (a `4`-path of good grid sites from column `0` to column `K - 1`);
* `PercBadTB K L good`: a top–bottom crossing by `*`-connected bad sites
  (a `*`-path of bad grid sites from row `L - 1` to row `0`).

Paths are `Relation.ReflTransGen` of the corresponding one-step relation; for the counting in
`LQGMetric.Perc.Peierls` they are turned into lists.

These are the notions of Ding–Gwynne, arXiv:1807.01072, proof of Lemma 3.11
(`metric-comparison-final.tex` lines 1257–1278): "two squares adjacent if they share an edge"
for the good crossing and the graph `𝒮*` ("share a corner or an edge") for the dual bad
crossing.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace LQGMetric

/-- Nearest-neighbour adjacency on `ℤ²` (the sites share an edge). -/
def PercAdj4 (x y : ℤ × ℤ) : Prop :=
  (x.1 = y.1 ∧ (x.2 = y.2 + 1 ∨ y.2 = x.2 + 1)) ∨ (x.2 = y.2 ∧ (x.1 = y.1 + 1 ∨ y.1 = x.1 + 1))

/-- `*`-adjacency on `ℤ²`: distinct sites at `ℓ^∞`-distance one (they share an edge or a
corner). -/
def PercAdjK (x y : ℤ × ℤ) : Prop :=
  (x.1 ≠ y.1 ∨ x.2 ≠ y.2) ∧ x.1 ≤ y.1 + 1 ∧ y.1 ≤ x.1 + 1 ∧ x.2 ≤ y.2 + 1 ∧ y.2 ≤ x.2 + 1

/-- The `K × L` rectangle of sites `[0, K) × [0, L)`. -/
def percInGrid (K L : ℤ) (x : ℤ × ℤ) : Prop :=
  0 ≤ x.1 ∧ x.1 < K ∧ 0 ≤ x.2 ∧ x.2 < L

/-- One step of a `4`-path of good grid sites. -/
def PercGoodStep (K L : ℤ) (good : ℤ × ℤ → Prop) (x y : ℤ × ℤ) : Prop :=
  percInGrid K L x ∧ good x ∧ percInGrid K L y ∧ good y ∧ PercAdj4 x y

/-- One step of a `*`-path of bad grid sites. -/
def PercBadStep (K L : ℤ) (good : ℤ × ℤ → Prop) (x y : ℤ × ℤ) : Prop :=
  percInGrid K L x ∧ ¬ good x ∧ percInGrid K L y ∧ ¬ good y ∧ PercAdjK x y

/-- A left–right crossing of the `K × L` rectangle by a `4`-path of good sites. -/
def PercGoodLR (K L : ℤ) (good : ℤ × ℤ → Prop) : Prop :=
  ∃ a b : ℤ × ℤ, a.1 = 0 ∧ b.1 = K - 1 ∧ percInGrid K L a ∧ good a ∧
    Relation.ReflTransGen (PercGoodStep K L good) a b

/-- A top–bottom crossing of the `K × L` rectangle by a `*`-path of bad sites. -/
def PercBadTB (K L : ℤ) (good : ℤ × ℤ → Prop) : Prop :=
  ∃ a b : ℤ × ℤ, a.2 = L - 1 ∧ b.2 = 0 ∧ percInGrid K L a ∧ ¬ good a ∧
    Relation.ReflTransGen (PercBadStep K L good) a b

end LQGMetric
