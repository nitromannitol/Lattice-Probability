import Mathlib

/-!
# Mathlib-only statement vocabulary for the comparator solutions

A verbatim copy of the vocabulary block (between `VOCABULARY-BEGIN` and
`VOCABULARY-END`) of `Audit/LatticeProbAudit/GFF/Challenge.lean`, the only
challenge that needs definitions beyond Mathlib's.  It imports only Mathlib, so
the definitions it declares elaborate exactly as they do in the challenge;
`Audit/check_standalone.sh --vocabulary` checks that the blocks are
byte-identical.
-/

-- VOCABULARY-BEGIN
namespace LatticeProbAudit

open scoped ENNReal

variable {V : Type*}

/-- The one-step averaging operator `(P f)(x) = deg(x)⁻¹ ∑_{y ∼ x} f(y)` of simple
random walk on a locally finite graph. -/
noncomputable def walkOp (G : SimpleGraph V) [G.LocallyFinite] (f : V → ℝ) (x : V) : ℝ :=
  (∑ y ∈ G.neighborFinset x, f y) / G.degree x

open scoped Classical in
/-- The `k`-step transition probability `P_x(X_k = y, X_0, …, X_k ∈ C)` of simple
random walk killed on leaving `C`, by the recursion in the starting point. -/
noncomputable def killedHeat (G : SimpleGraph V) [G.LocallyFinite] (C : Set V) :
    ℕ → V → V → ℝ
  | 0 => fun x y => if x ∈ C then (if x = y then 1 else 0) else 0
  | k + 1 => fun x y => if x ∈ C then walkOp G (fun z => killedHeat G C k z y) x else 0

/-- The killed Green function `g_C(y, v) = E_y[number of visits to v before leaving C] / deg(v)`,
valued in `[0, ∞]`. -/
noncomputable def killedGreen (G : SimpleGraph V) [G.LocallyFinite] (C : Set V) (y v : V) :
    ℝ≥0∞ :=
  (∑' k : ℕ, ENNReal.ofReal (killedHeat G C k y v)) / (G.degree v : ℝ≥0∞)

/-- The killed Green function as a real number. -/
noncomputable def killedGreenReal (G : SimpleGraph V) [G.LocallyFinite] (C : Set V) (y v : V) :
    ℝ :=
  (killedGreen G C y v).toReal

end LatticeProbAudit
-- VOCABULARY-END
