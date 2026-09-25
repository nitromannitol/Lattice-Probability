/-
The first-return time and the first-return (induced) map.

Setting: `T : Ω → Ω`, `A : Set Ω`. `retTime T A x` is the first `n > 0` with `T^[n] x ∈ A` (and
`0` if there is none); `inducedMap T A x = T^[retTime T A x] x` is the first-return map. `retSet`
and `avoidSet` record, respectively, the points whose first return to `A` after time `0`, and
whose first entrance to `A` at any time `≥ 0`, land at a given time in a given set; `entSet`
collects the points whose first entrance to `A` lands in a given set `E`.

These definitions are shared by `LatticeProb.Prob.Kac` (Kac's lemma) and by the still-in-progress
formalization of the induced map itself (Poincaré recurrence, measure preservation, ergodicity of
the induced map); they are stated once here instead of being duplicated in each.
-/
import Mathlib

namespace LatticeProb

variable {Ω : Type*}

open Classical in
/-- The first return time to `A` (`0` if the orbit never returns). -/
noncomputable def retTime (T : Ω → Ω) (A : Set Ω) (x : Ω) : ℕ :=
  if h : ∃ n, 0 < n ∧ T^[n] x ∈ A then Nat.find h else 0

/-- The first-return (induced) map. -/
noncomputable def inducedMap (T : Ω → Ω) (A : Set Ω) (x : Ω) : Ω := T^[retTime T A x] x

/-- Points whose first return to `A` after time `0` happens at time `n` and lands in `B`
(for `0 < n`). -/
def retSet (T : Ω → Ω) (A B : Set Ω) (n : ℕ) : Set Ω :=
  {x | T^[n] x ∈ B ∧ ∀ j, 0 < j → j < n → T^[j] x ∉ A}

/-- Points avoiding `A` at times `0, …, n-1` and in `B` at time `n`. -/
def avoidSet (T : Ω → Ω) (A B : Set Ω) (n : ℕ) : Set Ω :=
  {x | T^[n] x ∈ B ∧ ∀ j < n, T^[j] x ∉ A}

/-- Points whose first entrance to `A` (at a time `≥ 0`) lands in `E`. -/
def entSet (T : Ω → Ω) (A E : Set Ω) : Set Ω :=
  {x | ∃ n, T^[n] x ∈ A ∧ (∀ j < n, T^[j] x ∉ A) ∧ T^[n] x ∈ E}

end LatticeProb
