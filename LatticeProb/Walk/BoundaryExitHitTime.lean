import LatticeProb.Bonanno.MatedCRTHarmonic.Markov.HitTime
import Mathlib.Combinatorics.SimpleGraph.Basic

/-!
# Graph boundary and exit times

For a nearest-neighbour path, the last vertex before exiting a set lies in its
inner vertex boundary. Its first boundary hit may occur earlier.
-/

set_option autoImplicit false

open Set
open MatedCRTHarmonic.Markov

namespace LatticeProb

variable {V : Type*} (G : SimpleGraph V) (A : Set V) (ω : ℕ → V)

/-- The last inside vertex before a positive first exit is in the inner boundary. -/
theorem mem_innerBoundary_before_hit_compl {n : ℕ}
    (hτ : hitTime Aᶜ ω = (n + 1 : ℕ)) (hstep : G.Adj (ω n) (ω (n + 1))) :
    ω n ∈ {v | v ∈ A ∧ ∃ w, G.Adj v w ∧ w ∉ A} := by
  have h := hitTime_eq_coe_iff.mp hτ
  exact ⟨by simpa using h.2 n (Nat.lt_succ_self n), ω (n + 1), hstep, h.1⟩

/-- The first hit of the inner boundary is no later than the last inside vertex. -/
theorem hit_innerBoundary_le_before_hit_compl {n : ℕ}
    (hτ : hitTime Aᶜ ω = (n + 1 : ℕ)) (hstep : G.Adj (ω n) (ω (n + 1))) :
    hitTime {v | v ∈ A ∧ ∃ w, G.Adj v w ∧ w ∉ A} ω ≤ (n : ℕ∞) :=
  hitTime_le_of_mem (mem_innerBoundary_before_hit_compl G A ω hτ hstep)

/-- The first boundary hit is exactly the last inside time precisely when the
path avoided that boundary at all earlier times. -/
theorem hit_innerBoundary_eq_before_hit_compl_iff {n : ℕ}
    (hτ : hitTime Aᶜ ω = (n + 1 : ℕ)) (hstep : G.Adj (ω n) (ω (n + 1))) :
    hitTime {v | v ∈ A ∧ ∃ w, G.Adj v w ∧ w ∉ A} ω = (n : ℕ∞) ↔
      ∀ j < n, ω j ∉ {v | v ∈ A ∧ ∃ w, G.Adj v w ∧ w ∉ A} := by
  rw [hitTime_eq_coe_iff]
  exact ⟨And.right, fun h => ⟨mem_innerBoundary_before_hit_compl G A ω hτ hstep, h⟩⟩

end LatticeProb
