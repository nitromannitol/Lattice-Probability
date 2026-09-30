/-
Two facts about eventual stabilization of a sequence, moved from
`Dynamic-Dimensional-Reduction`'s `DimRed/Support/OneDimTerminal.lean` (proved
there in the course of Theorem 1.3's one-dimensional reduction, but with no
content specific to that argument): a monotone bounded sequence of naturals is
eventually constant, and pointwise eventual stabilization on a finite set gives
one common stabilization time.

`eventually_constant_of_monotone_bounded` is stated for `f : ℕ → ℕ` exactly as
in the source.  `finset_common_stable` is stated there only for
`g : ℕ → DimRed.Site 1 → ℤ`; the proof is a bare `Finset.induction_on` using
none of that structure, so it is given here for an arbitrary target type,
which is the form every consumer in this ecosystem's finite-domain
finiteness/termination arguments (the sandpile, parking, and rotor-walk
formalizations) needs.
-/
import Mathlib

namespace LatticeProb

/-- A monotone sequence of naturals bounded above by `K` is eventually
constant: past some time `T`, it equals its value at `T`. -/
theorem eventually_constant_of_monotone_bounded (f : ℕ → ℕ) (K : ℕ)
    (hmono : ∀ m n, m ≤ n → f m ≤ f n) (hbound : ∀ n, f n ≤ K) :
    ∃ T, ∀ n, f (T + n) = f T := by
  induction K with
  | zero =>
    refine ⟨0, ?_⟩
    intro n
    have h0 := hbound n
    have h1 := hbound 0
    have hn0 : f n = 0 := Nat.eq_zero_of_le_zero h0
    have h10 : f 0 = 0 := Nat.eq_zero_of_le_zero h1
    simpa using hn0.trans h10.symm
  | succ K ih =>
    by_cases hreach : ∃ n, f n = K + 1
    · obtain ⟨T, hT⟩ := hreach
      refine ⟨T, ?_⟩
      intro n
      have hle := hbound (T + n)
      have hmono' := hmono T (T + n) (by omega)
      omega
    · have hbound' : ∀ n, f n ≤ K := by
        intro n
        have hn : f n ≠ K + 1 := fun h => hreach ⟨n, h⟩
        have hle := hbound n
        omega
      exact ih hbound'

/-- If every point of a finite set `S` has its own stabilization time for a
sequence `g`, then `S` has a common one. -/
theorem finset_common_stable {α β : Type*} (g : ℕ → α → β) (S : Finset α)
    (hS : ∀ y ∈ S, ∃ T, ∀ n, g (T + n) y = g T y) :
    ∃ T, ∀ y ∈ S, ∀ n, g (T + n) y = g T y := by
  classical
  induction S using Finset.induction_on with
  | empty =>
    refine ⟨0, ?_⟩
    simp
  | @insert a S ha ih =>
    have ha' := hS a (Finset.mem_insert_self a S)
    obtain ⟨Ta, hTa⟩ := ha'
    obtain ⟨Ts, hTs⟩ := ih (fun y hy => hS y (Finset.mem_insert_of_mem hy))
    refine ⟨max Ta Ts, ?_⟩
    intro y hy n
    simp only [Finset.mem_insert] at hy
    rcases hy with hya | hy
    · subst y
      have h1 := hTa (max Ta Ts - Ta + n)
      have h2 := hTa (max Ta Ts - Ta)
      have e1 : max Ta Ts + n = Ta + (max Ta Ts - Ta + n) := by omega
      have e2 : max Ta Ts = Ta + (max Ta Ts - Ta) := by omega
      calc
        g (max Ta Ts + n) a = g (Ta + (max Ta Ts - Ta + n)) a := by rw [e1]
        _ = g Ta a := h1
        _ = g (Ta + (max Ta Ts - Ta)) a := h2.symm
        _ = g (max Ta Ts) a := by
          exact (congrArg (fun k => g k a) e2).symm
    · have h1 := hTs y hy (max Ta Ts - Ts + n)
      have h2 := hTs y hy (max Ta Ts - Ts)
      have e1 : max Ta Ts + n = Ts + (max Ta Ts - Ts + n) := by omega
      have e2 : max Ta Ts = Ts + (max Ta Ts - Ts) := by omega
      calc
        g (max Ta Ts + n) y = g (Ts + (max Ta Ts - Ts + n)) y := by rw [e1]
        _ = g Ts y := h1
        _ = g (Ts + (max Ta Ts - Ts)) y := h2.symm
        _ = g (max Ta Ts) y := by
          exact (congrArg (fun k => g k y) e2).symm

end LatticeProb
