/- Adapted from nitromannitol/rotor-23, Apache-2.0; copyright 2026 Ahmed Bou-Rabee and Yuval Peres. -/
import Mathlib

open Finset

namespace LatticeProb.Lattice.Planar

variable {V : Type*} [DecidableEq V] (G : SimpleGraph V) [G.LocallyFinite]

/-- A rotor mechanism on `G`: at each vertex `v`, a cyclic permutation `next v`
of the neighbors of `v`.  `cyclic` says the powers of `next v`
act transitively, which for a finite set is exactly "a single cycle". -/
structure Mechanism where
  /-- `π_v`: the next directed edge out of `v` after a given one. -/
  next : ∀ v : V, Equiv.Perm (G.neighborSet v)
  /-- `π_v` is a cyclic permutation. -/
  cyclic : ∀ (v : V) (a b : G.neighborSet v), ∃ k : ℕ, ((next v) ^ k) a = b
  /-- every vertex has an outgoing directed edge. -/
  nonempty : ∀ v : V, Nonempty (G.neighborSet v)

/-- A rotor configuration: one outgoing directed edge at every vertex. -/
abbrev Config := ∀ v : V, G.neighborSet v

variable {G} (π : Mechanism G)

omit [DecidableEq V] [G.LocallyFinite] in
theorem rank_exists (ρ : Config G) (v : V) (w : G.neighborSet v) :
    ∃ k : ℕ, 0 < k ∧ ((π.next v) ^ k) (ρ v) = w := by
  obtain ⟨d, hd⟩ := π.cyclic v (π.next v (ρ v)) w
  exact ⟨d + 1, Nat.succ_pos d, by simpa only [pow_succ, Equiv.Perm.mul_apply] using hd⟩

/-- The number of rotor advances from `ρ v` until the directed edge `v → w` is
selected: the least `k ≥ 1` with `(next v)^k (ρ v) = w`.  It lies in
`{1, …, deg v}`. -/
noncomputable def rank (ρ : Config G) (v : V) (w : G.neighborSet v) : ℕ :=
  Nat.find (rank_exists π ρ v w)

end LatticeProb.Lattice.Planar
