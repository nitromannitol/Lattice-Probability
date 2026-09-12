/- Adapted from nitromannitol/rotor-23, Apache-2.0; copyright 2026 Ahmed Bou-Rabee and Yuval Peres. -/
import Mathlib

open MeasureTheory Finset

namespace LatticeProb.Lattice.Planar

variable {V : Type*} [DecidableEq V] (G : SimpleGraph V) [G.LocallyFinite]

/-- The plane. -/
abbrev Plane := EuclideanSpace ℝ (Fin 2)

/-- A doubly periodic graph in the plane. -/
structure DoublyPeriodic where
  /-- The vertex set drawn in the plane: `V ⊂ ℝ²`. -/
  emb : V → Plane
  emb_injective : Function.Injective emb
  /-- The action of the lattice `Λ ≅ ℤ²` by translation. -/
  shift : ℤ × ℤ → V → V
  shift_zero : ∀ v, shift 0 v = v
  shift_add : ∀ z w v, shift (z + w) v = shift z (shift w v)
  /-- A basis of the lattice `Λ`. -/
  b : Fin 2 → Plane
  b_indep : LinearIndependent ℝ b
  emb_shift : ∀ z v, emb (shift z v) = emb v + (z.1 : ℝ) • b 0 + (z.2 : ℝ) • b 1
  /-- Translations are automorphisms. -/
  adj_shift : ∀ z u v, G.Adj (shift z u) (shift z v) ↔ G.Adj u v
  /-- Orbit representatives and coordinates. -/
  rep : V → V
  coord : V → ℤ × ℤ
  shift_coord_rep : ∀ v, shift (coord v) (rep v) = v
  rep_shift : ∀ z v, rep (shift z v) = rep v
  /-- Finitely many orbits. -/
  finite_orbits : (Set.range rep).Finite

end LatticeProb.Lattice.Planar
namespace LatticeProb.Lattice.Planar.DoublyPeriodic

variable {V : Type*} [DecidableEq V] {G : SimpleGraph V} [G.LocallyFinite]

variable (P : DoublyPeriodic G)

/-- A neighbor of `v`, shifted by `z`, is a neighbor of `shift z v`. -/
def shiftNbr (z : ℤ × ℤ) {v : V} (a : G.neighborSet v) : G.neighborSet (P.shift z v) :=
  ⟨P.shift z a.1, (P.adj_shift z v a.1).2 a.2⟩

omit [DecidableEq V] [G.LocallyFinite] in
theorem shift_neg_shift (z : ℤ × ℤ) (v : V) : P.shift z (P.shift (-z) v) = v := by
  rw [← P.shift_add, add_neg_cancel, P.shift_zero]

omit [DecidableEq V] [G.LocallyFinite] in
theorem shift_shift_neg (z : ℤ × ℤ) (v : V) : P.shift (-z) (P.shift z v) = v := by
  rw [← P.shift_add, neg_add_cancel, P.shift_zero]

end LatticeProb.Lattice.Planar.DoublyPeriodic
namespace LatticeProb.Lattice.Planar

end LatticeProb.Lattice.Planar
