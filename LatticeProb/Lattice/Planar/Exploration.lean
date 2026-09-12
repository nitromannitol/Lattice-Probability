/- Adapted from nitromannitol/rotor-23, Apache-2.0; copyright 2026 Ahmed Bou-Rabee and Yuval Peres. -/
import LatticeProb.Lattice.Planar.Dual

open Finset

namespace LatticeProb.Lattice.Planar

/-- Counterclockwise rotation of a unit step by `90°`. -/
def rotL (d : Site) : Site := (-d.2, d.1)

/-- Clockwise rotation of a unit step by `90°`. -/
def rotR (d : Site) : Site := (d.2, -d.1)

/-- The four directed dual edges leaving the face `a`, counterclockwise from
the step `d`. -/
def edgesFrom (a d : Site) : List (Site × Site) :=
  [(a, a + d), (a, a + rotL d), (a, a + rotL (rotL d)), (a, a + rotL (rotL (rotL d)))]

/-- After an open test of `a → b`: the three edges leaving `b` other than the
reverse, in right-turn, straight, left-turn order. -/
def continuations (a b : Site) : List (Site × Site) :=
  let d := b - a
  [(b, b + rotR d), (b, b + d), (b, b + rotL d)]

/-- The face `h` lies in a finite component of the complement of `visited`. -/
def InFiniteComponent (visited : Finset Site) (h : Site) : Prop :=
  h ∉ visited ∧ Set.Finite {y : Site | ∃ (hy : y ∉ visited) (hh : h ∉ visited),
    (squareGraph.induce {x : Site | x ∉ visited}).Reachable ⟨h, hh⟩ ⟨y, hy⟩}

/-- The state of the exploration. -/
structure ExplState where
  /-- The visited faces. -/
  visited : Finset Site
  /-- The active list; its head is the current edge. -/
  active : List (Site × Site)
  /-- The tested edges with their outcomes, oldest first. -/
  tested : List (Site × Site × Bool)
  /-- The number of forced tests so far. -/
  forced : ℕ

/-- The sides of the square of the current dual edge `a → b`: with `v` the tail
of the primal edge and `d` its direction, the side `E` is the current edge and
`N, W, S` are `dualEdge v (d - 1)`, `dualEdge v (d + 2)`, `dualEdge v (d + 1)`
(counterclockwise from `E`). -/
def sideW (a b : Site) : Site × Site :=
  let v := primalTail a b
  dualEdge v (primalDir a b + 2)

/-- The side `S` of the square of the current edge. -/
def sideS (a b : Site) : Site × Site :=
  let v := primalTail a b
  dualEdge v (primalDir a b + 1)

/-- `e` was tested with outcome `o` earlier in the history `h`. -/
def TestedAs (h : List (Site × Site × Bool)) (e : Site × Site) (o : Bool) : Prop :=
  (e.1, e.2, o) ∈ h

open Classical in
/-- One step with a prescribed outcome `o` for the current edge; the identity
when the active list is empty. -/
noncomputable def explStepWith (s : ExplState) (o : Bool) : ExplState :=
  match s.active with
  | [] => s
  | e :: rest =>
    let visited' := if o then insert e.2 s.visited else s.visited
    let added := if o then continuations e.1 e.2 else []
    let forced' := if TestedAs s.tested (sideW e.1 e.2) false then s.forced + 1 else s.forced
    { visited := visited',
      active := (added ++ rest).filter
        (fun g => ¬ (g.2 ∈ visited' ∨ InFiniteComponent visited' g.2)),
      tested := s.tested ++ [(e.1, e.2, o)],
      forced := forced' }

/-- The initial state: visited `{f}`, the four edges leaving `f` counterclockwise
from the chosen edge `f → f + d`. -/
def explInit (f d : Site) : ExplState :=
  { visited := {f}, active := edgesFrom f d, tested := [], forced := 0 }

open Classical in
/-- One step of the exploration with the outcome read from the rotors `ρ`. -/
noncomputable def explStep (ρ : Config squareGraph) (s : ExplState) : ExplState :=
  match s.active with
  | [] => s
  | e :: _ => explStepWith s (decide (DualOpen ρ e.1 e.2))

/-- The exploration from the face `f` along the edge `f → f + d`, after `n` tests. -/
noncomputable def explore (ρ : Config squareGraph) (f d : Site) (n : ℕ) : ExplState :=
  (explStep ρ)^[n] (explInit f d)

end LatticeProb.Lattice.Planar
