/- Adapted from nitromannitol/rotor-23, Apache-2.0; copyright 2026 Ahmed Bou-Rabee and Yuval Peres. -/
import LatticeProb.Lattice.Planar.Boundary
import LatticeProb.Lattice.Planar.Exploration
import LatticeProb.Lattice.Planar.SquareDual

open Finset

namespace LatticeProb.Lattice.Planar

/-- The bond of a directed dual edge. -/
def bond (e : Site × Site) : Sym2 Site := s(e.1, e.2)

theorem rightFace_primal {a b : Site} (h : squareGraph.Adj a b) :
    rightFace (primalTail a b) (primalDir a b) = a := by
  rcases adj_sub_mem h with hu | hu | hu | hu <;>
  · have hb : b = a + (b - a) := by abel
    rw [hu] at hb
    subst hb
    obtain ⟨x, y⟩ := a
    simp [primalTail, primalDir, rightFace, dirOf, dirVec]

theorem leftFace_primal {a b : Site} (h : squareGraph.Adj a b) :
    leftFace (primalTail a b) (primalDir a b) = b := by
  rcases adj_sub_mem h with hu | hu | hu | hu <;>
  · have hb : b = a + (b - a) := by abel
    rw [hu] at hb
    subst hb
    obtain ⟨x, y⟩ := a
    simp [primalTail, primalDir, leftFace, rightFace, dirOf, dirVec] <;> omega

theorem dualEdge_primal {a b : Site} (h : squareGraph.Adj a b) :
    dualEdge (primalTail a b) (primalDir a b) = (a, b) := by
  rw [dualEdge, rightFace_primal h, leftFace_primal h]

theorem rightFace_injective (v : Site) : Function.Injective (rightFace v) := by
  intro a b hab
  obtain ⟨x, y⟩ := v
  revert hab
  fin_cases a <;> fin_cases b <;> simp [rightFace, dirVec]

/-- Distinct sides of the square at `v` have distinct bonds. -/
theorem bond_dualEdge_injective (v : Site) : Function.Injective (fun k => bond (dualEdge v k)) := by
  intro k k' h
  simp only [bond, dualEdge, Sym2.eq_iff, leftFace_eq] at h
  rcases h with ⟨h1, -⟩ | ⟨h1, h2⟩
  · exact rightFace_injective v h1
  · have h3 := rightFace_injective v h1
    have h4 := rightFace_injective v h2
    clear h1 h2
    subst h3
    revert k'
    decide

theorem dualEdge_adj (v : Site) (k : Dir) : squareGraph.Adj (dualEdge v k).1 (dualEdge v k).2 :=
  adj_rightFace_leftFace v k

theorem sideW_eq (a b : Site) : sideW a b = dualEdge (primalTail a b) (primalDir a b + 2) := rfl

theorem sideS_eq (a b : Site) : sideS a b = dualEdge (primalTail a b) (primalDir a b + 1) := rfl

/-- The primal tail of the reverse dual edge is the head of the primal edge. -/
theorem primalTail_rev {a b : Site} (h : squareGraph.Adj a b) :
    primalTail b a = primalTail a b + dirVec (primalDir a b) := by
  rcases adj_sub_mem h with hu | hu | hu | hu <;>
  · have hb : b = a + (b - a) := by abel
    rw [hu] at hb
    subst hb
    obtain ⟨x, y⟩ := a
    simp [primalTail, primalDir, dirOf, dirVec]

theorem primalTail_rev_ne {a b : Site} (h : squareGraph.Adj a b) : primalTail b a ≠ primalTail a b := by
  rw [primalTail_rev h]
  intro h'
  have := congrArg (fun p => p - primalTail a b) h'
  simp only [add_sub_cancel_left, sub_self] at this
  revert this
  generalize primalDir a b = k
  fin_cases k <;> simp [dirVec]

/-- `d` is a unit step. -/
def IsUnit (d : Site) : Prop := d = (1, 0) ∨ d = (-1, 0) ∨ d = (0, 1) ∨ d = (0, -1)

theorem isUnit_of_adj {a b : Site} (h : squareGraph.Adj a b) : IsUnit (b - a) := adj_sub_mem h

theorem adj_add_of_isUnit (a : Site) {d : Site} (hd : IsUnit d) : squareGraph.Adj a (a + d) :=
  adj_of_unit (by rw [add_sub_cancel_left]; exact hd)

theorem isUnit_rotL {d : Site} (hd : IsUnit d) : IsUnit (rotL d) := by
  rcases hd with h | h | h | h <;> subst h <;> simp [IsUnit, rotL]

theorem isUnit_rotR {d : Site} (hd : IsUnit d) : IsUnit (rotR d) := by
  rcases hd with h | h | h | h <;> subst h <;> simp [IsUnit, rotR]

theorem edgesFrom_tail (a d : Site) : ∀ e ∈ edgesFrom a d, e.1 = a := by
  simp [edgesFrom]

theorem edgesFrom_adj (a : Site) {d : Site} (hd : IsUnit d) :
    ∀ e ∈ edgesFrom a d, squareGraph.Adj e.1 e.2 := by
  simp only [edgesFrom, List.mem_cons, List.not_mem_nil, or_false]
  rintro e (rfl | rfl | rfl | rfl)
  · exact adj_add_of_isUnit a hd
  · exact adj_add_of_isUnit a (isUnit_rotL hd)
  · exact adj_add_of_isUnit a (isUnit_rotL (isUnit_rotL hd))
  · exact adj_add_of_isUnit a (isUnit_rotL (isUnit_rotL (isUnit_rotL hd)))

theorem edgesFrom_nodup (a : Site) {d : Site} (hd : IsUnit d) : (edgesFrom a d).Nodup := by
  rcases hd with h | h | h | h <;> subst h <;> simp [edgesFrom, rotL, Prod.ext_iff]

theorem continuations_tail (a b : Site) : ∀ e ∈ continuations a b, e.1 = b := by
  simp [continuations]

theorem continuations_adj {a b : Site} (h : squareGraph.Adj a b) :
    ∀ e ∈ continuations a b, squareGraph.Adj e.1 e.2 := by
  have hd := isUnit_of_adj h
  simp only [continuations, List.mem_cons, List.not_mem_nil, or_false]
  rintro e (rfl | rfl | rfl)
  · exact adj_add_of_isUnit b (isUnit_rotR hd)
  · exact adj_add_of_isUnit b hd
  · exact adj_add_of_isUnit b (isUnit_rotL hd)

theorem continuations_nodup {a b : Site} (h : squareGraph.Adj a b) : (continuations a b).Nodup := by
  have hd := isUnit_of_adj h
  have hb : b = a + (b - a) := by abel
  rcases hd with h' | h' | h' | h' <;> rw [h'] at hb <;> subst hb <;>
    simp [continuations, rotL, rotR, Prod.ext_iff]

/-- No continuation returns to the tail of the tested edge. -/
theorem continuations_ne {a b : Site} (h : squareGraph.Adj a b) :
    ∀ e ∈ continuations a b, e.2 ≠ a := by
  have hd := isUnit_of_adj h
  have hb : b = a + (b - a) := by abel
  rcases hd with h' | h' | h' | h' <;> rw [h'] at hb <;> subst hb <;>
    simp [continuations, rotL, rotR, Prod.ext_iff] <;> (intros; omega)

end LatticeProb.Lattice.Planar
