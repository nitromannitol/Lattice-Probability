/- Adapted from nitromannitol/rotor-23, Apache-2.0; copyright 2026 Ahmed Bou-Rabee and Yuval Peres. -/
import LatticeProb.Lattice.Planar.FrameSector

open Finset List Fin.NatCast

namespace LatticeProb.Lattice.Planar

/-- For the current edge `dualEdge v a = (SE, NE)` with `S = dualEdge v (a + 1) = (SW, SE)`:
`NE - SE = rotR (SW - SE)`. -/
theorem corner_NE_sub_SE (v : Site) (a : Dir) :
    leftFace v a - rightFace v a = rotR (rightFace v (a + 1) - rightFace v a) := by
  obtain ⟨x, y⟩ := v
  fin_cases a <;> simp [leftFace, rightFace, rotR, dirVec]

/-- The parallelogram: `NW - SW = NE - SE`. -/
theorem corner_NW_sub_SW (v : Site) (a : Dir) :
    rightFace v (a + 2) - rightFace v (a + 1) = leftFace v a - rightFace v a := by
  obtain ⟨x, y⟩ := v
  fin_cases a <;> simp [leftFace, rightFace, dirVec]

theorem sideS_fst (a b : Site) : (sideS a b).1 = rightFace (primalTail a b) (primalDir a b + 1) := rfl

theorem sideS_snd (a b : Site) : (sideS a b).2 = rightFace (primalTail a b) (primalDir a b) := by
  show leftFace _ _ = _
  rw [leftFace_eq, add_sub_cancel_right]

theorem sideW_fst (a b : Site) : (sideW a b).1 = rightFace (primalTail a b) (primalDir a b + 2) := rfl

theorem sideW_snd (a b : Site) : (sideW a b).2 = rightFace (primalTail a b) (primalDir a b + 1) := by
  show leftFace _ _ = _
  rw [leftFace_eq]
  have h : primalDir a b + 2 - 1 = primalDir a b + 1 := by
    generalize primalDir a b = k
    revert k; decide
  rw [h]

/-- The direction `rotR w` lies in the right arc from `-u` to `w`, unless `u = -w` or `u = rotL w`. -/
theorem between_rotR {u w : Site} (hu : IsUnit u) (hw : IsUnit w) (h1 : u ≠ -w) (h2 : u ≠ rotL w) :
    Between (dirIdx (-u)) (dirIdx w) (dirIdx (rotR w)) := by
  rcases hu with rfl | rfl | rfl | rfl <;> rcases hw with rfl | rfl | rfl | rfl <;>
    first | decide | exact absurd rfl h1 | exact absurd rfl h2

/-- A direction after `rotR w` in the frame (strictly between `rotR w` and `-u`) other than `w`
lies strictly between `w` and `-u`. -/
theorem between_of_between_rotR {u w v : Site} (hu : IsUnit u) (hw : IsUnit w) (hv : IsUnit v)
    (h : Between (dirIdx (rotR w)) (dirIdx (-u)) (dirIdx v)) (hvw : v ≠ w) :
    Between (dirIdx w) (dirIdx (-u)) (dirIdx v) := by
  rcases hu with rfl | rfl | rfl | rfl <;> rcases hw with rfl | rfl | rfl | rfl <;>
    rcases hv with rfl | rfl | rfl | rfl <;> first | decide | exact absurd h (by decide) | exact absurd rfl hvw

/-- In a non-root frame with an earlier edge `c₀` before the child `c`, the parent direction
lies strictly between the child direction and `c₀`'s direction. -/
theorem between_parent_of_before {p z c c₀ : Site} (hd : IsUnit (z - p))
    {pre post : List (Site × Site)} (hfr : continuations p z = pre ++ (z, c) :: post)
    (hc₀ : (z, c₀) ∈ pre) :
    Between (dirIdx (c - z)) (dirIdx (c₀ - z)) (dirIdx (p - z)) := by
  have hpz : p - z = -(z - p) := by abel
  rw [hpz, continuations_eq] at *
  have key : ∀ d : Site, IsUnit d →
      Between (dirIdx d) (dirIdx (rotR d)) (dirIdx (-d)) ∧
      Between (dirIdx (rotL d)) (dirIdx (rotR d)) (dirIdx (-d)) ∧
      Between (dirIdx (rotL d)) (dirIdx d) (dirIdx (-d)) := by
    intro d hd; rcases hd with rfl | rfl | rfl | rfl <;> decide
  obtain ⟨h1, h2, h3⟩ := key (z - p) hd
  rcases pre with _ | ⟨a₁, _ | ⟨a₂, _ | ⟨a₃, pre'⟩⟩⟩
  · simp at hc₀
  · simp only [List.cons_append, List.nil_append, List.cons.injEq, Prod.mk.injEq, true_and] at hfr
    obtain ⟨ha₁, hc, -⟩ := hfr
    subst ha₁
    simp only [List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq, true_and] at hc₀
    subst hc₀
    rw [← hc]
    simp only [add_sub_cancel_left]
    exact h1
  · simp only [List.cons_append, List.nil_append, List.cons.injEq, Prod.mk.injEq, true_and] at hfr
    obtain ⟨ha₁, ha₂, hc, -⟩ := hfr
    subst ha₁ ha₂
    simp only [List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq, true_and] at hc₀
    rw [← hc]
    rcases hc₀ with rfl | rfl <;> simp only [add_sub_cancel_left]
    · exact h2
    · exact h3
  · simp only [List.cons_append, List.cons.injEq] at hfr
    have := congrArg List.length hfr.2.2.2
    simp only [List.length_nil, List.length_append, List.length_cons] at this
    omega

end LatticeProb.Lattice.Planar
