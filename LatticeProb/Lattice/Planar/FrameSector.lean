/- Adapted from nitromannitol/rotor-23, Apache-2.0; copyright 2026 Ahmed Bou-Rabee and Yuval Peres. -/
import LatticeProb.Lattice.Planar.Ring

open Finset List Fin.NatCast

namespace LatticeProb.Lattice.Planar

theorem continuations_eq (p z : Site) :
    continuations p z = [(z, z + rotR (z - p)), (z, z + (z - p)), (z, z + rotL (z - p))] := rfl

theorem edgesFrom_eq (f d : Site) :
    edgesFrom f d = [(f, f + d), (f, f + rotL d), (f, f + rotL (rotL d)), (f, f + rotL (rotL (rotL d)))] :=
  rfl

/-- The finite check behind the sector lemmas: the offsets of `rotR d, d, rotL d` from `-d`. -/
theorem between_frame_dirs (d : Site) (hd : IsUnit d) :
    Between (dirIdx (rotR d)) (dirIdx (-d)) (dirIdx d) ∧
    Between (dirIdx (rotR d)) (dirIdx (-d)) (dirIdx (rotL d)) ∧
    Between (dirIdx d) (dirIdx (-d)) (dirIdx (rotL d)) ∧
    Between (dirIdx d) (dirIdx (rotR d)) (dirIdx (rotL d)) := by
  rcases hd with rfl | rfl | rfl | rfl <;> decide

/-- A later edge of a non-root frame points strictly between the child direction and the parent
direction. -/
theorem between_of_after_child {p z c y : Site} (hd : IsUnit (z - p))
    {pre post : List (Site × Site)} (hfr : continuations p z = pre ++ (z, c) :: post)
    (hy : (z, y) ∈ post) :
    Between (dirIdx (c - z)) (dirIdx (p - z)) (dirIdx (y - z)) := by
  have hpz : p - z = -(z - p) := by abel
  rw [hpz, continuations_eq] at *
  obtain ⟨h1, h2, h3, h4⟩ := between_frame_dirs (z - p) hd
  rcases pre with _ | ⟨a₁, _ | ⟨a₂, _ | ⟨a₃, pre'⟩⟩⟩
  · simp only [List.nil_append, List.cons.injEq, Prod.mk.injEq, true_and] at hfr
    obtain ⟨hc, hpost⟩ := hfr
    subst hpost
    simp only [List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq, true_and] at hy
    rcases hy with rfl | rfl <;> rw [← hc] <;> simp only [add_sub_cancel_left]
    · exact h1
    · exact h2
  · simp only [List.cons_append, List.nil_append, List.cons.injEq, Prod.mk.injEq, true_and] at hfr
    obtain ⟨-, hc, hpost⟩ := hfr
    subst hpost
    simp only [List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq, true_and] at hy
    subst hy
    rw [← hc]
    simp only [add_sub_cancel_left]
    exact h3
  · simp only [List.cons_append, List.nil_append, List.cons.injEq, Prod.mk.injEq, true_and] at hfr
    obtain ⟨-, -, -, hpost⟩ := hfr
    subst hpost
    simp at hy
  · simp only [List.cons_append, List.cons.injEq] at hfr
    have := congrArg List.length hfr.2.2.2
    simp only [List.length_nil, List.length_append, List.length_cons] at this
    omega

/-- A later edge points strictly between the child direction and an earlier edge's direction. -/
theorem between_of_before_after {p z c c₀ y : Site} (hd : IsUnit (z - p))
    {pre post : List (Site × Site)} (hfr : continuations p z = pre ++ (z, c) :: post)
    (hc₀ : (z, c₀) ∈ pre) (hy : (z, y) ∈ post) :
    Between (dirIdx (c - z)) (dirIdx (c₀ - z)) (dirIdx (y - z)) := by
  rw [continuations_eq] at hfr
  obtain ⟨h1, h2, h3, h4⟩ := between_frame_dirs (z - p) hd
  rcases pre with _ | ⟨a₁, _ | ⟨a₂, _ | ⟨a₃, pre'⟩⟩⟩
  · simp at hc₀
  · simp only [List.cons_append, List.nil_append, List.cons.injEq, Prod.mk.injEq, true_and] at hfr
    obtain ⟨ha₁, hc, hpost⟩ := hfr
    subst hpost ha₁
    simp only [List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq, true_and] at hy hc₀
    subst hy hc₀
    rw [← hc]
    simp only [add_sub_cancel_left]
    exact h4
  · simp only [List.cons_append, List.nil_append, List.cons.injEq, Prod.mk.injEq, true_and] at hfr
    obtain ⟨-, -, -, hpost⟩ := hfr
    subst hpost
    simp at hy
  · simp only [List.cons_append, List.cons.injEq] at hfr
    have := congrArg List.length hfr.2.2.2
    simp only [List.length_nil, List.length_append, List.length_cons] at this
    omega

/-- The finite check for the root frame. -/
theorem between_root_dirs (d : Site) (hd : IsUnit d) :
    Between (dirIdx (rotL d)) (dirIdx d) (dirIdx (rotL (rotL d))) ∧
    Between (dirIdx (rotL d)) (dirIdx d) (dirIdx (rotL (rotL (rotL d)))) ∧
    Between (dirIdx (rotL (rotL d))) (dirIdx d) (dirIdx (rotL (rotL (rotL d)))) ∧
    Between (dirIdx (rotL (rotL d))) (dirIdx (rotL d)) (dirIdx (rotL (rotL (rotL d)))) := by
  rcases hd with rfl | rfl | rfl | rfl <;> decide

/-- At the root, a later edge points strictly between the child direction and an earlier
edge's direction. -/
theorem between_root_of_before_after {f d c c₀ y : Site} (hd : IsUnit d)
    {pre post : List (Site × Site)} (hfr : edgesFrom f d = pre ++ (f, c) :: post)
    (hc₀ : (f, c₀) ∈ pre) (hy : (f, y) ∈ post) :
    Between (dirIdx (c - f)) (dirIdx (c₀ - f)) (dirIdx (y - f)) := by
  rw [edgesFrom_eq] at hfr
  obtain ⟨h1, h2, h3, h4⟩ := between_root_dirs d hd
  rcases pre with _ | ⟨a₁, _ | ⟨a₂, _ | ⟨a₃, _ | ⟨a₄, pre'⟩⟩⟩⟩
  · simp at hc₀
  · simp only [List.cons_append, List.nil_append, List.cons.injEq, Prod.mk.injEq, true_and] at hfr
    obtain ⟨ha₁, hc, hpost⟩ := hfr
    subst hpost ha₁
    simp only [List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq, true_and] at hy hc₀
    subst hc₀
    rcases hy with rfl | rfl <;> rw [← hc] <;> simp only [add_sub_cancel_left]
    · exact h1
    · exact h2
  · simp only [List.cons_append, List.nil_append, List.cons.injEq, Prod.mk.injEq, true_and] at hfr
    obtain ⟨ha₁, ha₂, hc, hpost⟩ := hfr
    subst hpost ha₁ ha₂
    simp only [List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq, true_and] at hy hc₀
    subst hy
    rw [← hc]
    rcases hc₀ with rfl | rfl <;> simp only [add_sub_cancel_left]
    · exact h3
    · exact h4
  · simp only [List.cons_append, List.nil_append, List.cons.injEq, Prod.mk.injEq, true_and] at hfr
    obtain ⟨-, -, -, -, hpost⟩ := hfr
    subst hpost
    simp at hy
  · simp only [List.cons_append, List.cons.injEq] at hfr
    have := congrArg List.length hfr.2.2.2.2
    simp only [List.length_nil, List.length_append, List.length_cons] at this
    omega

end LatticeProb.Lattice.Planar
