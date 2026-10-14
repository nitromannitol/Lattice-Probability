/-
# Euclidean frames and finite polygonal edge traces

A unit direction supplies forward and transverse coordinates. A finite family of
nonzero edge vectors admits a direction parallel to none of them, by excluding
finitely many slopes and normalizing the vector `(1, a)`. The edge trace is the
literal union of closed affine segments. These facts support half-open ray
crossing parity without assuming general position of a query point.

Adapted from Álvaro Begué's Schoenflies plane, direction and subdivision modules.
-/
/-
Copyright (c) 2026 Álvaro Begué. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Álvaro Begué
-/
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Convex.Topology
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring



open Metric Set
namespace LatticeProb.Topology.PolygonalParity
/-- The plane. -/
abbrev Plane := EuclideanSpace ℝ (Fin 2)

namespace Plane

/-- Build a point of the plane from its two coordinates. -/
abbrev mk (x y : ℝ) : Plane := !₂[x, y]

/-- The first coordinate of `mk x y` is `x`. -/
@[simp] theorem mk_zero (x y : ℝ) : mk x y 0 = x := rfl
/-- The second coordinate of `mk x y` is `y`. -/
@[simp] theorem mk_one (x y : ℝ) : mk x y 1 = y := rfl

/-! ### The orientation form and the right-angle rotation -/

/-- The orientation form `det (a, b) = a₁b₂ - a₂b₁`. It is positive exactly when `b` lies
counterclockwise of `a`. -/
def det (a b : Plane) : ℝ := a 0 * b 1 - a 1 * b 0

/-- `u` turned counterclockwise through a right angle. -/
def perp (u : Plane) : Plane := mk (-u 1) (u 0)

/-- The first coordinate of the quarter turn is the negative second coordinate. -/
@[simp] theorem perp_zero (u : Plane) : perp u 0 = -u 1 := rfl
/-- The second coordinate of the quarter turn is the first coordinate. -/
@[simp] theorem perp_one (u : Plane) : perp u 1 = u 0 := rfl

/-- The determinant of a vector with itself is zero. -/
@[simp] theorem det_self (a : Plane) : det a a = 0 := by simp [det]; ring

/-- Exchanging determinant arguments reverses its sign. -/
theorem det_comm (a b : Plane) : det a b = -det b a := by simp [det]; ring

/-- Scaling the first argument scales the determinant by the same scalar. -/
@[simp] theorem det_smul_left (r : ℝ) (a b : Plane) : det (r • a) b = r * det a b := by
  simp [det]; ring

/-- Scaling the second argument scales the determinant by the same scalar. -/
@[simp] theorem det_smul_right (r : ℝ) (a b : Plane) : det a (r • b) = r * det a b := by
  simp [det]; ring

/-- The determinant is additive in its first argument. -/
theorem det_add_left (a b c : Plane) : det (a + b) c = det a c + det b c := by
  simp [det]; ring

/-- The determinant is additive in its second argument. -/
theorem det_add_right (a b c : Plane) : det a (b + c) = det a b + det a c := by
  simp [det]; ring

/-- The defining property of `perp`: it is the counterclockwise right-angle rotation, so it
pairs positively with its argument. -/
@[simp] theorem det_perp_self (u : Plane) : det u (perp u) = ‖u‖ ^ 2 := by
  rw [EuclideanSpace.real_norm_sq_eq]
  simp [det, Fin.sum_univ_two]
  ring

/-- The real inner product is the sum of the two coordinate products. -/
theorem inner_eq (u v : Plane) : inner ℝ u v = u 0 * v 0 + u 1 * v 1 := by
  simp [PiLp.inner_apply, Fin.sum_univ_two, mul_comm]

/-- Turning twice reverses. -/
@[simp] theorem perp_perp (u : Plane) : perp (perp u) = -u := by
  ext i; fin_cases i <;> simp

/-- A vector is orthogonal to its quarter turn. -/
@[simp] theorem inner_perp_self (u : Plane) : inner ℝ u (perp u) = 0 := by
  rw [inner_eq]; simp; ring

/-- Against `perp` on the right, `det` becomes the inner product. Together with
`det_perp_left` this is what lets the strip lemma trade one for the other. -/
@[simp] theorem det_perp_right (u v : Plane) : det u (perp v) = inner ℝ u v := by
  rw [inner_eq]; simp [det]

/-- A quarter turn in the first determinant argument gives the negative inner product. -/
@[simp] theorem det_perp_left (u v : Plane) : det (perp u) v = -inner ℝ u v := by
  rw [inner_eq]; simp [det]; ring

/-- A simultaneous quarter turn preserves the determinant. -/
@[simp] theorem det_perp_perp (u v : Plane) : det (perp u) (perp v) = det u v := by
  simp [det]; ring

/-- A quarter turn preserves the Euclidean norm. -/
@[simp] theorem norm_perp (u : Plane) : ‖perp u‖ = ‖u‖ := by
  rw [EuclideanSpace.norm_eq, EuclideanSpace.norm_eq]
  congr 1
  simp [Fin.sum_univ_two, sq_abs]
  ring

variable {u : Plane}

/-- A *direction* is a unit vector. Only the ray a direction spans ever matters below, but
normalising to unit length gives a canonical representative of that ray. -/
def IsDirection (u : Plane) : Prop := ‖u‖ = 1

/-- A unit direction is nonzero. -/
theorem IsDirection.ne_zero (hu : IsDirection u) : u ≠ 0 := by
  intro h
  rw [IsDirection, h, norm_zero] at hu
  exact zero_ne_one hu

/-- A unit direction has norm one. -/
theorem IsDirection.norm (hu : IsDirection u) : ‖u‖ = 1 := hu

/-- Normalize a vector by its Euclidean norm. At zero the value is zero;
`isDirection_dir` requires a nonzero input for the unit-direction conclusion. -/
noncomputable def dir (u : Plane) : Plane := ‖u‖⁻¹ • u

/-- Normalizing a nonzero vector yields a unit direction. -/
theorem isDirection_dir (hu : u ≠ 0) : IsDirection (dir u) := by
  have hpos : 0 < ‖u‖ := norm_pos_iff.2 hu
  rw [IsDirection, dir, norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hpos,
    inv_mul_cancel₀ hpos.ne']

/-- The direction of a nonzero vector is nonzero. -/
theorem dir_ne_zero (hu : u ≠ 0) : dir u ≠ 0 := (isDirection_dir hu).ne_zero

/-- `dir u` is a positive multiple of `u`, which is why every sign-of-`det` predicate is blind
to the difference. -/
theorem dir_eq_smul (hu : u ≠ 0) : ∃ c : ℝ, 0 < c ∧ dir u = c • u :=
  ⟨‖u‖⁻¹, inv_pos.2 (norm_pos_iff.2 hu), rfl⟩

/-- The family used to dodge finitely many directions. -/
private theorem mk_one_ne_zero (a : ℝ) : mk 1 a ≠ 0 := by
  intro h
  have h0 : mk 1 a 0 = (0 : Plane) 0 := by rw [h]
  simp at h0

private theorem det_mk_one (a : ℝ) (v : Plane) : det (mk 1 a) v = v 1 - a * v 0 := by
  simp [det]

/-- **Finite generic direction.** A finite family of nonzero vectors admits a
unit vector parallel to none of them. Only finitely many slopes are excluded. -/
theorem exists_isDirection_det_ne_zero {S : Set Plane} (hS : S.Finite) :
    ∃ u : Plane, IsDirection u ∧ ∀ v ∈ S, v ≠ 0 → det u v ≠ 0 := by
  -- The parameters ruled out by `S` are the slopes of its members, hence at most as many as `S`.
  have hbad : {a : ℝ | ∃ v ∈ S, v ≠ 0 ∧ det (mk 1 a) v = 0}.Finite := by
    refine Set.Finite.subset (hS.image fun v => v 1 / v 0) ?_
    rintro a ⟨v, hv, hv0, hdet⟩
    rw [det_mk_one] at hdet
    have h0 : v 0 ≠ 0 := by
      intro h
      refine hv0 ?_
      have h1 : v 1 = 0 := by rw [h] at hdet; linarith
      ext i
      fin_cases i <;> simp [h, h1]
    exact ⟨v, hv, by field_simp; linarith⟩
  obtain ⟨a, ha⟩ := hbad.infinite_compl.nonempty
  refine ⟨dir (mk 1 a), isDirection_dir (mk_one_ne_zero a),
    fun v hv hv0 hdet => ha ⟨v, hv, hv0, ?_⟩⟩
  -- `dir` only rescales, so it cannot create a vanishing orientation form.
  obtain ⟨c, hc, hcd⟩ := dir_eq_smul (mk_one_ne_zero a)
  rw [hcd, det_smul_left] at hdet
  rcases mul_eq_zero.1 hdet with h | h
  · exact absurd h hc.ne'
  · exact h


end Plane
/-- A polygonal edge is its pair of endpoints. -/
abbrev Piece := Plane × Plane

namespace Piece

/-- The closed segment a piece occupies. -/
def seg (P : Piece) : Set Plane := segment ℝ P.1 P.2

/-- The interior of a piece. -/
def interior (P : Piece) : Set Plane := openSegment ℝ P.1 P.2

/-- A piece is nondegenerate when its two ends differ. -/
def Nondeg (P : Piece) : Prop := P.1 ≠ P.2

end Piece

/-- What a list of pieces occupies. -/
def cover (pieces : List Piece) : Set Plane := ⋃ P ∈ pieces, P.seg

/-- The empty edge list has empty trace. -/
@[simp] theorem cover_nil : cover [] = ∅ := by simp [cover]

/-- Adding an edge adds its closed segment to the trace. -/
@[simp] theorem cover_cons (P : Piece) (ps : List Piece) :
    cover (P :: ps) = P.seg ∪ cover ps := by
  simp [cover]

/-- Concatenating edge lists unions their traces. -/
theorem cover_append (ps qs : List Piece) : cover (ps ++ qs) = cover ps ∪ cover qs := by
  induction ps with
  | nil => simp
  | cons P ps ih => rw [List.cons_append, cover_cons, cover_cons, ih, union_assoc]

end LatticeProb.Topology.PolygonalParity
