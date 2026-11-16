import LatticeProb.Vendor.FormalMathPercolation.Literature.PlanarDuality
import LatticeProb.Vendor.FormalMathPercolation.Literature.RSWLemma

/-!
# Subdivision of rotated dual walks

The centers of rotated lattice faces and the midpoints of their connecting segments form
nearest-neighbor walks in the doubled lattice. Their support and coordinate bounds are given
in terms of the original walk.
-/

namespace Percolation.Literature

open SimpleGraph

noncomputable section

private abbrev V := LatticeModels.Site 2
private abbrev G := LatticeModels.zdGraph 2

/-- Doubled center of a face after the inverse exposure rotation. -/
def rotatedFaceCenter (n : ℕ) (f : V) : V := ![2 * (n : ℤ) - 2 * f 1 - 1, 2 * f 0 + 1]

/-- Doubled midpoint between two rotated face centers. -/
def rotatedFaceMidpoint (n : ℕ) (f g : V) : V :=
  ![2 * (n : ℤ) - f 1 - g 1 - 1, f 0 + g 0 + 1]

@[simp] theorem rotatedFaceMidpoint_comm (n : ℕ) (f g : V) :
    rotatedFaceMidpoint n f g = rotatedFaceMidpoint n g f := by
  ext i; fin_cases i <;> simp [rotatedFaceMidpoint] <;> omega

/-- The midpoint is the coordinatewise integer average of the centers. -/
theorem rotatedFaceMidpoint_eq_average (n : ℕ) (f g : V) :
    rotatedFaceMidpoint n f g = fun i => (rotatedFaceCenter n f i + rotatedFaceCenter n g i) / 2 := by
  ext i; fin_cases i <;> simp [rotatedFaceMidpoint, rotatedFaceCenter] <;> omega

private theorem adj_center_midpoint (n : ℕ) {f g : V} (h : G.Adj f g) :
    G.Adj (rotatedFaceCenter n f) (rotatedFaceMidpoint n f g) := by
  apply adj_of_stepKind
  rcases stepKind_of_adj h with ⟨h0, h1⟩ | ⟨h0, h1⟩ | ⟨h1, h0⟩ | ⟨h1, h0⟩
  · apply StepKind.up <;> simp only [rotatedFaceCenter, rotatedFaceMidpoint, Matrix.cons_val_zero, Matrix.cons_val_one] <;> omega
  · apply StepKind.down <;> simp only [rotatedFaceCenter, rotatedFaceMidpoint, Matrix.cons_val_zero, Matrix.cons_val_one] <;> omega
  · apply StepKind.left <;> simp only [rotatedFaceCenter, rotatedFaceMidpoint, Matrix.cons_val_zero, Matrix.cons_val_one] <;> omega
  · apply StepKind.right <;> simp only [rotatedFaceCenter, rotatedFaceMidpoint, Matrix.cons_val_zero, Matrix.cons_val_one] <;> omega

private theorem adj_midpoint_center (n : ℕ) {f g : V} (h : G.Adj f g) :
    G.Adj (rotatedFaceMidpoint n f g) (rotatedFaceCenter n g) := by
  simpa only [rotatedFaceMidpoint_comm] using (adj_center_midpoint n h.symm).symm

/-- Replace each dual step by two lattice steps through its rotated midpoint. -/
def subdivideRotatedDualWalk (n : ℕ) {a b : V} : G.Walk a b →
    G.Walk (rotatedFaceCenter n a) (rotatedFaceCenter n b)
  | .nil => .nil
  | .cons h p => .cons (adj_center_midpoint n h) (.cons (adj_midpoint_center n h)
      (subdivideRotatedDualWalk n p))

/-- The support consists exactly of face centers and midpoints of edges of the original walk. -/
theorem mem_support_subdivideRotatedDualWalk (n : ℕ) {a b z : V} (p : G.Walk a b) :
    z ∈ (subdivideRotatedDualWalk n p).support ↔
      (∃ x ∈ p.support, z = rotatedFaceCenter n x) ∨
        ∃ x y, s(x, y) ∈ p.edges ∧ z = rotatedFaceMidpoint n x y := by
  induction p with
  | nil => simp [subdivideRotatedDualWalk]
  | @cons x y b h p ih =>
    simp only [subdivideRotatedDualWalk, Walk.support_cons, Walk.edges_cons, List.mem_cons, ih]
    constructor
    · rintro (hz | hz | ⟨v, hv, hz⟩ | ⟨v, w, he, hz⟩)
      · exact Or.inl ⟨x, Or.inl rfl, hz⟩
      · exact Or.inr ⟨x, y, Or.inl rfl, hz⟩
      · exact Or.inl ⟨v, Or.inr hv, hz⟩
      · exact Or.inr ⟨v, w, Or.inr he, hz⟩
    · rintro (⟨v, hv | hv, hz⟩ | ⟨v, w, he | he, hz⟩)
      · subst v; exact Or.inl hz
      · exact Or.inr (Or.inr (Or.inl ⟨v, hv, hz⟩))
      · rcases Sym2.eq_iff.mp he with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · exact Or.inr (Or.inl hz)
        · exact Or.inr (Or.inl (by simpa only [rotatedFaceMidpoint_comm] using hz))
      · exact Or.inr (Or.inr (Or.inr ⟨v, w, he, hz⟩))

/-- Bounds on the two coordinates of the rotated, subdivided walk. -/
theorem subdivideRotatedDualWalk_bounds (n : ℕ) {a b : V} (p : G.Walk a b)
    (h : ∀ x ∈ p.support, 0 ≤ x 0 ∧ x 0 ≤ (n : ℤ) - 1 ∧
      -1 ≤ x 1 ∧ x 1 ≤ (n : ℤ) - 1) :
    ∀ z ∈ (subdivideRotatedDualWalk n p).support,
      1 ≤ z 0 ∧ z 0 ≤ 2 * (n : ℤ) + 1 ∧ 1 ≤ z 1 ∧ z 1 ≤ 2 * (n : ℤ) - 1 := by
  intro z hz
  rcases (mem_support_subdivideRotatedDualWalk n p).mp hz with ⟨x, hx, rfl⟩ | ⟨x, y, he, rfl⟩
  · have hx' := h x hx
    simp only [rotatedFaceCenter, Matrix.cons_val_zero, Matrix.cons_val_one]
    omega
  · have hx := h x (p.fst_mem_support_of_mem_edges he)
    have hy := h y (p.snd_mem_support_of_mem_edges he)
    simp only [rotatedFaceMidpoint, Matrix.cons_val_zero, Matrix.cons_val_one]
    omega

/-- Rectangle containment and exclusion of the top side provide the walk bounds. -/
theorem subdivideRotatedDualWalk_bounds_of_region (n : ℕ) {a b : V} (p : G.Walk a b)
    (D : Finset V) (hD : D ⊆ dualRectangle n n)
    (htop : ∀ x ∈ dualTopSide n n, x ∉ D)
    (hp : ∀ x ∈ p.support, x ∈ D) :
    ∀ z ∈ (subdivideRotatedDualWalk n p).support,
      1 ≤ z 0 ∧ z 0 ≤ 2 * (n : ℤ) + 1 ∧ 1 ≤ z 1 ∧ z 1 ≤ 2 * (n : ℤ) - 1 := by
  apply subdivideRotatedDualWalk_bounds
  intro x hx
  have hxD := hp x hx
  have hr := mem_dualRectangle_iff.mp (hD hxD)
  have hn : x 1 ≠ (n : ℤ) := by
    intro heq
    have ht : x ∈ dualTopSide n n := by
      simp [dualTopSide, hD hxD, heq]
    exact htop x ht hxD
  omega

/-- The physical lower-left corner is the inverse image of the rotated upper-left corner. -/
theorem rotatedFace_lowerLeft (n : ℕ) (f : V) :
    ((reflX n).trans transposeIso).symm ![f 0, f 1 + 1] =
      ![(n : ℤ) - f 1 - 1, f 0] := by
  rw [RelIso.symm_apply_eq, LatticeModels.Site.eq_iff_two]
  simp only [RelIso.trans_apply, transposeIso_apply_zero, transposeIso_apply_one,
    reflX_apply_zero, reflX_apply_one, Matrix.cons_val_zero, Matrix.cons_val_one]
  constructor
  · trivial
  · omega

/-- The rotated center is the doubled physical lower-left corner plus `(1, 1)`. -/
theorem rotatedFaceCenter_eq_lowerLeft (n : ℕ) (f : V) :
    rotatedFaceCenter n f = ![2 * ((n : ℤ) - f 1 - 1) + 1, 2 * f 0 + 1] := by
  ext i; fin_cases i <;> simp [rotatedFaceCenter]; omega

/-- Coordinates of a physical corner whose image under the exposure rotation is a corner of `f`. -/
theorem rotatedFace_corner_coordinates (n : ℕ) (f v : V)
    (h₀ : ((reflX n).trans transposeIso) v 0 = f 0 ∨
      ((reflX n).trans transposeIso) v 0 = f 0 + 1)
    (h₁ : ((reflX n).trans transposeIso) v 1 = f 1 ∨
      ((reflX n).trans transposeIso) v 1 = f 1 + 1) :
    (v 0 = (n : ℤ) - f 1 - 1 ∨ v 0 = (n : ℤ) - f 1) ∧
      (v 1 = f 0 ∨ v 1 = f 0 + 1) := by
  simp only [RelIso.trans_apply, transposeIso_apply_zero, transposeIso_apply_one,
    reflX_apply_zero, reflX_apply_one] at h₀ h₁
  omega

/-- The horizontal-side midpoint joining a physical face corner to its center. -/
def rotatedFaceCornerMidpoint (n : ℕ) (f v : V) : V :=
  ![2 * ((n : ℤ) - f 1 - 1) + 1, 2 * v 1]

private theorem adj_corner_midpoint (n : ℕ) (f v : V)
    (hx : v 0 = (n : ℤ) - f 1 - 1 ∨ v 0 = (n : ℤ) - f 1) :
    G.Adj (v + v) (rotatedFaceCornerMidpoint n f v) := by
  apply adj_of_stepKind
  rcases hx with hx | hx
  · apply StepKind.right <;> simp only [rotatedFaceCornerMidpoint, Pi.add_apply,
      Matrix.cons_val_zero, Matrix.cons_val_one] <;> omega
  · apply StepKind.left <;> simp only [rotatedFaceCornerMidpoint, Pi.add_apply,
      Matrix.cons_val_zero, Matrix.cons_val_one] <;> omega

private theorem adj_cornerMidpoint_center (n : ℕ) (f v : V)
    (hy : v 1 = f 0 ∨ v 1 = f 0 + 1) :
    G.Adj (rotatedFaceCornerMidpoint n f v) (rotatedFaceCenter n f) := by
  apply adj_of_stepKind
  rcases hy with hy | hy
  · apply StepKind.up <;> simp only [rotatedFaceCornerMidpoint, rotatedFaceCenter,
      Matrix.cons_val_zero, Matrix.cons_val_one] <;> omega
  · apply StepKind.down <;> simp only [rotatedFaceCornerMidpoint, rotatedFaceCenter,
      Matrix.cons_val_zero, Matrix.cons_val_one] <;> omega

/-- The two-step connection from a physical corner to the rotated face center. -/
def rotatedFaceCornerWalk (n : ℕ) (f v : V)
    (hx : v 0 = (n : ℤ) - f 1 - 1 ∨ v 0 = (n : ℤ) - f 1)
    (hy : v 1 = f 0 ∨ v 1 = f 0 + 1) :
    G.Walk (v + v) (rotatedFaceCenter n f) :=
  .cons (adj_corner_midpoint n f v hx) (.cons (adj_cornerMidpoint_center n f v hy) .nil)

/-- The corner connection has exactly the displayed three vertices in its support. -/
theorem mem_support_rotatedFaceCornerWalk (n : ℕ) (f v z : V)
    (hx : v 0 = (n : ℤ) - f 1 - 1 ∨ v 0 = (n : ℤ) - f 1)
    (hy : v 1 = f 0 ∨ v 1 = f 0 + 1) :
    z ∈ (rotatedFaceCornerWalk n f v hx hy).support ↔
      z = v + v ∨ z = rotatedFaceCornerMidpoint n f v ∨ z = rotatedFaceCenter n f := by
  simp [rotatedFaceCornerWalk]

/-- The center of a bottom-side face lies in the right strip. -/
theorem rotatedFaceCenter_of_mem_dualBottomSide (n : ℕ) {b : V}
    (hb : b ∈ dualBottomSide n n) :
    rotatedFaceCenter n b = ![2 * (n : ℤ) + 1, 2 * b 0 + 1] ∧
      0 ≤ b 0 ∧ b 0 ≤ (n : ℤ) - 1 := by
  simp only [dualBottomSide, Finset.mem_filter, mem_dualRectangle_iff] at hb
  refine ⟨?_, hb.1.1, hb.1.2.1⟩
  ext i; fin_cases i <;> simp [rotatedFaceCenter, hb.2]; omega

/-- A rotated face center cannot coincide with a doubled lattice vertex. -/
theorem rotatedFaceCenter_ne_double (n : ℕ) (f v : V) :
    rotatedFaceCenter n f ≠ v + v := by
  intro h
  have h0 := congrFun h 0
  simp only [rotatedFaceCenter, Matrix.cons_val_zero, Pi.add_apply] at h0
  omega

/-- A rotated face center cannot coincide with the midpoint of a lattice edge. -/
theorem rotatedFaceCenter_ne_edgeMidpoint (n : ℕ) (f x y : V) (hxy : G.Adj x y) :
    rotatedFaceCenter n f ≠ x + y := by
  intro h
  have h0 := congrFun h 0
  have h1 := congrFun h 1
  simp only [rotatedFaceCenter, Matrix.cons_val_zero, Matrix.cons_val_one, Pi.add_apply] at h0 h1
  rcases stepKind_of_adj hxy with ⟨hx, hy⟩ | ⟨hx, hy⟩ | ⟨hy, hx⟩ | ⟨hy, hx⟩ <;> omega

/-- The corner midpoint is the sum of the endpoints of its horizontal face side. -/
theorem rotatedFaceCornerMidpoint_eq_edgeMidpoint (n : ℕ) (f v : V)
    (hx : v 0 = (n : ℤ) - f 1 - 1 ∨ v 0 = (n : ℤ) - f 1) :
    ∃ w : V, G.Adj v w ∧ w 1 = v 1 ∧
      (w 0 = (n : ℤ) - f 1 - 1 ∨ w 0 = (n : ℤ) - f 1) ∧
      rotatedFaceCornerMidpoint n f v = v + w := by
  let w : V := ![2 * ((n : ℤ) - f 1 - 1) + 1 - v 0, v 1]
  refine ⟨w, ?_, ?_, ?_, ?_⟩
  · apply adj_of_stepKind
    rcases hx with hx | hx
    · apply StepKind.right <;> simp only [w, Matrix.cons_val_zero, Matrix.cons_val_one]; omega
    · apply StepKind.left <;> simp only [w, Matrix.cons_val_zero, Matrix.cons_val_one]; omega
  · simp [w]
  · simp only [w, Matrix.cons_val_zero]
    omega
  · ext i; fin_cases i <;> simp [rotatedFaceCornerMidpoint, w, Pi.add_apply]; omega

/-- The final point just beyond the right strip. -/
def rotatedDualEndpoint (n : ℕ) (b : V) : V := ![2 * (n : ℤ) + 2, 2 * b 0 + 1]

/-- A bottom-side face center is adjacent to the right-strip endpoint. -/
theorem adj_rotatedFaceCenter_endpoint (n : ℕ) {b : V}
    (hb : b ∈ dualBottomSide n n) :
    G.Adj (rotatedFaceCenter n b) (rotatedDualEndpoint n b) := by
  have h := (rotatedFaceCenter_of_mem_dualBottomSide n hb).1
  apply adj_of_stepKind
  apply StepKind.right <;> simp only [h, rotatedDualEndpoint, Matrix.cons_val_zero,
    Matrix.cons_val_one]; omega

/-- Bounds on the center and endpoint arising from bottom-side membership. -/
theorem rotatedDualEndpoint_bounds (n : ℕ) {b : V} (hb : b ∈ dualBottomSide n n) :
    2 * (n : ℤ) < rotatedFaceCenter n b 0 ∧
    2 * (n : ℤ) < rotatedDualEndpoint n b 0 ∧
    1 ≤ rotatedFaceCenter n b 1 ∧ rotatedFaceCenter n b 1 ≤ 2 * (n : ℤ) - 1 ∧
    1 ≤ rotatedDualEndpoint n b 1 ∧ rotatedDualEndpoint n b 1 ≤ 2 * (n : ℤ) - 1 := by
  have ⟨hc, hb0, hb1⟩ := rotatedFaceCenter_of_mem_dualBottomSide n hb
  simp only [hc, rotatedDualEndpoint, Matrix.cons_val_zero, Matrix.cons_val_one]
  omega

end
end Percolation.Literature
