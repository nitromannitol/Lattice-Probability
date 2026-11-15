import LatticeProb.Analysis.WedgeArcSineCore
import LatticeProb.Analysis.WedgeArcSineComplete

/-! # Symmetry and density of the finite sine core -/

set_option autoImplicit false

open MeasureTheory Set
open scoped ComplexConjugate

namespace LatticeProb

/-- A diagonal operator with real eigenvalues on an orthonormal span is symmetric. -/
theorem orthonormalDiagonalCore_symmetric {ι : Type*} {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    {v : ι → E} (hv : Orthonormal ℂ v) (eig : ι → ℝ)
    (x y : Submodule.span ℂ (Set.range v)) :
    inner ℂ (orthonormalDiagonalCore hv eig x) y =
      inner ℂ (x : E) (orthonormalDiagonalCore hv eig y) := by
  classical
  obtain ⟨x, hx⟩ := x
  obtain ⟨y, hy⟩ := y
  induction hx, hy using Submodule.span_induction₂ with
  | mem_mem a b ha hb =>
    obtain ⟨i, rfl⟩ := ha
    obtain ⟨j, rfl⟩ := hb
    rw [orthonormalDiagonalCore_apply_mode, orthonormalDiagonalCore_apply_mode]
    simp only [inner_smul_left, inner_smul_right, Complex.conj_ofReal,
      orthonormal_iff_ite.mp hv]
    split_ifs <;> simp_all
  | zero_left y hy =>
    change inner ℂ (orthonormalDiagonalCore hv eig 0) y =
      inner ℂ (0 : E) (orthonormalDiagonalCore hv eig ⟨y, hy⟩)
    simp
  | zero_right x hx =>
    change inner ℂ (orthonormalDiagonalCore hv eig ⟨x, hx⟩) (0 : E) =
      inner ℂ x (orthonormalDiagonalCore hv eig 0)
    simp
  | add_left a b c ha hb hc ih₁ ih₂ =>
    change inner ℂ (orthonormalDiagonalCore hv eig (⟨a, ha⟩ + ⟨b, hb⟩)) c =
      inner ℂ (a + b) (orthonormalDiagonalCore hv eig ⟨c, hc⟩)
    simp only [map_add, inner_add_left, ih₁, ih₂]
  | add_right a b c ha hb hc ih₁ ih₂ =>
    change inner ℂ (orthonormalDiagonalCore hv eig ⟨a, ha⟩) (b + c) =
      inner ℂ a (orthonormalDiagonalCore hv eig (⟨b, hb⟩ + ⟨c, hc⟩))
    simp only [map_add, inner_add_right, ih₁, ih₂]
  | smul_left r a b ha hb ih =>
    change inner ℂ (orthonormalDiagonalCore hv eig (r • ⟨a, ha⟩)) b =
      inner ℂ (r • a) (orthonormalDiagonalCore hv eig ⟨b, hb⟩)
    simp only [map_smul, inner_smul_left, ih]
  | smul_right r a b ha hb ih =>
    change inner ℂ (orthonormalDiagonalCore hv eig ⟨a, ha⟩) (r • b) =
      inner ℂ a (orthonormalDiagonalCore hv eig (r • ⟨b, hb⟩))
    simp only [map_smul, inner_smul_right, ih]

/-- The finite angular sine core is symmetric. -/
theorem wedgeArcSineCore_symmetric {θ : ℝ}
    (hθ : 0 < θ) (hθ' : θ ≤ 2 * Real.pi)
    (x y : Submodule.span ℂ (Set.range (wedgeArcSineLp θ))) :
    inner ℂ (wedgeArcSineCore hθ hθ' x) y =
      inner ℂ (x : Lp ℂ 2 (wedgeArcSurfaceMeasure θ)) (wedgeArcSineCore hθ hθ' y) :=
  orthonormalDiagonalCore_symmetric (orthonormal_wedgeArcSineLp hθ hθ') _ x y

/-- The finite angular sine span is dense in the arc Hilbert space. -/
theorem wedgeArcSineCore_dense {θ : ℝ}
    (hθ : 0 < θ) (hθ' : θ ≤ 2 * Real.pi) :
    (Submodule.span ℂ (Set.range (wedgeArcSineLp θ))).topologicalClosure = ⊤ :=
  Submodule.topologicalClosure_eq_top_iff.mpr (wedgeArcSineLp_orthogonal_eq_bot hθ hθ')

end LatticeProb
