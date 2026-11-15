import LatticeProb.Analysis.ClassicalIntervalGradientCompositionGraphEquality
import Mathlib.Analysis.InnerProductSpace.LinearPMap

/-! # Adjoint of the finite interval sine operator -/

set_option autoImplicit false

open MeasureTheory Set

namespace LatticeProb

/-- The adjoint graph of a real diagonal operator on the finite span of a
Hilbert basis is the closure of its graph. -/
theorem hilbertBasis_diagonal_adjoint_graph_eq_closure {ι E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    (b : HilbertBasis ι ℂ E) (eig : ι → ℝ) :
    (show E →ₗ.[ℂ] E from ⟨_, orthonormalDiagonalCore b.orthonormal eig⟩).adjoint.graph =
      (show E →ₗ.[ℂ] E from ⟨_, orthonormalDiagonalCore b.orthonormal eig⟩).graph.topologicalClosure := by
  let T : E →ₗ.[ℂ] E := ⟨_, orthonormalDiagonalCore b.orthonormal eig⟩
  change T.adjoint.graph = T.graph.topologicalClosure
  have hd : Dense (T.domain : Set E) := by
    apply Submodule.dense_iff_topologicalClosure_eq_top.mpr
    exact b.dense_span
  rw [LinearPMap.adjoint_graph_eq_graph_adjoint hd]
  ext p
  rw [Submodule.mem_adjoint_iff, hilbertBasis_diagonal_graph_closure_iff b eig p.1 p.2]
  constructor
  · intro h n
    let v : T.domain := ⟨b n, Submodule.subset_span ⟨n, rfl⟩⟩
    have hv := h (b n) (T v) (LinearPMap.mem_graph T v)
    change inner ℂ (orthonormalDiagonalCore b.orthonormal eig v) p.1 -
      inner ℂ (b n) p.2 = 0 at hv
    rw [orthonormalDiagonalCore_apply_mode, inner_smul_left, Complex.conj_ofReal] at hv
    exact (sub_eq_zero.mp hv).symm
  · intro h a c hac
    obtain ⟨v, hv, hw⟩ := (LinearPMap.mem_graph_iff T).mp hac
    change (v : E) = a at hv
    change T v = c at hw
    rw [← hv, ← hw]
    have hclosed : IsClosed {q : E × E |
        inner ℂ (T v) q.1 = inner ℂ (v : E) q.2} :=
      isClosed_eq (by fun_prop) (by fun_prop)
    have hsub : (T.graph : Set (E × E)) ⊆
        {q | inner ℂ (T v) q.1 = inner ℂ (v : E) q.2} := by
      intro q hq
      obtain ⟨u, hu, hw⟩ := (LinearPMap.mem_graph_iff T).mp hq
      change inner ℂ (T v) q.1 = inner ℂ (v : E) q.2
      rw [← hu, ← hw]
      exact orthonormalDiagonalCore_symmetric b.orthonormal eig v u
    have hp := closure_minimal hsub hclosed
      ((hilbertBasis_diagonal_graph_closure_iff b eig p.1 p.2).2 h)
    exact sub_eq_zero.mpr hp

/-- On a nonempty interval the adjoint of the finite sine core has the graph
of the closed interval gradient followed by its adjoint. -/
theorem intervalSine_adjoint_graph_iff {a b : ℝ} (hab : a < b)
    (x y : Lp ℂ 2 (volume.restrict (Ioo a b))) :
    (x, y) ∈ (show (Lp ℂ 2 (volume.restrict (Ioo a b))) →ₗ.[ℂ]
      (Lp ℂ 2 (volume.restrict (Ioo a b))) from
      ⟨_, orthonormalDiagonalCore (intervalSineHilbertBasis hab).orthonormal
        (fun n => (Real.pi * (n + 1 : ℕ) / (b - a)) ^ 2)⟩).adjoint.graph ↔
    ∃ u : (classicalIntervalGradient a b).closure.domain,
      ∃ hu : (classicalIntervalGradient a b).closure u ∈
          (classicalIntervalGradient a b).closure.adjoint.domain,
        ((u : Lp ℂ 2 (volume.restrict (Ioo a b))),
          (classicalIntervalGradient a b).closure.adjoint ⟨_, hu⟩) = (x, y) := by
  rw [hilbertBasis_diagonal_adjoint_graph_eq_closure]
  exact classicalIntervalGradient_sineGraph_closure_iff hab x y

end LatticeProb
