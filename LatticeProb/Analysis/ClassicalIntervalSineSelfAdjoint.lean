import LatticeProb.Analysis.ClassicalIntervalSineAdjointGraph

/-! # Self-adjointness of diagonal Hilbert-basis operators -/

set_option autoImplicit false

open MeasureTheory Set

namespace LatticeProb

/-- The adjoint of a real diagonal operator on the finite span of a Hilbert
basis is self-adjoint. -/
theorem hilbertBasis_diagonal_adjoint_isSelfAdjoint {ι E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    (b : HilbertBasis ι ℂ E) (eig : ι → ℝ) :
    IsSelfAdjoint (show E →ₗ.[ℂ] E from
      ⟨_, orthonormalDiagonalCore b.orthonormal eig⟩).adjoint := by
  let T : E →ₗ.[ℂ] E := ⟨_, orthonormalDiagonalCore b.orthonormal eig⟩
  let A := T.adjoint
  have hgraph : A.graph = T.graph.topologicalClosure :=
    hilbertBasis_diagonal_adjoint_graph_eq_closure b eig
  have hcore : T.graph ≤ A.graph := by
    rw [hgraph]
    exact Submodule.le_topologicalClosure T.graph
  have htd : Dense (T.domain : Set E) := by
    apply Submodule.dense_iff_topologicalClosure_eq_top.mpr
    exact b.dense_span
  have hd : Dense (A.domain : Set E) := by
    apply htd.mono
    intro x hx
    have hg := hcore (LinearPMap.mem_graph T ⟨x, hx⟩)
    obtain ⟨z, hz, _⟩ := (LinearPMap.mem_graph_iff A).mp hg
    change (z : E) = x at hz
    rw [← hz]
    exact z.property
  have hsymm : ∀ p ∈ A.graph, ∀ q ∈ A.graph,
      inner ℂ p.1 q.2 = inner ℂ p.2 q.1 := by
    intro p hp q hq
    have hp' : ∀ v : T.domain, inner ℂ (v : E) p.2 = inner ℂ (T v) p.1 := by
      have hp'' : p ∈ T.graph.adjoint := by
        rw [← LinearPMap.adjoint_graph_eq_graph_adjoint htd]
        exact hp
      intro v
      exact (sub_eq_zero.mp ((Submodule.mem_adjoint_iff _ _).mp hp''
        (v : E) (T v) (LinearPMap.mem_graph T v))).symm
    have hclosed : IsClosed {r : E × E | inner ℂ p.1 r.2 = inner ℂ p.2 r.1} :=
      isClosed_eq (by fun_prop) (by fun_prop)
    have hsub : (T.graph : Set (E × E)) ⊆
        {r | inner ℂ p.1 r.2 = inner ℂ p.2 r.1} := by
      intro r hr
      obtain ⟨v, hv, hw⟩ := (LinearPMap.mem_graph_iff T).mp hr
      change inner ℂ p.1 r.2 = inner ℂ p.2 r.1
      rw [← hv, ← hw]
      have hh := hp' v
      rw [← inner_conj_symm p.1 (T v),
        ← inner_conj_symm p.2 (v : E), hh]
    apply closure_minimal hsub hclosed
    rw [hgraph] at hq
    exact hq
  change IsSelfAdjoint A
  rw [LinearPMap.isSelfAdjoint_def]
  apply LinearPMap.eq_of_eq_graph
  rw [LinearPMap.adjoint_graph_eq_graph_adjoint hd]
  ext p
  rw [Submodule.mem_adjoint_iff]
  constructor
  · intro hp
    rw [hgraph]
    apply (hilbertBasis_diagonal_graph_closure_iff b eig p.1 p.2).2
    intro n
    let v : T.domain := ⟨b n, Submodule.subset_span ⟨n, rfl⟩⟩
    have hh := hp (v : E) (T v) (hcore (LinearPMap.mem_graph T v))
    change inner ℂ (orthonormalDiagonalCore b.orthonormal eig v) p.1 -
      inner ℂ (b n) p.2 = 0 at hh
    rw [orthonormalDiagonalCore_apply_mode, inner_smul_left, Complex.conj_ofReal] at hh
    exact (sub_eq_zero.mp hh).symm
  · intro hp a c hac
    exact sub_eq_zero.mpr (hsymm (a, c) hac p hp).symm

/-- The adjoint of the finite sine core on a nonempty interval is self-adjoint. -/
theorem intervalSine_adjoint_isSelfAdjoint {a b : ℝ} (hab : a < b) :
    IsSelfAdjoint (show (Lp ℂ 2 (volume.restrict (Ioo a b))) →ₗ.[ℂ]
      (Lp ℂ 2 (volume.restrict (Ioo a b))) from
      ⟨_, orthonormalDiagonalCore (intervalSineHilbertBasis hab).orthonormal
        (fun n => (Real.pi * (n + 1 : ℕ) / (b - a)) ^ 2)⟩).adjoint :=
  hilbertBasis_diagonal_adjoint_isSelfAdjoint (intervalSineHilbertBasis hab) _

end LatticeProb
