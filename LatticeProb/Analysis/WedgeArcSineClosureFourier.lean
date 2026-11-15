import LatticeProb.Analysis.WedgeArcSineCoreClosure

/-! # Fourier characterization of the closed sine core -/

set_option autoImplicit false

open MeasureTheory Set Filter
open scoped Topology

namespace LatticeProb

/-- The graph closure of a real diagonal operator on a Hilbert basis is
characterized by the coefficient equations. -/
theorem hilbertBasis_diagonal_graph_closure_iff {ι E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    (b : HilbertBasis ι ℂ E) (eig : ι → ℝ) (x y : E) :
    (x, y) ∈ (show E →ₗ.[ℂ] E from
      ⟨_, orthonormalDiagonalCore b.orthonormal eig⟩).graph.topologicalClosure ↔
      ∀ n, inner ℂ (b n) y = (eig n : ℂ) * inner ℂ (b n) x := by
  classical
  let T : E →ₗ.[ℂ] E := ⟨_, orthonormalDiagonalCore b.orthonormal eig⟩
  change (x, y) ∈ T.graph.topologicalClosure ↔ _
  constructor
  · intro h n
    have hclosed : IsClosed {p : E × E |
        inner ℂ (b n) p.2 = (eig n : ℂ) * inner ℂ (b n) p.1} :=
      isClosed_eq (by fun_prop) (by fun_prop)
    have hsub : (T.graph : Set (E × E)) ⊆
        {p : E × E | inner ℂ (b n) p.2 = (eig n : ℂ) * inner ℂ (b n) p.1} := by
      intro p hp
      obtain ⟨u, hu, hv⟩ := (LinearPMap.mem_graph_iff T).mp hp
      change inner ℂ (b n) p.2 = (eig n : ℂ) * inner ℂ (b n) p.1
      rw [← hu, ← hv]
      have hs := orthonormalDiagonalCore_symmetric b.orthonormal eig
        ⟨b n, Submodule.subset_span ⟨n, rfl⟩⟩ u
      rw [orthonormalDiagonalCore_apply_mode, inner_smul_left] at hs
      change inner ℂ (b n) (orthonormalDiagonalCore b.orthonormal eig u) = _
      simpa only [Complex.conj_ofReal] using hs.symm
    exact closure_minimal hsub hclosed h
  · intro h
    let u : Finset ι → T.domain := fun s =>
      ∑ n ∈ s, (b.repr x n) • ⟨b n, Submodule.subset_span ⟨n, rfl⟩⟩
    have hu : Tendsto (fun s : Finset ι => ((u s : T.domain) : E)) atTop (𝓝 x) := by
      simp only [u, Submodule.coe_sum, Submodule.coe_smul]
      exact b.hasSum_repr x
    have hv : Tendsto (fun s : Finset ι => T (u s)) atTop (𝓝 y) := by
      have heq : (fun s : Finset ι => T (u s)) =
          (fun s : Finset ι => ∑ n ∈ s, b.repr y n • b n) := by
        funext s
        change orthonormalDiagonalCore b.orthonormal eig
          (∑ n ∈ s, (b.repr x n) • ⟨b n, Submodule.subset_span ⟨n, rfl⟩⟩) = _
        simp only [map_sum, map_smul, orthonormalDiagonalCore_apply_mode]
        apply Finset.sum_congr rfl
        intro n hn
        rw [← smul_assoc, b.repr_apply_apply, b.repr_apply_apply, h n]
        simp only [smul_eq_mul, mul_comm]
      rw [heq]
      exact b.hasSum_repr y
    exact mem_closure_of_tendsto (hu.prodMk_nhds hv)
      (Filter.Eventually.of_forall fun s => LinearPMap.mem_graph T (u s))

end LatticeProb
