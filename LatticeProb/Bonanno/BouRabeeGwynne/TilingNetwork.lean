/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module BouRabeeGwynne.TilingNetwork at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.BouRabeeGwynne.DiscretePDE
import LatticeProb.Bonanno.BouRabeeGwynne.FiniteDirichlet

open scoped BigOperators Classical

namespace BouRabeeGwynne
namespace OrthogonalTiling

variable {d : ℕ} (T : OrthogonalTiling d)

/-- Restriction of the canonical tiling conductances to a finite vertex region. -/
noncomputable def finiteNetwork (R : Set T.V) [Fintype R] :
    FiniteConductanceNetwork R where
  a v w := T.conductanceReal v w
  symm v w := T.conductanceReal_symm v w
  nonneg v w := T.conductanceReal_nonneg v w
  loop_zero v := T.conductanceReal_self v

/-- The finite-network sum is the paper's neighbor sum whenever all neighbors of
the vertex belong to the restricted region. No edge is discarded at that vertex. -/
theorem finiteNetwork_laplacian (R : Set T.V) [Fintype R] (f : T.V → ℝ)
    (v : R) (hv : (T.neighbors v).Finite) (hneighbors : T.neighbors v ⊆ R) :
    (T.finiteNetwork R).laplacian (fun w => f w) v = T.discreteLaplacian f v hv := by
  change (∑ w : R, T.conductanceReal v w * (f w - f v)) = _
  rw [Finset.sum_set_coe R (f := fun w : T.V =>
    T.conductanceReal v w * (f w - f v))]
  symm
  apply Finset.sum_subset
  · intro w hw
    exact Set.mem_toFinset.mpr (hneighbors (T.mem_neighborFinset hv |>.mp hw))
  · intro w _ hw
    have hnot : ¬ T.adj v w := fun h => hw ((T.mem_neighborFinset hv).mpr h)
    simp [conductanceReal, hnot]

/-- The interior predicate in the finite closed graph region. -/
def finiteInterior (U : Set (Euc d)) : Set (T.closedVertices U) :=
  {v | T.pos v ∈ U}

theorem closedNetwork_laplacian (U : Set (Euc d)) [Fintype (T.closedVertices U)]
    (f : T.V → ℝ) (v : T.closedVertices U) (hvU : v ∈ T.finiteInterior U)
    (hv : (T.neighbors v).Finite) :
    (T.finiteNetwork (T.closedVertices U)).laplacian (fun w => f w) v =
      T.discreteLaplacian f v hv :=
  T.finiteNetwork_laplacian _ f v hv
    (fun _ hw => T.neighbor_mem_closedVertices hvU hw)

lemma closedVertex_not_interior_iff (U : Set (Euc d)) (v : T.closedVertices U) :
    v ∉ T.finiteInterior U ↔ (v : T.V) ∈ T.boundaryVertices U := by
  constructor
  · intro hv
    exact v.property.resolve_left hv
  · intro hv
    exact hv.1

/-- Restricting a tiling solution gives the same Dirichlet problem on the actual
finite graph, with exactly the external graph boundary as boundary vertices. -/
theorem solvesDirichlet_restrict {U : Set (Euc d)} [Fintype (T.closedVertices U)]
    {g f : T.V → ℝ} (h : T.SolvesDirichlet U g f) :
    (T.finiteNetwork (T.closedVertices U)).SolvesDirichlet (T.finiteInterior U)
      (fun v => g v) (fun v => f v) := by
  constructor
  · intro v hv
    obtain ⟨hfinite, hzero⟩ := h.1 v hv
    rw [T.closedNetwork_laplacian U f v hv hfinite]
    exact hzero
  · intro v hv
    exact h.2 v ((T.closedVertex_not_interior_iff U v).mp hv)

/-- Agreement of the finite and ambient Dirichlet formulations. The local
finiteness premise is supplied by the collar and mesh lemmas in applications. -/
theorem solvesDirichlet_iff_restrict {U : Set (Euc d)} [Fintype (T.closedVertices U)]
    (hneighbors : ∀ v ∈ T.interiorVertices U, (T.neighbors v).Finite)
    (g f : T.V → ℝ) :
    T.SolvesDirichlet U g f ↔
      (T.finiteNetwork (T.closedVertices U)).SolvesDirichlet (T.finiteInterior U)
        (fun v => g v) (fun v => f v) := by
  refine ⟨T.solvesDirichlet_restrict, ?_⟩
  intro h
  constructor
  · intro v hv
    let vR : T.closedVertices U := ⟨v, Or.inl hv⟩
    refine ⟨hneighbors v hv, ?_⟩
    rw [← T.closedNetwork_laplacian U f vR hv (hneighbors v hv)]
    exact h.1 vR hv
  · intro v hv
    exact h.2 ⟨v, Or.inr hv⟩ hv.1

/-- Uniqueness is asserted on the closed graph region only: the equation places
no constraints on unrelated tiling vertices. -/
theorem dirichlet_unique_on_closed {U : Set (Euc d)} [Fintype (T.closedVertices U)]
    (haccess : (T.finiteNetwork (T.closedVertices U)).BoundaryAccessible
      (T.finiteInterior U))
    {g f₁ f₂ : T.V → ℝ} (h₁ : T.SolvesDirichlet U g f₁)
    (h₂ : T.SolvesDirichlet U g f₂) : Set.EqOn f₁ f₂ (T.closedVertices U) := by
  have heq := (T.finiteNetwork (T.closedVertices U)).dirichlet_unique
    (T.finiteInterior U) haccess (T.solvesDirichlet_restrict h₁)
    (T.solvesDirichlet_restrict h₂)
  intro v hv
  exact congr_fun heq ⟨v, hv⟩

end OrthogonalTiling
end BouRabeeGwynne
