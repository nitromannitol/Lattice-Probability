import LatticeProb.Bonanno.QuantumZipper.Proofs.Complex.TopoEilenberg

/-! # Frontiers of interior components -/

set_option autoImplicit false

open Set MeasureTheory

namespace LatticeProb

/-- The frontier of a component of the interior of a closed planar set lies in the
frontier of that set. -/
theorem frontier_component_interior_subset {K : Set ℂ} (hK : IsClosed K) (x : ℂ) :
    frontier (connectedComponentIn (interior K) x) ⊆ frontier K := by
  have hdis : frontier (connectedComponentIn (interior K) x) ⊆ (interior K)ᶜ := by
    simpa only [compl_compl] using
      (QuantumZipper.CA.Topo.frontier_connectedComponentIn_compl_subset
        isOpen_interior.isClosed_compl x)
  intro z hz
  have hzK : z ∈ K := hK.closure_subset_iff.mpr
    ((connectedComponentIn_subset (interior K) x).trans interior_subset)
    (frontier_subset_closure hz)
  rw [frontier, hK.closure_eq]
  exact ⟨hzK, hdis hz⟩

/-- Nullity of the frontier passes to every component of the interior. -/
theorem measure_frontier_component_interior_eq_zero {K : Set ℂ} (hK : IsClosed K)
    (μ : Measure ℂ) (hnull : μ (frontier K) = 0) (x : ℂ) :
    μ (frontier (connectedComponentIn (interior K) x)) = 0 := by
  exact measure_mono_null (frontier_component_interior_subset hK x) hnull

/-- The same containment for the image of a compact set under a continuous curve. -/
theorem frontier_curve_component_subset {T : Type*} [TopologicalSpace T]
    (η : T → ℂ) (hη : Continuous η) {A : Set T} (hA : IsCompact A) (x : ℂ) :
    frontier (connectedComponentIn (interior (η '' A)) x) ⊆ frontier (η '' A) :=
  frontier_component_interior_subset (hA.image hη).isClosed x

end LatticeProb
