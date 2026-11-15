import LatticeProb.MeasureTheory.AEOpenUnion
import Mathlib.Topology.Connected.LocallyConnected

/-! # Maximal connected almost-everywhere runs -/

set_option autoImplicit false

open Set MeasureTheory

namespace LatticeProb

/-- An almost-everywhere predicate has a maximal connected open run around any
point lying in an admissible open neighborhood. -/
theorem exists_maximal_connected_open_ae_run
    {α : Type*} [TopologicalSpace α] [SecondCountableTopology α]
    [LocallyConnectedSpace α] [MeasurableSpace α]
    (μ : Measure α) (s : Set α) (p : α → Prop) (x : α)
    (hx : ∃ V : Set α, IsOpen V ∧ x ∈ V ∧ V ⊆ s ∧
      ∀ᵐ y ∂(μ.restrict V), p y) :
    ∃ C : Set α, IsOpen C ∧ IsPreconnected C ∧ x ∈ C ∧ C ⊆ s ∧
      (∀ᵐ y ∂(μ.restrict C), p y) ∧
      ∀ V : Set α, IsOpen V → IsPreconnected V → x ∈ V → V ⊆ s →
        (∀ᵐ y ∂(μ.restrict V), p y) → V ⊆ C := by
  let ι := {V : Set α // IsOpen V ∧ V ⊆ s ∧ ∀ᵐ y ∂(μ.restrict V), p y}
  let U : Set α := ⋃ V : ι, (V : Set α)
  have hopen : IsOpen U := isOpen_iUnion fun V : ι => V.2.1
  have hUs : U ⊆ s := iUnion_subset fun V : ι => V.2.2.1
  have hUae : ∀ᵐ y ∂(μ.restrict U), p y :=
    ae_restrict_iUnion_of_isOpen μ (fun V : ι => V.1) p
      (fun V => V.2.1) (fun V => V.2.2.2)
  obtain ⟨V, hVopen, hxV, hVs, hVae⟩ := hx
  have hxU : x ∈ U := mem_iUnion.mpr ⟨⟨V, hVopen, hVs, hVae⟩, hxV⟩
  refine ⟨connectedComponentIn U x, hopen.connectedComponentIn,
    isPreconnected_connectedComponentIn, mem_connectedComponentIn hxU,
    (connectedComponentIn_subset U x).trans hUs,
    ae_restrict_of_ae_restrict_of_subset (connectedComponentIn_subset U x) hUae, ?_⟩
  intro W hWopen hWconn hxW hWs hWae
  apply hWconn.subset_connectedComponentIn hxW
  exact subset_iUnion (fun V : ι => (V : Set α)) ⟨W, hWopen, hWs, hWae⟩

end LatticeProb
