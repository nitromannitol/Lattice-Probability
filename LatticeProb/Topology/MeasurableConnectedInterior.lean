import LatticeProb.Topology.MeasurableCurveComponentSecondCountable

/-! # Measurability of connected interiors of curve images -/

set_option autoImplicit false

open Set MeasureTheory

namespace LatticeProb

/-- The connected-interior event for a measurable family of compact curve images
is measurable in a second-countable locally connected Hausdorff space. -/
theorem measurableSet_isConnected_interior_curve_image
    {Ω E : Type*} [MeasurableSpace Ω] [TopologicalSpace E] [T2Space E]
    [SecondCountableTopology E] [LocallyConnectedSpace E] [MeasurableSpace E] [BorelSpace E]
    (f : Ω → C(ℝ, E)) {K : Set ℝ} (hK : IsCompact K) (hf : Measurable f) :
    MeasurableSet {ω | IsConnected (interior (f ω '' K))} := by
  classical
  obtain ⟨D, hDc, hD⟩ := TopologicalSpace.exists_countable_dense E
  have : Countable D := hDc.to_subtype
  let C : D → D → Set Ω := fun x y =>
    {ω | (y : E) ∈ connectedComponentIn (interior (f ω '' K)) (x : E)}
  have hC (x y : D) : MeasurableSet (C x y) :=
    measurableSet_mem_component_interior_image_of_locallyConnected
      f (fun _ => (x : E)) (fun _ => (y : E)) hK hf measurable_const measurable_const
  have heq : {ω | IsConnected (interior (f ω '' K))} =
      ⋃ x : D, C x x ∩ ⋂ y : D, ((C y y)ᶜ ∪ C x y) := by
    ext ω
    simp only [mem_ofPred_eq, mem_iUnion, mem_inter_iff, mem_iInter, mem_union,
      mem_compl_iff, C]
    constructor
    · intro h
      obtain ⟨x, hxD, hx⟩ := hD.exists_mem_open isOpen_interior h.1
      refine ⟨⟨x, hxD⟩, mem_connectedComponentIn hx, ?_⟩
      intro y
      by_cases hy : (y : E) ∈ connectedComponentIn (interior (f ω '' K)) (y : E)
      · right
        exact h.2.subset_connectedComponentIn hx subset_rfl
          (connectedComponentIn_subset _ _ hy)
      · exact Or.inl hy
    · rintro ⟨x, hx, hall⟩
      have hxU : (x : E) ∈ interior (f ω '' K) := connectedComponentIn_subset _ _ hx
      have hsub : interior (f ω '' K) ⊆
          connectedComponentIn (interior (f ω '' K)) (x : E) := by
        intro z hz
        obtain ⟨y, hyD, hy⟩ := hD.exists_mem_open isOpen_interior.connectedComponentIn
          ⟨z, mem_connectedComponentIn hz⟩
        let yd : D := ⟨y, hyD⟩
        have hyU : y ∈ interior (f ω '' K) := connectedComponentIn_subset _ _ hy
        have hyx : y ∈ connectedComponentIn (interior (f ω '' K)) (x : E) := by
          rcases hall yd with hnot | hmem
          · exact (hnot (mem_connectedComponentIn hyU)).elim
          · exact hmem
        have h1 := connectedComponentIn_eq hyx
        have h2 := connectedComponentIn_eq hy
        rw [h1, ← h2]
        exact mem_connectedComponentIn hz
      have he : connectedComponentIn (interior (f ω '' K)) (x : E) =
          interior (f ω '' K) := (connectedComponentIn_subset _ _).antisymm hsub
      rw [← he]
      exact isConnected_connectedComponentIn_iff.mpr hxU
  rw [heq]
  exact MeasurableSet.iUnion fun x => (hC x x).inter <|
    MeasurableSet.iInter fun y => (hC y y).compl.union (hC x y)

end LatticeProb
