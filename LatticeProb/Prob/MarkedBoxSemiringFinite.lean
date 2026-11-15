import LatticeProb.Prob.MarkedBoxSemiring

/-! Marked half-open boxes indexed by a finite type form a set semiring. -/

open Set MeasureTheory

namespace LatticeProb

private theorem isSetSemiring_preimage_family {α β : Type*} (f : α → β)
    {C : Set (Set β)} (hC : IsSetSemiring C) :
    IsSetSemiring ((fun s => f ⁻¹' s) '' C) := by
  classical
  refine ⟨?_, ?_, ?_⟩
  · exact ⟨∅, hC.empty_mem, preimage_empty⟩
  · rintro _ ⟨s, hs, rfl⟩ _ ⟨t, ht, rfl⟩
    exact ⟨s ∩ t, hC.inter_mem s hs t ht, preimage_inter⟩
  · rintro _ ⟨s, hs, rfl⟩ _ ⟨t, ht, rfl⟩
    obtain ⟨F, hF, hd, heq⟩ := hC.sdiff_eq_sUnion' s hs t ht
    refine ⟨F.image (fun u => f ⁻¹' u), ?_, ?_, ?_⟩
    · intro u hu
      obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hu
      exact ⟨v, hF hv, rfl⟩
    · intro u hu v hv huv
      obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hu
      obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp hv
      apply disjoint_left.mpr
      intro x hxa hxb
      have hab : a ≠ b := fun h => huv (congrArg (fun u => f ⁻¹' u) h)
      exact (disjoint_left.mp (hd ha hb hab)) hxa hxb
    · ext x
      simp only [mem_sdiff, mem_preimage, Finset.coe_image, mem_sUnion, mem_image,
        Finset.mem_coe]
      have hx : f x ∈ s \ t ↔ ∃ u ∈ F, f x ∈ u := by
        rw [heq]
        simp only [mem_sUnion, Finset.mem_coe]
      constructor
      · intro hxst
        obtain ⟨u, hu, hxu⟩ := hx.mp hxst
        exact ⟨f ⁻¹' u, ⟨u, hu, rfl⟩, hxu⟩
      · rintro ⟨_, ⟨u, hu, rfl⟩, hxu⟩
        exact hx.mpr ⟨u, hu, hxu⟩

/-- Measurable marks times half-open boxes indexed by any finite type form a set semiring. -/
theorem isSetSemiring_marked_Ico_boxes_finite {E ι : Type*} [MeasurableSpace E] [Finite ι] :
    IsSetSemiring (Set.image2 (· ×ˢ ·) {s : Set E | MeasurableSet s}
      (Set.univ.pi '' Set.univ.pi (fun _ : ι =>
        {s : Set ℝ | ∃ u v : ℝ, s = Ico u v}))) := by
  classical
  let : Fintype ι := Fintype.ofFinite ι
  let e : ι ≃ Fin (Fintype.card ι) := Fintype.equivFin ι
  let f : E × (ι → ℝ) → E × (Fin (Fintype.card ι) → ℝ) :=
    fun p => (p.1, fun j => p.2 (e.symm j))
  have h := isSetSemiring_preimage_family f
    (isSetSemiring_marked_Ico_boxes (Fintype.card ι) (E := E))
  convert h using 1
  ext S
  constructor
  · rintro ⟨M, hM, _, ⟨A, hA, rfl⟩, rfl⟩
    refine ⟨M ×ˢ univ.pi (fun j => A (e.symm j)), ?_, ?_⟩
    · exact ⟨M, hM, _, ⟨_, by simpa using (fun j => hA (e.symm j)), rfl⟩, rfl⟩
    · ext ⟨x, y⟩
      simp only [mem_preimage, f, mem_prod, mem_univ_pi]
      constructor
      · rintro ⟨hx, hy⟩
        exact ⟨hx, fun i => by simpa using hy (e i)⟩
      · rintro ⟨hx, hy⟩
        exact ⟨hx, fun j => hy (e.symm j)⟩
  · rintro ⟨_, ⟨M, hM, _, ⟨A, hA, rfl⟩, rfl⟩, rfl⟩
    refine ⟨M, hM, _, ⟨fun i => A (e i), ?_, rfl⟩, ?_⟩
    · simpa using (fun i => hA (e i))
    · ext ⟨x, y⟩
      simp only [mem_preimage, f, mem_prod, mem_univ_pi]
      constructor
      · rintro ⟨hx, hy⟩
        exact ⟨hx, fun j => by simpa using hy (e.symm j)⟩
      · rintro ⟨hx, hy⟩
        exact ⟨hx, fun i => by simpa using hy (e i)⟩

end LatticeProb
