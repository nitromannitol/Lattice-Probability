import LatticeProb.Bonanno.ReflectedGMS.GMS.Theorem116Statement

/-! # Indexed admissibility of cell configurations -/

set_option autoImplicit false

open Set

namespace ReflectedGMS.GMS.CellConfig

/-- Admissibility can be checked on any enumerations of the restricted cell families.
All labels of each image cell are tested, so the enumerations need not be injective. -/
theorem admissibleAt_iff_indexed {I J : Type*} (H H' : CellConfig) (r : ℝ)
    (f : Plane ≃ₜ Plane) (K : I → Cell) (L : J → Cell) (A : I → Prop) (B : J → Prop)
    (hK : ∀ C, C ∈ H.restrict (Metric.ball 0 r) ↔ ∃ i, A i ∧ K i = C)
    (hL : ∀ C, C ∈ H'.restrict (Metric.ball 0 r) ↔ ∃ j, B j ∧ L j = C) :
    AdmissibleAt H H' r f ↔
      (∀ i, A i → ∃ j, B j ∧ mapCell f (K i) = L j) ∧
      (∀ j, B j → ∃ i, A i ∧ mapCell f.symm (L j) = K i) ∧
      (∀ i i' j j', A i → A i' → B j → B j' →
        mapCell f (K i) = L j → mapCell f (K i') = L j' →
        H.Adj (K i) (K i') → H'.Adj (L j) (L j')) ∧
      (∀ j j' i i', B j → B j' → A i → A i' →
        mapCell f.symm (L j) = K i → mapCell f.symm (L j') = K i' →
        H'.Adj (L j) (L j') → H.Adj (K i) (K i')) := by
  constructor
  · rintro ⟨hfor, hback, hadj, hadj'⟩
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro i hi
      obtain ⟨j, hj, heq⟩ := (hL _).1 (hfor _ ((hK _).2 ⟨i, hi, rfl⟩))
      exact ⟨j, hj, heq.symm⟩
    · intro j hj
      obtain ⟨i, hi, heq⟩ := (hK _).1 (hback _ ((hL _).2 ⟨j, hj, rfl⟩))
      exact ⟨i, hi, heq.symm⟩
    · intro i i' j j' hi hi' hj hj' he he' ha
      have ht := hadj _ ((hK _).2 ⟨i, hi, rfl⟩) _ ((hK _).2 ⟨i', hi', rfl⟩) ha
      rw [he, he'] at ht
      exact ht
    · intro j j' i i' hj hj' hi hi' he he' ha
      have ht := hadj' _ ((hL _).2 ⟨j, hj, rfl⟩) _ ((hL _).2 ⟨j', hj', rfl⟩) ha
      rw [he, he'] at ht
      exact ht
  · rintro ⟨hfor, hback, hadj, hadj'⟩
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro C hC
      obtain ⟨i, hi, rfl⟩ := (hK _).1 hC
      obtain ⟨j, hj, he⟩ := hfor i hi
      exact (hL _).2 ⟨j, hj, he.symm⟩
    · intro C hC
      obtain ⟨j, hj, rfl⟩ := (hL _).1 hC
      obtain ⟨i, hi, he⟩ := hback j hj
      exact (hK _).2 ⟨i, hi, he.symm⟩
    · intro C hC C' hC' ha
      obtain ⟨i, hi, rfl⟩ := (hK _).1 hC
      obtain ⟨i', hi', rfl⟩ := (hK _).1 hC'
      obtain ⟨j, hj, he⟩ := hfor i hi
      obtain ⟨j', hj', he'⟩ := hfor i' hi'
      rw [he, he']
      exact hadj i i' j j' hi hi' hj hj' he he' ha
    · intro C hC C' hC' ha
      obtain ⟨j, hj, rfl⟩ := (hL _).1 hC
      obtain ⟨j', hj', rfl⟩ := (hL _).1 hC'
      obtain ⟨i, hi, he⟩ := hback j hj
      obtain ⟨i', hi', he'⟩ := hback j' hj'
      rw [he, he']
      exact hadj' j j' i i' hj hj' hi hi' he he' ha

end ReflectedGMS.GMS.CellConfig
