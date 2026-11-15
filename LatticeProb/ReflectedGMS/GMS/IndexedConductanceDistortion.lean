import LatticeProb.ReflectedGMS.GMS.AdmissibleIndexed

/-! # Indexed conductance distortion -/

set_option autoImplicit false

open Set

namespace ReflectedGMS.GMS.CellConfig

/-- The conductance term can be indexed by any enumerations of the restricted cells,
provided each source image belongs to the restricted target family. -/
theorem conductance_iSup_eq_indexed {I J : Type*} (H H' : CellConfig) (r : ℝ)
    (f : Plane ≃ₜ Plane) (K : I → Cell) (L : J → Cell) (A : I → Prop) (B : J → Prop)
    (hK : ∀ C, C ∈ H.restrict (Metric.ball 0 r) ↔ ∃ i, A i ∧ K i = C)
    (hL : ∀ C, C ∈ H'.restrict (Metric.ball 0 r) ↔ ∃ j, B j ∧ L j = C)
    (hf : ∀ C ∈ H.restrict (Metric.ball 0 r),
      mapCell f C ∈ H'.restrict (Metric.ball 0 r)) :
    (⨆ (C ∈ H.restrict (Metric.ball 0 r)) (C' ∈ H.restrict (Metric.ball 0 r))
      (_ : H.Adj C C'), ENNReal.ofReal |H.c C C' - H'.c (mapCell f C) (mapCell f C')|) =
    ⨆ (i : I) (i' : I) (j : J) (j' : J) (_ : A i) (_ : A i') (_ : B j) (_ : B j')
      (_ : mapCell f (K i) = L j) (_ : mapCell f (K i') = L j')
      (_ : H.Adj (K i) (K i')),
      ENNReal.ofReal |H.c (K i) (K i') - H'.c (L j) (L j')| := by
  refine le_antisymm ?_ ?_
  · refine iSup_le fun C => iSup_le fun hC => iSup_le fun C' => iSup_le fun hC' =>
      iSup_le fun ha => ?_
    obtain ⟨i, hi, rfl⟩ := (hK C).1 hC
    obtain ⟨i', hi', rfl⟩ := (hK C').1 hC'
    obtain ⟨j, hj, he⟩ := (hL _).1 (hf _ ((hK _).2 ⟨i, hi, rfl⟩))
    obtain ⟨j', hj', he'⟩ := (hL _).1 (hf _ ((hK _).2 ⟨i', hi', rfl⟩))
    rw [← he, ← he']
    exact le_iSup_of_le i (le_iSup_of_le i' (le_iSup_of_le j (le_iSup_of_le j'
      (le_iSup_of_le hi (le_iSup_of_le hi' (le_iSup_of_le hj (le_iSup_of_le hj'
        (le_iSup_of_le he.symm (le_iSup_of_le he'.symm (le_iSup_of_le ha le_rfl))))))))))
  · refine iSup_le fun i => iSup_le fun i' => iSup_le fun j => iSup_le fun j' =>
      iSup_le fun hi => iSup_le fun hi' => iSup_le fun _ => iSup_le fun _ =>
      iSup_le fun he => iSup_le fun he' => iSup_le fun ha => ?_
    rw [← he, ← he']
    exact le_iSup_of_le (K i) (le_iSup_of_le ((hK _).2 ⟨i, hi, rfl⟩)
      (le_iSup_of_le (K i') (le_iSup_of_le ((hK _).2 ⟨i', hi', rfl⟩)
        (le_iSup_of_le ha le_rfl))))

end ReflectedGMS.GMS.CellConfig
