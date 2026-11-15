import Mathlib.MeasureTheory.MeasurableSpace.Constructions

/-! # Germs of countably indexed observations -/

set_option autoImplicit false

open Set MeasureTheory

namespace LatticeProb

/-- If a sigma algebra observes a selected index and the observation at that
index, it contains the intersection of the fixed-index observation algebras. -/
theorem iInf_comap_le_of_measurable_selected {Ω Y : Type*}
    [MeasurableSpace Y] (m : MeasurableSpace Ω) (X : ℕ → Ω → Y)
    (f : Ω → ℕ) (hf : Measurable[m] f)
    (hX : Measurable[m] (fun ω => X (f ω) ω)) :
    (⨅ k, MeasurableSpace.comap (X k) inferInstance) ≤ m := by
  intro E hE
  have hEk : ∀ k, MeasurableSet[MeasurableSpace.comap (X k) inferInstance] E :=
    MeasurableSpace.measurableSet_iInf.mp hE
  choose B hB hpre using fun k => MeasurableSpace.measurableSet_comap.mp (hEk k)
  let : MeasurableSpace Ω := m
  have heq : E = ⋃ k : ℕ, {ω | f ω = k} ∩ (fun ω => X (f ω) ω) ⁻¹' B k := by
    ext ω
    simp only [mem_iUnion, mem_inter_iff, mem_ofPred_eq, mem_preimage]
    constructor
    · intro hω
      refine ⟨f ω, rfl, ?_⟩
      exact (show ω ∈ X (f ω) ⁻¹' B (f ω) by rw [hpre]; exact hω)
    · rintro ⟨k, hk, hω⟩
      have hx : ω ∈ X k ⁻¹' B k := by
        change X k ω ∈ B k
        simpa only [hk] using hω
      rwa [hpre k] at hx
  rw [heq]
  exact MeasurableSet.iUnion fun k =>
    (measurableSet_singleton k |>.preimage hf).inter (hB k |>.preimage hX)

end LatticeProb
