import Mathlib

/-!
# Directions of segments meeting a closed set

For `z ∈ ℂ`, `ρ ∈ ℝ` and a closed set `H ⊆ ℂ`, the set of angles `θ` for which the segment
`{z + t e^{iθ} : 0 ≤ t ≤ ρ}` meets `H` is closed: it is the projection to the first factor of a
closed subset of `ℝ × [0, ρ]`, and projections along a compact factor are closed maps. In particular
it is Borel, so the event that a segment in a random direction meets `H` is measurable, and it is
contained in the set of directions of rays from `z` meeting `H`.
-/

namespace LatticeProb

open Complex Set

/-- **The directions of segments meeting a closed set form a closed set.** -/
theorem isClosed_setOf_exists_segment_mem (z : ℂ) (ρ : ℝ) {H : Set ℂ} (hH : IsClosed H) :
    IsClosed {θ : ℝ | ∃ t ∈ Icc (0 : ℝ) ρ, z + t * exp (θ * I) ∈ H} := by
  have : CompactSpace (Icc (0 : ℝ) ρ) := isCompact_iff_compactSpace.mp isCompact_Icc
  have hc : IsClosed {q : ℝ × Icc (0 : ℝ) ρ | z + ((q.2 : ℝ) : ℂ) * exp ((q.1 : ℂ) * I) ∈ H} :=
    hH.preimage (continuous_const.add
      ((continuous_ofReal.comp (continuous_subtype_val.comp continuous_snd)).mul
        (continuous_exp.comp ((continuous_ofReal.comp continuous_fst).mul continuous_const))))
  convert isClosedMap_fst_of_compactSpace _ hc using 1
  ext θ
  constructor
  · rintro ⟨t, ht, h⟩
    exact ⟨(θ, ⟨t, ht⟩), h, rfl⟩
  · rintro ⟨⟨θ', t⟩, h, rfl⟩
    exact ⟨t, t.2, h⟩

/-- The directions of segments meeting a closed set form a Borel set. -/
theorem measurableSet_setOf_exists_segment_mem (z : ℂ) (ρ : ℝ) {H : Set ℂ} (hH : IsClosed H) :
    MeasurableSet {θ : ℝ | ∃ t ∈ Icc (0 : ℝ) ρ, z + t * exp (θ * I) ∈ H} :=
  (isClosed_setOf_exists_segment_mem z ρ hH).measurableSet

/-- A segment from `z` meeting `H` lies on a ray from `z` meeting `H`. -/
theorem setOf_exists_segment_mem_subset (z : ℂ) (ρ : ℝ) (H : Set ℂ) :
    {θ : ℝ | ∃ t ∈ Icc (0 : ℝ) ρ, z + t * exp (θ * I) ∈ H} ⊆
      {θ : ℝ | ∃ t : ℝ, 0 ≤ t ∧ z + t * exp (θ * I) ∈ H} :=
  fun _ ⟨t, ht, h⟩ => ⟨t, ht.1, h⟩

end LatticeProb
