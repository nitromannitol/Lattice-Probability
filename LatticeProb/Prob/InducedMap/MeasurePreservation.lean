import LatticeProb.Prob.InducedMap.TowerComputation

/-!
# Poincaré recurrence and invariance of the restricted measure

`retTime T A x = 0` only off a `μ`-null subset of `A` (Poincaré recurrence). Writing
`A ∩ inducedMap T A ⁻¹' B` as a null set together with the disjoint union of the pieces
`A ∩ retSet T A B (k + 1)` and applying `measure_eq_tsum_measure_inter_retSet` shows that
`inducedMap T A` preserves `μ.restrict A`, with no hypothesis `μ A > 0`.
-/

open MeasureTheory Filter Topology Set

namespace LatticeProb

variable {Ω : Type*} [MeasurableSpace Ω]

/-- The set of points of `A` that never return to `A` is `μ`-null (Poincaré recurrence, via
Mathlib's `MeasurePreserving.conservative`). -/
theorem measure_inter_setOf_retTime_eq_zero {μ : Measure Ω} [IsFiniteMeasure μ] {T : Ω → Ω}
    (hT : MeasurePreserving T μ μ) {A : Set Ω} (hA : MeasurableSet A) :
    μ (A ∩ {x | retTime T A x = 0}) = 0 := by
  have h : A ∩ {x | retTime T A x = 0} = {x | x ∈ A ∧ ∀ m ≥ 1, T^[m] x ∉ A} :=
    Set.ext fun x => by
      simp only [Set.mem_inter_iff, Set.mem_setOf_eq]
      constructor
      · rintro ⟨hxA, h0⟩
        exact ⟨hxA, fun m hm => (retTime_eq_zero_iff T A x).mp h0 m (by omega)⟩
      · rintro ⟨hxA, h'⟩
        exact ⟨hxA, (retTime_eq_zero_iff T A x).mpr (fun n hn => h' n (by omega))⟩
  rw [h]
  exact hT.conservative.measure_mem_forall_ge_image_notMem_eq_zero hA.nullMeasurableSet 1

/-- Poincaré recurrence: `retTime T A x > 0` for `μ`-a.e. `x ∈ A`. -/
theorem ae_retTime_pos {μ : Measure Ω} [IsFiniteMeasure μ] {T : Ω → Ω}
    (hT : MeasurePreserving T μ μ) {A : Set Ω} (hA : MeasurableSet A) :
    ∀ᵐ x ∂μ, x ∈ A → 0 < retTime T A x := by
  have h16 := measure_inter_setOf_retTime_eq_zero hT hA
  rw [measure_eq_zero_iff_ae_notMem] at h16
  filter_upwards [h16] with x hx hxA
  exact Nat.pos_of_ne_zero fun h0 => hx ⟨hxA, h0⟩

omit [MeasurableSpace Ω] in
/-- `A ∩ inducedMap T A ⁻¹' B` splits as the null set `A ∩ {retTime = 0} ∩ B` together with the
disjoint union, over `k`, of `A ∩ retSet T A B (k + 1)`. -/
private theorem inter_preimage_inducedMap_eq_union (T : Ω → Ω) {A B : Set Ω} (hBA : B ⊆ A) :
    A ∩ inducedMap T A ⁻¹' B =
      (A ∩ {x | retTime T A x = 0} ∩ B) ∪ ⋃ k : ℕ, A ∩ retSet T A B (k + 1) := by
  apply Set.ext
  intro x
  simp only [inducedMap, Set.mem_inter_iff, Set.mem_preimage, Set.mem_union, Set.mem_iUnion,
    Set.mem_setOf_eq]
  constructor
  · rintro ⟨hxA, hxB⟩
    by_cases h0 : retTime T A x = 0
    · refine Or.inl ⟨⟨hxA, h0⟩, ?_⟩
      rw [h0, Function.iterate_zero] at hxB
      exact hxB
    · have hne : retTime T A x ≠ 0 := h0
      obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero hne
      have hk' : retTime T A x = k + 1 := hk
      have hchar : T^[k + 1] x ∈ A ∧ ∀ j, 0 < j → j < k + 1 → T^[j] x ∉ A :=
        (retTime_eq_iff T A x (Nat.succ_pos k)).mp hk'
      rw [hk'] at hxB
      exact Or.inr ⟨k, hxA, hxB, hchar.2⟩
  · rintro (h | h)
    · obtain ⟨⟨hxA, h0⟩, hxB⟩ := h
      refine ⟨hxA, ?_⟩
      rw [h0, Function.iterate_zero]
      exact hxB
    · obtain ⟨k, hAk⟩ := h
      obtain ⟨hxA, hk⟩ := hAk
      simp only [retSet, Set.mem_setOf_eq] at hk
      have hBk : T^[k+1] x ∈ B := hk.1
      have hret : retTime T A x = k + 1 :=
        (retTime_eq_iff T A x (Nat.succ_pos k)).mpr ⟨hBA hBk, hk.2⟩
      refine ⟨hxA, ?_⟩
      rw [hret]
      exact hBk

omit [MeasurableSpace Ω] in
/-- The pieces `A ∩ retSet T A B (k + 1)`, `k : ℕ`, are pairwise disjoint (each records a
distinct value of `retTime`, using `B ⊆ A`). -/
private theorem pairwise_disjoint_inter_retSet (T : Ω → Ω) {A B : Set Ω} (hBA : B ⊆ A) :
    Pairwise (Function.onFun Disjoint (fun k : ℕ => A ∩ retSet T A B (k + 1))) := by
  intro k l hkl
  rcases lt_or_gt_of_ne hkl with h | h
  · exact Set.disjoint_left.2 fun x hx1 hx2 => by
      simp only [Set.mem_inter_iff, retSet, Set.mem_setOf_eq] at hx1 hx2
      exact hx2.2.2 (k + 1) (Nat.succ_pos k) (Nat.succ_lt_succ h) (hBA hx1.2.1)
  · exact Set.disjoint_left.2 fun x hx1 hx2 => by
      simp only [Set.mem_inter_iff, retSet, Set.mem_setOf_eq] at hx1 hx2
      exact hx1.2.2 (l + 1) (Nat.succ_pos l) (Nat.succ_lt_succ h) (hBA hx2.2.1)

/-- `μ (A ∩ inducedMap T A ⁻¹' B) = μ B`: the null piece of `inter_preimage_inducedMap_eq_union`
drops out, and the remaining union has the same measure as `B` by
`measure_eq_tsum_measure_inter_retSet`. -/
private theorem measure_inter_preimage_inducedMap_eq {μ : Measure Ω} [IsFiniteMeasure μ]
    {T : Ω → Ω} (hT : MeasurePreserving T μ μ) {A B : Set Ω} (hA : MeasurableSet A)
    (hB : MeasurableSet B) (hBA : B ⊆ A) : μ (A ∩ inducedMap T A ⁻¹' B) = μ B := by
  have hUeq : μ (⋃ k : ℕ, A ∩ retSet T A B (k + 1))
      = ∑' k : ℕ, μ (A ∩ retSet T A B (k + 1)) :=
    measure_iUnion (μ := μ) (pairwise_disjoint_inter_retSet T hBA)
      (fun k => hA.inter (measurableSet_retSet_avoidSet hT.measurable hA hB (k + 1)).1)
  have hU : μ (⋃ k : ℕ, A ∩ retSet T A B (k + 1)) = μ B :=
    hUeq.trans (measure_eq_tsum_measure_inter_retSet hT hA hB hBA).symm
  have hN : μ (A ∩ {x | retTime T A x = 0} ∩ B) = 0 :=
    measure_mono_null
      (s := A ∩ {x | retTime T A x = 0} ∩ B) (t := A ∩ {x | retTime T A x = 0})
      (fun x hx => ⟨hx.1.1, hx.1.2⟩) (measure_inter_setOf_retTime_eq_zero hT hA)
  rw [inter_preimage_inducedMap_eq_union T hBA]
  apply le_antisymm
  · calc μ ((A ∩ {x | retTime T A x = 0} ∩ B) ∪ ⋃ k : ℕ, A ∩ retSet T A B (k + 1))
        ≤ μ (A ∩ {x | retTime T A x = 0} ∩ B) + μ (⋃ k : ℕ, A ∩ retSet T A B (k + 1)) :=
          measure_union_le _ _
      _ = μ B := (by rw [hN, zero_add, hU])
  · rw [← hU]
    exact measure_mono Set.subset_union_right

omit [MeasurableSpace Ω] in
/-- `(A ∩ inducedMap T A ⁻¹' B) \ (A ∩ inducedMap T A ⁻¹' (B ∩ A))` sits inside the null set
`A ∩ {retTime = 0}` (off it, `inducedMap T A x ∈ A` automatically). -/
private lemma preimage_inducedMap_sdiff_inter_subset_retTime_zero (T : Ω → Ω) (A B : Set Ω) :
    (A ∩ inducedMap T A ⁻¹' B) \ (A ∩ inducedMap T A ⁻¹' (B ∩ A)) ⊆
      A ∩ {x | retTime T A x = 0} := by
  rintro x ⟨hx1, hx2⟩
  obtain ⟨hxA, hxB⟩ := hx1
  refine ⟨hxA, ?_⟩
  by_contra hr
  exact hx2 ⟨hxA, hxB, inducedMap_mem_of_retTime_ne_zero T A x hr⟩

omit [MeasurableSpace Ω] in
/-- The reverse difference `(A ∩ inducedMap T A ⁻¹' (B ∩ A)) \ (A ∩ inducedMap T A ⁻¹' B)` also
sits inside `A ∩ {retTime = 0}`. -/
private lemma inter_sdiff_preimage_inducedMap_subset_retTime_zero (T : Ω → Ω) (A B : Set Ω) :
    (A ∩ inducedMap T A ⁻¹' (B ∩ A)) \ (A ∩ inducedMap T A ⁻¹' B) ⊆
      A ∩ {x | retTime T A x = 0} := by
  rintro x ⟨hx1, hx2⟩
  obtain ⟨hxA, hxB⟩ := hx1
  refine ⟨hxA, ?_⟩
  by_contra hr
  exact hx2 ⟨hxA, hxB.1⟩

/-- `μ (A ∩ inducedMap T A ⁻¹' B) = μ (A ∩ inducedMap T A ⁻¹' (B ∩ A))`, since the two events
differ only inside the null set `A ∩ {retTime = 0}`. -/
private theorem measure_inter_preimage_inducedMap_eq_inter {μ : Measure Ω} [IsFiniteMeasure μ]
    {T : Ω → Ω} (hT : MeasurePreserving T μ μ) {A : Set Ω} (hA : MeasurableSet A) (B : Set Ω) :
    μ (A ∩ inducedMap T A ⁻¹' B) = μ (A ∩ inducedMap T A ⁻¹' (B ∩ A)) := by
  have hNnull : μ (A ∩ {x | retTime T A x = 0}) = 0 := measure_inter_setOf_retTime_eq_zero hT hA
  exact measure_congr (ae_eq_set.mpr
    ⟨measure_mono_null (preimage_inducedMap_sdiff_inter_subset_retTime_zero T A B) hNnull,
     measure_mono_null (inter_sdiff_preimage_inducedMap_subset_retTime_zero T A B) hNnull⟩)

/-- **Invariance of the restricted measure.** `inducedMap T A` preserves `μ.restrict A`, with no
hypothesis that `μ A > 0`. -/
theorem measurePreserving_inducedMap {μ : Measure Ω} [IsFiniteMeasure μ] {T : Ω → Ω}
    (hT : MeasurePreserving T μ μ) {A : Set Ω} (hA : MeasurableSet A) :
    MeasurePreserving (inducedMap T A) (μ.restrict A) (μ.restrict A) := by
  refine ⟨?_, ?_⟩
  · exact measurable_inducedMap (T := T) hT.measurable hA
  · ext B hB
    have hmeas : Measurable (inducedMap T A) := measurable_inducedMap (T := T) hT.measurable hA
    rw [Measure.map_apply hmeas hB, Measure.restrict_apply (hB.preimage hmeas),
      Measure.restrict_apply hB, Set.inter_comm (inducedMap T A ⁻¹' B) A]
    rw [measure_inter_preimage_inducedMap_eq_inter hT hA B,
      measure_inter_preimage_inducedMap_eq hT (A := A) (B := B ∩ A) hA (hB.inter hA)
        Set.inter_subset_right]

end LatticeProb
