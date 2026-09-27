import LatticeProb.Prob.InducedMap.MeasurePreservation

/-!
# Ergodicity of the first-return map

For `E` with `inducedMap T A ⁻¹' E = E`, the first-entrance set
`entSet T A E = {x | ∃ n, T^[n] x ∈ A ∧ (∀ j < n, T^[j] x ∉ A) ∧ T^[n] x ∈ E}` satisfies
`T⁻¹ entSet =ᵐ[μ] entSet` (they agree exactly off the null set `A ∩ {retTime = 0}`) and
`entSet ∩ A = E ∩ A`. Mathlib's `QuasiErgodic.aeconst_set₀` applied to `entSet`, restricted to
`A`, shows `inducedMap T A` is ergodic for `μ.restrict A` whenever `T` is ergodic for `μ`.
-/

open MeasureTheory Filter Topology Set

namespace LatticeProb

variable {Ω : Type*} [MeasurableSpace Ω]

omit [MeasurableSpace Ω] in
/-- `entSet T A E` is the union, over the first-entrance time `n`, of the points that first
enter `A` at time `n`, in `E`. -/
private theorem entSet_eq_iUnion_iter {T : Ω → Ω} {A E : Set Ω} :
    entSet T A E = ⋃ n : ℕ, ({x : Ω | T^[n] x ∈ A} ∩
      (⋂ j : Fin n, {x : Ω | T^[(j : ℕ)] x ∉ A}) ∩ {x : Ω | T^[n] x ∈ E}) := by
  ext x
  simp only [entSet, Set.mem_setOf_eq, Set.mem_iUnion, Set.mem_inter_iff, Set.mem_iInter]
  constructor
  · rintro ⟨n, h1, h2, h3⟩
    exact ⟨n, ⟨h1, fun j => h2 j.val j.isLt⟩, h3⟩
  · rintro ⟨n, ⟨h1, h2⟩, h3⟩
    exact ⟨n, h1, fun j hj => h2 ⟨j, hj⟩, h3⟩

/-- The first-entrance set `entSet T A E` is measurable. -/
private theorem measurableSet_entSet {T : Ω → Ω} (hT : Measurable T) {A E : Set Ω}
    (hA : MeasurableSet A) (hE : MeasurableSet E) : MeasurableSet (entSet T A E) := by
  rw [entSet_eq_iUnion_iter]
  apply MeasurableSet.iUnion
  intro n
  exact MeasurableSet.inter
    (MeasurableSet.inter (hA.preimage (hT.iterate n))
      (MeasurableSet.iInter (fun j : Fin n => (hA.preimage (hT.iterate (j : ℕ))).compl)))
    (hE.preimage (hT.iterate n))

omit [MeasurableSpace Ω] in
/-- On `A`, the first-entrance time is `0`, so `entSet T A E ∩ A = E ∩ A`. -/
private theorem entSet_inter_eq (T : Ω → Ω) (A E : Set Ω) : entSet T A E ∩ A = E ∩ A := by
  ext x
  constructor
  · intro hx
    obtain ⟨hex, hxA⟩ := hx
    rw [entSet] at hex
    obtain ⟨n, hnA, hna, hnE⟩ := hex
    have hn0 : n = 0 := by
      by_contra h
      exact hna 0 (Nat.pos_of_ne_zero h) hxA
    subst hn0
    exact ⟨by simpa using hnE, hxA⟩
  · intro hx
    obtain ⟨hxE, hxA⟩ := hx
    exact ⟨⟨0, hxA, (by intro j hj; exact absurd hj (Nat.not_lt_zero j)), hxE⟩, hxA⟩

omit [MeasurableSpace Ω] in
/-- Restates `entSet_inter_eq`, for use as the `hES` hypothesis of
`eventuallyConst_restrict_of_inter_eq`. -/
private theorem entSet_inter_eq' (T : Ω → Ω) (A E : Set Ω) : entSet T A E ∩ A = E ∩ A := by
  exact entSet_inter_eq T A E

omit [MeasurableSpace Ω] in
/-- Off `A`, `T x` has first-entrance time one less than `x`'s (or both never enter), so
`T x ∈ entSet T A E ↔ x ∈ entSet T A E`. -/
private theorem entSet_comp_iff_of_notMem (T : Ω → Ω) (A E : Set Ω) {x : Ω} (hx : x ∉ A) :
    T x ∈ entSet T A E ↔ x ∈ entSet T A E := by
  simp only [entSet, Set.mem_setOf_eq]
  constructor
  · rintro ⟨n, h1, h2, h3⟩
    refine ⟨n.succ, ?_, ?_, ?_⟩
    · rw [Function.iterate_succ_apply T n x]; exact h1
    · intro j hj
      cases j with
      | zero => rw [Function.iterate_zero_apply]; exact hx
      | succ m =>
          rw [Function.iterate_succ_apply T m x]
          exact h2 m (Nat.succ_lt_succ_iff.mp hj)
    · rw [Function.iterate_succ_apply T n x]; exact h3
  · rintro ⟨n, h1, h2, h3⟩
    cases n with
    | zero => rw [Function.iterate_zero_apply] at h1; exact absurd h1 hx
    | succ k =>
        refine ⟨k, ?_, ?_, ?_⟩
        · rw [Function.iterate_succ_apply T k x] at h1; exact h1
        · intro j hj
          rw [← Function.iterate_succ_apply T j x]
          exact h2 (j + 1) (Nat.succ_lt_succ_iff.mpr hj)
        · rw [Function.iterate_succ_apply T k x] at h3; exact h3

omit [MeasurableSpace Ω] in
/-- If `x` returns to `A` at time `k + 1`, then `T x` first enters `A` (after time `0`) at time
`k`, at the point `inducedMap T A x`, so `T x ∈ entSet T A E ↔ inducedMap T A x ∈ E`. -/
private theorem entSet_comp_iff_inducedMap_mem (T : Ω → Ω) (A E : Set Ω) {x : Ω} {k : ℕ}
    (hk : retTime T A x = k + 1) : T x ∈ entSet T A E ↔ inducedMap T A x ∈ E := by
  have hchar := (retTime_eq_iff T A x (Nat.succ_pos k)).mp hk
  have hkA : T^[k + 1] x ∈ A := hchar.1
  have hkavoid : ∀ j, 0 < j → j < k + 1 → T^[j] x ∉ A := hchar.2
  have hid : inducedMap T A x = T^[k] (T x) := by
    unfold inducedMap
    rw [hk, Function.iterate_succ_apply]
  rw [hid]
  simp only [entSet, Set.mem_setOf_eq]
  constructor
  · rintro ⟨n, hnA, hnavoid, hnE⟩
    have hret : retTime T A x = n + 1 := by
      refine (retTime_eq_iff T A x (Nat.succ_pos n)).mpr ⟨?_, ?_⟩
      · simpa only [Function.iterate_succ_apply] using hnA
      · intro j hj0 hjlt
        obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.pos_iff_ne_zero.mp hj0)
        simpa only [Function.iterate_succ_apply] using hnavoid m (by omega)
    have hkn : k = n := by omega
    rw [hkn]
    exact hnE
  · intro h
    refine ⟨k, ?_, ?_, h⟩
    · simpa only [Function.iterate_succ_apply] using hkA
    · intro j hj
      have h1 := hkavoid (j + 1) (Nat.succ_pos j) (by omega)
      simpa only [Function.iterate_succ_apply] using h1

omit [MeasurableSpace Ω] in
/-- A second derivation of `entSet_comp_iff_inducedMap_mem`, tracking `T^[m] (T x) = T^[m+1] x`
directly instead of unfolding `entSet` at `k`. -/
private theorem entSet_comp_iff_inducedMap_mem' (T : Ω → Ω) (A E : Set Ω) {x : Ω} {k : ℕ}
    (hk : retTime T A x = k + 1) : T x ∈ entSet T A E ↔ inducedMap T A x ∈ E := by
  have hchar : T^[k + 1] x ∈ A ∧ ∀ j, 0 < j → j < k + 1 → T^[j] x ∉ A :=
    (retTime_eq_iff T A x (Nat.succ_pos k)).mp hk
  have hshift : ∀ m : ℕ, T^[m] (T x) = T^[m + 1] x :=
    fun m => (Function.iterate_succ_apply T m x).symm
  have h2' : ∀ m, m < k → T^[m] (T x) ∉ A := by
    intro m hm
    rw [hshift m]
    exact hchar.2 (m + 1) (Nat.succ_pos m) (by omega)
  constructor
  · rintro ⟨n, h1, h2, h3⟩
    have hnk : n ≤ k := by
      by_contra h
      have hlt : k < n := by omega
      have hkA : T^[k] (T x) ∉ A := h2 k hlt
      rw [hshift k] at hkA
      exact hkA hchar.1
    have hkn : k ≤ n := by
      by_contra h
      have hlt : n < k := by omega
      exact h2' n hlt h1
    have hnk' : n = k := le_antisymm hnk hkn
    have hid : inducedMap T A x = T^[n] (T x) := by
      rw [inducedMap, hk, ← hshift k, ← hnk']
    rwa [hid]
  · intro hE
    have hkE : T^[k] (T x) ∈ E := by
      rw [hshift k]
      rw [inducedMap, hk] at hE
      exact hE
    exact ⟨k, by rw [hshift k]; exact hchar.1, fun j hj => h2' j hj, hkE⟩

omit [MeasurableSpace Ω] in
/-- If `x ∈ A` returns at time `k + 1` and `E` is `inducedMap T A`-invariant, then
`T x ∈ entSet T A E ↔ x ∈ entSet T A E`. -/
private theorem entSet_comp_iff_of_mem (T : Ω → Ω) (A E : Set Ω)
    (hinv : inducedMap T A ⁻¹' E = E) {x : Ω} (hxA : x ∈ A) {k : ℕ}
    (hk : retTime T A x = k + 1) : T x ∈ entSet T A E ↔ x ∈ entSet T A E := by
  have h26 : T x ∈ entSet T A E ↔ inducedMap T A x ∈ E := entSet_comp_iff_inducedMap_mem' T A E hk
  have h6 : inducedMap T A x ∈ E ↔ x ∈ E := by simpa using Set.ext_iff.mp hinv x
  have hh := Set.ext_iff.mp (entSet_inter_eq T A E) x
  rw [Set.mem_inter_iff, Set.mem_inter_iff] at hh
  have hiff : x ∈ entSet T A E ↔ x ∈ E :=
    ⟨fun h1 => (hh.mp ⟨h1, hxA⟩).1, fun h1 => (hh.mpr ⟨h1, hxA⟩).1⟩
  exact h26.trans (h6.trans hiff.symm)

omit [MeasurableSpace Ω] in
/-- `T⁻¹ entSet T A E \ entSet T A E` sits inside the null set `A ∩ {retTime = 0}`, using
`entSet_comp_iff_of_notMem` off `A` and `entSet_comp_iff_of_mem` on `A`. -/
private theorem preimage_entSet_sdiff_subset_retTime_zero (T : Ω → Ω) (A E : Set Ω)
    (hinv : inducedMap T A ⁻¹' E = E) :
    T ⁻¹' entSet T A E \ entSet T A E ⊆ A ∩ {x | retTime T A x = 0} := by
  intro x hx
  simp only [Set.mem_sdiff] at hx
  obtain ⟨hxT, hxnot⟩ := hx
  rw [Set.mem_preimage] at hxT
  have hxA : x ∈ A := by
    by_contra h
    exact hxnot ((entSet_comp_iff_of_notMem T A E h).mp hxT)
  refine ⟨hxA, ?_⟩
  by_contra h0
  obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero h0
  exact hxnot ((entSet_comp_iff_of_mem T A E hinv hxA hk).mp hxT)

omit [MeasurableSpace Ω] in
/-- The reverse difference `entSet T A E \ T⁻¹ entSet T A E` also sits inside
`A ∩ {retTime = 0}`. -/
private theorem entSet_sdiff_preimage_subset_retTime_zero (T : Ω → Ω) (A E : Set Ω)
    (hinv : inducedMap T A ⁻¹' E = E) :
    entSet T A E \ T ⁻¹' entSet T A E ⊆ A ∩ {x | retTime T A x = 0} := by
  intro x hx
  simp only [Set.mem_sdiff] at hx
  obtain ⟨hxent, hxT⟩ := hx
  rw [Set.mem_preimage] at hxT
  have hxA : x ∈ A := by
    by_contra h
    exact hxT ((entSet_comp_iff_of_notMem T A E h).mpr hxent)
  refine ⟨hxA, ?_⟩
  by_contra h0
  obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero h0
  exact hxT ((entSet_comp_iff_of_mem T A E hinv hxA hk).mpr hxent)

/-- `T⁻¹ entSet T A E =ᵐ[μ] entSet T A E`, since the symmetric difference is null by
`measure_inter_setOf_retTime_eq_zero`. -/
private theorem preimage_entSet_ae_eq_entSet {μ : Measure Ω} [IsFiniteMeasure μ] {T : Ω → Ω}
    (hT : MeasurePreserving T μ μ) {A E : Set Ω} (hA : MeasurableSet A)
    (hinv : inducedMap T A ⁻¹' E = E) :
    T ⁻¹' entSet T A E =ᵐ[μ] entSet T A E := by
  rw [MeasureTheory.ae_eq_set]
  exact ⟨measure_mono_null (preimage_entSet_sdiff_subset_retTime_zero T A E hinv)
      (measure_inter_setOf_retTime_eq_zero hT hA),
    measure_mono_null (entSet_sdiff_preimage_subset_retTime_zero T A E hinv)
      (measure_inter_setOf_retTime_eq_zero hT hA)⟩

/-- If `S` is `μ`-a.e. constant (`∅` or `univ`) and `S ∩ A = E ∩ A`, then `E` is a.e. constant
for `μ.restrict A`. -/
private theorem eventuallyConst_restrict_of_inter_eq {μ : Measure Ω} {A E S : Set Ω}
    (hA : MeasurableSet A) (hES : S ∩ A = E ∩ A) (hS : EventuallyConst S (ae μ)) :
    EventuallyConst E (ae (μ.restrict A)) := by
  rw [Filter.eventuallyConst_set] at hS ⊢
  rcases hS with hS | hS
  · left
    rw [MeasureTheory.ae_restrict_iff' hA]
    filter_upwards [hS] with x hx hxA
    exact ((Set.ext_iff.mp hES x).mp ⟨hx, hxA⟩).1
  · right
    rw [MeasureTheory.ae_restrict_iff' hA]
    filter_upwards [hS] with x hx hxA
    exact fun hE => hx ((Set.ext_iff.mp hES x).mpr ⟨hE, hxA⟩).1

/-- **Ergodicity of the first-return map.** If `T` is ergodic for `μ`, then `inducedMap T A` is
ergodic for `μ.restrict A`. -/
theorem ergodic_inducedMap_of_ergodic {μ : Measure Ω} [IsFiniteMeasure μ] {T : Ω → Ω}
    (herg : Ergodic T μ) {A : Set Ω} (hA : MeasurableSet A) :
    Ergodic (inducedMap T A) (μ.restrict A) := by
  refine ⟨measurePreserving_inducedMap herg.toMeasurePreserving hA, ?_⟩
  refine ⟨fun E hE hinv => ?_⟩
  exact eventuallyConst_restrict_of_inter_eq hA (entSet_inter_eq' T A E)
    (herg.quasiErgodic.aeconst_set₀
      (measurableSet_entSet herg.toMeasurePreserving.measurable hA hE).nullMeasurableSet
      (preimage_entSet_ae_eq_entSet herg.toMeasurePreserving hA hinv))

end LatticeProb
