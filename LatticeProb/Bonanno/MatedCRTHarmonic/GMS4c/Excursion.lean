/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module MatedCRTHarmonic.GMS4c.Excursion at commit fdb5cad; only the module paths of local imports are changed.
   Declarations, examples and checks that the copied results do not use are omitted. -/
import LatticeProb.Bonanno.MatedCRTHarmonic.GMS4c.Defs
import LatticeProb.Bonanno.MatedCRTHarmonic.GMS4b.Window

/-!
# Excursions of a transient curve into a bounded open set

For a surjective transient curve `c` and a point `z` of a bounded open set `V`, the bundle's (frozen) entry and exit
times `T_z = entryBefore c V z`, `S_z = exitAfter c V z` around the first hit `τ_z = firstHit c z`
bound an *excursion* of `c` into `V`: `T_z < τ_z < S_z`, `c(T_z), c(S_z) ∉ V` and `c((T_z, S_z)) ⊂ V`
(`isExcursion_entry_exit`). Two excursions sharing a time coincide (`IsExcursion.unique`), and for a curve
parametrized by the mass of a measure two excursions with the same segment coincide (`IsExcursion.eq_of_segment`).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Metric Filter Topology
open scoped ENNReal

namespace MatedCRTHarmonic.GMS4c

open MatedCRTHarmonic.GMS4b MatedCRTHarmonic.MatedCRT

/-- `(A, B)` is an excursion interval of `c` into `V`: `A < B`, the endpoints are outside `V`, the open interval is
mapped into `V`. -/
structure IsExcursion (c : ℝ → ℂ) (V : Set ℂ) (A B : ℝ) : Prop where
  lt : A < B
  left : c A ∉ V
  right : c B ∉ V
  inside : ∀ t ∈ Ioo A B, c t ∈ V

variable {c : C(ℝ, ℂ)} {V : Set ℂ}

/-- A transient curve leaves a bounded set before any given time. -/
theorem exists_le_not_mem (htr : Tendsto c (cocompact ℝ) (cocompact ℂ)) (hVb : Bornology.IsBounded V)
    (T : ℝ) : ∃ t ≤ T, c t ∉ V := by
  have hmem : c ⁻¹' (closure V)ᶜ ∈ cocompact ℝ := htr hVb.isCompact_closure.compl_mem_cocompact
  obtain ⟨K, hK, hKsub⟩ := mem_cocompact.mp hmem
  obtain ⟨m, hm⟩ := hK.bddBelow
  refine ⟨min T (m - 1), min_le_left _ _, fun hV => ?_⟩
  have hnK : min T (m - 1) ∉ K := fun h => by
    have := hm h
    linarith [min_le_right T (m - 1)]
  exact hKsub hnK (subset_closure hV)

/-- A transient curve leaves a bounded set after any given time. -/
theorem exists_ge_not_mem (htr : Tendsto c (cocompact ℝ) (cocompact ℂ)) (hVb : Bornology.IsBounded V)
    (T : ℝ) : ∃ t, T ≤ t ∧ c t ∉ V := by
  have hmem : c ⁻¹' (closure V)ᶜ ∈ cocompact ℝ := htr hVb.isCompact_closure.compl_mem_cocompact
  obtain ⟨K, hK, hKsub⟩ := mem_cocompact.mp hmem
  obtain ⟨m, hm⟩ := hK.bddAbove
  refine ⟨max T (m + 1), le_max_left _ _, fun hV => ?_⟩
  have hnK : max T (m + 1) ∉ K := fun h => by
    have := hm h
    linarith [le_max_right T (m + 1)]
  exact hKsub hnK (subset_closure hV)

/-- **The first-hit excursion.** For `z ∈ V` (open, bounded) and `c` surjective and transient, `(T_z, S_z)` is an
excursion interval of `c` into `V` containing `τ_z`. -/
theorem isExcursion_entry_exit (hV : IsOpen V) (hVb : Bornology.IsBounded V) (hsurj : Function.Surjective c)
    (htr : Tendsto c (cocompact ℝ) (cocompact ℂ)) {z : ℂ} (hz : z ∈ V) :
    IsExcursion c V (entryBefore c V z) (exitAfter c V z) ∧
      firstHit c z ∈ Ioo (entryBefore c V z) (exitAfter c V z) := by
  set T := firstHit c z with hT
  have hcT : c T = z := hitTime_spec c.continuous htr (hsurj z)
  have hclosedV : IsClosed {t : ℝ | c t ∉ V} := hV.isClosed_compl.preimage c.continuous
  -- the entry time
  set L : Set ℝ := {t | t ≤ T ∧ c t ∉ V} with hL
  have hLc : IsClosed L := isClosed_Iic.inter hclosedV
  obtain ⟨t₁, ht₁, ht₁V⟩ := exists_le_not_mem htr hVb T
  have hLne : L.Nonempty := ⟨t₁, ht₁, ht₁V⟩
  have hLbdd : BddAbove L := ⟨T, fun t ht => ht.1⟩
  have hAmem : sSup L ∈ L := hLc.csSup_mem hLne hLbdd
  have hA : entryBefore c V z = sSup L := rfl
  -- the exit time
  set R : Set ℝ := {t | T ≤ t ∧ c t ∉ V} with hR
  have hRc : IsClosed R := isClosed_Ici.inter hclosedV
  obtain ⟨t₂, ht₂, ht₂V⟩ := exists_ge_not_mem htr hVb T
  have hRne : R.Nonempty := ⟨t₂, ht₂, ht₂V⟩
  have hRbdd : BddBelow R := ⟨T, fun t ht => ht.1⟩
  have hBmem : sInf R ∈ R := hRc.csInf_mem hRne hRbdd
  have hB : exitAfter c V z = sInf R := rfl
  have hAT : sSup L < T := by
    refine lt_of_le_of_ne hAmem.1 fun h => hAmem.2 ?_
    rw [h, hcT]; exact hz
  have hTB : T < sInf R := by
    refine lt_of_le_of_ne hBmem.1 fun h => hBmem.2 ?_
    rw [← h, hcT]; exact hz
  rw [hA, hB]
  refine ⟨⟨hAT.trans hTB, hAmem.2, hBmem.2, fun t ht => ?_⟩, hAT, hTB⟩
  by_contra htV
  rcases le_or_gt t T with htT | htT
  · exact absurd (le_csSup hLbdd ⟨htT, htV⟩) (not_le.mpr ht.1)
  · exact absurd (csInf_le hRbdd ⟨htT.le, htV⟩) (not_le.mpr ht.2)

/-- Two excursion intervals sharing a time coincide. -/
theorem IsExcursion.unique {c : ℝ → ℂ} {A B A' B' : ℝ} (h1 : IsExcursion c V A B)
    (h2 : IsExcursion c V A' B') {t : ℝ} (ht1 : t ∈ Ioo A B) (ht2 : t ∈ Ioo A' B') :
    A = A' ∧ B = B' := by
  constructor
  · rcases lt_trichotomy A A' with h | h | h
    · exact absurd (h1.inside A' ⟨h, ht2.1.trans ht1.2⟩) h2.left
    · exact h
    · exact absurd (h2.inside A ⟨h, ht1.1.trans ht2.2⟩) h1.left
  · rcases lt_trichotomy B B' with h | h | h
    · exact absurd (h2.inside B ⟨ht2.1.trans ht1.2, h⟩) h1.right
    · exact h
    · exact absurd (h1.inside B' ⟨ht1.1.trans ht2.2, h⟩) h2.right

/-- The clamp `max 0 (min u ℓ)`. -/
theorem clamp_of_mem {u ℓ : ℝ} (hu : u ∈ Icc 0 ℓ) : max 0 (min u ℓ) = u := by
  rw [min_eq_left hu.2, max_eq_right hu.1]

/-- **Distinct excursions have distinct segments** for a curve parametrized by the mass of a measure. -/
theorem IsExcursion.eq_of_segment {c : ℝ → ℂ} {μ : Measure ℂ}
    (hμ : ∀ s t : ℝ, s ≤ t → μ (c '' Icc s t) = ENNReal.ofReal (t - s)) {A B A' B' : ℝ}
    (h1 : IsExcursion c V A B) (h2 : IsExcursion c V A' B')
    (hseg : ∀ u, c (A + max 0 (min u (B - A))) = c (A' + max 0 (min u (B' - A')))) : A = A' := by
  -- equal lengths
  have hlen : ∀ {A B A' B' : ℝ}, IsExcursion c V A B → IsExcursion c V A' B' →
      (∀ u, c (A + max 0 (min u (B - A))) = c (A' + max 0 (min u (B' - A')))) → B - A ≤ B' - A' := by
    intro A B A' B' h1 h2 hseg
    by_contra hlt
    push Not at hlt
    set u := ((B' - A') + (B - A)) / 2 with hu
    have hu1 : B' - A' < u := by rw [hu]; linarith
    have hu2 : u < B - A := by rw [hu]; linarith
    have hpos' : 0 < B' - A' := sub_pos.mpr h2.lt
    have e1 : max 0 (min u (B - A)) = u := clamp_of_mem ⟨by linarith, hu2.le⟩
    have e2 : max 0 (min u (B' - A')) = B' - A' := by
      rw [min_eq_right hu1.le, max_eq_right hpos'.le]
    have := hseg u
    rw [e1, e2, add_sub_cancel] at this
    exact h2.right (this ▸ h1.inside (A + u) ⟨by linarith, by linarith⟩)
  have hl1 := hlen h1 h2 hseg
  have hl2 := hlen h2 h1 fun u => (hseg u).symm
  have hℓ : B' - A' = B - A := le_antisymm hl2 hl1
  -- disjoint excursions with equal segments contradict the parametrization
  have key : ∀ {A B A' B' : ℝ}, IsExcursion c V A B → IsExcursion c V A' B' → B' - A' = B - A →
      (∀ u, c (A + max 0 (min u (B - A))) = c (A' + max 0 (min u (B' - A')))) → ¬ A < A' := by
    intro A B A' B' h1 h2 hℓ hseg hAA'
    have hBA' : B ≤ A' := by
      by_contra h
      push Not at h
      exact h2.left (h1.inside A' ⟨hAA', h⟩)
    have himg : c '' Icc A' B' ⊆ c '' Icc A B := by
      rintro _ ⟨t, ht, rfl⟩
      refine ⟨A + (t - A'), ⟨by linarith [ht.1], by linarith [ht.2]⟩, ?_⟩
      have h3 := hseg (t - A')
      rw [clamp_of_mem ⟨by linarith [ht.1], by linarith [ht.2]⟩,
        clamp_of_mem ⟨by linarith [ht.1], by linarith [ht.2]⟩, add_sub_cancel] at h3
      exact h3
    have hcover : c '' Icc A B' ⊆ c '' Icc A B ∪ c '' Icc B A' := by
      rintro _ ⟨t, ht, rfl⟩
      rcases le_or_gt t B with htB | htB
      · exact Or.inl ⟨t, ⟨ht.1, htB⟩, rfl⟩
      rcases le_or_gt t A' with htA | htA
      · exact Or.inr ⟨t, ⟨htB.le, htA⟩, rfl⟩
      · exact Or.inl (himg ⟨t, ⟨htA.le, ht.2⟩, rfl⟩)
    have hAB' : A ≤ B' := by linarith [h1.lt, h2.lt]
    have hle := (measure_mono (μ := μ) hcover).trans (measure_union_le _ _)
    rw [hμ A B' hAB', hμ A B h1.lt.le, hμ B A' hBA', ← ENNReal.ofReal_add (by linarith [h1.lt])
      (by linarith)] at hle
    have := (ENNReal.ofReal_le_ofReal_iff (by linarith [h1.lt])).mp hle
    linarith [h2.lt]
  rcases lt_trichotomy A A' with h | h | h
  · exact absurd h (key h1 h2 hℓ hseg)
  · exact h
  · exact absurd h (key h2 h1 hℓ.symm fun u => (hseg u).symm)

end MatedCRTHarmonic.GMS4c
