import LatticeProb.Prob.SemiringBoxDifference
import LatticeProb.Prob.HalfOpenIntervalSemiring
import LatticeProb.Prob.MarkedRectangleGeneration

/-! Measurable marks times finite-dimensional half-open boxes form a set semiring. -/

open Set MeasureTheory

namespace LatticeProb

/-- Measurable marked half-open boxes on finitely many coordinates form a set semiring. -/
theorem isSetSemiring_marked_Ico_boxes (n : ℕ) {E : Type*} [MeasurableSpace E] :
    IsSetSemiring (Set.image2 (· ×ˢ ·) {s : Set E | MeasurableSet s}
      (Set.univ.pi '' Set.univ.pi (fun _ : Fin n =>
        {s : Set ℝ | ∃ u v : ℝ, s = Ico u v}))) := by
  classical
  let C : Set (Set ℝ) := {s | ∃ u v : ℝ, s = Ico u v}
  have hC : IsSetSemiring C := isSetSemiring_Ico_real
  have mem_box (M : Set E) (hM : MeasurableSet M) (A : Fin n → Set ℝ)
      (hA : ∀ i, A i ∈ C) :
      M ×ˢ univ.pi A ∈ Set.image2 (· ×ˢ ·) {s : Set E | MeasurableSet s}
        (univ.pi '' univ.pi (fun _ : Fin n => C)) := by
    exact ⟨M, hM, univ.pi A, ⟨A, by simpa using hA, rfl⟩, rfl⟩
  have unpack (S : Set (E × (Fin n → ℝ)))
      (hS : S ∈ Set.image2 (· ×ˢ ·) {s : Set E | MeasurableSet s}
        (univ.pi '' univ.pi (fun _ : Fin n => C))) :
      ∃ M : Set E, MeasurableSet M ∧ ∃ A : Fin n → Set ℝ,
        (∀ i, A i ∈ C) ∧ S = M ×ˢ univ.pi A := by
    rcases hS with ⟨M, hM, _, ⟨A, hA, rfl⟩, rfl⟩
    exact ⟨M, hM, A, by simpa using hA, rfl⟩
  change IsSetSemiring (Set.image2 (· ×ˢ ·) {s : Set E | MeasurableSet s}
      (univ.pi '' univ.pi (fun _ : Fin n => C)))
  refine ⟨?_, ?_, ?_⟩
  · simpa using mem_box (∅ : Set E) MeasurableSet.empty
      (fun _ => (∅ : Set ℝ)) (fun _ => hC.empty_mem)
  · intro s hs t ht
    obtain ⟨M, hM, A, hA, rfl⟩ := unpack s hs
    obtain ⟨N, hN, B, hB, rfl⟩ := unpack t ht
    have hi : (M ×ˢ univ.pi A) ∩ (N ×ˢ univ.pi B) =
        (M ∩ N) ×ˢ univ.pi (fun i => A i ∩ B i) := by
      ext ⟨x, y⟩
      simp only [mem_inter_iff, mem_prod, mem_univ_pi]
      constructor
      · rintro ⟨⟨hx, hy⟩, ⟨hx', hy'⟩⟩
        exact ⟨⟨hx, hx'⟩, fun i => ⟨hy i, hy' i⟩⟩
      · rintro ⟨⟨hx, hx'⟩, hy⟩
        exact ⟨⟨hx, fun i => (hy i).1⟩, ⟨hx', fun i => (hy i).2⟩⟩
    rw [hi]
    exact mem_box _ (hM.inter hN) _ (fun i => hC.inter_mem _ (hA i) _ (hB i))
  · intro s hs t ht
    obtain ⟨M, hM, A, hA, rfl⟩ := unpack s hs
    obtain ⟨N, hN, B, hB, rfl⟩ := unpack t ht
    obtain ⟨F, hF, hd, hdiff⟩ :=
      pi_sdiff_pi_finite_disjoint (fun _ : Fin n => C) (fun _ => hC) A B hA hB
    let f : Set (Fin n → ℝ) → Set (E × (Fin n → ℝ)) := fun T => (M ∩ N) ×ˢ T
    let q : Set (E × (Fin n → ℝ)) := (M \ N) ×ˢ univ.pi A
    refine ⟨insert q (F.image f), ?_, ?_, ?_⟩
    · intro U hU
      simp only [Finset.mem_coe, Finset.mem_insert, Finset.mem_image] at hU
      rcases hU with rfl | ⟨T, hT, rfl⟩
      · exact mem_box _ (hM.diff hN) A hA
      · obtain ⟨D, hD, rfl⟩ := hF T hT
        exact mem_box _ (hM.inter hN) D hD
    · intro U hU V hV hUV
      simp only [Finset.mem_coe, Finset.mem_insert, Finset.mem_image] at hU hV
      rcases hU with rfl | ⟨T, hT, rfl⟩ <;>
        rcases hV with rfl | ⟨R, hR, rfl⟩
      · exact (hUV rfl).elim
      · apply Set.disjoint_prod.mpr
        left
        exact disjoint_left.mpr (by intro x hx hy; exact hx.2 hy.2)
      · apply Set.disjoint_prod.mpr
        left
        exact disjoint_left.mpr (by intro x hx hy; exact hy.2 hx.2)
      · apply Set.disjoint_prod.mpr
        right
        apply hd hT hR
        intro hTR
        subst R
        exact hUV rfl
    · ext ⟨x, y⟩
      simp only [Finset.coe_insert, sUnion_insert, Finset.coe_image, mem_union,
        mem_sUnion, mem_image, mem_prod, mem_sdiff, f, q]
      have hy : y ∈ univ.pi A \ univ.pi B ↔ ∃ T ∈ F, y ∈ T := by
        rw [hdiff]
        simp only [mem_sUnion, Finset.mem_coe]
      simp only [mem_sdiff] at hy
      constructor
      · rintro ⟨⟨hx, ha⟩, hnot⟩
        by_cases hn : x ∈ N
        · right
          have hb : y ∉ univ.pi B := fun hb => hnot ⟨hn, hb⟩
          obtain ⟨T, hT, hyt⟩ := hy.mp ⟨ha, hb⟩
          exact ⟨_, ⟨T, hT, rfl⟩, ⟨⟨hx, hn⟩, hyt⟩⟩
        · exact Or.inl ⟨⟨hx, hn⟩, ha⟩
      · rintro (⟨⟨hx, hn⟩, ha⟩ | ⟨_, ⟨T, hT, rfl⟩, ⟨⟨hx, hn⟩, hyt⟩⟩)
        · exact ⟨⟨hx, ha⟩, fun h => hn h.1⟩
        · obtain ⟨ha, hb⟩ := hy.mpr ⟨T, hT, hyt⟩
          exact ⟨⟨hx, ha⟩, fun h => hb h.2⟩

end LatticeProb
