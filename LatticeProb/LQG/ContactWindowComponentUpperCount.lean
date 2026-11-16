import LatticeProb.LQG.ContactWindowFibreLocalization
import LatticeProb.LQG.ContactWindowComponentCount

/-! # Conditional upper bounds for contact-window component counts -/

set_option autoImplicit false

open MeasureTheory Set
open scoped NNReal

namespace LatticeProb

/-- Fibre localization confines all nonsingleton components to two given components. -/
theorem nonSingletonComponents_subset_pair_of_fibre_localization
    {α β : Type*} [TopologicalSpace β] (f : α → β) (Q : α → α → Prop)
    (I J Kₗ Kᵣ : Set α) (S L R : Set β)
    (hQ : ∀ s t, f s = f t ↔ Q s t)
    (hL : L ∈ connectedComponentIn S '' S)
    (hR : R ∈ connectedComponentIn S '' S)
    (hleft : f '' Kₗ ⊆ L) (hright : f '' Kᵣ ⊆ R)
    (hloc : ∀ C ∈ nonSingletonComponents S,
      ∃ s ∈ I, ∃ t ∈ J, f s ∈ C ∧ Q s t ∧ ∃ k ∈ Kₗ ∪ Kᵣ, Q s k) :
    nonSingletonComponents S ⊆ {L, R} := by
  intro C hC
  have h := component_eq_left_or_right_of_fibre_localization f Q I J Kₗ Kᵣ S C L R
    hQ hC.1 hL hR hleft hright (hloc C hC)
  simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using h

/-- A component family contained in a pair is finite and has at most two members. -/
theorem nonSingletonComponents_count_le_two_of_subset_pair
    {β : Type*} [TopologicalSpace β] (S L R : Set β)
    (h : nonSingletonComponents S ⊆ {L, R}) :
    (nonSingletonComponents S).Finite ∧ (nonSingletonComponents S).ncard ≤ 2 ∧
      (nonSingletonComponents S).encard ≤ 2 := by
  have hcount : (nonSingletonComponents S).encard ≤ 2 := calc
    _ ≤ ({L, R} : Set (Set β)).encard := Set.encard_mono h
    _ ≤ 2 := by
      calc
        _ ≤ ({R} : Set (Set β)).encard + 1 := Set.encard_insert_le _ _
        _ = 2 := by rw [Set.encard_singleton]; norm_num
  exact ⟨(Set.encard_le_coe_iff_finite_ncard_le.mp hcount).1,
    (Set.encard_le_coe_iff_finite_ncard_le.mp hcount).2, hcount⟩

end LatticeProb

namespace MatedCRTHarmonic.MoTInput

open MatedCRTHarmonic.MatedCRT
open MatedCRTHarmonic.RouteM

variable {γ : ℝ} {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
  {X X₀ hIG₀ : Ω → Field} {B B' B₀ B₀' : ℝ≥0 → Ω → ℝ} {U : Ω → ℝ}
  {ηL η η₀ : Ω → C(ℝ, ℂ)} {bm : Ω → Path2}

/-- If each nonsingleton cell-intersection component meets a strict contact window,
there are at most two such components. -/
theorem ae_contact_window_components_count_le_two_of_meets_windows
    (D : IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm) :
    ∀ᵐ ω ∂P, ∀ (ε : ℝ) (x y : ℤ),
      0 < ε → x + 1 < y →
      dWinLo ε (lCoord (bm ω)) x y < dWinHi ε (lCoord (bm ω)) x y →
      dWinLo ε (rCoord (bm ω)) x y < dWinHi ε (rCoord (bm ω)) x y →
      let S := (η ω) '' Icc (ε * ((x : ℝ) - 1)) (ε * x) ∩
        (η ω) '' Icc (ε * ((y : ℝ) - 1)) (ε * y)
      (∀ C ∈ LatticeProb.nonSingletonComponents S,
        (C ∩ ((fun level => η ω (ellMinus (bm ω) (ε * x) level)) ''
          Ioo (dWinLo ε (lCoord (bm ω)) x y) (dWinHi ε (lCoord (bm ω)) x y) ∪
          (fun level => η ω (rhoMinus (bm ω) (ε * x) level)) ''
          Ioo (dWinLo ε (rCoord (bm ω)) x y) (dWinHi ε (rCoord (bm ω)) x y))).Nonempty) →
      ∃ C ∈ LatticeProb.nonSingletonComponents S, ∃ E ∈ LatticeProb.nonSingletonComponents S,
        (∀ a b, dWinLo ε (lCoord (bm ω)) x y < a →
          b < dWinHi ε (lCoord (bm ω)) x y → a < b →
          (fun level => η ω (ellMinus (bm ω) (ε * x) level)) '' Icc a b ⊆ C) ∧
        (∀ a b, dWinLo ε (rCoord (bm ω)) x y < a →
          b < dWinHi ε (rCoord (bm ω)) x y → a < b →
          (fun level => η ω (rhoMinus (bm ω) (ε * x) level)) '' Icc a b ⊆ E) ∧
        LatticeProb.nonSingletonComponents S = {C, E} ∧
        (LatticeProb.nonSingletonComponents S).Finite ∧
        (LatticeProb.nonSingletonComponents S).ncard ≤ 2 ∧
        (LatticeProb.nonSingletonComponents S).encard ≤ 2 := by
  filter_upwards [ae_contact_window_components_count D] with ω hw
  intro ε x y hε hxy hl hr
  dsimp only
  intro hmeet
  obtain ⟨C, hC, E, hE, hCl, hEr, _, _⟩ := hw ε x y hε hxy hl hr
  have hleft : (fun level => η ω (ellMinus (bm ω) (ε * x) level)) ''
      Ioo (dWinLo ε (lCoord (bm ω)) x y) (dWinHi ε (lCoord (bm ω)) x y) ⊆ C := by
    rintro z ⟨t, ⟨htl, htr⟩, rfl⟩
    obtain ⟨a, ha, hat⟩ := exists_between htl
    obtain ⟨b, htb, hb⟩ := exists_between htr
    exact hCl a b ha hb (lt_trans hat htb) ⟨t, ⟨le_of_lt hat, le_of_lt htb⟩, rfl⟩
  have hright : (fun level => η ω (rhoMinus (bm ω) (ε * x) level)) ''
      Ioo (dWinLo ε (rCoord (bm ω)) x y) (dWinHi ε (rCoord (bm ω)) x y) ⊆ E := by
    rintro z ⟨t, ⟨htl, htr⟩, rfl⟩
    obtain ⟨a, ha, hat⟩ := exists_between htl
    obtain ⟨b, htb, hb⟩ := exists_between htr
    exact hEr a b ha hb (lt_trans hat htb) ⟨t, ⟨le_of_lt hat, le_of_lt htb⟩, rfl⟩
  have hsub : LatticeProb.nonSingletonComponents
      ((η ω) '' Icc (ε * ((x : ℝ) - 1)) (ε * x) ∩
        (η ω) '' Icc (ε * ((y : ℝ) - 1)) (ε * y)) ⊆ {C, E} := by
    intro A hA
    obtain ⟨z, hzA, hz⟩ := hmeet A hA
    rcases hz with hz | hz
    · have h := LatticeProb.components_eq_of_meets_subset hA.1 hC.1 hleft ⟨z, hzA, hz⟩
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff, h, true_or]
    · have h := LatticeProb.components_eq_of_meets_subset hA.1 hE.1 hright ⟨z, hzA, hz⟩
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff, h, or_true]
  have hcounts := LatticeProb.nonSingletonComponents_count_le_two_of_subset_pair _ C E hsub
  exact ⟨C, hC, E, hE, hCl, hEr, Set.Subset.antisymm hsub (Set.pair_subset hC hE), hcounts⟩

end MatedCRTHarmonic.MoTInput
