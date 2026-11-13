import LatticeProb.Analysis.ExcursionCountMonotone

/-!
# Rational witnesses for the excursion count

For a set `K ⊆ ℝ` and `ε > 0`, the excursion count `excursionCount K s t ε` (the number of connected components of
`[s, t] \ K` of diameter larger than `ε`) is at least `k` iff there are `k` closed intervals with rational end
points, each of length larger than `ε` and contained in `[s, t] \ K`, any two of them separated by a point of `K`
(`le_excursionCount_iff`).

The condition on the right involves countably many intervals only. For the ladder set of a continuous path it is
therefore a countable combination of conditions on the values of the path at rational times, which is how the
excursion count of a random continuous path is seen to be a random variable.
-/

open Set Metric

namespace LatticeProb.LadderSet

variable {K : Set ℝ} {s t ε : ℝ}

/-- A complementary interval of diameter larger than `ε` contains a closed interval with rational end points of
length larger than `ε`. -/
theorem exists_rat_Icc_subset_of_mem_complementaryIntervals {C : Set ℝ} (hC : C ∈ complementaryIntervals K s t)
    (hd : ε < diam C) : ∃ p q : ℚ, (p : ℝ) + ε < q ∧ Icc (p : ℝ) q ⊆ C := by
  have hbdd := isBounded_of_mem_complementaryIntervals hC
  have hIoo := (isConnected_of_mem_complementaryIntervals hC).Ioo_csInf_csSup_subset hbdd.bddBelow
    hbdd.bddAbove
  rw [Real.diam_eq hbdd] at hd
  obtain ⟨p, hp1, hp2⟩ := exists_rat_btwn (show sInf C < sInf C + (sSup C - sInf C - ε) / 3 by linarith)
  obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn (show sSup C - (sSup C - sInf C - ε) / 3 < sSup C by linarith)
  exact ⟨p, q, by linarith, fun x hx => hIoo ⟨by linarith [hx.1], by linarith [hx.2]⟩⟩

/-- Two different complementary intervals are separated by a point of `K`. -/
theorem exists_mem_Icc_of_mem_complementaryIntervals {C D : Set ℝ} (hC : C ∈ complementaryIntervals K s t)
    (hD : D ∈ complementaryIntervals K s t) (hne : C ≠ D) {p q : ℝ} (hp : p ∈ C) (hq : q ∈ D) (hpq : p ≤ q) :
    ∃ x ∈ K, p ≤ x ∧ x ≤ q := by
  by_contra h
  push Not at h
  have hpF := subset_of_mem_complementaryIntervals hC hp
  have hqF := subset_of_mem_complementaryIntervals hD hq
  have hsub : Icc p q ⊆ Icc s t \ K := fun x hx =>
    ⟨⟨hpF.1.1.trans hx.1, hx.2.trans hqF.1.2⟩, fun hxK => absurd hx.2 (not_le.2 (h x hxK hx.1))⟩
  have hqC : q ∈ C := by
    obtain ⟨x, -, rfl⟩ := hC
    rw [connectedComponentIn_eq hp]
    exact isPreconnected_Icc.subset_connectedComponentIn (left_mem_Icc.2 hpq) hsub (right_mem_Icc.2 hpq)
  exact hne (eq_of_mem_complementaryIntervals hC hD hqC hq)

/-- **Rational witnesses for the excursion count.** For `ε > 0`, at least `k` complementary intervals of `K` in
`[s, t]` have diameter larger than `ε` iff there are `k` closed intervals `[r j, u j]` with rational end points, of
length larger than `ε` and contained in `[s, t] \ K`, any two of them separated by a point of `K`. -/
theorem le_excursionCount_iff (hε : 0 < ε) (k : ℕ) :
    k ≤ excursionCount K s t ε ↔ ∃ r u : Fin k → ℚ,
      (∀ j, s ≤ r j ∧ (r j : ℝ) + ε < u j ∧ (u j : ℝ) ≤ t ∧ ∀ x ∈ Icc (r j : ℝ) (u j), x ∉ K) ∧
      ∀ i j, i ≠ j → ∃ x ∈ K, ((u i : ℝ) ≤ x ∧ x ≤ r j) ∨ ((u j : ℝ) ≤ x ∧ x ≤ r i) := by
  have hS : {C ∈ complementaryIntervals K s t | ε < diam C}.Finite := finite_setOf_lt_diam K s t hε
  constructor
  · intro hk
    have := hS.to_subtype
    have hk' : k ≤ Nat.card {C ∈ complementaryIntervals K s t | ε < diam C} := by
      rw [Nat.card_coe_set_eq]
      exact hk
    let f : Fin k → {C ∈ complementaryIntervals K s t | ε < diam C} := fun j =>
      (Finite.equivFin _).symm (Fin.castLE hk' j)
    have hf : Function.Injective f := (Finite.equivFin _).symm.injective.comp (Fin.castLE_injective hk')
    have hCf : ∀ j, (f j : Set ℝ) ∈ complementaryIntervals K s t := fun j => (Set.mem_sep_iff.1 (f j).2).1
    have hwit : ∀ j, ∃ p q : ℚ, (p : ℝ) + ε < q ∧ Icc (p : ℝ) q ⊆ (f j : Set ℝ) := fun j =>
      exists_rat_Icc_subset_of_mem_complementaryIntervals (hCf j) (Set.mem_sep_iff.1 (f j).2).2
    choose r u hru hsub using hwit
    have hle : ∀ j, (r j : ℝ) ≤ u j := fun j => by linarith [hru j]
    refine ⟨r, u, fun j => ?_, fun i j hij => ?_⟩
    · have hsub' := (hsub j).trans (subset_of_mem_complementaryIntervals (hCf j))
      have hr := hsub' (left_mem_Icc.2 (hle j))
      have hu := hsub' (right_mem_Icc.2 (hle j))
      exact ⟨hr.1.1, hru j, hu.1.2, fun x hx => (hsub' hx).2⟩
    · have hne : (f i : Set ℝ) ≠ f j := fun h => hij (hf (Subtype.ext h))
      rcases lt_or_ge (u i : ℝ) (r j) with h1 | h1
      · obtain ⟨x, hxK, hx1, hx2⟩ := exists_mem_Icc_of_mem_complementaryIntervals (hCf i) (hCf j) hne
          (hsub i (right_mem_Icc.2 (hle i))) (hsub j (left_mem_Icc.2 (hle j))) h1.le
        exact ⟨x, hxK, Or.inl ⟨hx1, hx2⟩⟩
      rcases lt_or_ge (u j : ℝ) (r i) with h2 | h2
      · obtain ⟨x, hxK, hx1, hx2⟩ := exists_mem_Icc_of_mem_complementaryIntervals (hCf j) (hCf i) hne.symm
          (hsub j (right_mem_Icc.2 (hle j))) (hsub i (left_mem_Icc.2 (hle i))) h2.le
        exact ⟨x, hxK, Or.inr ⟨hx1, hx2⟩⟩
      · exact absurd (eq_of_mem_complementaryIntervals (hCf i) (hCf j) (y := max (r i : ℝ) (r j))
          (hsub i ⟨le_max_left _ _, max_le (hle i) h1⟩) (hsub j ⟨le_max_right _ _, max_le h2 (hle j)⟩)) hne
  · rintro ⟨r, u, hI, hsep⟩
    have hle : ∀ j, (r j : ℝ) ≤ u j := fun j => by linarith [(hI j).2.1]
    have hsubF : ∀ j, Icc (r j : ℝ) (u j) ⊆ Icc s t \ K := fun j x hx =>
      ⟨⟨(hI j).1.trans hx.1, hx.2.trans (hI j).2.2.1⟩, (hI j).2.2.2 x hx⟩
    have hsubC : ∀ j, Icc (r j : ℝ) (u j) ⊆ connectedComponentIn (Icc s t \ K) (r j) := fun j =>
      isPreconnected_Icc.subset_connectedComponentIn (left_mem_Icc.2 (hle j)) (hsubF j)
    have hmem : ∀ j, connectedComponentIn (Icc s t \ K) (r j) ∈ complementaryIntervals K s t := fun j =>
      ⟨r j, hsubF j (left_mem_Icc.2 (hle j)), rfl⟩
    have hdiam : ∀ j, ε < diam (connectedComponentIn (Icc s t \ K) (r j)) := fun j => by
      have h1 := diam_mono (hsubC j) (isBounded_of_mem_complementaryIntervals (hmem j))
      rw [Real.diam_Icc (hle j)] at h1
      linarith [(hI j).2.1]
    have hinj : Function.Injective fun j => connectedComponentIn (Icc s t \ K) (r j) := by
      intro i j hij
      by_contra hne
      have hij' : connectedComponentIn (Icc s t \ K) (r i) = connectedComponentIn (Icc s t \ K) (r j) := hij
      obtain ⟨x, hxK, hx | hx⟩ := hsep i j hne
      · have hrj : (r j : ℝ) ∈ connectedComponentIn (Icc s t \ K) (r i) := by
          rw [hij']
          exact hsubC j (left_mem_Icc.2 (hle j))
        have hx' := isPreconnected_connectedComponentIn.Icc_subset (hsubC i (right_mem_Icc.2 (hle i))) hrj hx
        exact (connectedComponentIn_subset _ _ hx').2 hxK
      · have hri : (r i : ℝ) ∈ connectedComponentIn (Icc s t \ K) (r j) := by
          rw [← hij']
          exact hsubC i (left_mem_Icc.2 (hle i))
        have hx' := isPreconnected_connectedComponentIn.Icc_subset (hsubC j (right_mem_Icc.2 (hle j))) hri hx
        exact (connectedComponentIn_subset _ _ hx').2 hxK
    have hcard := Set.ncard_le_ncard_of_injOn (fun j => connectedComponentIn (Icc s t \ K) (r j))
      (s := (univ : Set (Fin k))) (t := {C ∈ complementaryIntervals K s t | ε < diam C})
      (fun j _ => ⟨hmem j, hdiam j⟩) hinj.injOn hS
    rw [Set.ncard_univ, Nat.card_eq_fintype_card, Fintype.card_fin] at hcard
    exact hcard

end LatticeProb.LadderSet
