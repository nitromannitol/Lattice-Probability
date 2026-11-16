import LatticeProb.Bonanno.MatedCRTHarmonic.RouteM.PsiBundle

/-! # Crossing links in contour fibres -/

open Set

namespace MatedCRTHarmonic.RouteM

/-- A chain connecting opposite sides of a cut contains a generating link
crossing the cut and belonging to the same equivalence class. -/
theorem eqvGen_exists_crossing_link {α : Type*} {r : α → α → Prop} {s t : α}
    (h : Relation.EqvGen r s t) (A : Set α) (hs : s ∈ A) (ht : t ∉ A) :
    ∃ u v, r u v ∧ Relation.EqvGen r s u ∧
      ((u ∈ A ∧ v ∉ A) ∨ (v ∈ A ∧ u ∉ A)) := by
  classical
  have aux : ∀ {a b : α}, Relation.EqvGen r a b → ∀ A : Set α,
      ((a ∈ A ∧ b ∉ A) ∨ (b ∈ A ∧ a ∉ A)) →
      ∃ u v, r u v ∧ Relation.EqvGen r a u ∧
        ((u ∈ A ∧ v ∉ A) ∨ (v ∈ A ∧ u ∉ A)) := by
    intro a b hab
    induction hab with
    | rel a b hab =>
      intro A hcut
      exact ⟨a, b, hab, Relation.EqvGen.refl a, hcut⟩
    | refl a =>
      intro A hcut
      tauto
    | symm a b hab ih =>
      intro A hcut
      obtain ⟨u, v, huv, hau, hcross⟩ := ih A (by tauto)
      exact ⟨u, v, huv, Relation.EqvGen.trans _ _ _ (Relation.EqvGen.symm _ _ hab) hau,
        hcross⟩
    | trans a b c hab hbc ih₁ ih₂ =>
      intro A hcut
      by_cases hcut₁ : (a ∈ A ∧ b ∉ A) ∨ (b ∈ A ∧ a ∉ A)
      · exact ih₁ A hcut₁
      · obtain ⟨u, v, huv, hbu, hcross⟩ := ih₂ A (by tauto)
        exact ⟨u, v, huv, Relation.EqvGen.trans _ _ _ hab hbu, hcross⟩
  exact aux h A (Or.inl ⟨hs, ht⟩)

/-- A mating fibre crossing a time boundary contains a direct contour chord
crossing that boundary. -/
theorem Peanosphere.exists_direct_contact_crossing {ω : MatedCRT.Path2} {η : ℝ → ℂ}
    (P : Peanosphere ω η) {s t b : ℝ} (hst : η s = η t) (hs : s ≤ b) (ht : b < t) :
    ∃ u v, (directRel (lCoord ω) u v ∨ directRel (rCoord ω) u v) ∧
      η s = η u ∧ u ≤ b ∧ b < v := by
  obtain ⟨u, v, huv, hsu, hcross⟩ :=
    eqvGen_exists_crossing_link (P.onlyMerge s t hst) (Iic b) hs (not_le_of_gt ht)
  have huvlt : u < v := huv.elim (fun h => h.1) (fun h => h.1)
  have hcross' : u ≤ b ∧ b < v := by
    rcases hcross with h | h
    · exact ⟨h.1, lt_of_not_ge h.2⟩
    · exact False.elim ((not_le_of_gt huvlt) (le_trans h.1 (le_of_not_ge h.2)))
  exact ⟨u, v, huv, eta_eq_of_eqvGen P hsu, hcross'.1, hcross'.2⟩

end MatedCRTHarmonic.RouteM
