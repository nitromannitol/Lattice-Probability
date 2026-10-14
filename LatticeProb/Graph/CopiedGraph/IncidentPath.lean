/- Elementary incident-copy path lemmas adapted from the finite-avalanche proof.
The exact source pins and namespace adaptations are retained in EXTRACTION.json. -/
import LatticeProb.Graph.CopiedGraph.TwoRootForest

namespace LatticeProb.Graph.CopiedGraph
open scoped Classical
noncomputable section
variable {V E : Type*}

/-- A walk in a component avoiding a vertex avoids each edge incident to that vertex. -/
theorem reaches_erase_incident_of_not_reaches (J : CopiedGraph V E)
    (A : Finset E) (p x y : V) (f : E)
    (hf : J.left f = p ∨ J.right f = p) (hx : ¬J.reaches A x p)
    (h : J.reaches A x y) : J.reaches (A.erase f) x y := by
  induction h with
  | refl => exact .refl
  | @tail z y hprev hadj ih =>
    obtain ⟨e, he, hends⟩ := hadj
    have hef : e ≠ f := by
      intro heq
      subst e
      have hwhole := hprev.tail ⟨f, he, hends⟩
      rcases hf with hfp | hfp <;> rcases hends with hh | hh
      · exact hx ((hh.1.symm.trans hfp) ▸ hprev)
      · exact hx ((hh.2.symm.trans hfp) ▸ hwhole)
      · exact hx ((hh.2.symm.trans hfp) ▸ hwhole)
      · exact hx ((hh.1.symm.trans hfp) ▸ hprev)
    exact ih.tail ⟨e, Finset.mem_erase.mpr ⟨hef, he⟩, hends⟩

/-- Two selected edges at the first vertex cannot both separate the same tree path. -/
theorem tree_path_incident_unique (J : CopiedGraph V E) (T : J.SpanningTree)
    (p q : V) (e f : E) (he : e ∈ T.val)
    (hep : J.left e = p ∨ J.right e = p)
    (hfp : J.left f = p ∨ J.right f = p)
    (hecut : ¬J.reaches (T.val.erase e) p q)
    (hfcut : ¬J.reaches (T.val.erase f) p q) : e = f := by
  by_contra hef
  have monotone {x y : V} (h : J.reaches ((T.val.erase e).erase f) x y) :
      J.reaches (T.val.erase f) x y :=
    J.reaches_mono (by
      intro a ha
      exact Finset.mem_erase.mpr ⟨(Finset.mem_erase.mp ha).1,
        Finset.mem_of_mem_erase (Finset.mem_of_mem_erase ha)⟩) h
  have conn := T.property.2.1 p q
  rw [← Finset.insert_erase he, J.reaches_insert_iff] at conn
  have heF : e ∈ T.val.erase f := Finset.mem_erase.mpr ⟨hef, he⟩
  rcases hep with hep | hep
  · have hother : J.reaches (T.val.erase e) (J.right e) q := by
      rcases conn with h | ⟨_, h⟩ | ⟨h, _⟩
      · exact (hecut h).elim
      · exact h
      · exfalso
        apply T.property.2.2 e he
        rwa [hep]
    have hotherp : ¬J.reaches (T.val.erase e) (J.right e) p := by
      intro h
      apply T.property.2.2 e he
      rw [hep]
      exact J.reaches_symm h
    have havoid := reaches_erase_incident_of_not_reaches J (T.val.erase e)
      p (J.right e) q f hfp hotherp hother
    have hedge : J.reaches (T.val.erase f) p (J.right e) :=
      .single ⟨e, heF, Or.inl ⟨hep, rfl⟩⟩
    exact hfcut (hedge.trans (monotone havoid))
  · have hother : J.reaches (T.val.erase e) (J.left e) q := by
      rcases conn with h | ⟨h, _⟩ | ⟨_, h⟩
      · exact (hecut h).elim
      · exfalso
        apply T.property.2.2 e he
        rw [hep]
        exact J.reaches_symm h
      · exact h
    have hotherp : ¬J.reaches (T.val.erase e) (J.left e) p := by
      intro h
      apply T.property.2.2 e he
      rwa [hep]
    have havoid := reaches_erase_incident_of_not_reaches J (T.val.erase e)
      p (J.left e) q f hfp hotherp hother
    have hedge : J.reaches (T.val.erase f) p (J.left e) :=
      .single ⟨e, heF, Or.inr ⟨hep, rfl⟩⟩
    exact hfcut (hedge.trans (monotone havoid))


/-- Every nontrivial forest path has an incident selected copy whose deletion separates it. -/
theorem forest_path_incident_exists (J : CopiedGraph V E) (A : Finset E)
    (ha : ∀ e ∈ A, ¬J.reaches (A.erase e) (J.left e) (J.right e))
    (p q : V) (hne : p ≠ q) (h : J.reaches A p q) :
    ∃ e ∈ A, (J.left e = p ∨ J.right e = p) ∧ ¬J.reaches (A.erase e) p q := by
  have claim : ∀ {q : V}, J.reaches A p q →
      q = p ∨ ∃ e ∈ A, (J.left e = p ∨ J.right e = p) ∧
        ¬J.reaches (A.erase e) p q := by
    intro q h
    induction h with
    | refl => exact Or.inl rfl
    | @tail z y _ hadj ih =>
      obtain ⟨f, hf, hends⟩ := hadj
      by_cases hyp : y = p
      · exact Or.inl hyp
      · apply Or.inr
        rcases ih with rfl | ⟨e, he, hep, hcut⟩
        · refine ⟨f, hf, ?_, ?_⟩
          · exact hends.elim (fun h => Or.inl h.1) (fun h => Or.inr h.1)
          · intro h
            apply ha f hf
            rcases hends with ⟨hl, hr⟩ | ⟨hr, hl⟩
            · exact hl ▸ hr ▸ h
            · exact hl ▸ hr ▸ J.reaches_symm h
        · by_cases hfe : f = e
          · subst f
            rcases hep with hep | hep <;> rcases hends with hh | hh
            · exact (hcut (hh.1.symm.trans hep ▸ Relation.ReflTransGen.refl)).elim
            · exact (hyp (hh.2.symm.trans hep)).elim
            · exact (hyp (hh.2.symm.trans hep)).elim
            · exact (hcut (hh.1.symm.trans hep ▸ Relation.ReflTransGen.refl)).elim
          · refine ⟨e, he, hep, ?_⟩
            intro hpy
            have hzy : J.reaches (A.erase e) z y :=
              .single ⟨f, Finset.mem_erase.mpr ⟨hfe, hf⟩, hends⟩
            exact hcut (hpy.trans (J.reaches_symm hzy))
  exact (claim h).resolve_left (Ne.symm hne)


end
end LatticeProb.Graph.CopiedGraph
