module

/-
Two-root forests, tree-copy deletion, and rerooting on the same original carrier.
The elementary constructions are adapted from the finite-avalanches development;
precise source paths and byte pins are recorded with the extraction.
-/
public import LatticeProb.Graph.CopiedGraph.Basic

@[expose] public section

namespace LatticeProb.Graph.CopiedGraph
open scoped Classical
noncomputable section
variable {V E : Type*}

/-- Every vertex belongs to exactly one of two rooted components; every copy is acyclic. -/
abbrev TwoRootForest (J : CopiedGraph V E) (u v : V) := {F : Finset E //
  (∀ e ∈ F, ¬J.reaches (F.erase e) (J.left e) (J.right e)) ∧
    ∀ x, ∃ r ∈ ({u, v} : Set V), J.reaches F x r ∧
      ∀ r' ∈ ({u, v} : Set V), J.reaches F x r' → r' = r}

/-- Distinct specified roots belong to different components. -/
theorem twoRootForest_roots_separated (J : CopiedGraph V E) (u v : V) (hne : u ≠ v)
    (F : J.TwoRootForest u v) : ¬J.reaches F.val u v := by
  intro h
  obtain ⟨r, _, _, hu⟩ := F.property.2 u
  exact hne ((hu u (Or.inl rfl) .refl).trans (hu v (Or.inr rfl) h).symm)

/-- Adding any original copy between the two components gives a full spanning tree. -/
theorem twoRootForest_insert_tree (J : CopiedGraph V E) (u v : V)
    (F : J.TwoRootForest u v) (e : E)
    (hsep : ¬J.reaches F.val (J.left e) (J.right e)) :
    (Set.univ : Set V).Nonempty ∧ (∀ x y, J.reaches (insert e F.val) x y) ∧
      ∀ f ∈ insert e F.val, ¬J.reaches ((insert e F.val).erase f) (J.left f) (J.right f) := by
  obtain ⟨r, hr, hl, _⟩ := F.property.2 (J.left e)
  obtain ⟨s, hs, ht, _⟩ := F.property.2 (J.right e)
  have hrs : r ≠ s := by
    intro heq
    exact hsep (hl.trans (heq ▸ reaches_symm J ht))
  have lift {x y : V} (h : J.reaches F.val x y) : J.reaches (insert e F.val) x y :=
    reaches_mono J (Finset.subset_insert _ _) h
  have hedge : J.reaches (insert e F.val) (J.left e) (J.right e) :=
    .single ⟨e, Finset.mem_insert_self _ _, Or.inl ⟨rfl, rfl⟩⟩
  have huv : J.reaches (insert e F.val) u v := by
    rcases hr with rfl | rfl <;> rcases hs with rfl | rfl
    · exact (hrs rfl).elim
    · exact ((reaches_symm J (lift hl)).trans hedge).trans (lift ht)
    · exact ((reaches_symm J (lift ht)).trans
        (reaches_symm J hedge)).trans (lift hl)
    · exact (hrs rfl).elim
  have cover (x : V) : J.reaches (insert e F.val) x u := by
    obtain ⟨r, hr, hx, _⟩ := F.property.2 x
    rcases hr with rfl | rfl
    · exact lift hx
    · exact (lift hx).trans (reaches_symm J huv)
  exact ⟨⟨u, Set.mem_univ _⟩,
    fun x y => (cover x).trans (reaches_symm J (cover y)),
    forest_insert J F.property.1 e hsep⟩

/-- Every vertex reaches one of the specified roots. -/
theorem twoRootForest_cover (J : CopiedGraph V E) (u v : V)
    (F : J.TwoRootForest u v) (x : V) : J.reaches F.val x u ∨ J.reaches F.val x v := by
  obtain ⟨r, hr, hx, _⟩ := F.property.2 x
  rcases hr with rfl | rfl
  · exact Or.inl hx
  · exact Or.inr hx

/-- Reachability is exactly equality of the component labeled by the first root. -/
theorem twoRootForest_reaches_iff (J : CopiedGraph V E) (u v : V)
    (F : J.TwoRootForest u v) (x y : V) :
    J.reaches F.val x y ↔ (J.reaches F.val x u ↔ J.reaches F.val y u) := by
  constructor
  · intro h
    exact ⟨fun hx => (reaches_symm J h).trans hx, fun hy => h.trans hy⟩
  · intro h
    by_cases hx : J.reaches F.val x u
    · exact hx.trans (reaches_symm J (h.mp hx))
    · have hy : ¬J.reaches F.val y u := fun hy => hx (h.mpr hy)
      exact ((twoRootForest_cover J u v F x).resolve_left hx).trans
        (reaches_symm J ((twoRootForest_cover J u v F y).resolve_left hy))


/-- Acyclicity, coverage by two roots, and separation give the exact rooted predicate. -/
theorem twoRootForest_of_cover (J : CopiedGraph V E) (A : Finset E) (u v : V)
    (ha : ∀ e ∈ A, ¬J.reaches (A.erase e) (J.left e) (J.right e))
    (hc : ∀ x, J.reaches A x u ∨ J.reaches A x v)
    (hs : ¬J.reaches A u v) :
    (∀ e ∈ A, ¬J.reaches (A.erase e) (J.left e) (J.right e)) ∧
      ∀ x, ∃ r ∈ ({u, v} : Set V), J.reaches A x r ∧
        ∀ r' ∈ ({u, v} : Set V), J.reaches A x r' → r' = r := by
  refine ⟨ha, ?_⟩
  intro x
  rcases hc x with hx | hx
  · refine ⟨u, Or.inl rfl, hx, ?_⟩
    intro r hr hxr
    rcases hr with rfl | rfl
    · rfl
    · exact (hs ((reaches_symm J hx).trans hxr)).elim
  · refine ⟨v, Or.inr rfl, hx, ?_⟩
    intro r hr hxr
    rcases hr with rfl | rfl
    · exact (hs ((reaches_symm J hxr).trans hx)).elim
    · rfl

/-- Deleting a selected copy leaves the two components rooted at its endpoints. -/
theorem tree_erase_twoRootForest (J : CopiedGraph V E) (T : J.SpanningTree)
    (e : E) (he : e ∈ T.val) :
    (∀ f ∈ T.val.erase e, ¬J.reaches ((T.val.erase e).erase f) (J.left f) (J.right f)) ∧
      ∀ x, ∃ r ∈ ({J.left e, J.right e} : Set V), J.reaches (T.val.erase e) x r ∧
        ∀ r' ∈ ({J.left e, J.right e} : Set V),
          J.reaches (T.val.erase e) x r' → r' = r := by
  apply twoRootForest_of_cover J _ _ _
  · intro f hf h
    apply T.property.2.2 f (Finset.mem_of_mem_erase hf)
    exact reaches_mono J (by
      intro a ha
      exact Finset.mem_erase.mpr ⟨(Finset.mem_erase.mp ha).1,
        Finset.mem_of_mem_erase (Finset.mem_of_mem_erase ha)⟩) h
  · intro x
    have h := T.property.2.1 (J.left e) x
    rw [← Finset.insert_erase he, reaches_insert_iff J] at h
    rcases h with h | ⟨_, h⟩ | ⟨h, _⟩
    · exact Or.inl (reaches_symm J h)
    · exact Or.inr (reaches_symm J h)
    · exact (T.property.2.2 e he h).elim
  · exact T.property.2.2 e he

/-- Two separated vertices can replace the roots of the same two components. -/
theorem twoRootForest_reroot (J : CopiedGraph V E) (a b u v : V)
    (F : J.TwoRootForest a b) (hs : ¬J.reaches F.val u v) :
    (∀ e ∈ F.val, ¬J.reaches (F.val.erase e) (J.left e) (J.right e)) ∧
      ∀ x, ∃ r ∈ ({u, v} : Set V), J.reaches F.val x r ∧
        ∀ r' ∈ ({u, v} : Set V), J.reaches F.val x r' → r' = r := by
  apply twoRootForest_of_cover J F.val u v F.property.1 _ hs
  intro x
  rcases twoRootForest_cover J a b F u with hu | hu <;>
    rcases twoRootForest_cover J a b F v with hv | hv
  · exact (hs (hu.trans (reaches_symm J hv))).elim
  · exact (twoRootForest_cover J a b F x).imp
      (fun hx => hx.trans (reaches_symm J hu))
      (fun hx => hx.trans (reaches_symm J hv))
  · exact (twoRootForest_cover J a b F x).symm.imp
      (fun hx => hx.trans (reaches_symm J hu))
      (fun hx => hx.trans (reaches_symm J hv))
  · exact (hs (hu.trans (reaches_symm J hv))).elim


end
end LatticeProb.Graph.CopiedGraph
