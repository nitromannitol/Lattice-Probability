module

/-
# Cardinality of rooted copied forests

Every selected copy in a forest separates its endpoints when erased. A root set
selects exactly one vertex of every component, including isolated vertices.
The ambient graph may contain loops and parallel copies.
-/

public import LatticeProb.Graph.CopiedGraph.Basic
public import Mathlib.Data.Finset.Card
public import Mathlib.Data.Fintype.Card

@[expose] public section



namespace LatticeProb.Graph.CopiedGraph
open scoped Classical
noncomputable section
variable {V E : Type*}

/-- Every selected original copy disconnects its endpoints when erased. -/
def IsForest (J : CopiedGraph V E) (F : Finset E) : Prop :=
  ∀ e ∈ F, ¬J.reaches (F.erase e) (J.left e) (J.right e)

/-- An acyclic copied edge set with exactly one supplied root in each component,
including isolated vertices. -/
def IsRootedForest (J : CopiedGraph V E) (R : Set V) (F : Finset E) : Prop :=
  J.IsForest F ∧ ∀ x, ∃ r ∈ R, J.reaches F x r ∧
    ∀ r' ∈ R, J.reaches F x r' → r' = r

private theorem reaches_empty_iff (J : CopiedGraph V E) (x y : V) :
    J.reaches ∅ x y ↔ x = y := by
  constructor
  · intro h
    induction h with
    | refl => rfl
    | tail _ h _ => exact (Finset.notMem_empty h.choose h.choose_spec.1).elim
  · rintro rfl
    exact .refl

private theorem isForest_mono (J : CopiedGraph V E) {F H : Finset E}
    (hFH : F ⊆ H) (hH : J.IsForest H) : J.IsForest F := by
  intro e he h
  apply hH e (hFH he)
  exact J.reaches_mono (by
    intro f hf
    exact Finset.mem_erase.mpr ⟨(Finset.mem_erase.mp hf).1,
      hFH (Finset.mem_of_mem_erase hf)⟩) h

private theorem rooted_after_erase_right (J : CopiedGraph V E) (R : Finset V)
    (F : Finset E) (hF : J.IsRootedForest (R : Set V) F)
    (e : E) (he : e ∈ F) (r : V) (hr : r ∈ R)
    (hur : J.reaches (F.erase e) (J.left e) r) :
    J.right e ∉ R ∧
      J.IsRootedForest ((insert (J.right e) R : Finset V) : Set V) (F.erase e) := by
  have sep := hF.1 e he
  have lift {x y : V} (h : J.reaches (F.erase e) x y) : J.reaches F x y :=
    J.reaches_mono (Finset.erase_subset _ _) h
  have step : J.reaches F (J.left e) (J.right e) :=
    .single ⟨e, he, Or.inl ⟨rfl, rfl⟩⟩
  have unique {x a b : V} (ha : a ∈ R) (hb : b ∈ R)
      (hxa : J.reaches F x a) (hxb : J.reaches F x b) : a = b := by
    obtain ⟨q, _, _, hq⟩ := hF.2 x
    exact (hq a ha hxa).trans (hq b hb hxb).symm
  have no_right_root (s : V) (hs : s ∈ R) :
      ¬J.reaches (F.erase e) (J.right e) s := by
    intro hvs
    have hsr : s = r := unique hs hr (step.trans (lift hvs)) (lift hur)
    exact sep (hur.trans (J.reaches_symm (hsr ▸ hvs)))
  have hv : J.right e ∉ R := fun hv => no_right_root _ hv .refl
  refine ⟨hv, isForest_mono J (Finset.erase_subset _ _) hF.1, ?_⟩
  intro x
  obtain ⟨s, hs, hxs, _⟩ := hF.2 x
  rw [← Finset.insert_erase he, J.reaches_insert_iff] at hxs
  have cover : (∃ s ∈ R, J.reaches (F.erase e) x s) ∨
      J.reaches (F.erase e) x (J.right e) := by
    rcases hxs with hxs | ⟨_, hvs⟩ | ⟨hxv, _⟩
    · exact Or.inl ⟨s, hs, hxs⟩
    · exact (no_right_root s hs hvs).elim
    · exact Or.inr hxv
  rcases cover with ⟨s, hs, hxs⟩ | hxv
  · refine ⟨s, Finset.mem_insert_of_mem hs, hxs, ?_⟩
    intro t ht hxt
    rcases Finset.mem_insert.mp ht with rfl | ht
    · exact (no_right_root s hs ((J.reaches_symm hxt).trans hxs)).elim
    · exact unique ht hs (lift hxt) (lift hxs)
  · refine ⟨J.right e, Finset.mem_insert_self _ _, hxv, ?_⟩
    intro t ht hxt
    rcases Finset.mem_insert.mp ht with rfl | ht
    · rfl
    · exact (no_right_root t ht ((J.reaches_symm hxv).trans hxt)).elim

private theorem exists_root_after_erase
    (J : CopiedGraph V E) (R : Finset V) (F : Finset E)
    (hF : J.IsRootedForest (R : Set V) F) (e : E) (he : e ∈ F) :
    ∃ v, v ∉ R ∧ (v = J.left e ∨ v = J.right e) ∧
      J.IsRootedForest ((insert v R : Finset V) : Set V) (F.erase e) := by
  obtain ⟨r, hr, hur, _⟩ := hF.2 (J.left e)
  rw [← Finset.insert_erase he, J.reaches_insert_iff] at hur
  have orient : J.reaches (F.erase e) (J.left e) r ∨
      J.reaches (F.erase e) (J.right e) r := by
    rcases hur with hur | ⟨_, hvr⟩ | ⟨huv, _⟩
    · exact Or.inl hur
    · exact Or.inr hvr
    · exact (hF.1 e he huv).elim
  rcases orient with hur | hvr
  · obtain ⟨hv, hroot⟩ := rooted_after_erase_right J R F hF e he r hr hur
    exact ⟨J.right e, hv, Or.inr rfl, hroot⟩
  · let K : CopiedGraph V E := ⟨J.right, J.left⟩
    have reach (A : Finset E) : K.reaches A = J.reaches A := by
      simp only [reaches, K, or_comm]
    have hK : K.IsRootedForest (R : Set V) F := by
      refine ⟨?_, ?_⟩
      · intro f hf h
        change K.reaches (F.erase f) (J.right f) (J.left f) at h
        rw [reach] at h
        exact hF.1 f hf (J.reaches_symm h)
      · simpa only [reach] using hF.2
    have hvrK : K.reaches (F.erase e) (K.left e) r := by
      change K.reaches (F.erase e) (J.right e) r
      rw [reach]
      exact hvr
    obtain ⟨hu, hroot⟩ := rooted_after_erase_right K R F hK e he r hr hvrK
    refine ⟨J.left e, hu, Or.inl rfl, ?_, ?_⟩
    · intro f hf h
      apply hroot.1 f hf
      change K.reaches ((F.erase e).erase f) (J.right f) (J.left f)
      rw [reach]
      exact J.reaches_symm h
    · simpa only [reach] using hroot.2

/-- **Rooted forest cardinality.** A rooted copied forest has one fewer selected copy than vertices per root. -/
theorem IsRootedForest.card_add_card_roots [Fintype V]
    {J : CopiedGraph V E} {R : Finset V} {F : Finset E}
    (hF : J.IsRootedForest (R : Set V) F) :
    F.card + R.card = Fintype.card V := by
  induction F using Finset.induction_on generalizing R with
  | empty =>
    have hR : R = Finset.univ := Finset.eq_univ_iff_forall.mpr (fun x => by
      obtain ⟨r, hr, hxr, _⟩ := hF.2 x
      have hxr' := (reaches_empty_iff J x r).mp hxr
      exact hxr' ▸ hr)
    simp only [Finset.card_empty, hR, Finset.card_univ, Nat.zero_add]
  | @insert e F he ih =>
    obtain ⟨v, hv, _, hroot⟩ := exists_root_after_erase J R (insert e F) hF e
      (Finset.mem_insert_self _ _)
    rw [Finset.erase_insert he] at hroot
    have hcard := ih hroot
    rw [Finset.card_insert_of_notMem hv] at hcard
    rw [Finset.card_insert_of_notMem he]
    simpa only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hcard

end
end LatticeProb.Graph.CopiedGraph
