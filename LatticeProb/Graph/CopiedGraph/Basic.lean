module

/-
Finite graphs with individually indexed edge copies, including loops and parallel copies.
The walk and insertion proofs are adapted from the finite-avalanches development;
precise source paths and byte pins are recorded with the extraction.
-/
public import Mathlib.Logic.Relation
public import Mathlib.Data.Finset.Erase
public import Mathlib.Data.Finset.Insert
public import Mathlib.Data.Fintype.Powerset

@[expose] public section

namespace LatticeProb.Graph

/-- An undirected graph specified by two endpoint maps on its original edge-copy carrier.
No looplessness or injectivity condition is imposed on the endpoints. -/
structure CopiedGraph (V E : Type*) where
  left : E → V
  right : E → V

namespace CopiedGraph
open scoped Classical
noncomputable section
variable {V E : Type*}

/-- Finite copied-walk reachability, including the walk of length zero. -/
def reaches (J : CopiedGraph V E) (A : Finset E) : V → V → Prop :=
  Relation.ReflTransGen (fun x y => ∃ e ∈ A,
    (J.left e = x ∧ J.right e = y) ∨ (J.right e = x ∧ J.left e = y))

/-- A spanning tree on the full nonempty vertex carrier, retaining the original copies. -/
abbrev SpanningTree (J : CopiedGraph V E) := {A : Finset E //
  (Set.univ : Set V).Nonempty ∧ (∀ x y, J.reaches A x y) ∧
    ∀ e ∈ A, ¬J.reaches (A.erase e) (J.left e) (J.right e)}

/-- A loop is excluded by the deletion criterion for a spanning tree. -/
theorem loop_not_mem (J : CopiedGraph V E) (T : J.SpanningTree)
    (e : E) (hloop : J.left e = J.right e) : e ∉ T.val := by
  intro he
  apply T.property.2.2 e he
  rw [hloop]
  exact Relation.ReflTransGen.refl

variable (J : CopiedGraph V E)

/-- Every copied walk can be traversed in reverse. -/
theorem reaches_symm {F : Finset E} {x y : V} (h : J.reaches F x y) :
    J.reaches F y x := by
  induction h with
  | refl => exact .refl
  | @tail y z _ hyz ih =>
    obtain ⟨e,he,hh⟩ := hyz
    exact Relation.ReflTransGen.head ⟨e,he,hh.elim
      (fun h => Or.inr ⟨h.2,h.1⟩) (fun h => Or.inl ⟨h.2,h.1⟩)⟩ ih

/-- Adding available copies preserves reachability. -/
theorem reaches_mono {F H : Finset E} (hFH : F ⊆ H) {x y : V}
    (h : J.reaches F x y) : J.reaches H x y := by
  induction h with
  | refl => exact .refl
  | tail _ h ih => exact ih.tail ⟨h.choose,hFH h.choose_spec.1,h.choose_spec.2⟩

/-- An inserted copy joins its endpoint components in either orientation. -/
theorem reaches_insert_iff (F : Finset E) (e : E) (x y : V) :
    J.reaches (insert e F) x y ↔ J.reaches F x y ∨
      (J.reaches F x (J.left e) ∧ J.reaches F (J.right e) y) ∨
      (J.reaches F x (J.right e) ∧ J.reaches F (J.left e) y) := by
  constructor
  · intro h
    induction h with
    | refl => exact Or.inl .refl
    | @tail z y _ h ih =>
      obtain ⟨f,hf,hends⟩ := h
      rcases Finset.mem_insert.mp hf with rfl | hf
      · rcases hends with hends | hends
        · rw [← hends.1] at ih
          rw [← hends.2]
          rcases ih with h | ⟨h,_⟩ | ⟨h,_⟩
          · exact Or.inr (Or.inl ⟨h,.refl⟩)
          · exact Or.inr (Or.inl ⟨h,.refl⟩)
          · exact Or.inl h
        · rw [← hends.1] at ih
          rw [← hends.2]
          rcases ih with h | ⟨h,_⟩ | ⟨h,_⟩
          · exact Or.inr (Or.inr ⟨h,.refl⟩)
          · exact Or.inl h
          · exact Or.inr (Or.inr ⟨h,.refl⟩)
      · have hs : J.reaches F z y := .single ⟨f,hf,hends⟩
        exact ih.imp (fun h => h.trans hs)
          (fun h => h.imp (fun h => ⟨h.1,h.2.trans hs⟩) (fun h => ⟨h.1,h.2.trans hs⟩))
  · intro h
    have mono {z w : V} (h : J.reaches F z w) : J.reaches (insert e F) z w :=
      reaches_mono J (Finset.subset_insert _ _) h
    have step : J.reaches (insert e F) (J.left e) (J.right e) :=
      .single ⟨e,Finset.mem_insert_self _ _,Or.inl ⟨rfl,rfl⟩⟩
    rcases h with h | ⟨h,k⟩ | ⟨h,k⟩
    · exact mono h
    · exact ((mono h).trans step).trans (mono k)
    · exact ((mono h).trans (reaches_symm J step)).trans (mono k)

/-- Adding a copy between distinct components preserves acyclicity. -/
theorem forest_insert {F : Finset E}
    (hF : ∀ f ∈ F, ¬J.reaches (F.erase f) (J.left f) (J.right f))
    (e : E) (hsep : ¬J.reaches F (J.left e) (J.right e)) :
    ∀ f ∈ insert e F, ¬J.reaches ((insert e F).erase f) (J.left f) (J.right f) := by
  have he : e ∉ F := fun he => hsep (.single ⟨e,he,Or.inl ⟨rfl,rfl⟩⟩)
  intro f hf h
  by_cases hfe : f = e
  · subst f
    exact hsep (by simpa [he] using h)
  · have hfF := (Finset.mem_insert.mp hf).resolve_left hfe
    have h' : J.reaches (insert e (F.erase f)) (J.left f) (J.right f) := by
      simpa only [Finset.erase_insert_of_ne (Ne.symm hfe)] using h
    have mono {x y : V} (h : J.reaches (F.erase f) x y) : J.reaches F x y :=
      reaches_mono J (Finset.erase_subset _ _) h
    have step : J.reaches F (J.left f) (J.right f) :=
      .single ⟨f,hfF,Or.inl ⟨rfl,rfl⟩⟩
    rcases (reaches_insert_iff J _ _ _ _).mp h' with h' | ⟨ha,hb⟩ | ⟨hb,ha⟩
    · exact hF f hfF h'
    · exact hsep (((reaches_symm J (mono ha)).trans step).trans (reaches_symm J (mono hb)))
    · exact hsep (reaches_symm J
        (((reaches_symm J (mono hb)).trans step).trans (reaches_symm J (mono ha))))


end
end CopiedGraph
end LatticeProb.Graph
