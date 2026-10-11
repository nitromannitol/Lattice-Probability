/-
Deleting a specified original copy from a tree path and inserting that same copy
are inverse constructions. The elementary forest lemmas used here were adapted
from finite-avalanches; precise source pins accompany the extraction.
-/
import LatticeProb.Graph.CopiedGraph.TwoRootForest

namespace LatticeProb.Graph.CopiedGraph
open scoped Classical
noncomputable section
variable {V E : Type*}

/-- Deleting the specified copy identifies trees in which that copy separates the
terminals with two-root forests whose components it joins. Both directions retain
all original vertex and edge-copy IDs. -/
def treeCutEquiv (J : CopiedGraph V E) (u v : V) (hu : u ≠ v) (e : E) :
    {T : J.SpanningTree // e ∈ T.val ∧ ¬J.reaches (T.val.erase e) u v} ≃
      {F : J.TwoRootForest u v // ¬J.reaches F.val (J.left e) (J.right e)} where
  toFun T :=
    ⟨⟨T.val.val.erase e,
      twoRootForest_reroot J (J.left e) (J.right e) u v
        ⟨T.val.val.erase e, tree_erase_twoRootForest J T.val e T.property.1⟩
        T.property.2⟩,
      T.val.property.2.2 e T.property.1⟩
  invFun F := by
    have he : e ∉ F.val.val := fun he =>
      F.property (.single ⟨e, he, Or.inl ⟨rfl, rfl⟩⟩)
    exact ⟨⟨insert e F.val.val, twoRootForest_insert_tree J u v F.val e F.property⟩,
      Finset.mem_insert_self _ _, by
        simpa only [Finset.erase_insert he] using twoRootForest_roots_separated J u v hu F.val⟩
  left_inv T := by
    apply Subtype.ext
    apply Subtype.ext
    exact Finset.insert_erase T.property.1
  right_inv F := by
    have he : e ∉ F.val.val := fun he =>
      F.property (.single ⟨e, he, Or.inl ⟨rfl, rfl⟩⟩)
    apply Subtype.ext
    apply Subtype.ext
    exact Finset.erase_insert he

/-- The forward map erases exactly the specified original copy. -/
@[simp] theorem treeCutEquiv_apply_val (J : CopiedGraph V E) (u v : V)
    (hu : u ≠ v) (e : E)
    (T : {T : J.SpanningTree // e ∈ T.val ∧ ¬J.reaches (T.val.erase e) u v}) :
    (treeCutEquiv J u v hu e T).val.val = T.val.val.erase e := rfl

/-- The inverse map inserts exactly the same specified original copy. -/
@[simp] theorem treeCutEquiv_symm_apply_val (J : CopiedGraph V E) (u v : V)
    (hu : u ≠ v) (e : E)
    (F : {F : J.TwoRootForest u v // ¬J.reaches F.val (J.left e) (J.right e)}) :
    ((treeCutEquiv J u v hu e).symm F).val.val = insert e F.val.val := rfl

end
end LatticeProb.Graph.CopiedGraph
