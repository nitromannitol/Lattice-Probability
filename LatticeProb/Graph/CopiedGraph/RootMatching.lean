module

/-
The unique component correspondence between root sets of the same copied forest.
-/

public import LatticeProb.Graph.CopiedGraph.RootedForest
public import Mathlib.Logic.Equiv.Defs

@[expose] public section



namespace LatticeProb.Graph.CopiedGraph
open scoped Classical
noncomputable section
variable {V E : Type*} {J : CopiedGraph V E} {R S : Set V} {F : Finset E}

/-- Two supplied roots in the same component of a rooted forest are equal. -/
theorem IsRootedForest.eq_of_reaches
    (hR : J.IsRootedForest R F) {r s : R}
    (hrs : J.reaches F r.val s.val) : r = s := by
  apply Subtype.ext
  obtain ⟨q, hq, _, hu⟩ := hR.2 r.val
  exact (hu r.val r.property .refl).trans (hu s.val s.property hrs).symm

/-- Two root sets of the same copied forest have a unique reachability-preserving equivalence. -/
theorem IsRootedForest.existsUnique_rootEquiv
    (hR : J.IsRootedForest R F) (hS : J.IsRootedForest S F) :
    ∃! e : R ≃ S, ∀ r : R, J.reaches F r.val (e r).val := by
  choose f hf hreachf _ using hS.2
  choose g hg hreachg _ using hR.2
  let e : R ≃ S :=
    { toFun := fun r => ⟨f r.val, hf r.val⟩
      invFun := fun s => ⟨g s.val, hg s.val⟩
      left_inv := fun r => hR.eq_of_reaches
        (J.reaches_symm ((hreachf r.val).trans (hreachg (f r.val))))
      right_inv := fun s => hS.eq_of_reaches
        (J.reaches_symm ((hreachg s.val).trans (hreachf (g s.val)))) }
  refine ⟨e, fun r => hreachf r.val, ?_⟩
  intro e' he'
  apply Equiv.ext
  intro r
  exact hS.eq_of_reaches ((J.reaches_symm (he' r)).trans (hreachf r.val))

/-- A reachability-preserving root equivalence supplies exactly one new root per component. -/
theorem IsRootedForest.of_rootEquiv
    (hR : J.IsRootedForest R F) (e : R ≃ S)
    (he : ∀ r : R, J.reaches F r.val (e r).val) :
    J.IsRootedForest S F := by
  refine ⟨hR.1, ?_⟩
  intro x
  obtain ⟨r, hr, hxr, hu⟩ := hR.2 x
  let r' : R := ⟨r, hr⟩
  refine ⟨(e r').val, (e r').property, hxr.trans (he r'), ?_⟩
  intro s hs hxs
  let s' : S := ⟨s, hs⟩
  have hxsR : J.reaches F x (e.symm s').val := by
    apply hxs.trans
    apply J.reaches_symm
    simpa only [e.apply_symm_apply] using he (e.symm s')
  have hrEq : e.symm s' = r' :=
    Subtype.ext (hu (e.symm s').val (e.symm s').property hxsR)
  exact congrArg Subtype.val ((e.apply_symm_apply s').symm.trans (congrArg e hrEq))

/-- Rootedness at a second set is equivalent to a unique component root correspondence. -/
theorem IsRootedForest.iff_existsUnique_rootEquiv
    (hR : J.IsRootedForest R F) :
    J.IsRootedForest S F ↔
      ∃! e : R ≃ S, ∀ r : R, J.reaches F r.val (e r).val := by
  constructor
  · exact hR.existsUnique_rootEquiv
  · rintro ⟨e, he, _⟩
    exact hR.of_rootEquiv e he

/-- **Root matching.** Enumerating both root sets on a common carrier turns component matching into a unique permutation. -/
theorem IsRootedForest.iff_existsUnique_perm {ι : Type*}
    (hR : J.IsRootedForest R F) (i : ι ≃ R) (j : ι ≃ S) :
    J.IsRootedForest S F ↔
      ∃! π : Equiv.Perm ι, ∀ a : ι, J.reaches F (i a).val (j (π a)).val := by
  rw [hR.iff_existsUnique_rootEquiv]
  let c : Equiv.Perm ι ≃ (R ≃ S) := Equiv.equivCongr i j
  refine (c.existsUnique_congr
    (p := fun π => ∀ a : ι, J.reaches F (i a).val (j (π a)).val)
    (q := fun e => ∀ r : R, J.reaches F r.val (e r).val) ?_).symm
  intro π
  change (∀ a : ι, J.reaches F (i a).val (j (π a)).val) ↔
    ∀ r : R, J.reaches F r.val (j (π (i.symm r))).val
  constructor
  · intro h r
    simpa only [i.apply_symm_apply] using h (i.symm r)
  · intro h a
    simpa only [i.symm_apply_apply] using h (i a)

end
end LatticeProb.Graph.CopiedGraph
