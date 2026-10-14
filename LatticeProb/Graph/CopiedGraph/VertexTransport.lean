/-
# Vertex relabeling of copied forests

A vertex equivalence relabels the two endpoint maps and leaves every edge ID
unchanged. Lifting each copied-walk step through the equivalence and its inverse
proves reachability transport. The same walk equivalence transports the forest
and unique-root predicates with explicit root witnesses, giving equivalences
which fix every selected finite edge subset.
-/
import LatticeProb.Graph.CopiedGraph.RootedForest
import Mathlib.SetTheory.Cardinal.Finite



namespace LatticeProb.Graph.CopiedGraph

open scoped Classical
noncomputable section

variable {V W E : Type*}

/-- Relabel the vertices through `e`, retaining the entire edge-copy carrier
and the two original endpoint maps composed with `e`. -/
def relabelVertices (J : CopiedGraph V E) (e : V ≃ W) : CopiedGraph W E :=
  ⟨e ∘ J.left, e ∘ J.right⟩

/-- Copied-walk reachability transports in both directions through a vertex
equivalence, with the identical selected finite edge subset. -/
theorem reaches_relabelVertices_iff (J : CopiedGraph V E) (e : V ≃ W)
    (F : Finset E) (x y : V) :
    (J.relabelVertices e).reaches F (e x) (e y) ↔ J.reaches F x y := by
  constructor
  · intro h
    have h' : J.reaches F (e.symm (e x)) (e.symm (e y)) := h.lift e.symm (by
      rintro u v ⟨c, hc, hends⟩
      refine ⟨c, hc, ?_⟩
      rcases hends with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩
      · refine Or.inl ⟨?_, ?_⟩
        · simpa only [relabelVertices, Function.comp_apply, Equiv.symm_apply_apply]
            using congrArg e.symm h₁
        · simpa only [relabelVertices, Function.comp_apply, Equiv.symm_apply_apply]
            using congrArg e.symm h₂
      · refine Or.inr ⟨?_, ?_⟩
        · simpa only [relabelVertices, Function.comp_apply, Equiv.symm_apply_apply]
            using congrArg e.symm h₁
        · simpa only [relabelVertices, Function.comp_apply, Equiv.symm_apply_apply]
            using congrArg e.symm h₂)
    simpa only [Equiv.symm_apply_apply] using h'
  · intro h
    exact h.lift e (by
      rintro u v ⟨c, hc, hends⟩
      refine ⟨c, hc, ?_⟩
      rcases hends with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩
      · exact Or.inl ⟨congrArg e h₁, congrArg e h₂⟩
      · exact Or.inr ⟨congrArg e h₁, congrArg e h₂⟩)

/-- Acyclicity of the original selected copied subset is invariant under
vertex relabeling, including graphs with loops or parallel IDs. -/
theorem isForest_relabelVertices_iff (J : CopiedGraph V E) (e : V ≃ W)
    (F : Finset E) : (J.relabelVertices e).IsForest F ↔ J.IsForest F := by
  unfold IsForest
  change (∀ c ∈ F, ¬(J.relabelVertices e).reaches (F.erase c)
    (e (J.left c)) (e (J.right c))) ↔ _
  simp only [J.reaches_relabelVertices_iff e]

/-- The exact unique-root forest predicate transports to the image root set.
Both directions produce actual original or relabeled vertices and walk
witnesses; no finite or nonempty-carrier premise is required. -/
theorem isRootedForest_relabelVertices_iff (J : CopiedGraph V E) (e : V ≃ W)
    (R : Set V) (F : Finset E) :
    (J.relabelVertices e).IsRootedForest (e '' R) F ↔ J.IsRootedForest R F := by
  constructor
  · rintro ⟨hf, hc⟩
    refine ⟨(J.isForest_relabelVertices_iff e F).mp hf, ?_⟩
    intro x
    obtain ⟨w, ⟨r, hr, rfl⟩, hx, hu⟩ := hc (e x)
    refine ⟨r, hr, (J.reaches_relabelVertices_iff e F x r).mp hx, ?_⟩
    intro s hs hxs
    apply e.injective
    exact hu (e s) ⟨s, hs, rfl⟩ ((J.reaches_relabelVertices_iff e F x s).mpr hxs)
  · rintro ⟨hf, hc⟩
    refine ⟨(J.isForest_relabelVertices_iff e F).mpr hf, ?_⟩
    intro y
    obtain ⟨r, hr, hx, hu⟩ := hc (e.symm y)
    refine ⟨e r, ⟨r, hr, rfl⟩, ?_, ?_⟩
    · simpa only [Equiv.apply_symm_apply] using
        (J.reaches_relabelVertices_iff e F (e.symm y) r).mpr hx
    · rintro w ⟨s, hs, rfl⟩ hy
      apply congrArg e
      apply hu s hs
      apply (J.reaches_relabelVertices_iff e F (e.symm y) s).mp
      simpa only [Equiv.apply_symm_apply] using hy

/-- **Rooted forest vertex transport.** Relabeling vertices and the root set
induces an equivalence of rooted forests, identity on the original copied
finite subsets. -/
def rootedForestRelabelEquiv (J : CopiedGraph V E) (e : V ≃ W) (R : Set V) :
    {F : Finset E // J.IsRootedForest R F} ≃
      {F : Finset E // (J.relabelVertices e).IsRootedForest (e '' R) F} :=
  Equiv.subtypeEquivRight (fun F => (J.isRootedForest_relabelVertices_iff e R F).symm)

/-- Relabeling rooted forests preserves every selected original edge ID. -/
theorem rootedForestRelabelEquiv_apply_val (J : CopiedGraph V E) (e : V ≃ W)
    (R : Set V) (F : {F : Finset E // J.IsRootedForest R F}) :
    (J.rootedForestRelabelEquiv e R F).val = F.val := rfl

/-- The inverse rooted-forest transport preserves every selected original ID. -/
theorem rootedForestRelabelEquiv_symm_apply_val (J : CopiedGraph V E) (e : V ≃ W)
    (R : Set V) (F : {F : Finset E // (J.relabelVertices e).IsRootedForest (e '' R) F}) :
    ((J.rootedForestRelabelEquiv e R).symm F).val = F.val := rfl

/-- The whole rooted-forest count is invariant under a vertex equivalence. -/
theorem card_rootedForest_relabelVertices (J : CopiedGraph V E) (e : V ≃ W) (R : Set V) :
    Nat.card {F : Finset E // (J.relabelVertices e).IsRootedForest (e '' R) F} =
      Nat.card {F : Finset E // J.IsRootedForest R F} :=
  (Nat.card_congr (J.rootedForestRelabelEquiv e R)).symm

end
end LatticeProb.Graph.CopiedGraph
