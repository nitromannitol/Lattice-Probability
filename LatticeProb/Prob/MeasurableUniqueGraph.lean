import Mathlib.MeasureTheory.Constructions.Polish.Basic

/-!
# Measurable functions characterized by a unique Borel graph

A measurable subset of a product of standard Borel spaces with exactly one point in
every vertical fiber is the full graph of a measurable function. The proof uses the
Lusin–Souslin theorem on the first-coordinate projection of the measurable subtype.
-/

namespace LatticeProb.Prob

variable {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    [StandardBorelSpace α] [StandardBorelSpace β]

/-- A function between standard Borel spaces is measurable if its complete graph is
measurable. Both directions of the graph characterization are required. -/
theorem measurable_of_complete_graph {Γ : Set (α × β)} (hΓ : MeasurableSet Γ)
    {f : α → β} (hgraph : ∀ a b, (a, b) ∈ Γ ↔ f a = b) : Measurable f := by
  letI : StandardBorelSpace Γ := hΓ.standardBorel
  let p : Γ → α := fun z => z.val.1
  have hp : Measurable p := measurable_fst.comp measurable_subtype_coe
  have hinj : Function.Injective p := by
    intro z w hzw
    apply Subtype.ext
    apply Prod.ext
    · exact hzw
    · have hz := (hgraph z.val.1 z.val.2).mp z.property
      have hw := (hgraph w.val.1 w.val.2).mp w.property
      change z.val.1 = w.val.1 at hzw
      exact hz.symm.trans ((congrArg f hzw).trans hw)
  have hemb : MeasurableEmbedding p := hp.measurableEmbedding hinj
  let s : α → Γ := fun a => ⟨(a, f a), (hgraph a (f a)).mpr rfl⟩
  have hs : Measurable s := hemb.measurable_comp_iff.mp measurable_id
  exact (measurable_snd.comp measurable_subtype_coe).comp hs

/-- A measurable relation between standard Borel spaces with exactly one point in each
vertical fiber is the complete graph of a measurable function. -/
theorem exists_measurable_of_unique_graph {Γ : Set (α × β)} (hΓ : MeasurableSet Γ)
    (hunique : ∀ a, ∃! b, (a, b) ∈ Γ) :
    ∃ f : α → β, Measurable f ∧ ∀ a b, (a, b) ∈ Γ ↔ f a = b := by
  classical
  choose f hf using fun a => (hunique a).exists
  have hgraph : ∀ a b, (a, b) ∈ Γ ↔ f a = b := by
    intro a b
    constructor
    · intro hb
      exact ((hunique a).unique (hf a) hb)
    · intro hb
      rw [← hb]
      exact hf a
  exact ⟨f, measurable_of_complete_graph hΓ hgraph, hgraph⟩

end LatticeProb.Prob
