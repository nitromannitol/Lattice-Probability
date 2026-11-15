/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module MatedCRTHarmonic.CellScaling.MeshMeasurableDisconnect at commit fdb5cad;
   local imports are adapted. -/
import LatticeProb.Bonanno.MatedCRTHarmonic.CellScaling.MeshMeasurableWalk

/-!
# Borel graph separation on fixed candidate-edge codes

Each fixed vertex walk is a finite list. Its edge conditions are finite intersections of
measurable candidate-edge events; separation quantifies over the countable set of lists.
-/

set_option autoImplicit false
set_option linter.deprecated false
set_option linter.unnecessarySimpa false

noncomputable section

open MeasureTheory Set

namespace MatedCRTHarmonic.CellScaling

def meshGridCodeAdj (ε : ℝ) (ω : MatedCRT.Path2) (a b : ℤ) : Prop :=
  a ≠ b ∧ ∃ e : MeshGridEdgeCode, MatedCRT.edgePredicate ε ω e = true ∧
    ((e.1 = a ∧ e.2.1 = b) ∨ (e.1 = b ∧ e.2.1 = a))

theorem meshGridCodeAdj_iff_graphAdj (ε : ℝ) (ω : MatedCRT.Path2)
    (hlf : MatedCRT.IsLocallyFinite ε ω) (a b : ℤ) :
    meshGridCodeAdj ε ω a b ↔ (MatedCRT.graph ε ω hlf).adj.Adj a b := by
  rw [Harmonic.adj_iff]
  unfold meshGridCodeAdj
  constructor
  · rintro ⟨hne, e, he, hdir⟩
    have he' : MatedCRT.IsEdge ε ω e := by simpa [MatedCRT.edgePredicate] using he
    refine ⟨hne, ?_⟩
    rcases hdir with h | h
    · exact Or.inl ⟨⟨e, he'⟩, h.1, h.2⟩
    · exact Or.inr ⟨⟨e, he'⟩, h.1, h.2⟩
  · rintro ⟨hne, hdir⟩
    refine ⟨hne, ?_⟩
    rcases hdir with ⟨⟨e, he⟩, ha, hb⟩ | ⟨⟨e, he⟩, ha, hb⟩
    · exact ⟨e, by simpa [MatedCRT.edgePredicate] using he, Or.inl ⟨ha, hb⟩⟩
    · exact ⟨e, by simpa [MatedCRT.edgePredicate] using he, Or.inr ⟨ha, hb⟩⟩

theorem measurableSet_meshGridCodeAdj (ε : ℝ) (a b : ℤ) :
    MeasurableSet {ω : MatedCRT.Path2 | meshGridCodeAdj ε ω a b} := by
  classical
  by_cases hne : a ≠ b
  · have hEdge (e : MeshGridEdgeCode) :
        MeasurableSet {ω : MatedCRT.Path2 | MatedCRT.edgePredicate ε ω e = true} := by
      have hm := (MatedCRT.matedCRT_edgePredicate_measurable_holds ε).eval (a := e)
      exact (measurableSet_singleton true).preimage hm
    have hUnion : MeasurableSet (⋃ e : MeshGridEdgeCode,
        {ω : MatedCRT.Path2 | MatedCRT.edgePredicate ε ω e = true ∧
          ((e.1 = a ∧ e.2.1 = b) ∨ (e.1 = b ∧ e.2.1 = a))}) := by
      apply MeasurableSet.iUnion
      intro e
      by_cases hdir : ((e.1 = a ∧ e.2.1 = b) ∨ (e.1 = b ∧ e.2.1 = a))
      · simpa [hdir] using hEdge e
      · simp [hdir]
    simpa [meshGridCodeAdj, hne, Set.iUnion_setOf] using hUnion
  · simp [meshGridCodeAdj, hne]

theorem measurableSet_meshGridCodeIsChain (ε : ℝ) (l : List ℤ) :
    MeasurableSet {ω : MatedCRT.Path2 | l.IsChain (meshGridCodeAdj ε ω)} := by
  classical
  induction l with
  | nil => simp
  | cons a l ih =>
    cases l with
    | nil => simp
    | cons b tail =>
      have hrel := measurableSet_meshGridCodeAdj ε a b
      simpa only [List.isChain_cons_cons, Set.setOf_and] using hrel.inter ih

def meshGridCodeDisconnects (ε : ℝ) (ω : MatedCRT.Path2)
    (U S T : Set ℤ) : Prop :=
  ∀ (l : List ℤ) (hne : l ≠ []),
    l.head hne ∈ S → l.getLast hne ∈ T →
      l.IsChain (meshGridCodeAdj ε ω) → ∃ y ∈ l, y ∈ U

theorem meshGridCodeDisconnects_iff_graphDisconnects (ε : ℝ) (ω : MatedCRT.Path2)
    (hlf : MatedCRT.IsLocallyFinite ε ω) (U S T : Set ℤ) :
    meshGridCodeDisconnects ε ω U S T ↔
      (MatedCRT.graph ε ω hlf).Disconnects U S T := by
  let G := MatedCRT.graph ε ω hlf
  constructor
  · intro hc a ha b hb w
    have hne : w.support ≠ [] := w.support_ne_nil
    have hhead : w.support.head hne = a := by
      simpa using w.head_support
    have hlast : w.support.getLast hne = b := by
      simpa using w.getLast_support
    have hchain : w.support.IsChain (meshGridCodeAdj ε ω) := by
      have hw := w.isChain_adj_support
      exact hw.imp fun a b hab => (meshGridCodeAdj_iff_graphAdj ε ω hlf a b).mpr hab
    exact hc w.support hne (hhead.symm ▸ ha) (hlast.symm ▸ hb) hchain
  · intro hg l hne ha hb hchain
    have hchain' : l.IsChain G.adj.Adj :=
      hchain.imp fun a b hab => (meshGridCodeAdj_iff_graphAdj ε ω hlf a b).mp hab
    let w := SimpleGraph.Walk.ofSupport l hne hchain'
    have hwa : l.head hne ∈ S := ha
    have hwb : l.getLast hne ∈ T := hb
    obtain ⟨y, hy, hyU⟩ := hg (l.head hne) hwa (l.getLast hne) hwb w
    exact ⟨y, by simpa [w] using hy, hyU⟩

/-- Separation by a fixed removed set is Borel when each endpoint-membership event is Borel. -/
theorem measurableSet_meshGridCodeDisconnects {Ω : Type*} [MeasurableSpace Ω]
    (ε : ℝ) (ω : Ω → MatedCRT.Path2) (hω : Measurable ω)
    (U : Set ℤ) (S T : Ω → Set ℤ)
    (hS : ∀ a, MeasurableSet {d | a ∈ S d})
    (hT : ∀ b, MeasurableSet {d | b ∈ T d}) :
    MeasurableSet {d | meshGridCodeDisconnects ε (ω d) U (S d) (T d)} := by
  classical
  have hfixed (l : List ℤ) (hne : l ≠ []) :
      MeasurableSet {d : Ω | l.head hne ∈ S d → l.getLast hne ∈ T d →
        l.IsChain (meshGridCodeAdj ε (ω d)) → ∃ y ∈ l, y ∈ U} := by
    by_cases hhit : ∃ y ∈ l, y ∈ U
    · simpa [hhit] using (MeasurableSet.univ : MeasurableSet (Set.univ : Set Ω))
    · have hchain : MeasurableSet {d : Ω | l.IsChain (meshGridCodeAdj ε (ω d))} :=
        (measurableSet_meshGridCodeIsChain ε l).preimage hω
      have hE : {d : Ω | l.head hne ∈ S d → l.getLast hne ∈ T d →
          l.IsChain (meshGridCodeAdj ε (ω d)) → ∃ y ∈ l, y ∈ U} =
          ({d | l.head hne ∈ S d} ∩ {d | l.getLast hne ∈ T d} ∩
            {d | l.IsChain (meshGridCodeAdj ε (ω d))})ᶜ := by
        ext d
        simp [hhit]
      rw [hE]
      exact ((hS _).inter (hT _)).inter hchain |>.compl
  rw [show {d : Ω | meshGridCodeDisconnects ε (ω d) U (S d) (T d)} =
      ⋂ l : List ℤ, ⋂ hne : l ≠ [],
        {d : Ω | l.head hne ∈ S d → l.getLast hne ∈ T d →
          l.IsChain (meshGridCodeAdj ε (ω d)) → ∃ y ∈ l, y ∈ U} by
        ext d
        simp [meshGridCodeDisconnects]]
  exact MeasurableSet.iInter fun l => MeasurableSet.iInter fun hne => hfixed l hne

end MatedCRTHarmonic.CellScaling
