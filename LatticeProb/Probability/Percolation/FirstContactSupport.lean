import LatticeProb.Probability.Percolation.FirstContactBarrier
import LatticeProb.Probability.Percolation.ExposureIndependence

/-!
# Finite edge support for first contact

The first-contact event depends only on edges inside the square with an endpoint
outside the crossing barrier. Disjoint supports give product independence.
-/

namespace EdgeCrossing

open MeasureTheory ProbabilityTheory Percolation.Literature SimpleGraph
open scoped ProbabilityTheory

noncomputable section

private abbrev Edge := (LatticeModels.zdGraph 2).edgeSet
private abbrev Config := Edge → Prop

/-- Edges in the square with at least one endpoint outside the reflected barrier. -/
def firstContactEdges (n : ℕ) {c d : LatticeModels.Site 2}
    (Q : (LatticeModels.zdGraph 2).Walk c d) : Finset Edge := by
  classical
  exact ((centeredSquare n).sym2.filter fun e =>
    ∃ z ∈ e, z ∉ Q.support ∧ reflY 0 z ∉ Q.support).subtype
      (fun e => e ∈ (LatticeModels.zdGraph 2).edgeSet)

/-- Membership specifies both square containment and an endpoint outside the barrier. -/
theorem mem_firstContactEdges_iff (n : ℕ) {c d : LatticeModels.Site 2}
    (Q : (LatticeModels.zdGraph 2).Walk c d) (e : Edge) :
    e ∈ firstContactEdges n Q ↔
      (∀ z ∈ e.1, z ∈ centeredSquare n) ∧
        ∃ z ∈ e.1, z ∉ Q.support ∧ reflY 0 z ∉ Q.support := by
  classical
  simp [firstContactEdges, Finset.mem_sym2_iff]

/-- Agreement on the indicated edges preserves first-contact membership. -/
theorem firstContact_congr (n : ℕ) {c d : LatticeModels.Site 2}
    (Q : (LatticeModels.zdGraph 2).Walk c d) (reflected : Bool)
    (ω τ : Config) (h : ∀ e ∈ firstContactEdges n Q, ω e = τ e) :
    ω ∈ firstContact n Q reflected ↔ τ ∈ firstContact n Q reflected := by
  classical
  suffices key : ∀ ω τ : Config,
      (∀ e ∈ firstContactEdges n Q, ω e = τ e) →
      ω ∈ firstContact n Q reflected → τ ∈ firstContact n Q reflected by
    exact ⟨key ω τ h, key τ ω (fun e he => (h e he).symm)⟩
  intro ω τ h ⟨t, ht, v, hv, q, hq, ho, he⟩
  refine ⟨t, ht, v, hv, q, hq, ho, ?_⟩
  intro e heq
  have hedge := q.edges_subset_edgeSet heq
  have hT : (⟨e, hedge⟩ : Edge) ∈ firstContactEdges n Q := by
    rw [mem_firstContactEdges_iff]
    rw [Walk.edges, List.mem_map] at heq
    obtain ⟨dart, hdart, rfl⟩ := heq
    constructor
    ·
      exact Finset.mem_sym2_iff.mp (Finset.mk_mem_sym2_iff.mpr
        ⟨hq _ (q.dart_fst_mem_support_of_mem_darts hdart),
          hq _ (q.dart_snd_mem_support_of_mem_darts hdart)⟩)
    · refine ⟨dart.fst, Sym2.mem_mk_left _ _, ?_⟩
      simpa only [Set.mem_ofPred_eq, not_or] using ho dart hdart
  exact ⟨hedge, (h ⟨e, hedge⟩ hT).mp (he e heq).2⟩

/-- First contact is a measurable finite-coordinate event. -/
theorem measurableSet_firstContact (n : ℕ) {c d : LatticeModels.Site 2}
    (Q : (LatticeModels.zdGraph 2).Walk c d) (reflected : Bool) :
    MeasurableSet (firstContact n Q reflected) := by
  exact LatticeProb.Prob.FiniteCellFactorization.measurableSet_event
    (fun e ω => ω e) (fun e => measurable_pi_apply e) (firstContactEdges n Q) _
    (firstContact_congr n Q reflected)

/-- A first-contact event factors from each exposure event with disjoint support. -/
theorem exposure_real_inter_firstContact_of_disjoint {ι : Type*} (s : Finset ι)
    (D : ι → Set Config) (S : ι → Finset Edge) (n : ℕ)
    {c d : LatticeModels.Site 2} (Q : (LatticeModels.zdGraph 2).Walk c d)
    (reflected : ι → Bool)
    (hST : ∀ i ∈ s, Disjoint (S i) (firstContactEdges n Q))
    (hD : ∀ i ∈ s, ∀ ω τ, (∀ e ∈ S i, ω e = τ e) → (ω ∈ D i ↔ τ ∈ D i)) :
    ∀ i ∈ s, (Measure.infinitePi (fun _ : Edge => bernoulliMeasure True False half)).real
        (D i ∩ firstContact n Q (reflected i)) =
      (Measure.infinitePi (fun _ : Edge => bernoulliMeasure True False half)).real (D i) *
      (Measure.infinitePi (fun _ : Edge => bernoulliMeasure True False half)).real
        (firstContact n Q (reflected i)) := by
  exact exposure_real_inter_of_disjoint s D (fun i => firstContact n Q (reflected i))
    S (fun _ => firstContactEdges n Q) hST hD
    (fun i _ => firstContact_congr n Q (reflected i))

end
end EdgeCrossing
