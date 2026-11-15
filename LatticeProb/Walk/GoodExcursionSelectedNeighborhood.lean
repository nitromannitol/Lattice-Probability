import LatticeProb.Bonanno.BouRabeeGwynne.WalkBrownianGoodEvent
import LatticeProb.Prob.SelectorCommonNeighborhood

/-! # Selected neighborhoods for good excursion pairs -/

set_option autoImplicit false

open MeasureTheory Set Metric BouRabeeGwynne
open scoped unitInterval

namespace LatticeProb

/-- An active good excursion pair has endpoints in one common selected
neighborhood when its cell diameter is smaller than the selector margin. -/
theorem goodExcursionPair_common_selected_neighborhood
    {d : ℕ} {V ι J : Type*} (pos : V → Euc d)
    (E : ι → Set (Euc d)) (choice : ι → Option J) (C : Set (Euc d))
    (G : J → Set (Euc d)) {a r : ℝ} (hr : 0 < r) (har : a < r)
    (hdisj : Pairwise (fun i j => Disjoint (E i) (E j)))
    (hdiam : ∀ i, ∀ x ∈ E i, ∀ y ∈ E i, dist x y ≤ a)
    (hactive : ∀ y ∈ C, cellSelector E choice y ≠ none)
    (hmargin : ∀ y j, cellSelector E choice y = some j → ball y r ⊆ G j)
    {p : (Bool × ClockedWalkExcursion d) × (Bool × C(unitInterval, Euc d))}
    (hp : p ∈ goodExcursionPair pos E a) (hw : p.1.1 = false)
    (hb : p.2.2 1 ∈ C) :
    ∃ j, cellSelector E choice (ClockedWalkExcursion.endPoint p.1.2) = some j ∧
      cellSelector E choice (p.2.2 1) = some j ∧
      ClockedWalkExcursion.endPoint p.1.2 ∈ G j ∧ p.2.2 1 ∈ G j := by
  apply exists_common_selected_neighborhood (cellSelector E choice) C G hr hactive hmargin hb
  · exact goodExcursionPair_same_selector pos E a hdisj choice hp hw
  · exact (goodExcursionPair_dist_le pos E hdiam hp).trans_lt har

end LatticeProb
