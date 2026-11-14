import LatticeProb.Bonanno.BouRabeeGwynne.WalkBrownianGoodEvent
import LatticeProb.Euclidean.SeparatedAbsorbedIndexGap

/-! # Terminal indices of matched excursion endpoints -/

set_option autoImplicit false

open Set
open scoped unitInterval

namespace BouRabeeGwynne

/-- Good excursion pairs have equal flags and close endpoints. If their endpoint
sequences are absorbed at bounded indices and all complete steps before the
last are separated, the two terminal indices differ by at most one. -/
theorem goodExcursionPair_terminal_indices_close {d : ℕ} {V : Type*}
    (pos : V → Euc d) (m : ℕ → ℕ) (E : ∀ i, Fin (m i) → Set (Euc d))
    (p : ℕ → (Bool × ClockedWalkExcursion d) × (Bool × C(unitInterval, Euc d)))
    (K N M : ℕ) (a r : ℝ) (hN : N ≤ K) (hM : M ≤ K) (hr : 2 * a < r)
    (hdiam : ∀ i ≤ K, ∀ j, ∀ x ∈ E i j, ∀ y ∈ E i j, dist x y ≤ a)
    (hgood : ∀ i ≤ K, p i ∈ goodExcursionPair pos (E i) a)
    (hwabsorb : ∀ i, N ≤ i →
      ClockedWalkExcursion.endPoint (p i).1.2 = ClockedWalkExcursion.endPoint (p N).1.2)
    (hbabsorb : ∀ i, M ≤ i → (p i).2.2 1 = (p M).2.2 1)
    (hwsep : ∀ i, i + 1 < N → r ≤ dist
      (ClockedWalkExcursion.endPoint (p i).1.2)
      (ClockedWalkExcursion.endPoint (p (i + 1)).1.2))
    (hbsep : ∀ i, i + 1 < M → r ≤ dist ((p i).2.2 1) ((p (i + 1)).2.2 1)) :
    (∀ i ≤ K, (p i).1.1 = (p i).2.1) ∧ N ≤ M + 1 ∧ M ≤ N + 1 := by
  refine ⟨fun i hi => goodExcursionPair_flags pos (E i) a (hgood i hi), ?_⟩
  apply LatticeProb.terminal_indices_close_of_absorbed_close
    (fun i => ClockedWalkExcursion.endPoint (p i).1.2)
    (fun i => (p i).2.2 1) N M a r hr ?_ hwabsorb hbabsorb hwsep hbsep
  intro i hi
  have hiK : i ≤ K := hi.trans (max_le hN hM)
  exact goodExcursionPair_dist_le pos (E i) (hdiam i hiK) (hgood i hiK)

end BouRabeeGwynne
