import LatticeProb.Prob.CorrelatedBMConeTimes
import LatticeProb.Order.CountableExceptionalPairs
import LatticeProb.Prob.CorrelatedBMLocalMinCountable

/-!
# Exceptional direct-excursion pairs

For two real paths, pairs formed from an apex and either direct partner are
countable when a partner belongs to a countable exceptional set. This applies
to both directions of the direct relation and, almost surely, to local minima
of the coordinates of correlated Brownian motion.
-/

set_option autoImplicit false

open MeasureTheory Set
open MatedCRTHarmonic.MatedCRT (DirectRel lrCoord Path2 IsCorrelatedBM2)

namespace LatticeProb.CorrelatedBM

private theorem directRel_right_unique {X : ℝ → ℝ} {a c c' : ℝ}
    (h : DirectRel X a c) (h' : DirectRel X a c') : c = c' := by
  rcases lt_trichotomy c c' with hlt | heq | hgt
  · have hh := h'.2.2 c ⟨h.1, hlt⟩
    rw [h.2.1] at hh
    exact absurd hh (lt_irrefl _)
  · exact heq
  · have hh := h.2.2 c' ⟨h'.1, hgt⟩
    rw [h'.2.1] at hh
    exact absurd hh (lt_irrefl _)

private theorem directRel_left_unique {X : ℝ → ℝ} {a a' c : ℝ}
    (h : DirectRel X a c) (h' : DirectRel X a' c) : a = a' := by
  rcases lt_trichotomy a a' with hlt | heq | hgt
  · have hh := h.2.2 a' ⟨hlt, h'.1⟩
    rw [h.2.1, ← h'.2.1] at hh
    exact absurd hh (lt_irrefl _)
  · exact heq
  · have hh := h'.2.2 a ⟨hgt, h.1⟩
    rw [h'.2.1, ← h.2.1] at hh
    exact absurd hh (lt_irrefl _)

/-- Exceptional pairs for simultaneous direct excursions in either direction. -/
theorem countable_exceptional_direct_pairs (X Y : ℝ → ℝ) (E F : Set ℝ)
    (hE : E.Countable) (hF : F.Countable) :
    {p : ℝ × ℝ | ∃ a b,
      ((DirectRel X p.1 a ∧ DirectRel Y p.1 b) ∨
       (DirectRel X a p.1 ∧ DirectRel Y b p.1)) ∧
      (a ∈ E ∨ b ∈ F) ∧ (p.2 = p.1 ∨ p.2 = a ∨ p.2 = b)}.Countable := by
  have hforward (Z : ℝ → ℝ) (x : ℝ) : {y | DirectRel Z x y}.Countable := by
    apply Set.Subsingleton.countable
    intro a ha b hb
    exact directRel_right_unique ha hb
  have hbackward (Z : ℝ → ℝ) (x : ℝ) : {y | DirectRel Z y x}.Countable := by
    apply Set.Subsingleton.countable
    intro a ha b hb
    exact directRel_left_unique ha hb
  have hp := LatticeProb.countable_exceptional_relation_pairs
    (DirectRel X) (DirectRel Y) E F hE hF (hforward X) (hforward Y)
    (hbackward X) (hbackward Y)
  have hm := LatticeProb.countable_exceptional_relation_pairs
    (fun s t => DirectRel X t s) (fun s t => DirectRel Y t s) E F hE hF
    (hbackward X) (hbackward Y) (hforward X) (hforward Y)
  apply (hp.union hm).mono
  rintro p ⟨a, b, (⟨hx, hy⟩ | ⟨hx, hy⟩), he, ht⟩
  · exact Or.inl ⟨a, b, hx, hy, he, ht⟩
  · exact Or.inr ⟨a, b, hx, hy, he, ht⟩

/-- For correlated Brownian coordinates, pairs with a local-minimum partner
are almost surely countable. -/
theorem ae_countable_localMin_direct_pairs {γ : ℝ} {μ : Measure Path2}
    (hμ : IsCorrelatedBM2 γ μ) :
    ∀ᵐ ω ∂μ, {p : ℝ × ℝ | ∃ a b,
      ((DirectRel (lrCoord 0 · ω) p.1 a ∧ DirectRel (lrCoord 1 · ω) p.1 b) ∨
       (DirectRel (lrCoord 0 · ω) a p.1 ∧ DirectRel (lrCoord 1 · ω) b p.1)) ∧
      (IsLocalMin (lrCoord 0 · ω) a ∨ IsLocalMin (lrCoord 1 · ω) b) ∧
      (p.2 = p.1 ∨ p.2 = a ∨ p.2 = b)}.Countable := by
  filter_upwards [LatticeProb.CorrelatedBM.ae_countable_coordinate_localMin hμ] with ω hω
  exact countable_exceptional_direct_pairs (lrCoord 0 · ω) (lrCoord 1 · ω)
    {t | IsLocalMin (lrCoord 0 · ω) t} {t | IsLocalMin (lrCoord 1 · ω) t} (hω 0) (hω 1)

end LatticeProb.CorrelatedBM
