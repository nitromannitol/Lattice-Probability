import LatticeProb.LQG.DyadicHullAnchors
import LatticeProb.LQG.SelectedHullFieldCodeAdjacentScales

/-! # Anchored test families for dyadic hull observations -/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set LQGMetric LQGMetric.Blueprint LQGMetric.CONF

namespace LatticeProb.LQG

/-- Adjoin a sequence of tests to an existing test family. -/
def adjoinTestSequence {I : Type*} (φ : I → TestC) (ψ : ℕ → TestC) :
    I ⊕ ℕ → TestC := Sum.elim φ ψ

@[simp] theorem adjoinTestSequence_inl {I : Type*} (φ : I → TestC)
    (ψ : ℕ → TestC) (i : I) : adjoinTestSequence φ ψ (Sum.inl i) = φ i := rfl

@[simp] theorem adjoinTestSequence_inr {I : Type*} (φ : I → TestC)
    (ψ : ℕ → TestC) (n : ℕ) : adjoinTestSequence φ ψ (Sum.inr n) = ψ n := rfl

/-- A normalized anchor family supplies adjacent overlap after being adjoined
    to any existing test family. -/
theorem adjoinTestSequence_adjacent_overlap {I : Type*} (φ : I → TestC)
    (ψ : ℕ → TestC) (A : Set ℂ)
    (hunit : ∀ n, ∫ x, ψ n x = 1)
    (hsupport : ∀ n, tsupport (ψ n : ℂ → ℝ) ⊆ interior (dyadicHull n A)) :
    ∀ n, ∃ i : I ⊕ ℕ, (∫ x, adjoinTestSequence φ ψ i x) = 1 ∧
      tsupport (adjoinTestSequence φ ψ i : ℂ → ℝ) ∪ tsupport (ψ n : ℂ → ℝ) ⊆
        interior (dyadicHull n A) ∧
      tsupport (adjoinTestSequence φ ψ i : ℂ → ℝ) ∪ tsupport (ψ (n + 1) : ℂ → ℝ) ⊆
        interior (dyadicHull (n + 1) A) := by
  intro n
  obtain ⟨i, hi, hleft, hright⟩ := dyadicHull_anchor_adjacent_overlap A ψ hunit hsupport n
  exact ⟨Sum.inr i, hi, hleft, hright⟩

/-- For a fixed point, anchors can be chosen once for all sets containing it,
    and can be adjoined to any prescribed family of tests. -/
theorem exists_adjoined_dyadicHull_overlap {I : Type*} (z : ℂ) (φ : I → TestC) :
    ∃ ψ : ℕ → TestC, (∀ n, ∫ x, ψ n x = 1) ∧
      ∀ A : Set ℂ, z ∈ A → ∀ n, ∃ i : I ⊕ ℕ,
        (∫ x, adjoinTestSequence φ ψ i x) = 1 ∧
        tsupport (adjoinTestSequence φ ψ i : ℂ → ℝ) ∪ tsupport (ψ n : ℂ → ℝ) ⊆
          interior (dyadicHull n A) ∧
        tsupport (adjoinTestSequence φ ψ i : ℂ → ℝ) ∪ tsupport (ψ (n + 1) : ℂ → ℝ) ⊆
          interior (dyadicHull (n + 1) A) := by
  obtain ⟨ψ, hψ⟩ := exists_dyadicHull_anchors z
  refine ⟨ψ, (fun n => (hψ n).1), ?_⟩
  intro A hz
  exact adjoinTestSequence_adjacent_overlap φ ψ A (fun n => (hψ n).1)
    (fun n => (hψ n).2 A hz)

/-- Equal codes for a family extended by normalized anchors determine a common
    period shift at every scale when the anchors are supported in the hulls. -/
theorem adjoinTestSequence_pairings_of_eq {Ω : Type} {I : Type*}
    (g h : Ω → DistC) (A : Ω → Set ℂ) (φ : I → TestC) (ψ : ℕ → TestC)
    {p : ℝ} (hp : 0 < p) (ω : Ω)
    (hunit : ∀ n, ∫ x, ψ n x = 1)
    (hsupport : ∀ n, tsupport (ψ n : ℂ → ℝ) ⊆ interior (dyadicHull n (A ω)))
    (heq : ∀ n, selectedHullFieldCode g A n (adjoinTestSequence φ ψ) ψ hp (fun _ => n) ω =
      selectedHullFieldCode h A n (adjoinTestSequence φ ψ) ψ hp (fun _ => n) ω) :
    ∃ k : ℤ, ∀ n,
      h ω (ψ n) = g ω (ψ n) + (k : ℝ) * p ∧
      ∀ i, tsupport (adjoinTestSequence φ ψ i : ℂ → ℝ) ∪
        tsupport (ψ n : ℂ → ℝ) ⊆ interior (dyadicHull n (A ω)) →
        h ω (adjoinTestSequence φ ψ i) = g ω (adjoinTestSequence φ ψ i) +
          ((k : ℝ) * p) * (∫ z, adjoinTestSequence φ ψ i z) := by
  exact selectedHullFieldCode_pairings_of_eq_adjacent_scales g h A (adjoinTestSequence φ ψ)
    ψ hp (fun n _ => n) ω (adjoinTestSequence_adjacent_overlap φ ψ (A ω) hunit hsupport) heq

end LatticeProb.LQG
