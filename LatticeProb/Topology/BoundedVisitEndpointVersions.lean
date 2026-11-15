import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
import Mathlib.Data.Rat.Cast.Order

/-! # Measurable endpoint versions from bounded visits -/

set_option autoImplicit false

open Set MeasureTheory

namespace LatticeProb

/-- Countable observable visits determine versions of bounded endpoints even when the
almost-everywhere hypotheses are stated in a different measurable space. -/
theorem exists_measurable_endpoints_of_bounded_ae_visits
    {Ω : Type*} [MeasurableSpace Ω] (obs : MeasurableSpace Ω) (P : Measure Ω)
    (visit : Ω → ℚ → Prop) (a b : Ω → ℝ) (s t : ℝ) (hst : s ≤ t)
    (hvisit : ∀ q, @MeasurableSet Ω obs {ω | visit ω q})
    (hgood : ∀ᵐ ω ∂P,
      s ≤ a ω ∧ b ω ≤ t ∧
      (∀ q, visit ω q → a ω ≤ q ∧ (q : ℝ) ≤ b ω) ∧
      (∀ r, a ω < r → ∃ q : ℚ, visit ω q ∧ (q : ℝ) < r) ∧
      (∀ r, r < b ω → ∃ q : ℚ, visit ω q ∧ r < (q : ℝ))) :
    ∃ a' b' : Ω → ℝ, @Measurable Ω ℝ obs _ a' ∧ @Measurable Ω ℝ obs _ b' ∧
      (∀ᵐ ω ∂P, a' ω = a ω ∧ b' ω = b ω) := by
  classical
  let l : ℚ → Ω → ℝ := fun q ω => if visit ω q then min t (max s q) else t
  let r : ℚ → Ω → ℝ := fun q ω => if visit ω q then min t (max s q) else s
  have hl : ∀ q, @Measurable Ω ℝ obs _ (l q) := by
    let : MeasurableSpace Ω := obs
    intro q
    exact Measurable.ite (hvisit q) measurable_const measurable_const
  have hr : ∀ q, @Measurable Ω ℝ obs _ (r q) := by
    let : MeasurableSpace Ω := obs
    intro q
    exact Measurable.ite (hvisit q) measurable_const measurable_const
  refine ⟨fun ω => ⨅ q, l q ω, fun ω => ⨆ q, r q ω, ?_, ?_, ?_⟩
  · let : MeasurableSpace Ω := obs
    exact Measurable.iInf hl
  · let : MeasurableSpace Ω := obs
    exact Measurable.iSup hr
  · filter_upwards [hgood] with ω hω
    have hlower : ∀ q, s ≤ l q ω := by
      intro q
      dsimp [l]
      split_ifs
      · exact le_min hst (le_max_left _ _)
      · exact hst
    have hupper : ∀ q, r q ω ≤ t := by
      intro q
      dsimp [r]
      split_ifs
      · exact min_le_left _ _
      · exact hst
    have hbl : BddBelow (range fun q => l q ω) := ⟨s, by rintro _ ⟨q, rfl⟩; exact hlower q⟩
    have hbu : BddAbove (range fun q => r q ω) := ⟨t, by rintro _ ⟨q, rfl⟩; exact hupper q⟩
    have hab : a ω ≤ b ω := by
      obtain ⟨q, hq, _⟩ := hω.2.2.2.1 (a ω + 1) (by linarith)
      exact (hω.2.2.1 q hq).1.trans (hω.2.2.1 q hq).2
    constructor
    · apply le_antisymm
      · apply le_of_forall_gt
        intro z hz
        obtain ⟨q, hq, hqz⟩ := hω.2.2.2.1 z hz
        have hqrange := hω.2.2.1 q hq
        have hs : s ≤ (q : ℝ) := hω.1.trans hqrange.1
        have ht : (q : ℝ) ≤ t := hqrange.2.trans hω.2.1
        have hle := ciInf_le hbl q
        simp only [l, hq, ite_true, max_eq_right hs, min_eq_right ht] at hle
        exact hle.trans_lt hqz
      · apply le_ciInf
        intro q
        dsimp [l]
        split_ifs with hq
        · exact le_min (hab.trans hω.2.1) (le_trans (hω.2.2.1 q hq).1 (le_max_right _ _))
        · exact hab.trans hω.2.1
    · apply le_antisymm
      · apply ciSup_le
        intro q
        dsimp [r]
        split_ifs with hq
        · exact (min_le_right _ _).trans (max_le (hω.1.trans hab) (hω.2.2.1 q hq).2)
        · exact hω.1.trans hab
      · apply le_of_forall_lt
        intro z hz
        obtain ⟨q, hq, hzq⟩ := hω.2.2.2.2 z hz
        have hqrange := hω.2.2.1 q hq
        have hs : s ≤ (q : ℝ) := hω.1.trans hqrange.1
        have ht : (q : ℝ) ≤ t := hqrange.2.trans hω.2.1
        have hle := le_ciSup hbu q
        simp only [r, hq, ite_true, max_eq_right hs, min_eq_right ht] at hle
        exact hzq.trans_le hle

end LatticeProb
