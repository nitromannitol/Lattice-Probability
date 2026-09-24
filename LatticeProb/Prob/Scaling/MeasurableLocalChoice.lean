/- Selecting a measurable local representative from a countable family.

Moved from Parking-Sharpness.
-/
import Mathlib.MeasureTheory.MeasurableSpace.Constructions

open MeasureTheory Set
namespace LatticeProb.Scaling.MeasurableLocalChoice

/-- Given a countable family of measurable local conditions `p n`, each with its own measurable
representative `f n`, a single measurable function `g` selects, at each point where some
condition holds, a representative for one of the holding conditions, and falls back to a given
measurable default `b` where no condition holds. -/
theorem exists_measurable_selection {Ω E : Type*} [MeasurableSpace Ω] [MeasurableSpace E]
    (p : ℕ → Ω → Prop) (hp : ∀ n, MeasurableSet {ω | p n ω})
    (f : ℕ → Ω → E) (hf : ∀ n, Measurable (f n))
    (b : Ω → E) (hb : Measurable b) :
    ∃ g : Ω → E, Measurable g ∧
      (∀ ω, (∃ n, p n ω) → ∃ n, p n ω ∧ g ω = f n ω) ∧
      (∀ ω, (¬∃ n, p n ω) → g ω = b ω) := by
  classical
  let q : ℕ → Ω → Prop
    | 0, ω => ¬∃ n, p n ω
    | n + 1, ω => p n ω
  let F : ℕ → Ω → E
    | 0, ω => b ω
    | n + 1, ω => f n ω
  have hq : ∀ ω, ∃ n, q n ω := by
    intro ω
    by_cases h : ∃ n, p n ω
    · obtain ⟨n, hn⟩ := h
      exact ⟨n + 1, hn⟩
    · exact ⟨0, h⟩
  have hqm : ∀ n, MeasurableSet {ω | q n ω} := by
    intro n
    cases n with
    | zero =>
      convert (MeasurableSet.iUnion hp).compl using 1
      ext ω
      simp [q]
    | succ n => exact hp n
  have hFm : ∀ n, Measurable (F n) := by
    intro n
    cases n with
    | zero => exact hb
    | succ n => exact hf n
  refine ⟨fun ω => F (Nat.find (hq ω)) ω, Measurable.find hFm hqm hq, ?_, ?_⟩
  · intro ω h
    have hs := Nat.find_spec (hq ω)
    cases hn : Nat.find (hq ω) with
    | zero =>
      rw [hn] at hs
      exact (hs h).elim
    | succ n =>
      rw [hn] at hs
      exact ⟨n, hs, by simp only [hn, F]⟩
  · intro ω h
    have hn : Nat.find (hq ω) = 0 := Nat.eq_zero_of_le_zero (Nat.find_min' (hq ω) h)
    simp [hn, F]

end LatticeProb.Scaling.MeasurableLocalChoice
