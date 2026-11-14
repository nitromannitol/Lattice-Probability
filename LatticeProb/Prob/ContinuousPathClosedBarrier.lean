/-
Copyright (c) 2026. Released under the Apache 2.0 license.
-/
import LatticeProb.Prob.ContinuousPathOpenBarrier

/-!
# Measurability of closed-interval path barriers

Weak barriers and endpoint increment conditions are measurable for continuous paths.
-/

open Set MeasureTheory

namespace LatticeProb

/-- A weak random lower barrier on a closed interval is a measurable event. -/
theorem measurableSet_continuousPath_closedBarrier {Ω : Type*} [MeasurableSpace Ω]
    (X : Ω → ℝ → ℝ) (Y : Ω → ℝ) (a b : ℝ)
    (hcont : ∀ ω, Continuous (X ω))
    (hX : ∀ t, Measurable (fun ω => X ω t)) (hY : Measurable Y) :
    MeasurableSet {ω | ∀ t ∈ Icc a b, Y ω ≤ X ω t} := by
  by_cases hab : a ≤ b
  · have heq : {ω | ∀ t ∈ Icc a b, Y ω ≤ X ω t} =
        {ω | Y ω ≤ X ω a} ∩ {ω | Y ω ≤ X ω b} ∩
          {ω | ∀ t ∈ Ioo a b, Y ω ≤ X ω t} := by
      ext ω
      simp only [mem_ofPred_eq, mem_inter_iff]
      constructor
      · intro h
        exact ⟨⟨h a ⟨le_rfl, hab⟩, h b ⟨hab, le_rfl⟩⟩,
          fun t ht => h t ⟨le_of_lt ht.1, le_of_lt ht.2⟩⟩
      · rintro ⟨⟨ha, hb⟩, hi⟩ t ht
        rcases lt_or_eq_of_le ht.1 with hta | rfl
        · rcases lt_or_eq_of_le ht.2 with htb | rfl
          · exact hi t ⟨hta, htb⟩
          · exact hb
        · exact ha
    rw [heq]
    exact ((measurableSet_le hY (hX a)).inter (measurableSet_le hY (hX b))).inter
      (measurableSet_continuousPath_openBarrier X Y a b hcont hX hY)
  · have hempty : Icc a b = (∅ : Set ℝ) := Icc_eq_empty hab
    simp [hempty]

/-- An endpoint increment bound together with a lower barrier is measurable. -/
theorem measurableSet_continuousPath_increment_closedBarrier {Ω : Type*}
    [MeasurableSpace Ω] (X : Ω → ℝ → ℝ) (C : Ω → ℝ) (a b : ℝ)
    (hcont : ∀ ω, Continuous (X ω))
    (hX : ∀ t, Measurable (fun ω => X ω t)) (hC : Measurable C) :
    MeasurableSet {ω | |X ω b - X ω a| ≤ C ω ∧
      ∀ t ∈ Icc a b, X ω b - C ω ≤ X ω t} := by
  exact (measurableSet_le ((hX b).sub (hX a)).abs hC).inter
    (measurableSet_continuousPath_closedBarrier X (fun ω => X ω b - C ω) a b
      hcont hX ((hX b).sub hC))

end LatticeProb
