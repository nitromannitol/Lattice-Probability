/-
Copyright (c) 2026. Released under the Apache 2.0 license.
-/
import LatticeProb.Prob.ContinuousPathClosedBarrier

/-!
# Measurable approximate cone-vector events

The two possible coordinate orientations of a fixed-grid barrier event are
measurable for continuous paths with measurable fixed-time evaluations.
-/

set_option autoImplicit false

open Set MeasureTheory

namespace LatticeProb

/-- The local and interval barriers for one coordinate orientation. -/
def approximateConeGridEvent {Ω : Type*} (X Y : Ω → ℝ → ℝ)
    (E : Ω → ℝ) (a b H : ℝ) : Set Ω :=
  {ω | (∀ u ∈ Icc 0 H, X ω a - E ω ≤ X ω (a + u)) ∧
    (∀ u ∈ Icc 0 H, X ω b - E ω ≤ X ω (b - u) ∧
      Y ω b - E ω ≤ Y ω (b - u)) ∧
    |X ω b - X ω a| ≤ E ω ∧
    ∀ t ∈ Icc a b, X ω b - E ω ≤ X ω t}

/-- A fixed-grid approximate cone-vector event is measurable. -/
theorem measurableSet_approximateConeGridEvent {Ω : Type*} [MeasurableSpace Ω]
    (X Y : Ω → ℝ → ℝ) (E : Ω → ℝ) (a b H : ℝ)
    (hXcont : ∀ ω, Continuous (X ω)) (hYcont : ∀ ω, Continuous (Y ω))
    (hX : ∀ t, Measurable (fun ω => X ω t))
    (hY : ∀ t, Measurable (fun ω => Y ω t)) (hE : Measurable E) :
    MeasurableSet (approximateConeGridEvent X Y E a b H) := by
  have hf : MeasurableSet {ω | ∀ u ∈ Icc 0 H,
      X ω a - E ω ≤ X ω (a + u)} :=
    measurableSet_continuousPath_closedBarrier
      (fun ω u => X ω (a + u)) (fun ω => X ω a - E ω) 0 H
      (fun ω => (hXcont ω).comp (continuous_const.add continuous_id))
      (fun u => hX (a + u)) ((hX a).sub hE)
  have hbX : MeasurableSet {ω | ∀ u ∈ Icc 0 H,
      X ω b - E ω ≤ X ω (b - u)} :=
    measurableSet_continuousPath_closedBarrier
      (fun ω u => X ω (b - u)) (fun ω => X ω b - E ω) 0 H
      (fun ω => (hXcont ω).comp (continuous_const.sub continuous_id))
      (fun u => hX (b - u)) ((hX b).sub hE)
  have hbY : MeasurableSet {ω | ∀ u ∈ Icc 0 H,
      Y ω b - E ω ≤ Y ω (b - u)} :=
    measurableSet_continuousPath_closedBarrier
      (fun ω u => Y ω (b - u)) (fun ω => Y ω b - E ω) 0 H
      (fun ω => (hYcont ω).comp (continuous_const.sub continuous_id))
      (fun u => hY (b - u)) ((hY b).sub hE)
  have hi := measurableSet_continuousPath_increment_closedBarrier X E a b hXcont hX hE
  have heq : approximateConeGridEvent X Y E a b H =
      {ω | ∀ u ∈ Icc 0 H, X ω a - E ω ≤ X ω (a + u)} ∩
      ({ω | ∀ u ∈ Icc 0 H, X ω b - E ω ≤ X ω (b - u)} ∩
       {ω | ∀ u ∈ Icc 0 H, Y ω b - E ω ≤ Y ω (b - u)}) ∩
      {ω | |X ω b - X ω a| ≤ E ω ∧
        ∀ t ∈ Icc a b, X ω b - E ω ≤ X ω t} := by
    ext ω
    simp only [approximateConeGridEvent, mem_ofPred_eq, mem_inter_iff]
    constructor
    · rintro ⟨hf, hb, hi⟩
      exact ⟨⟨hf, ⟨fun u hu => (hb u hu).1, fun u hu => (hb u hu).2⟩⟩, hi⟩
    · rintro ⟨⟨hf, hx, hy⟩, hi⟩
      exact ⟨hf, fun u hu => ⟨hx u hu, hy u hu⟩, hi⟩
  rw [heq]
  exact (hf.inter (hbX.inter hbY)).inter hi

/-- Allowing either coordinate orientation preserves measurability. -/
theorem measurableSet_approximateConeGridEvent_union {Ω : Type*} [MeasurableSpace Ω]
    (X Y : Ω → ℝ → ℝ) (E : Ω → ℝ) (a b H : ℝ)
    (hXcont : ∀ ω, Continuous (X ω)) (hYcont : ∀ ω, Continuous (Y ω))
    (hX : ∀ t, Measurable (fun ω => X ω t))
    (hY : ∀ t, Measurable (fun ω => Y ω t)) (hE : Measurable E) :
    MeasurableSet (approximateConeGridEvent X Y E a b H ∪
      approximateConeGridEvent Y X E a b H) :=
  (measurableSet_approximateConeGridEvent X Y E a b H hXcont hYcont hX hY hE).union
    (measurableSet_approximateConeGridEvent Y X E a b H hYcont hXcont hY hX hE)

/-- Closed local barriers imply their open-interval counterparts. -/
theorem approximateConeGridEvent_open {Ω : Type*} {X Y : Ω → ℝ → ℝ}
    {E : Ω → ℝ} {a b H : ℝ} {ω : Ω}
    (h : ω ∈ approximateConeGridEvent X Y E a b H) :
    (∀ u ∈ Ioo 0 H, X ω a - E ω ≤ X ω (a + u)) ∧
    (∀ u ∈ Ioo 0 H, X ω b - E ω ≤ X ω (b - u) ∧
      Y ω b - E ω ≤ Y ω (b - u)) ∧
    |X ω b - X ω a| ≤ E ω ∧
    ∀ t ∈ Icc a b, X ω b - E ω ≤ X ω t := by
  rcases h with ⟨hf, hb, hi⟩
  exact ⟨fun u hu => hf u ⟨le_of_lt hu.1, le_of_lt hu.2⟩,
    fun u hu => hb u ⟨le_of_lt hu.1, le_of_lt hu.2⟩, hi⟩

end LatticeProb
