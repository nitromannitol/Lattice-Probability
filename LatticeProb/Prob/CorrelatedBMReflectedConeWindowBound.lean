/-
Copyright (c) 2026. Released under the Apache 2.0 license.
-/
import LatticeProb.Prob.CorrelatedBMGaussianWindow
import LatticeProb.Prob.CorrelatedBMWindowBarrier
import LatticeProb.Prob.ApproximateConeWindowSplit

/-! # Reflected approximate cone events

A three-window estimate for approximate cone events evaluated at negative times. -/

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal

namespace LatticeProb.CorrelatedBM

open MatedCRTHarmonic.MatedCRT

/-- Reflected-time cone barriers are bounded by two outer-window probabilities
and a Gaussian middle-window factor. -/
theorem measure_reflected_approximateConeGridEvent_le {γ : ℝ} {μ : Measure Path2}
    (hμ : IsCorrelatedBM2 γ μ) (a b h H q : ℝ) (i j : Fin 2)
    (hh : 0 ≤ h) (hH : h ≤ H) (hgap : a + h < b - h) (hq : 0 ≤ q) :
    let A : Set Path2 := {ω | ∀ t ∈ Icc (-a - h) (-a),
      -q ≤ coneIncr i t (-a - h) ω - coneIncr i (-a) (-a - h) ω}
    let B : Set Path2 := {ω | ∀ t ∈ Icc (-b) (-b + h),
      -q ≤ coneIncr i t (-b) ω} ∩
      {ω | ∀ t ∈ Icc (-b) (-b + h), -q ≤ coneIncr j t (-b) ω}
    μ (approximateConeGridEvent (fun ω t => lrCoord i (-t) ω)
      (fun ω t => lrCoord j (-t) ω) (fun _ => q) a b H) ≤
      μ A * μ B * ENNReal.ofReal (2 * q / √(2 * Real.pi * (b - h - (a + h)))) := by
  dsimp only
  let A : Set Path2 := {ω | ∀ t ∈ Icc (-a - h) (-a),
    -q ≤ coneIncr i t (-a - h) ω - coneIncr i (-a) (-a - h) ω}
  let B : Set Path2 := {ω | ∀ t ∈ Icc (-b) (-b + h),
    -q ≤ coneIncr i t (-b) ω} ∩
    {ω | ∀ t ∈ Icc (-b) (-b + h), -q ≤ coneIncr j t (-b) ω}
  let Y : Path2 → ℝ := fun ω =>
    coneIncr i (-a) (-a - h) ω + coneIncr i (-b + h) (-b) ω
  let l : Fin 3 → ℝ := ![-a - h, -b, -b + h]
  let r : Fin 3 → ℝ := ![-a, -b + h, -a - h]
  have hsep : ∀ x y, x ≠ y → r x ≤ l y ∨ r y ≤ l x := by
    intro x y hxy
    fin_cases x <;> fin_cases y <;> simp_all [l, r] <;>
      first | left; linarith | right; linarith
  have hA : MeasurableSet[MeasurableSpace.comap
      (fun ω (p : Fin 2 × {x : ℝ // x ∈ Icc (l 0) (r 0)}) =>
        coneIncr p.1 p.2.1 (l 0) ω) inferInstance] A := by
    exact measurableSet_window_barrier (-a - h) (-a) (-q) (by linarith) i true
  have hB : MeasurableSet[MeasurableSpace.comap
      (fun ω (p : Fin 2 × {x : ℝ // x ∈ Icc (l 1) (r 1)}) =>
        coneIncr p.1 p.2.1 (l 1) ω) inferInstance] B := by
    change MeasurableSet[MeasurableSpace.comap
      (fun ω : Path2 => fun (p : Fin 2 × {x : ℝ // x ∈ Icc (-b) (-b + h)}) =>
        coneIncr p.1 p.2.1 (-b) ω) inferInstance]
      ({ω | ∀ t ∈ Icc (-b) (-b + h), -q ≤ coneIncr i t (-b) ω} ∩
       {ω | ∀ t ∈ Icc (-b) (-b + h), -q ≤ coneIncr j t (-b) ω})
    simpa only [Bool.false_eq_true, ↓reduceIte, sub_zero] using
      (measurableSet_window_barrier (-b) (-b + h) (-q) (by linarith) i false).inter
        (measurableSet_window_barrier (-b) (-b + h) (-q) (by linarith) j false)
  have hY : Measurable[MeasurableSpace.comap
      (fun ω => ((fun (p : Fin 2 × {x : ℝ // x ∈ Icc (l 0) (r 0)}) =>
          coneIncr p.1 p.2.1 (l 0) ω),
        (fun (p : Fin 2 × {x : ℝ // x ∈ Icc (l 1) (r 1)}) =>
          coneIncr p.1 p.2.1 (l 1) ω))) inferInstance] Y := by
    exact measurable_window_endpoint_sum (-a - h) (-a) (-b) (-b + h)
      (by linarith) (by linarith) i
  have hbound := measure_outer_inter_middle_window_le hμ l r hsep 0 1 2
    (by decide) (by decide) (by decide) (by dsimp [l, r]; linarith) i hA hB hY hq
  calc
    μ (approximateConeGridEvent (fun ω t => lrCoord i (-t) ω)
        (fun ω t => lrCoord j (-t) ω) (fun _ => q) a b H) ≤
        μ ((A ∩ B) ∩ {ω | |Y ω + coneIncr i (-a - h) (-b + h) ω| ≤ q}) := by
      apply measure_mono
      intro ω hω
      obtain ⟨hf, hb, hi⟩ := approximateConeGridEvent_window_split hH hω
      refine ⟨⟨?_, ?_⟩, ?_⟩
      · intro t ht
        have hf' := hf (-a - t) ⟨by linarith [ht.2], by linarith [ht.1]⟩
        have : -(a + (-a - t)) = t := by ring
        rw [this] at hf'
        dsimp only [coneIncr]
        linarith
      · constructor <;> intro t ht
        · have hb' := (hb (t + b) ⟨by linarith [ht.1], by linarith [ht.2]⟩).1
          have : -(b - (t + b)) = t := by ring
          rw [this] at hb'
          dsimp only [coneIncr]
          linarith
        · have hb' := (hb (t + b) ⟨by linarith [ht.1], by linarith [ht.2]⟩).2
          have : -(b - (t + b)) = t := by ring
          rw [this] at hb'
          dsimp only [coneIncr]
          linarith
      · change |Y ω + coneIncr i (-a - h) (-b + h) ω| ≤ q
        dsimp only [Y, coneIncr]
        have heq : lrCoord i (-a) ω - lrCoord i (-a - h) ω +
            (lrCoord i (-b + h) ω - lrCoord i (-b) ω) +
            (lrCoord i (-a - h) ω - lrCoord i (-b + h) ω) =
            -(lrCoord i (-b) ω - lrCoord i (-a) ω) := by ring
        rw [heq, abs_neg]
        have hi_eq : lrCoord i (-(b - h)) ω - lrCoord i (-(a + h)) ω +
            (lrCoord i (-(a + h)) ω - lrCoord i (-a) ω) -
            (lrCoord i (-(b - h)) ω - lrCoord i (-b) ω) =
            lrCoord i (-b) ω - lrCoord i (-a) ω := by ring
        rw [hi_eq] at hi
        exact hi
    _ ≤ μ A * μ B * ENNReal.ofReal (2 * q / √(2 * Real.pi * (b - h - (a + h)))) := by
      have heq : -a - h - (-b + h) = b - h - (a + h) := by ring
      simpa [l, r, heq] using hbound

end LatticeProb.CorrelatedBM
