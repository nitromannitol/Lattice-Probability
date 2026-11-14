/-
Copyright (c) 2026. Released under the Apache 2.0 license.
-/
import LatticeProb.Prob.CorrelatedBMGaussianWindow
import LatticeProb.Prob.CorrelatedBMWindowBarrier
import LatticeProb.Prob.ApproximateConeWindowSplit

/-! # Approximate cone events and Gaussian windows

An approximate cone event is controlled by two local barrier probabilities
and a Gaussian interval bound for the intervening increment. -/

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal

namespace LatticeProb.CorrelatedBM

open MatedCRTHarmonic.MatedCRT

/-- A three-window estimate for a fixed approximate cone event. -/
theorem measure_approximateConeGridEvent_le {γ : ℝ} {μ : Measure Path2}
    (hμ : IsCorrelatedBM2 γ μ) (a b h H q : ℝ) (i j : Fin 2)
    (hh : 0 ≤ h) (hH : h ≤ H) (hgap : a + h < b - h) (hq : 0 ≤ q) :
    let A : Set Path2 := {ω | ∀ t ∈ Icc a (a + h),
      -q ≤ coneIncr i t a ω}
    let B : Set Path2 := {ω | ∀ t ∈ Icc (b - h) b,
      -q ≤ coneIncr i t (b - h) ω - coneIncr i b (b - h) ω} ∩
      {ω | ∀ t ∈ Icc (b - h) b,
      -q ≤ coneIncr j t (b - h) ω - coneIncr j b (b - h) ω}
    μ (approximateConeGridEvent (fun ω t => lrCoord i t ω)
      (fun ω t => lrCoord j t ω) (fun _ => q) a b H) ≤
      μ A * μ B * ENNReal.ofReal (2 * q / √(2 * Real.pi * (b - h - (a + h)))) := by
  dsimp only
  let A : Set Path2 := {ω | ∀ t ∈ Icc a (a + h),
    -q ≤ coneIncr i t a ω}
  let B : Set Path2 := {ω | ∀ t ∈ Icc (b - h) b,
    -q ≤ coneIncr i t (b - h) ω - coneIncr i b (b - h) ω} ∩
    {ω | ∀ t ∈ Icc (b - h) b,
    -q ≤ coneIncr j t (b - h) ω - coneIncr j b (b - h) ω}
  let Y : Path2 → ℝ := fun ω => coneIncr i (a + h) a ω + coneIncr i b (b - h) ω
  let l : Fin 3 → ℝ := ![a, b - h, a + h]
  let r : Fin 3 → ℝ := ![a + h, b, b - h]
  have hsep : ∀ x y, x ≠ y → r x ≤ l y ∨ r y ≤ l x := by
    intro x y hxy
    fin_cases x <;> fin_cases y <;> simp_all [l, r] <;>
      first | left; linarith | right; linarith
  have hA : MeasurableSet[MeasurableSpace.comap
      (fun ω (p : Fin 2 × {x : ℝ // x ∈ Icc (l 0) (r 0)}) =>
        coneIncr p.1 p.2.1 (l 0) ω) inferInstance] A := by
    change MeasurableSet[MeasurableSpace.comap
      (fun ω : Path2 => fun (p : Fin 2 × {x : ℝ // x ∈ Icc a (a + h)}) =>
        coneIncr p.1 p.2.1 a ω) inferInstance]
      {ω | ∀ t ∈ Icc a (a + h), -q ≤ coneIncr i t a ω}
    simpa only [Bool.false_eq_true, ↓reduceIte, sub_zero] using
      measurableSet_window_barrier a (a + h) (-q) (by linarith) i false
  have hB : MeasurableSet[MeasurableSpace.comap
      (fun ω (p : Fin 2 × {x : ℝ // x ∈ Icc (l 1) (r 1)}) =>
        coneIncr p.1 p.2.1 (l 1) ω) inferInstance] B := by
    exact
      (measurableSet_window_barrier (b - h) b (-q) (by linarith) i true).inter
        (measurableSet_window_barrier (b - h) b (-q) (by linarith) j true)
  have hY : Measurable[MeasurableSpace.comap
      (fun ω => ((fun (p : Fin 2 × {x : ℝ // x ∈ Icc (l 0) (r 0)}) =>
          coneIncr p.1 p.2.1 (l 0) ω),
        (fun (p : Fin 2 × {x : ℝ // x ∈ Icc (l 1) (r 1)}) =>
          coneIncr p.1 p.2.1 (l 1) ω))) inferInstance] Y := by
    exact measurable_window_endpoint_sum a (a + h) (b - h) b
      (by linarith) (by linarith) i
  have hbound := measure_outer_inter_middle_window_le hμ l r hsep 0 1 2
    (by decide) (by decide) (by decide) (by simpa [l, r] using hgap) i hA hB hY hq
  calc
    μ (approximateConeGridEvent (fun ω t => lrCoord i t ω)
        (fun ω t => lrCoord j t ω) (fun _ => q) a b H) ≤
        μ ((A ∩ B) ∩ {ω | |Y ω + coneIncr i (b - h) (a + h) ω| ≤ q}) := by
      apply measure_mono
      intro ω hω
      obtain ⟨hf, hb, hi⟩ := approximateConeGridEvent_window_split hH hω
      refine ⟨⟨?_, ?_⟩, ?_⟩
      · intro t ht
        have hf' := hf (t - a) ⟨by linarith [ht.1], by linarith [ht.2]⟩
        unfold coneIncr
        have : a + (t - a) = t := by ring
        rw [this] at hf'
        exact hf'
      · constructor <;> intro t ht
        · have hb' := (hb (b - t) ⟨by linarith [ht.2], by linarith [ht.1]⟩).1
          unfold coneIncr
          have : b - (b - t) = t := by ring
          rw [this] at hb'
          linarith
        · have hb' := (hb (b - t) ⟨by linarith [ht.2], by linarith [ht.1]⟩).2
          unfold coneIncr
          have : b - (b - t) = t := by ring
          rw [this] at hb'
          linarith
      · dsimp [Y, coneIncr]
        convert hi using 1; congr 1; ring
    _ ≤ μ A * μ B * ENNReal.ofReal (2 * q / √(2 * Real.pi * (b - h - (a + h)))) := by
      simpa [l, r] using hbound

end LatticeProb.CorrelatedBM
