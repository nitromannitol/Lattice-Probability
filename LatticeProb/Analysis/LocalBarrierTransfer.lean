/-
Copyright (c) 2026. Released under the Apache 2.0 license.
-/
import Mathlib

/-!
# Transfer of local path barriers

A lower barrier based at one time transfers to a nearby anchor, with an error
controlled by a local modulus of continuity. Both time directions are covered.
-/

set_option autoImplicit false

open Set

namespace LatticeProb

/-- A forward lower barrier transfers to a nearby anchor. The shifted interval
must end within the original barrier interval. -/
theorem forward_localBarrier_of_modulus {f : ℝ → ℝ} {s t δ L H e : ℝ}
    (hδ : 0 ≤ δ) (hL : 0 ≤ L) (hH : 0 ≤ H)
    (hst : |t - s| ≤ δ) (hend : t + H ≤ s + L)
    (hmod : ∀ x ∈ Icc (s - δ) (s + L), ∀ y ∈ Icc (s - δ) (s + L),
      |x - y| ≤ δ → |f x - f y| ≤ e)
    (hbar : ∀ x ∈ Icc s (s + L), f s ≤ f x) :
    ∀ u ∈ Icc 0 H, f t - e ≤ f (t + u) := by
  have hst' := abs_le.mp hst
  have hs : s ∈ Icc (s - δ) (s + L) := ⟨by linarith, by linarith⟩
  have ht : t ∈ Icc (s - δ) (s + L) := ⟨by linarith, by linarith⟩
  intro u hu
  have hx : t + u ∈ Icc (s - δ) (s + L) := ⟨by linarith [hu.1], by linarith [hu.2]⟩
  by_cases h : s ≤ t + u
  · have hb := hbar (t + u) ⟨h, hx.2⟩
    have hm := abs_le.mp (hmod t ht s hs hst)
    linarith
  · have hdist : |t - (t + u)| ≤ δ := abs_le.mpr ⟨by linarith [hu.1], by linarith [hu.1]⟩
    have hm := abs_le.mp (hmod t ht (t + u) hx hdist)
    linarith

/-- A backward lower barrier transfers to a nearby anchor. The shifted interval
must begin within the original barrier interval. -/
theorem backward_localBarrier_of_modulus {f : ℝ → ℝ} {s t δ L H e : ℝ}
    (hδ : 0 ≤ δ) (hL : 0 ≤ L) (hH : 0 ≤ H)
    (hst : |t - s| ≤ δ) (hend : s - L ≤ t - H)
    (hmod : ∀ x ∈ Icc (s - L) (s + δ), ∀ y ∈ Icc (s - L) (s + δ),
      |x - y| ≤ δ → |f x - f y| ≤ e)
    (hbar : ∀ x ∈ Icc (s - L) s, f s ≤ f x) :
    ∀ u ∈ Icc 0 H, f t - e ≤ f (t - u) := by
  have hst' := abs_le.mp hst
  have hs : s ∈ Icc (s - L) (s + δ) := ⟨by linarith, by linarith⟩
  have ht : t ∈ Icc (s - L) (s + δ) := ⟨by linarith, by linarith⟩
  intro u hu
  have hx : t - u ∈ Icc (s - L) (s + δ) := ⟨by linarith [hu.2], by linarith [hu.1]⟩
  by_cases h : t - u ≤ s
  · have hb := hbar (t - u) ⟨hx.1, h⟩
    have hm := abs_le.mp (hmod t ht s hs hst)
    linarith
  · have hdist : |t - (t - u)| ≤ δ := abs_le.mpr ⟨by linarith [hu.1], by linarith [hu.1]⟩
    have hm := abs_le.mp (hmod t ht (t - u) hx hdist)
    linarith

end LatticeProb
