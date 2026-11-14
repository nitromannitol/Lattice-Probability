/-
Copyright (c) 2026. Released under the Apache 2.0 license.
-/
import Mathlib

/-!
# Transfer of closed-interval path barriers

Equal endpoint values and a lower barrier transfer to nearby ordered endpoints
under a uniform local modulus of continuity.
-/

set_option autoImplicit false

open Set

namespace LatticeProb

/-- An interval lower barrier with equal endpoint values yields an approximate
barrier and a small endpoint increment on a nearby ordered interval. -/
theorem closedInterval_barrier_of_modulus {f : ℝ → ℝ} {s₁ s₂ t₁ t₂ δ e : ℝ}
    (hs : s₁ ≤ s₂) (ht : t₁ ≤ t₂) (hδ : 0 ≤ δ)
    (h₁ : |t₁ - s₁| ≤ δ) (h₂ : |t₂ - s₂| ≤ δ)
    (hmod : ∀ x ∈ Icc (s₁ - δ) (s₂ + δ), ∀ y ∈ Icc (s₁ - δ) (s₂ + δ),
      |x - y| ≤ δ → |f x - f y| ≤ e)
    (heq : f s₁ = f s₂)
    (hbar : ∀ x ∈ Icc s₁ s₂, f s₂ ≤ f x) :
    |f t₂ - f t₁| ≤ 2 * e ∧ ∀ x ∈ Icc t₁ t₂, f t₂ - 2 * e ≤ f x := by
  have h₁' := abs_le.mp h₁
  have h₂' := abs_le.mp h₂
  have hs₁ : s₁ ∈ Icc (s₁ - δ) (s₂ + δ) := ⟨by linarith, by linarith⟩
  have hs₂ : s₂ ∈ Icc (s₁ - δ) (s₂ + δ) := ⟨by linarith, by linarith⟩
  have ht₁ : t₁ ∈ Icc (s₁ - δ) (s₂ + δ) := ⟨by linarith, by linarith⟩
  have ht₂ : t₂ ∈ Icc (s₁ - δ) (s₂ + δ) := ⟨by linarith, by linarith⟩
  have hm₁ := abs_le.mp (hmod t₁ ht₁ s₁ hs₁ h₁)
  have hm₂ := abs_le.mp (hmod t₂ ht₂ s₂ hs₂ h₂)
  have he : 0 ≤ e := by
    have hm := hmod s₂ hs₂ s₂ hs₂ (by simpa using hδ)
    simpa using hm
  constructor
  · apply abs_le.mpr
    constructor <;> linarith
  · intro x hx
    have hx' : x ∈ Icc (s₁ - δ) (s₂ + δ) := ⟨by linarith [hx.1], by linarith [hx.2]⟩
    by_cases hleft : x < s₁
    · have hd : |x - s₁| ≤ δ := abs_le.mpr ⟨by linarith [hx.1], by linarith⟩
      have hm := abs_le.mp (hmod x hx' s₁ hs₁ hd)
      linarith
    · by_cases hright : s₂ < x
      · have hd : |x - s₂| ≤ δ := abs_le.mpr ⟨by linarith, by linarith [hx.2]⟩
        have hm := abs_le.mp (hmod x hx' s₂ hs₂ hd)
        linarith
      · have hb := hbar x ⟨le_of_not_gt hleft, le_of_not_gt hright⟩
        linarith

end LatticeProb
