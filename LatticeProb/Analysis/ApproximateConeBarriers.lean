import LatticeProb.Analysis.LocalBarrierTransfer
import LatticeProb.Analysis.ClosedBarrierTransfer

/-!
# Approximate barriers near two path anchors

Local forward and backward barriers and a matching interval barrier persist
at nearby ordered anchors, with an error controlled by a uniform modulus.
-/

set_option autoImplicit false

open Set

namespace LatticeProb

/-- Transfer two local path barriers and an equal-endpoint interval barrier
simultaneously to nearby ordered anchors. -/
theorem approximate_twoAnchor_barriers_of_modulus
    {X Y : ℝ → ℝ} {s₀ s₁ t₀ t₁ δ L₁ H e : ℝ}
    (hs : s₀ ≤ s₁) (ht : t₀ ≤ t₁) (hδ : 0 ≤ δ)
    (hL₁ : 0 ≤ L₁) (hH : 0 ≤ H)
    (h₀ : |t₀ - s₀| ≤ δ) (h₁ : |t₁ - s₁| ≤ δ)
    (hforward : t₀ + H ≤ s₁) (hbackward : s₁ - L₁ ≤ t₁ - H)
    (hmodX : ∀ x ∈ Icc (s₀ - δ - L₁) (s₁ + δ),
      ∀ y ∈ Icc (s₀ - δ - L₁) (s₁ + δ), |x - y| ≤ δ → |X x - X y| ≤ e)
    (hmodY : ∀ x ∈ Icc (s₀ - δ - L₁) (s₁ + δ),
      ∀ y ∈ Icc (s₀ - δ - L₁) (s₁ + δ), |x - y| ≤ δ → |Y x - Y y| ≤ e)
    (heq : X s₀ = X s₁)
    (hinterval : ∀ x ∈ Icc s₀ s₁, X s₁ ≤ X x)
    (hlocal₁ : ∀ x ∈ Icc (s₁ - L₁) s₁, X s₁ ≤ X x ∧ Y s₁ ≤ Y x) :
    (∀ u ∈ Icc 0 H, X t₀ - 2 * e ≤ X (t₀ + u)) ∧
    (∀ u ∈ Icc 0 H, X t₁ - 2 * e ≤ X (t₁ - u) ∧
      Y t₁ - 2 * e ≤ Y (t₁ - u)) ∧
    |X t₁ - X t₀| ≤ 2 * e ∧
    ∀ x ∈ Icc t₀ t₁, X t₁ - 2 * e ≤ X x := by
  have he : 0 ≤ e := by
    have hmem : s₀ ∈ Icc (s₀ - δ - L₁) (s₁ + δ) := ⟨by linarith, by linarith⟩
    have h := hmodX s₀ hmem s₀ hmem (by simpa using hδ)
    simpa using h
  have hf := forward_localBarrier_of_modulus (L := s₁ - s₀) hδ
    (sub_nonneg.mpr hs) hH h₀ (by linarith)
    (fun x hx y hy h => hmodX x ⟨by linarith [hx.1], by linarith [hx.2]⟩ y ⟨by linarith [hy.1], by linarith [hy.2]⟩ h) (by
      intro x hx
      have h := hinterval x ⟨hx.1, by linarith [hx.2]⟩
      linarith)
  have hbX := backward_localBarrier_of_modulus hδ hL₁ hH h₁ hbackward
    (fun x hx y hy h => hmodX x ⟨by linarith [hx.1], by linarith [hx.2]⟩ y ⟨by linarith [hy.1], by linarith [hy.2]⟩ h) (fun x hx => (hlocal₁ x hx).1)
  have hbY := backward_localBarrier_of_modulus hδ hL₁ hH h₁ hbackward
    (fun x hx y hy h => hmodY x ⟨by linarith [hx.1], by linarith [hx.2]⟩ y ⟨by linarith [hy.1], by linarith [hy.2]⟩ h) (fun x hx => (hlocal₁ x hx).2)
  have hc := closedInterval_barrier_of_modulus hs ht hδ h₀ h₁
    (fun x hx y hy h => hmodX x ⟨by linarith [hx.1], by linarith [hx.2]⟩ y ⟨by linarith [hy.1], by linarith [hy.2]⟩ h) heq hinterval
  refine ⟨?_, ?_, hc⟩
  · intro u hu
    have h := hf u hu
    linarith
  · intro u hu
    have hx := hbX u hu
    have hy := hbY u hu
    constructor <;> linarith

end LatticeProb
