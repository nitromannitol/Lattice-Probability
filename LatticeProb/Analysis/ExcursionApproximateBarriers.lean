import LatticeProb.Analysis.ApproximateConeBarriers
import LatticeProb.Analysis.ConeVectorMembership

/-!
# Approximate barriers from backward excursions

A pair of strict backward excursions with ordered endpoints supplies the
barriers at the true anchors, and hence the approximate barriers at nearby
anchors when a modulus of continuity and horizon margins are available.
-/

set_option autoImplicit false

open Set

namespace LatticeProb

/-- Ordered backward excursions provide a cone vector and the corresponding
approximate local and interval barriers. -/
theorem backwardExcursions_approximate_barriers
    {X Y : ℝ → ℝ} {a b s t₀ t₁ δ H e : ℝ}
    (hab : a < b) (hbs : b < s)
    (hXa : X a = X s) (hX : ∀ x ∈ Ioo a s, X a < X x)
    (hYa : Y b = Y s) (hY : ∀ x ∈ Ioo b s, Y b < Y x)
    (hXmin : ¬ IsLocalMin X a) (hYmin : ¬ IsLocalMin Y b)
    (ht : t₀ ≤ t₁) (hδ : 0 ≤ δ) (hH : 0 ≤ H)
    (h₀ : |t₀ - a| ≤ δ) (h₁ : |t₁ - s| ≤ δ)
    (hforward : t₀ + H ≤ s) (hbackward : b ≤ t₁ - H)
    (hmodX : ∀ x ∈ Icc (a - δ - (s - b)) (s + δ),
      ∀ y ∈ Icc (a - δ - (s - b)) (s + δ), |x - y| ≤ δ → |X x - X y| ≤ e)
    (hmodY : ∀ x ∈ Icc (a - δ - (s - b)) (s + δ),
      ∀ y ∈ Icc (a - δ - (s - b)) (s + δ), |x - y| ≤ δ → |Y x - Y y| ≤ e) :
    (a, s) ∈ backwardConeVectors X Y ∧
    (∀ u ∈ Icc 0 H, X t₀ - 2 * e ≤ X (t₀ + u)) ∧
    (∀ u ∈ Icc 0 H, X t₁ - 2 * e ≤ X (t₁ - u) ∧
      Y t₁ - 2 * e ≤ Y (t₁ - u)) ∧
    |X t₁ - X t₀| ≤ 2 * e ∧
    ∀ x ∈ Icc t₀ t₁, X t₁ - 2 * e ≤ X x := by
  have has : a < s := lt_trans hab hbs
  have hinterval : ∀ x ∈ Icc a s, X s ≤ X x := by
    intro x hx
    rcases eq_or_lt_of_le hx.1 with rfl | hax
    · exact le_of_eq hXa.symm
    rcases eq_or_lt_of_le hx.2 with rfl | hxs
    · exact le_rfl
    · have h := hX x ⟨hax, hxs⟩
      linarith
  have hlocal : ∀ x ∈ Icc (s - (s - b)) s, X s ≤ X x ∧ Y s ≤ Y x := by
    intro x hx
    have hbx : b ≤ x := by linarith [hx.1]
    refine ⟨hinterval x ⟨le_trans (le_of_lt hab) hbx, hx.2⟩, ?_⟩
    rcases eq_or_lt_of_le hbx with rfl | hbx
    · exact le_of_eq hYa.symm
    rcases eq_or_lt_of_le hx.2 with rfl | hxs
    · exact le_rfl
    · have h := hY x ⟨hbx, hxs⟩
      linarith
  have hcone := backwardConeVector_of_excursions has hXa hX hXmin hbs hYa hY hYmin
    (ne_of_lt hab)
  have hvec : (a, s) ∈ backwardConeVectors X Y := by
    rcases hcone.2 with h | h
    · have hj := hcone.1.2.1
      rw [← h.1, ← h.2] at hj
      linarith
    · rw [h.1]
      exact hcone.1
  exact ⟨hvec, approximate_twoAnchor_barriers_of_modulus (le_of_lt has) ht hδ
    (sub_nonneg.mpr (le_of_lt hbs)) hH h₀ h₁ hforward (by linarith)
    hmodX hmodY hXa hinterval hlocal⟩

end LatticeProb
