import LatticeProb.Analysis.OrderedGridAnchors
import LatticeProb.Analysis.ExcursionApproximateBarriers

/-!
# Grid approximation of ordered excursions

Ordered strict excursions yield approximate path barriers at a pair of finite
grid points, provided the mesh is small relative to the separation and horizons.
-/

set_option autoImplicit false

open Set

namespace LatticeProb

/-- Ordered backward excursions have grid anchors with approximate barriers. -/
theorem backwardExcursions_exists_grid_barriers
    {X Y : ℝ → ℝ} {N : ℕ} (hN : 0 < N) {a b s d H e : ℝ}
    (ha : 0 < a) (hab : a < b) (hbs : b < s) (hs : s < 1)
    (hXa : X a = X s) (hX : ∀ x ∈ Ioo a s, X a < X x)
    (hYa : Y b = Y s) (hY : ∀ x ∈ Ioo b s, Y b < Y x)
    (hXmin : ¬ IsLocalMin X a) (hYmin : ¬ IsLocalMin Y b)
    (hd : 0 ≤ d) (hH : 0 ≤ H)
    (hmesh : 1 / (N : ℝ) < a)
    (hsep : d + 1 / (N : ℝ) < s - a)
    (hforward : a + H ≤ s) (hbackward : b + H + 1 / (N : ℝ) < s)
    (hmodX : ∀ x ∈ Icc (a - 1 / (N : ℝ) - (s - b)) (s + 1 / (N : ℝ)),
      ∀ y ∈ Icc (a - 1 / (N : ℝ) - (s - b)) (s + 1 / (N : ℝ)),
        |x - y| ≤ 1 / (N : ℝ) → |X x - X y| ≤ e)
    (hmodY : ∀ x ∈ Icc (a - 1 / (N : ℝ) - (s - b)) (s + 1 / (N : ℝ)),
      ∀ y ∈ Icc (a - 1 / (N : ℝ) - (s - b)) (s + 1 / (N : ℝ)),
        |x - y| ≤ 1 / (N : ℝ) → |Y x - Y y| ≤ e) :
    ∃ i j : Fin N,
      let t₀ : ℝ := (i.val : ℝ) / N
      let t₁ : ℝ := (j.val : ℝ) / N
      0 < t₀ ∧ t₁ < 1 ∧ d < t₁ - t₀ ∧
      |t₀ - a| ≤ 1 / (N : ℝ) ∧ |t₁ - s| ≤ 1 / (N : ℝ) ∧
      (a, s) ∈ backwardConeVectors X Y ∧
      (∀ u ∈ Icc 0 H, X t₀ - 2 * e ≤ X (t₀ + u)) ∧
      (∀ u ∈ Icc 0 H, X t₁ - 2 * e ≤ X (t₁ - u) ∧
        Y t₁ - 2 * e ≤ Y (t₁ - u)) ∧
      |X t₁ - X t₀| ≤ 2 * e ∧
      ∀ x ∈ Icc t₀ t₁, X t₁ - 2 * e ≤ X x := by
  obtain ⟨i, j, hi, hj, hdist, h₀, h₁, hf, hb⟩ :=
    exists_ordered_grid_anchors hN ha hs hd hmesh hsep hforward hbackward
  have ht : (i.val : ℝ) / N ≤ (j.val : ℝ) / N := by linarith
  have hδ : 0 ≤ 1 / (N : ℝ) := by positivity
  have hbar := backwardExcursions_approximate_barriers hab hbs hXa hX hYa hY
    hXmin hYmin ht hδ hH h₀ h₁ hf hb hmodX hmodY
  exact ⟨i, j, hi, hj, hdist, h₀, h₁, hbar⟩

/-- Backward cone vectors are unchanged by exchanging the coordinates. -/
theorem backwardConeVectors_swap (X Y : ℝ → ℝ) :
    backwardConeVectors Y X = backwardConeVectors X Y := by
  ext p
  simp only [backwardConeVectors, mem_ofPred_eq, coneJointExitBackward,
    coneFirstExitBackward, or_comm, and_comm]

/-- The same grid construction applies with the two coordinates exchanged. -/
theorem backwardExcursions_exists_grid_barriers_swap
    {X Y : ℝ → ℝ} {N : ℕ} (hN : 0 < N) {a b s d H e : ℝ}
    (ha : 0 < a) (hab : a < b) (hbs : b < s) (hs : s < 1)
    (hXa : Y a = Y s) (hX : ∀ x ∈ Ioo a s, Y a < Y x)
    (hYa : X b = X s) (hY : ∀ x ∈ Ioo b s, X b < X x)
    (hXmin : ¬ IsLocalMin Y a) (hYmin : ¬ IsLocalMin X b)
    (hd : 0 ≤ d) (hH : 0 ≤ H)
    (hmesh : 1 / (N : ℝ) < a)
    (hsep : d + 1 / (N : ℝ) < s - a)
    (hforward : a + H ≤ s) (hbackward : b + H + 1 / (N : ℝ) < s)
    (hmodX : ∀ x ∈ Icc (a - 1 / (N : ℝ) - (s - b)) (s + 1 / (N : ℝ)),
      ∀ y ∈ Icc (a - 1 / (N : ℝ) - (s - b)) (s + 1 / (N : ℝ)),
        |x - y| ≤ 1 / (N : ℝ) → |Y x - Y y| ≤ e)
    (hmodY : ∀ x ∈ Icc (a - 1 / (N : ℝ) - (s - b)) (s + 1 / (N : ℝ)),
      ∀ y ∈ Icc (a - 1 / (N : ℝ) - (s - b)) (s + 1 / (N : ℝ)),
        |x - y| ≤ 1 / (N : ℝ) → |X x - X y| ≤ e) :
    ∃ i j : Fin N,
      let t₀ : ℝ := (i.val : ℝ) / N
      let t₁ : ℝ := (j.val : ℝ) / N
      0 < t₀ ∧ t₁ < 1 ∧ d < t₁ - t₀ ∧
      |t₀ - a| ≤ 1 / (N : ℝ) ∧ |t₁ - s| ≤ 1 / (N : ℝ) ∧
      (a, s) ∈ backwardConeVectors X Y ∧
      (∀ u ∈ Icc 0 H, Y t₀ - 2 * e ≤ Y (t₀ + u)) ∧
      (∀ u ∈ Icc 0 H, Y t₁ - 2 * e ≤ Y (t₁ - u) ∧
        X t₁ - 2 * e ≤ X (t₁ - u)) ∧
      |Y t₁ - Y t₀| ≤ 2 * e ∧
      ∀ x ∈ Icc t₀ t₁, Y t₁ - 2 * e ≤ Y x := by
  simpa only [backwardConeVectors_swap Y X] using
    (backwardExcursions_exists_grid_barriers hN ha hab hbs hs hXa hX hYa hY
      hXmin hYmin hd hH hmesh hsep hforward hbackward hmodX hmodY)

end LatticeProb
