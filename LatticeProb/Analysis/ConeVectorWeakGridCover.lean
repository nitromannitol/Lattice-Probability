import LatticeProb.Analysis.OrderedGridAnchors
import LatticeProb.Analysis.ApproximateConeBarriers
import LatticeProb.Analysis.ConeJointExitEndpoint

/-!
# Grid barriers for backward cone vectors

Closed barriers associated with a backward cone vector yield approximate
barriers on an ordered finite grid, in one of the coordinate orientations.
-/

set_option autoImplicit false

open Set

namespace LatticeProb

/-- An equal-endpoint closed barrier and a joint terminal barrier transfer to
ordered grid anchors. -/
theorem closedBarriers_exists_grid_barriers
    {X Y : ℝ → ℝ} {N : ℕ} (hN : 0 < N) {a b s d H e : ℝ}
    (ha : 0 < a) (hab : a < b) (hbs : b < s) (hs : s < 1)
    (heq : X a = X s) (hinterval : ∀ x ∈ Icc a s, X s ≤ X x)
    (hlocal : ∀ x ∈ Icc b s, X s ≤ X x ∧ Y s ≤ Y x)
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
      (∀ u ∈ Icc 0 H, X t₀ - 2 * e ≤ X (t₀ + u)) ∧
      (∀ u ∈ Icc 0 H, X t₁ - 2 * e ≤ X (t₁ - u) ∧
        Y t₁ - 2 * e ≤ Y (t₁ - u)) ∧
      |X t₁ - X t₀| ≤ 2 * e ∧
      ∀ x ∈ Icc t₀ t₁, X t₁ - 2 * e ≤ X x := by
  obtain ⟨i, j, hi, hj, hdist, h₀, h₁, hf, hb⟩ :=
    exists_ordered_grid_anchors hN ha hs hd hmesh hsep hforward hbackward
  have ht : (i.val : ℝ) / N ≤ (j.val : ℝ) / N := by linarith
  have hδ : 0 ≤ 1 / (N : ℝ) := by positivity
  have hbar := approximate_twoAnchor_barriers_of_modulus (le_of_lt (lt_trans hab hbs))
    ht hδ (sub_nonneg.mpr hbs.le) hH h₀ h₁ hf (by linarith) hmodX hmodY
    heq hinterval (by simpa using hlocal)
  exact ⟨i, j, hi, hj, hdist, h₀, h₁, hbar⟩

/-- Every backward cone vector with earlier strict drops has approximate grid
barriers in one of the two coordinate orientations. -/
theorem backwardConeVector_exists_grid_barriers
    {X Y : ℝ → ℝ} {N : ℕ} (hN : 0 < N) {a s d H e : ℝ}
    (hX : Continuous X) (hY : Continuous Y)
    (hx : ∃ r < s, X r < X s) (hy : ∃ r < s, Y r < Y s)
    (hvec : (a, s) ∈ backwardConeVectors X Y)
    (ha : 0 < a) (hs : s < 1) (hd : 0 ≤ d) (hH : 0 ≤ H)
    (hmesh : 1 / (N : ℝ) < a)
    (hsep : d + 1 / (N : ℝ) < s - a)
    (hforward : a + H ≤ s)
    (hbackward : coneFirstExitBackward X Y s + H + 1 / (N : ℝ) < s)
    (hmodX : ∀ x ∈ Icc (a - 1 / (N : ℝ) - (s - coneFirstExitBackward X Y s))
        (s + 1 / (N : ℝ)),
      ∀ y ∈ Icc (a - 1 / (N : ℝ) - (s - coneFirstExitBackward X Y s))
        (s + 1 / (N : ℝ)), |x - y| ≤ 1 / (N : ℝ) → |X x - X y| ≤ e)
    (hmodY : ∀ x ∈ Icc (a - 1 / (N : ℝ) - (s - coneFirstExitBackward X Y s))
        (s + 1 / (N : ℝ)),
      ∀ y ∈ Icc (a - 1 / (N : ℝ) - (s - coneFirstExitBackward X Y s))
        (s + 1 / (N : ℝ)), |x - y| ≤ 1 / (N : ℝ) → |Y x - Y y| ≤ e) :
    ∃ i j : Fin N,
      let t₀ : ℝ := (i.val : ℝ) / N
      let t₁ : ℝ := (j.val : ℝ) / N
      0 < t₀ ∧ t₁ < 1 ∧ d < t₁ - t₀ ∧
      |t₀ - a| ≤ 1 / (N : ℝ) ∧ |t₁ - s| ≤ 1 / (N : ℝ) ∧
      (((∀ u ∈ Icc 0 H, X t₀ - 2 * e ≤ X (t₀ + u)) ∧
        (∀ u ∈ Icc 0 H, X t₁ - 2 * e ≤ X (t₁ - u) ∧
          Y t₁ - 2 * e ≤ Y (t₁ - u)) ∧
        |X t₁ - X t₀| ≤ 2 * e ∧
        ∀ x ∈ Icc t₀ t₁, X t₁ - 2 * e ≤ X x) ∨
      ((∀ u ∈ Icc 0 H, Y t₀ - 2 * e ≤ Y (t₀ + u)) ∧
        (∀ u ∈ Icc 0 H, Y t₁ - 2 * e ≤ Y (t₁ - u) ∧
          X t₁ - 2 * e ≤ X (t₁ - u)) ∧
        |Y t₁ - Y t₀| ≤ 2 * e ∧
        ∀ x ∈ Icc t₀ t₁, Y t₁ - 2 * e ≤ Y x)) := by
  have hab : a < coneFirstExitBackward X Y s := by simpa only [← hvec.1] using hvec.2.1
  have hbs : coneFirstExitBackward X Y s < s := hvec.2.2.1
  have hlocal := hvec.2.2.2
  have hbar := jointBackwardExit_closed_barrier hX hY hx hy
  rw [← hvec.1] at hbar
  rcases hbar with ⟨heq, hinterval⟩ | ⟨heq, hinterval⟩
  · obtain ⟨i, j, hi, hj, hdist, h₀, h₁, hrest⟩ :=
      closedBarriers_exists_grid_barriers hN ha hab hbs hs heq hinterval hlocal
        hd hH hmesh hsep hforward hbackward hmodX hmodY
    exact ⟨i, j, hi, hj, hdist, h₀, h₁, Or.inl hrest⟩
  · have hlocal' : ∀ x ∈ Icc (coneFirstExitBackward X Y s) s,
        Y s ≤ Y x ∧ X s ≤ X x := by
      intro x hx
      exact ⟨(hlocal x hx).2, (hlocal x hx).1⟩
    obtain ⟨i, j, hi, hj, hdist, h₀, h₁, hrest⟩ :=
      closedBarriers_exists_grid_barriers hN ha hab hbs hs heq hinterval hlocal'
        hd hH hmesh hsep hforward hbackward hmodY hmodX
    exact ⟨i, j, hi, hj, hdist, h₀, h₁, Or.inr hrest⟩

end LatticeProb
