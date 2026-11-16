import LatticeProb.Bonanno.BouRabeeGwynne.FixedBallCover

/-! # Finite ball geometry for excursion selectors -/

set_option autoImplicit false

open Set Metric BouRabeeGwynne

namespace LatticeProb

/-- A compact set in an open neighborhood admits a finite family of balls
with compact inner and intermediate balls and a common positive collar. -/
theorem exists_selector_ball_geometry {d : ℕ} {K W : Set (Euc d)}
    (hK : IsCompact K) (hW : IsOpen W) (hKW : K ⊆ W)
    {rmax : ℝ} (hrmax : 0 < rmax) :
    ∃ (r : ℝ) (centers : Finset (Euc d)),
      0 < r ∧ r ≤ rmax ∧
      (∀ x ∈ K, ∃ j : centers, x ∈ ball j.val (r / 4)) ∧
      (∀ j : centers, closedBall j.val r ⊆ W) ∧
      (∀ j : centers, IsCompact (closedBall j.val (r / 2))) ∧
      (∀ j : centers, IsCompact (closedBall j.val (3 * r / 4))) ∧
      (∀ j : centers, closedBall j.val (r / 2) ⊆ ball j.val r) ∧
      (∀ j : centers, ball j.val (r / 2) ⊆ closedBall j.val (r / 2)) ∧
      (∀ (j : centers) x, x ∈ closedBall j.val (r / 2) →
        ∀ y, dist y x < r / 4 → y ∈ closedBall j.val (3 * r / 4)) := by
  obtain ⟨r, hr, hrmax', centers, _, hcover, hballs⟩ :=
    exists_fixed_ball_cover hK hW hKW hrmax
  refine ⟨r, centers, hr, hrmax', ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro x hx
    obtain ⟨c, hc, hxc⟩ := hcover x hx
    exact ⟨⟨c, hc⟩, hxc⟩
  · exact fun j => hballs j.val j.property
  · exact fun j => isCompact_closedBall j.val _
  · exact fun j => isCompact_closedBall j.val _
  · exact fun j => closedBall_subset_ball (half_lt_self hr)
  · exact fun _ => ball_subset_closedBall
  · intro j x hx y hy
    have htri := dist_triangle y x j.val
    change dist x j.val ≤ r / 2 at hx
    change dist y j.val ≤ 3 * r / 4
    linarith

end LatticeProb
