import LatticeProb.Analysis.ConeVectorMembership

/-!
# Barriers after a joint backward exit

After the last time at which both coordinates have dropped below their
terminal values, at least one coordinate stays above its terminal value.
-/

set_option autoImplicit false

open Set

namespace LatticeProb

/-- One coordinate has a weak barrier between the joint backward exit and
the terminal time. No regularity of the paths is needed. -/
theorem jointBackwardExit_one_coordinate_barrier (X Y : ℝ → ℝ) (s : ℝ) :
    (∀ t ∈ Ioc (coneJointExitBackward X Y s) s, X s ≤ X t) ∨
      (∀ t ∈ Ioc (coneJointExitBackward X Y s) s, Y s ≤ Y t) := by
  classical
  by_cases hx : ∃ x ∈ Ioc (coneJointExitBackward X Y s) s, X x < X s
  · right
    obtain ⟨x, hx, hX⟩ := hx
    intro y hy
    by_contra hY
    have hYs : Y y < Y s := lt_of_not_ge hY
    have hxlt : x < s := lt_of_le_of_ne hx.2 (by
      intro h
      subst x
      exact (lt_irrefl _ hX))
    have hylt : y < s := lt_of_le_of_ne hy.2 (by
      intro h
      subst y
      exact (lt_irrefl _ hYs))
    let t := min x y
    have ht : t ∈ {t : ℝ | t < s ∧ (∃ r ∈ Icc t s, X r < X s) ∧
        (∃ r ∈ Icc t s, Y r < Y s)} := by
      refine ⟨lt_of_le_of_lt (min_le_left x y) hxlt, ?_, ?_⟩
      · exact ⟨x, ⟨min_le_left x y, hx.2⟩, hX⟩
      · exact ⟨y, ⟨min_le_right x y, hy.2⟩, hYs⟩
    have hb : BddAbove {t : ℝ | t < s ∧ (∃ r ∈ Icc t s, X r < X s) ∧
        (∃ r ∈ Icc t s, Y r < Y s)} :=
      ⟨s, fun _ ht => le_of_lt ht.1⟩
    have hle : t ≤ coneJointExitBackward X Y s := le_csSup hb ht
    have hgt : coneJointExitBackward X Y s < t := lt_min hx.1 hy.1
    exact (not_lt_of_ge hle) hgt
  · left
    intro t ht
    exact le_of_not_gt (fun h => hx ⟨t, ht, h⟩)

/-- The recorded coordinate of a backward cone vector has the same barrier
property in at least one coordinate. -/
theorem backwardConeVector_one_coordinate_barrier {X Y : ℝ → ℝ} {a s : ℝ}
    (h : (a, s) ∈ backwardConeVectors X Y) :
    (∀ t ∈ Ioc a s, X s ≤ X t) ∨ (∀ t ∈ Ioc a s, Y s ≤ Y t) := by
  have ha : a = coneJointExitBackward X Y s := h.1
  simpa only [ha] using jointBackwardExit_one_coordinate_barrier X Y s

end LatticeProb
