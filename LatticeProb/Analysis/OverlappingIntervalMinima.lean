import Mathlib.Order.Filter.Extr

/-! # Minima on overlapping intervals -/

set_option autoImplicit false

open Set

namespace LatticeProb

/-- Two minima agree when each interval contains a witness for the other's
minimum. The witness for the first minimum lies in its right subinterval and
the witness for the second lies in its left subinterval. -/
theorem overlapping_interval_minima_eq {α β : Type*} [LinearOrder α] [PartialOrder β]
    (f : α → β) {a a' b b' c c' x y x' : α}
    (haa : a ≤ a') (hab : a' ≤ b) (hbc : b' ≤ c)
    (hcc : c ≤ c') (hy : y ∈ Icc b c) (hx' : x' ∈ Icc a' b')
    (hmin : IsMinOn f (Icc a c) x) (hmin' : IsMinOn f (Icc a' c') x')
    (hxy : f y = f x) : f x = f x' := by
  apply le_antisymm
  · apply hmin
    exact ⟨le_trans haa hx'.1, le_trans hx'.2 hbc⟩
  · rw [← hxy]
    apply hmin'
    exact ⟨le_trans hab hy.1, le_trans hy.2 hcc⟩

end LatticeProb
