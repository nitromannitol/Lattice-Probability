import LatticeProb.Bonanno.MatedCRTHarmonic.Frozen.MatedCRTSideCond

/-! # Barriers for mated-CRT side edges -/

set_option autoImplicit false

noncomputable section

open Set

namespace MatedCRTHarmonic.MatedCRT

/-- A low point between the two cells excludes the side condition, using the left cell. -/
theorem not_sideCond_of_low_from_left {X : ℝ → ℝ} (hX : Continuous X)
    {ε t : ℝ} {x y : ℤ}
    (ht : t ∈ Icc (ε * x) (ε * ((y : ℝ) - 1)))
    (hlow : X t < intervalInf X (ε * ((x : ℝ) - 1)) (ε * x)) :
    ¬ SideCond ε X x y := by
  intro hs
  have hm : intervalInf X (ε * x) (ε * ((y : ℝ) - 1)) ≤ X t := by
    unfold intervalInf
    exact csInf_le (isCompact_Icc.bddBelow_image hX.continuousOn) ⟨t, ht, rfl⟩
  exact (not_le_of_gt hlow) ((le_max_left _ _).trans hs |>.trans hm)

/-- A low point between the two cells excludes the side condition, using the right cell. -/
theorem not_sideCond_of_low_from_right {X : ℝ → ℝ} (hX : Continuous X)
    {ε t : ℝ} {x y : ℤ}
    (ht : t ∈ Icc (ε * x) (ε * ((y : ℝ) - 1)))
    (hlow : X t < intervalInf X (ε * ((y : ℝ) - 1)) (ε * y)) :
    ¬ SideCond ε X x y := by
  intro hs
  have hm : intervalInf X (ε * x) (ε * ((y : ℝ) - 1)) ≤ X t := by
    unfold intervalInf
    exact csInf_le (isCompact_Icc.bddBelow_image hX.continuousOn) ⟨t, ht, rfl⟩
  exact (not_le_of_gt hlow) ((le_max_right _ _).trans hs |>.trans hm)

/-- A lower excursion arbitrarily far right rules out sufficiently distant right side edges. -/
theorem eventually_not_sideCond_right {X : ℝ → ℝ} (hX : Continuous X)
    {ε : ℝ} (hε : 0 < ε) (x : ℤ)
    (hlow : ∀ M T : ℝ, ∃ t ≥ T, X t < M) :
    ∃ N : ℕ, ∀ y : ℤ, (N : ℤ) < y → ¬ SideCond ε X x y := by
  obtain ⟨t, ht, hvalue⟩ := hlow (intervalInf X (ε * ((x : ℝ) - 1)) (ε * x)) (ε * x)
  obtain ⟨N, hN⟩ := exists_nat_gt (t / ε + 1)
  refine ⟨N, fun y hy => ?_⟩
  have hy' : (N : ℝ) < (y : ℝ) := by exact_mod_cast hy
  have ht' : t ≤ ε * ((y : ℝ) - 1) := by
    have h := (div_lt_iff₀ hε).mp (show t / ε < (y : ℝ) - 1 by linarith)
    linarith
  exact not_sideCond_of_low_from_left hX ⟨ht, ht'⟩ hvalue

/-- A lower excursion arbitrarily far left rules out sufficiently distant left side edges. -/
theorem eventually_not_sideCond_left {X : ℝ → ℝ} (hX : Continuous X)
    {ε : ℝ} (hε : 0 < ε) (x : ℤ)
    (hlow : ∀ M T : ℝ, ∃ t ≤ -T, X t < M) :
    ∃ N : ℕ, ∀ y : ℤ, y < -(N : ℤ) → ¬ SideCond ε X y x := by
  obtain ⟨t, ht, hvalue⟩ := hlow (intervalInf X (ε * ((x : ℝ) - 1)) (ε * x))
    (-(ε * ((x : ℝ) - 1)))
  obtain ⟨N, hN⟩ := exists_nat_gt (-t / ε + 1)
  refine ⟨N, fun y hy => ?_⟩
  have hy' : (y : ℝ) < -(N : ℝ) := by exact_mod_cast hy
  have ht' : ε * (y : ℝ) ≤ t := by
    have hdiv : -t / ε < -(y : ℝ) := by linarith
    have h := (div_lt_iff₀ hε).mp hdiv
    nlinarith
  exact not_sideCond_of_low_from_right hX ⟨ht', by linarith⟩ hvalue

end MatedCRTHarmonic.MatedCRT
