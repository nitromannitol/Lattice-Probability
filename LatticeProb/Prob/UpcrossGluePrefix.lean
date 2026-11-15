import LatticeProb.Prob.UpcrossGluePathwise

/-!
# Initial segments of glued paths

For a continuous path that reaches every negative integer level, the first hitting times of these
levels eventually exceed any fixed time. Consequently two glued paths with the same initial path
and equally initialized continuations eventually agree on every fixed compact time interval.
-/

open Set Filter
open scoped ENNReal NNReal

noncomputable section

namespace LatticeProb

/-- Deep negative levels are first reached after any given finite time. -/
theorem eventually_lt_glueTime (y : C(ℝ≥0, ℝ))
    (hfin : ∀ n : ℕ, hitFrom (-(n : ℝ)) 0 (y : ℝ≥0 → ℝ) ≠ ⊤)
    (T : ℝ≥0) : ∀ᶠ n : ℕ in atTop, T < glueTime (n : ℝ) y := by
  obtain ⟨b, hb⟩ := (isCompact_Icc.bddBelow_image y.continuous.continuousOn :
    BddBelow (y '' Icc (0 : ℝ≥0) T))
  obtain ⟨N, hN⟩ := exists_nat_gt (-b)
  filter_upwards [eventually_ge_atTop N] with n hn
  by_contra h
  have hle : glueTime (n : ℝ) y ≤ T := le_of_not_gt h
  have hy := coe_y_glueTime (hfin n)
  have hb' : b ≤ y (glueTime (n : ℝ) y) := hb ⟨_, ⟨zero_le, hle⟩, rfl⟩
  have hn' : (N : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  linarith

/-- Equal initial values of the continuations make the glued paths agree before the seam. -/
theorem glueC_eqOn_before_glueTime (a : ℝ) (y z₁ z₂ : C(ℝ≥0, ℝ))
    (hz : z₁ 0 = z₂ 0) :
    EqOn (glueC a y z₁) (glueC a y z₂) (Iic (glueTime a y)) := by
  intro s hs
  rw [glueC_apply_of_le hs, glueC_apply_of_le hs, hz]

/-- Glued paths with equal continuation starting values eventually agree on any fixed interval. -/
theorem eventually_glueC_eqOn (y z₁ z₂ : C(ℝ≥0, ℝ))
    (hfin : ∀ n : ℕ, hitFrom (-(n : ℝ)) 0 (y : ℝ≥0 → ℝ) ≠ ⊤)
    (hz : z₁ 0 = z₂ 0) (T : ℝ≥0) :
    ∀ᶠ n : ℕ in atTop, EqOn (glueC (n : ℝ) y z₁) (glueC (n : ℝ) y z₂) (Iic T) := by
  filter_upwards [eventually_lt_glueTime y hfin T] with n hn
  exact (glueC_eqOn_before_glueTime (n : ℝ) y z₁ z₂ hz).mono (Iic_subset_Iic.mpr hn.le)

end LatticeProb
