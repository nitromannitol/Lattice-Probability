/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module BouRabeeGwynne.BoundarySurvivalScales at commit fdb5cad; local import paths and linter settings are adjusted. -/
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

set_option linter.unusedSimpArgs false

/-! Scalar choices for finite nested boundary excursions: first fix the
number of probability contractions, then fit every spatial scale. -/

open scoped NNReal ENNReal

namespace BouRabeeGwynne

theorem exists_boundary_survival_scales {q R s κ η ε : ℝ}
    (hq : 0 ≤ q) (hqone : q < 1) (hR : 1 < R) (hs : 0 < s)
    (hκ : 0 < κ) (hη : 0 < η) (hε : 0 < ε) :
    ∃ N : ℕ, 0 < N ∧ ∃ r : ℝ≥0, 0 < r ∧ ∃ a : ℝ, 0 < a ∧ a ≤ (r : ℝ) ∧
      (∀ i < N, (r : ℝ) * R ^ i < s) ∧
      R * ((r : ℝ) * R ^ (N - 1)) + (r : ℝ) ≤ η ∧
      a < κ * (r : ℝ) / 2 ∧ ENNReal.ofReal q ^ N ≤ ENNReal.ofReal ε := by
  obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one hε hqone
  let N := n + 1
  have hN : 0 < N := Nat.succ_pos n
  have hpow : q ^ N ≤ ε := by
    calc
      q ^ N = q ^ n * q := pow_succ q n
      _ ≤ q ^ n * 1 := mul_le_mul_of_nonneg_left hqone.le (pow_nonneg hq n)
      _ ≤ ε := by simpa only [mul_one] using hn.le
  let A := R ^ N
  have hA : 0 < A := pow_pos (by linarith) N
  let ρ := min ((s / 2) / A) (η / (A + 1))
  have hρ : 0 < ρ := lt_min (div_pos (half_pos hs) hA)
    (div_pos hη (by linarith))
  have hρS : ρ * A ≤ s / 2 := (le_div_iff₀ hA).mp (min_le_left _ _)
  have hρη : ρ * (A + 1) ≤ η :=
    (le_div_iff₀ (by linarith : 0 < A + 1)).mp (min_le_right _ _)
  let a := min (ρ / 2) (κ * ρ / 4)
  have ha : 0 < a := lt_min (half_pos hρ) (by positivity)
  refine ⟨N, hN, ⟨ρ, hρ.le⟩, hρ, a, ha, ?_, ?_, ?_, ?_, ?_⟩
  · exact (min_le_left _ _).trans (half_le_self hρ.le)
  · intro i hi
    calc
      ρ * R ^ i ≤ ρ * A := mul_le_mul_of_nonneg_left
        (pow_le_pow_right₀ hR.le hi.le) hρ.le
      _ ≤ s / 2 := hρS
      _ < s := half_lt_self hs
  · have heq : R * (ρ * R ^ (N - 1)) + ρ = ρ * (A + 1) := by
      dsimp [A, N]
      simp only [Nat.add_sub_cancel, pow_succ]
      ring
    exact heq.trans_le hρη
  · have hsmall : a ≤ κ * ρ / 4 := min_le_right _ _
    have hpos : 0 < κ * ρ := mul_pos hκ hρ
    change a < κ * ρ / 2
    linarith
  · rw [← ENNReal.ofReal_pow hq N]
    exact ENNReal.ofReal_le_ofReal hpow

end BouRabeeGwynne
