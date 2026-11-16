import Mathlib.Basic.Real.Basic
import Mathlib.Tactic

/-! # Parameters for a finite-horizon collar estimate -/

set_option autoImplicit false

namespace LatticeProb

/-- Positive error tolerances can be fixed before a horizon, while the
per-step error can be chosen after it. -/
theorem exists_collar_transfer_parameters {r : ℝ} (hr : 0 < r) :
    ∃ η τ : ℝ, 0 < η ∧ 0 < τ ∧
      ∀ c : ℝ, 0 < c →
        ∃ a e δ mesh : ℝ,
          0 < a ∧ 0 < e ∧ 0 < δ ∧ 0 < mesh ∧
          a + e ≤ c ∧ δ ≤ c ∧ a + e + mesh < δ ∧ a + e + η < r ∧
          ∀ L : ℕ, ∃ b : ℝ, 0 < b ∧
            2 * (L + 1 : ℝ) * b + 3 * τ ≤ r := by
  refine ⟨r / 4, r / 12, by positivity, by positivity, ?_⟩
  intro c hc
  let u := min c r
  have hu : 0 < u := lt_min hc hr
  have huc : u ≤ c := min_le_left _ _
  have hur : u ≤ r := min_le_right _ _
  refine ⟨u / 100, u / 100, u / 2, u / 100,
    by positivity, by positivity, by positivity, by positivity, ?_, ?_, ?_, ?_, ?_⟩
  · linarith
  · linarith
  · linarith
  · linarith
  · intro L
    have hL : (0 : ℝ) < L + 1 := by positivity
    refine ⟨r / (12 * (L + 1 : ℝ)), by positivity, ?_⟩
    have heq : (2 : ℝ) * (L + 1 : ℝ) * (r / (12 * (L + 1 : ℝ))) = r / 6 := by
      field_simp
      ring
    rw [heq]
    linarith

end LatticeProb
