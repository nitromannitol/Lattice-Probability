import LatticeProb.Bonanno.MatedCRTHarmonic.GMS4.Probability
import Mathlib.MeasureTheory.Function.Floor
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-! # Cardinality of logarithmic scale intervals -/

set_option autoImplicit false

open Set MeasureTheory

namespace LatticeProb

/-- The number of integers in a real interval is at most its length plus one. -/
theorem int_interval_card_le_length_add_one {a b : ℝ} (hab : a ≤ b) :
    ((Finset.Icc (⌈a⌉ : ℤ) (⌊b⌋ : ℤ)).card : ℝ) ≤ b - a + 1 := by
  classical
  by_cases h : (⌈a⌉ : ℤ) ≤ ⌊b⌋
  · have hc : ((Finset.Icc (⌈a⌉ : ℤ) (⌊b⌋ : ℤ)).card : ℤ) =
        ⌊b⌋ + 1 - ⌈a⌉ := Int.card_Icc_of_le _ _ (by omega)
    have hc' : ((Finset.Icc (⌈a⌉ : ℤ) (⌊b⌋ : ℤ)).card : ℝ) =
        (⌊b⌋ : ℝ) + 1 - (⌈a⌉ : ℝ) := by exact_mod_cast hc
    rw [hc']
    have ha := Int.le_ceil a
    have hb := Int.floor_le b
    linarith
  · have hempty : Finset.Icc (⌈a⌉ : ℤ) (⌊b⌋ : ℤ) = ∅ := Finset.Icc_eq_empty_of_lt (lt_of_not_ge h)
    simp only [hempty, Finset.card_empty, Nat.cast_zero]
    linarith

/-- The integer logarithmic scales between two positive radii, with one unit
of padding at each end, are controlled by their log ratio. -/
theorem log_scale_interval_card_le {r s : ℝ} (hr : 0 < r) (hrs : r ≤ s) :
    ((Finset.Icc (⌈Real.log r - 1⌉ : ℤ) (⌊Real.log s + 1⌋ : ℤ)).card : ℝ) ≤
      Real.log (s / r) + 3 := by
  have hs : 0 < s := lt_of_lt_of_le hr hrs
  have hlog : Real.log r ≤ Real.log s := Real.log_le_log hr hrs
  have h := int_interval_card_le_length_add_one (a := Real.log r - 1)
    (b := Real.log s + 1) (by linarith)
  rw [Real.log_div (ne_of_gt hs) (ne_of_gt hr)]
  linarith

/-- A tail estimate for the log ratio controls the cardinality tail of the
corresponding padded integer logarithmic scale interval. -/
theorem measure_log_scale_card_gt_le {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (r s : Ω → ℝ) (N : ℕ)
    (hr : ∀ ω, 0 < r ω) (hrs : ∀ ω, r ω ≤ s ω) :
    μ {ω | N < (Finset.Icc (⌈Real.log (r ω) - 1⌉ : ℤ)
      (⌊Real.log (s ω) + 1⌋ : ℤ)).card} ≤
      μ {ω | (N : ℝ) < Real.log (s ω / r ω) + 3} := by
  apply measure_mono
  intro ω hω
  have h := log_scale_interval_card_le (hr ω) (hrs ω)
  have hn : (N : ℝ) < ((Finset.Icc (⌈Real.log (r ω) - 1⌉ : ℤ)
      (⌊Real.log (s ω) + 1⌋ : ℤ)).card : ℝ) := by exact_mod_cast hω
  exact lt_of_lt_of_le hn h

end LatticeProb
