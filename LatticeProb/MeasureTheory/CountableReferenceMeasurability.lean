import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
import Mathlib.Probability.Kernel.Basic
import Mathlib.Tactic

/-! # Measurability from countable reference comparisons -/

set_option autoImplicit false

open Set
open scoped ENNReal

namespace LatticeProb

/-- An observable is measurable if it admits measurable comparisons with a countable
family of reference values which approximate it at arbitrarily small discrepancy. -/
theorem measurable_of_countable_reference_discrepancies
    {Ω : Type*} [MeasurableSpace Ω] (f : Ω → ℝ) (c : ℕ → ℝ)
    (d : ℕ → Ω → ℝ) (C : ℝ) (hC : 0 ≤ C)
    (hd : ∀ n, Measurable (d n))
    (hbound : ∀ n ω, |f ω - c n| ≤ C * d n ω)
    (hcover : ∀ ω ε, 0 < ε → ∃ n, d n ω < ε) : Measurable f := by
  apply measurable_of_Iio
  intro r
  have heq : f ⁻¹' Iio r = ⋃ n, {ω | c n + C * d n ω < r} := by
    ext ω
    simp only [mem_preimage, mem_Iio, mem_iUnion, mem_ofPred_eq]
    constructor
    · intro hr
      have hden : 0 < 2 * (C + 1) := by positivity
      have hε : 0 < (r - f ω) / (2 * (C + 1)) := div_pos (sub_pos.mpr hr) hden
      obtain ⟨n, hn⟩ := hcover ω _ hε
      have habs := (abs_le.mp (hbound n ω)).1
      have hmul := mul_lt_mul_of_pos_left hn hden
      have hdiv : 2 * (C + 1) * ((r - f ω) / (2 * (C + 1))) = r - f ω := by
        field_simp
      refine ⟨n, ?_⟩
      nlinarith
    · rintro ⟨n, hn⟩
      have habs := (abs_le.mp (hbound n ω)).2
      linarith
  rw [heq]
  exact MeasurableSet.iUnion fun n =>
    measurableSet_lt (measurable_const.add (measurable_const.mul (hd n))) measurable_const

/-- A uniformly finite family of measures is a finite kernel if countably many
reference measures control every measurable evaluation by the same discrepancies. -/
theorem exists_finite_kernel_of_countable_reference_discrepancies
    {Ω X : Type*} [MeasurableSpace Ω] [MeasurableSpace X]
    (M : Ω → MeasureTheory.Measure X) (N : ℕ → MeasureTheory.Measure X)
    (K : ℝ≥0∞) (hK : K < ∞) (hfinite : ∀ ω, M ω univ ≤ K)
    (d : ℕ → Ω → ℝ) (C : ℝ) (hC : 0 ≤ C)
    (hd : ∀ n, Measurable (d n))
    (hbound : ∀ s, MeasurableSet s → ∀ n ω,
      |(M ω s).toReal - (N n s).toReal| ≤ C * d n ω)
    (hcover : ∀ ω ε, 0 < ε → ∃ n, d n ω < ε) :
    ∃ κ : ProbabilityTheory.Kernel Ω X, ProbabilityTheory.IsFiniteKernel κ ∧
      ∀ ω, κ ω = M ω := by
  have htop (ω : Ω) (s : Set X) : M ω s ≠ ∞ :=
    (lt_of_le_of_lt ((MeasureTheory.measure_mono (subset_univ s)).trans (hfinite ω)) hK).ne
  have hmeas : Measurable M := by
    apply MeasureTheory.Measure.measurable_of_measurable_coe
    intro s hs
    have h := measurable_of_countable_reference_discrepancies
      (fun ω => (M ω s).toReal) (fun n => (N n s).toReal) d C hC hd (hbound s hs) hcover
    have h' := ENNReal.measurable_ofReal.comp h
    convert h' using 1
    funext ω
    exact (ENNReal.ofReal_toReal (htop ω s)).symm
  refine ⟨⟨M, hmeas⟩, ⟨⟨K, hK, hfinite⟩⟩, ?_⟩
  intro ω
  rfl

end LatticeProb
