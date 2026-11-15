import LatticeProb.Prob.ConditionalTrialFailure

/-! # Exponential bounds for floored numbers of conditional trials -/

set_option autoImplicit false

open MeasureTheory ProbabilityTheory

namespace LatticeProb

/-- The loss of at most two trials can be absorbed into a fixed exponential factor. -/
theorem exp_neg_mul_floor_sub_one_le (x c : ℝ) (hc : 0 ≤ c) :
    Real.exp (-c * ((⌊x⌋₊ - 1 : ℕ) : ℝ)) ≤
      Real.exp (2 * c) * Real.exp (-c * x) := by
  have hnat : ⌊x⌋₊ ≤ (⌊x⌋₊ - 1) + 1 := by omega
  have hcast : (⌊x⌋₊ : ℝ) ≤ ((⌊x⌋₊ - 1 : ℕ) : ℝ) + 1 := by exact_mod_cast hnat
  have hfloor : x < (⌊x⌋₊ : ℝ) + 1 := Nat.lt_floor_add_one x
  have hn : x - 2 ≤ ((⌊x⌋₊ - 1 : ℕ) : ℝ) := by linarith
  rw [← Real.exp_add]
  apply Real.exp_le_exp.mpr
  nlinarith

/-- Conditional successes at a uniform rate yield an inverse-scale exponential failure bound. -/
theorem measureReal_no_success_floor_inv_le
    {Ω : Type*} {m : MeasurableSpace Ω} {μ : Measure Ω} [IsProbabilityMeasure μ]
    (ℱ : Filtration ℕ m) (A : ℕ → Set Ω)
    (hA : ∀ k, MeasurableSet[ℱ (k + 1)] (A k)) {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (hp : ∀ k, ∀ᵐ ω ∂μ, p ≤ μ[(A k).indicator (fun _ => (1 : ℝ)) | ℱ k] ω)
    (C ε : ℝ) :
    μ.real {ω | ∀ k ∈ Finset.range (⌊(C * ε)⁻¹⌋₊ - 1), ω ∉ A k} ≤
      Real.exp (p ^ 2) * Real.exp (-(p ^ 2 / 2) * (C * ε)⁻¹) := by
  calc
    _ ≤ Real.exp (-(p ^ 2 / 2) * ((⌊(C * ε)⁻¹⌋₊ - 1 : ℕ) : ℝ)) :=
      measureReal_no_success_le_of_condExp_ge ℱ A hA hp0 hp1 hp _
    _ ≤ Real.exp (2 * (p ^ 2 / 2)) * Real.exp (-(p ^ 2 / 2) * (C * ε)⁻¹) :=
      exp_neg_mul_floor_sub_one_le _ _ (by positivity)
    _ = _ := by
      congr 1
      ring

end LatticeProb
