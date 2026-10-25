import LatticeProb.Prob.JumpChain.PositionFdd

/-!
# Killing including the initial state

Restricting the initial point corrects the arrival-filtered Poisson kernel.
The resulting mass is exactly the regular path law with survival through time zero.
-/

namespace LatticeProb.JumpChain.BoundedRates

open MeasureTheory Set
open scoped NNReal ENNReal

noncomputable section

attribute [local instance] Classical.propDecidable

variable {S : Type*}

/-- The arrival-filtered kernel restricted to initial states in the survival set. -/
def initialKilledKernel (rates : BoundedRates S) (U : Set S)
    (t : ℝ≥0) (x y : S) : ℝ :=
  if x ∈ U then rates.killedKernel U t x y else 0

/-- Initial killing gives nonnegative masses. -/
theorem initialKilledKernel_nonneg (rates : BoundedRates S) (U : Set S)
    (t : ℝ≥0) (x y : S) : 0 ≤ rates.initialKilledKernel U t x y := by
  classical
  by_cases hx : x ∈ U
  · simpa only [initialKilledKernel, if_pos hx] using rates.killedKernel_nonneg U t x y
  · simp only [initialKilledKernel, if_neg hx, le_refl]

/-- At time zero the initial restriction also applies to the diagonal mass. -/
@[simp] theorem initialKilledKernel_zero (rates : BoundedRates S) (U : Set S)
    (x y : S) : rates.initialKilledKernel U 0 x y =
      if x ∈ U then (if x = y then 1 else 0) else 0 := by
  classical
  simp only [initialKilledKernel, killedKernel_zero]

/-- A surviving initial point has positive diagonal mass, including at positive times. -/
theorem initialKilledKernel_self_pos (rates : BoundedRates S) (U : Set S)
    (t : ℝ≥0) (x : S) (hx : x ∈ U) : 0 < rates.initialKilledKernel U t x x := by
  classical
  rw [initialKilledKernel, if_pos hx]
  have hterm : 0 < Real.exp (-(rates.R * t)) * (rates.R * t) ^ 0 /
      (0 : ℕ).factorial * kernelPow (rates.killedP U) 0 x x := by
    simpa only [pow_zero, mul_one, Nat.factorial_zero, Nat.cast_one, div_one,
      kernelPow, if_true] using Real.exp_pos (-(rates.R * t))
  exact hterm.trans_le ((rates.killedKernel_summable U t x x).le_tsum 0
    (fun n _ ↦ rates.killedKernel_term_nonneg U t x x n))

variable [MeasurableSpace S] [Countable S] [MeasurableSingletonClass S]

/-- Initial killing is dominated by the full transition mass. -/
theorem initialKilledKernel_le_transitionKernel (rates : BoundedRates S) (U : Set S)
    (t : ℝ≥0) (x y : S) :
    rates.initialKilledKernel U t x y ≤ (rates.transitionKernel t x).real {y} := by
  classical
  by_cases hx : x ∈ U
  · simpa only [initialKilledKernel, if_pos hx] using
      rates.killedKernel_le_transitionKernel U t x y
  · simpa only [initialKilledKernel, if_neg hx] using measureReal_nonneg

/-- The restricted kernel is the actual Dirac-started surviving position law at every time. -/
theorem regularLaw_dirac_initialKilledKernel (rates : BoundedRates S) (U : Set S)
    (t : ℝ≥0) (x y : S) :
    rates.regularLaw (Measure.dirac x)
      {h | h.position t = y ∧ ∀ s ≤ t, h.position s ∈ U} =
      ENNReal.ofReal (rates.initialKilledKernel U t x y) := by
  classical
  let times : Fin 2 → ℝ≥0 := ![0, t]
  have hmono : Monotone times := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all [times]
  have hfdd := rates.regularLaw_killed_position_fdd (Measure.dirac x) U 1 times
    hmono rfl (fun _ ↦ y)
  have hevent : {h : RegularHistory S |
      (∀ i : Fin 2, 0 < i → h.position (times i) = y) ∧
        ∀ s ≤ times (Fin.last 1), h.position s ∈ U} =
      {h | h.position t = y ∧ ∀ s ≤ t, h.position s ∈ U} := by
    ext h
    simp [Fin.forall_fin_two, times]
  rw [hevent] at hfdd
  rw [tsum_eq_single x] at hfdd
  · by_cases hx : x ∈ U <;>
      simpa [Fin.prod_univ_one, times, Measure.dirac_apply', initialKilledKernel,
        Function.update_apply, hx] using hfdd
  · intro b hb
    by_cases hU : b ∈ U <;>
      simp [hU, Measure.dirac_apply', Ne.symm hb]

/-- Taking real mass gives the complete real-valued surviving position characterization. -/
theorem initialKilledKernel_eq_position_mass (rates : BoundedRates S) (U : Set S)
    (t : ℝ≥0) (x y : S) :
    rates.initialKilledKernel U t x y =
      (rates.regularLaw (Measure.dirac x)).real
        {h | h.position t = y ∧ ∀ s ≤ t, h.position s ∈ U} := by
  rw [measureReal_def, rates.regularLaw_dirac_initialKilledKernel,
    ENNReal.toReal_ofReal (rates.initialKilledKernel_nonneg U t x y)]

end

end LatticeProb.JumpChain.BoundedRates
