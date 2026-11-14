import LatticeProb.Prob.CorrelatedBMConeSurvivalPower
import LatticeProb.Prob.CorrelatedBMConePowerCost

/-! # Power estimates for cone grid events from joint window survival -/

set_option autoImplicit false

open MeasureTheory Set
open scoped ENNReal NNReal
open MatedCRTHarmonic.MatedCRT

namespace LatticeProb.CorrelatedBM

/-- A positive gap and finite horizon have a strictly separated window. -/
theorem exists_cone_window (k : ℕ) (d : ℝ) (hd : 0 < d) :
    ∃ h : ℝ, 0 < h ∧ h ≤ 1 / (k + 1 : ℝ) ∧ 2 * h < d := by
  have hH : (0 : ℝ) < 1 / (k + 1 : ℝ) := by positivity
  refine ⟨min d (1 / (k + 1 : ℝ)) / 4, by positivity, ?_, ?_⟩
  · have hmin := min_le_right d (1 / (k + 1 : ℝ))
    linarith
  · have hmin := min_le_left d (1 / (k + 1 : ℝ))
    linarith

/-- A joint backward-window power bound gives the forward grid-event power bound. -/
theorem measure_factorialConeGridEvent_one_le_of_joint_power
    {γ : ℝ} {μ : Measure Path2} (hμ : IsCorrelatedBM2 γ μ)
    (C α h d B p : ℝ) (k n : ℕ)
    (hC : 0 < C) (hh : 0 < h) (hH : h ≤ 1 / (k + 1 : ℝ))
    (hd : 2 * h < d) (hB : 0 ≤ B)
    (hJ : ∀ b : ℝ,
      μ ({ω | ∀ t ∈ Icc (b - h) b,
        -(C * (factorialGridMesh n) ^ α) ≤
          coneIncr 0 t (b - h) ω - coneIncr 0 b (b - h) ω} ∩
        {ω | ∀ t ∈ Icc (b - h) b,
        -(C * (factorialGridMesh n) ^ α) ≤
          coneIncr 1 t (b - h) ω - coneIncr 1 b (b - h) ω}) ≤
        ENNReal.ofReal (B * (C * (factorialGridMesh n) ^ α) ^ p))
    (i j : Fin (n.factorial ^ 6))
    (hsep : d < (j.val : ℝ) / (n.factorial ^ 6 : ℕ) -
      (i.val : ℝ) / (n.factorial ^ 6 : ℕ)) :
    μ (factorialConeGridEvent 1 C α k n i j) ≤
      ENNReal.ofReal ((12 * B * C ^ (p + 2) /
        (√h * √(2 * Real.pi * (d - 2 * h)))) * (factorialGridMesh n ^ α) ^ (p + 2)) := by
  have hx : 0 < factorialGridMesh n ^ α := Real.rpow_pos_of_pos (by
    unfold factorialGridMesh
    positivity) _
  have hq : 0 ≤ C * factorialGridMesh n ^ α := (mul_pos hC hx).le
  have hbound := measure_factorialConeGridEvent_one_le_uniform hμ C α k n h d hh hH hd
    (by simpa only [factorialGridMesh] using hq)
    (ENNReal.ofReal (B * (C * factorialGridMesh n ^ α) ^ p))
    (by simpa only [factorialGridMesh] using hJ) i j hsep
  exact hbound.trans (by
    simpa only [factorialGridMesh] using
      (cone_survival_power_bound C (factorialGridMesh n ^ α) h
        (2 * Real.pi * (d - 2 * h)) B p
        (ENNReal.ofReal (B * (C * factorialGridMesh n ^ α) ^ p))
        hC hx hh hB le_rfl))

/-- A joint forward-window power bound gives the reflected grid-event power bound. -/
theorem measure_factorialConeGridEvent_neg_one_le_of_joint_power
    {γ : ℝ} {μ : Measure Path2} (hμ : IsCorrelatedBM2 γ μ)
    (C α h d B p : ℝ) (k n : ℕ)
    (hC : 0 < C) (hh : 0 < h) (hH : h ≤ 1 / (k + 1 : ℝ))
    (hd : 2 * h < d) (hB : 0 ≤ B)
    (hJ : ∀ b : ℝ,
      μ ({ω | ∀ t ∈ Icc b (b + h),
        -(C * (factorialGridMesh n) ^ α) ≤ coneIncr 0 t b ω} ∩
        {ω | ∀ t ∈ Icc b (b + h),
        -(C * (factorialGridMesh n) ^ α) ≤ coneIncr 1 t b ω}) ≤
        ENNReal.ofReal (B * (C * (factorialGridMesh n) ^ α) ^ p))
    (i j : Fin (n.factorial ^ 6))
    (hsep : d < (j.val : ℝ) / (n.factorial ^ 6 : ℕ) -
      (i.val : ℝ) / (n.factorial ^ 6 : ℕ)) :
    μ (factorialConeGridEvent (-1) C α k n i j) ≤
      ENNReal.ofReal ((12 * B * C ^ (p + 2) /
        (√h * √(2 * Real.pi * (d - 2 * h)))) * (factorialGridMesh n ^ α) ^ (p + 2)) := by
  have hx : 0 < factorialGridMesh n ^ α := Real.rpow_pos_of_pos (by
    unfold factorialGridMesh
    positivity) _
  have hq : 0 ≤ C * factorialGridMesh n ^ α := (mul_pos hC hx).le
  have hbound := measure_factorialConeGridEvent_neg_one_le_uniform hμ C α k n h d hh hH hd
    (by simpa only [factorialGridMesh] using hq)
    (ENNReal.ofReal (B * (C * factorialGridMesh n ^ α) ^ p))
    (by simpa only [factorialGridMesh] using hJ) i j hsep
  exact hbound.trans (by
    simpa only [factorialGridMesh] using
      (cone_survival_power_bound C (factorialGridMesh n ^ α) h
        (2 * Real.pi * (d - 2 * h)) B p
        (ENNReal.ofReal (B * (C * factorialGridMesh n ^ α) ^ p))
        hC hx hh hB le_rfl))


/-- A joint backward-window power bound gives a finite forward grid cost. -/
theorem exists_finite_one_grid_cost_bound_of_joint_power
    {γ : ℝ} {μ : Measure Path2} (hμ : IsCorrelatedBM2 γ μ)
    (C α h d B p : ℝ) (k : ℕ) (β : ℝ≥0)
    (hC : 0 < C) (hh : 0 < h) (hH : h ≤ 1 / (k + 1 : ℝ))
    (hd : 2 * h < d) (hB : 0 ≤ B)
    (hslack : 2 < (β : ℝ) + α * (p + 2))
    (hJ : ∀ (n : ℕ) (b : ℝ),
      μ ({ω | ∀ t ∈ Icc (b - h) b,
        -(C * (factorialGridMesh n) ^ α) ≤
          coneIncr 0 t (b - h) ω - coneIncr 0 b (b - h) ω} ∩
        {ω | ∀ t ∈ Icc (b - h) b,
        -(C * (factorialGridMesh n) ^ α) ≤
          coneIncr 1 t (b - h) ω - coneIncr 1 b (b - h) ω}) ≤
        ENNReal.ofReal (B * (C * (factorialGridMesh n) ^ α) ^ p)) :
    ∃ K : ℝ≥0∞, K ≠ ∞ ∧ ∀ n : ℕ,
      (∑ ij : Fin (n.factorial ^ 6) × Fin (n.factorial ^ 6),
        if d < (ij.2.val : ℝ) / (n.factorial ^ 6 : ℕ) -
            (ij.1.val : ℝ) / (n.factorial ^ 6 : ℕ) then
          Metric.ediam (factorialGridNeighborhood n ij.1 ij.2) ^ (β : ℝ) *
            μ (factorialConeGridEvent 1 C α k n ij.1 ij.2)
        else 0) ≤ K := by
  apply exists_finite_separated_grid_cost_bound_of_power_bound μ 1 C α d p
    (12 * B * C ^ (p + 2) / (√h * √(2 * Real.pi * (d - 2 * h)))) k β hslack
  intro n i j hsep
  exact measure_factorialConeGridEvent_one_le_of_joint_power hμ C α h d B p k n
    hC hh hH hd hB (hJ n) i j hsep

/-- A joint forward-window power bound gives a finite reflected grid cost. -/
theorem exists_finite_neg_one_grid_cost_bound_of_joint_power
    {γ : ℝ} {μ : Measure Path2} (hμ : IsCorrelatedBM2 γ μ)
    (C α h d B p : ℝ) (k : ℕ) (β : ℝ≥0)
    (hC : 0 < C) (hh : 0 < h) (hH : h ≤ 1 / (k + 1 : ℝ))
    (hd : 2 * h < d) (hB : 0 ≤ B)
    (hslack : 2 < (β : ℝ) + α * (p + 2))
    (hJ : ∀ (n : ℕ) (b : ℝ),
      μ ({ω | ∀ t ∈ Icc b (b + h),
        -(C * (factorialGridMesh n) ^ α) ≤ coneIncr 0 t b ω} ∩
        {ω | ∀ t ∈ Icc b (b + h),
        -(C * (factorialGridMesh n) ^ α) ≤ coneIncr 1 t b ω}) ≤
        ENNReal.ofReal (B * (C * (factorialGridMesh n) ^ α) ^ p)) :
    ∃ K : ℝ≥0∞, K ≠ ∞ ∧ ∀ n : ℕ,
      (∑ ij : Fin (n.factorial ^ 6) × Fin (n.factorial ^ 6),
        if d < (ij.2.val : ℝ) / (n.factorial ^ 6 : ℕ) -
            (ij.1.val : ℝ) / (n.factorial ^ 6 : ℕ) then
          Metric.ediam (factorialGridNeighborhood n ij.1 ij.2) ^ (β : ℝ) *
            μ (factorialConeGridEvent (-1) C α k n ij.1 ij.2)
        else 0) ≤ K := by
  apply exists_finite_separated_grid_cost_bound_of_power_bound μ (-1) C α d p
    (12 * B * C ^ (p + 2) / (√h * √(2 * Real.pi * (d - 2 * h)))) k β hslack
  intro n i j hsep
  exact measure_factorialConeGridEvent_neg_one_le_of_joint_power hμ C α h d B p k n
    hC hh hH hd hB (hJ n) i j hsep


end LatticeProb.CorrelatedBM
