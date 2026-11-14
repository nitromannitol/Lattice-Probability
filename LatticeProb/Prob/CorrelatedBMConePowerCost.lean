import LatticeProb.Prob.CorrelatedBMConeGridCost
import LatticeProb.Analysis.GridPowerDecay

/-!
# Power bounds for separated grid costs

A uniform power bound for grid-event probabilities gives a vanishing
expected covering cost when the exponents have sufficient slack.
-/

set_option autoImplicit false

open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal
open MatedCRTHarmonic.MatedCRT

namespace LatticeProb.CorrelatedBM

/-- A finite-valued sequence converging to zero has a finite uniform bound. -/
theorem exists_finite_bound_of_tendsto_zero {f : ℕ → ℝ≥0∞}
    (hfin : ∀ n, f n ≠ ∞) (hlim : Tendsto f atTop (𝓝 0)) :
    ∃ K : ℝ≥0∞, K ≠ ∞ ∧ ∀ n, f n ≤ K := by
  have hev : ∀ᶠ n in atTop, f n < 1 :=
    hlim.eventually (Iio_mem_nhds (by norm_num))
  obtain ⟨N, hN⟩ := eventually_atTop.1 hev
  refine ⟨1 + ∑ n ∈ Finset.range N, f n, ?_, ?_⟩
  · apply ENNReal.add_ne_top.mpr
    exact ⟨ENNReal.one_ne_top, ENNReal.sum_ne_top.mpr (fun n _ => hfin n)⟩
  · intro n
    by_cases hn : n < N
    · have hh : f n ≤ ∑ i ∈ Finset.range N, f i :=
        Finset.single_le_sum (fun _ _ => bot_le) (Finset.mem_range.mpr hn)
      exact hh.trans (le_add_left le_rfl)
    · exact (hN n (Nat.le_of_not_gt hn)).le.trans (le_add_right le_rfl)

/-- A uniform power estimate for separated events yields a vanishing cost. -/
theorem tendsto_separated_grid_cost_of_power_bound
    (μ : Measure Path2) (direction C α d p A : ℝ) (k : ℕ) (β : ℝ≥0)
    (hslack : 2 < (β : ℝ) + α * (p + 2))
    (hP : ∀ n : ℕ, ∀ i j : Fin (n.factorial ^ 6),
      d < (j.val : ℝ) / (n.factorial ^ 6 : ℕ) -
          (i.val : ℝ) / (n.factorial ^ 6 : ℕ) →
      μ (factorialConeGridEvent direction C α k n i j) ≤
        ENNReal.ofReal (A * (factorialGridMesh n ^ α) ^ (p + 2))) :
    Tendsto (fun n : ℕ =>
      ∑ ij : Fin (n.factorial ^ 6) × Fin (n.factorial ^ 6),
        if d < (ij.2.val : ℝ) / (n.factorial ^ 6 : ℕ) -
            (ij.1.val : ℝ) / (n.factorial ^ 6 : ℕ) then
          Metric.ediam (factorialGridNeighborhood n ij.1 ij.2) ^ (β : ℝ) *
            μ (factorialConeGridEvent direction C α k n ij.1 ij.2)
        else 0) atTop (𝓝 0) := by
  have hx (n : ℕ) : 0 < factorialGridMesh n := by
    unfold factorialGridMesh
    positivity
  have hmesh : Tendsto factorialGridMesh atTop (𝓝 0) := by
    change Tendsto (fun n : ℕ => 1 / ((n.factorial ^ 6 : ℕ) : ℝ)) atTop (𝓝 0)
    simpa only [Nat.cast_pow] using tendsto_one_div_factorial_pow 6 (by norm_num)
  have hreal := (tendsto_grid_power_cost hx hmesh α β p hslack).const_mul
    (2 ^ (β : ℝ) * A)
  have hlim : Tendsto (fun n : ℕ => ENNReal.ofReal
      ((2 ^ (β : ℝ) * A) * ((factorialGridMesh n)⁻¹ ^ 2 *
        factorialGridMesh n ^ (β : ℝ) *
        (factorialGridMesh n ^ α) ^ (p + 2)))) atTop (𝓝 0) := by
    simpa only [mul_zero, ENNReal.ofReal_zero] using ENNReal.tendsto_ofReal hreal
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hlim
  · intro n
    exact bot_le
  · intro n
    refine (separated_grid_cost_le_of_uniform_probability μ direction C α d k n β _
      (hP n)).trans ?_
    have hnat : (((n.factorial ^ 6 : ℕ) : ℝ≥0∞)) =
        ENNReal.ofReal ((factorialGridMesh n)⁻¹) := by
      simp [factorialGridMesh]
    rw [hnat, ← ENNReal.ofReal_pow (inv_nonneg.mpr (hx n).le),
      ENNReal.ofReal_rpow_of_pos (mul_pos (by norm_num) (hx n)),
      ← ENNReal.ofReal_mul (Real.rpow_nonneg (mul_nonneg (by norm_num) (hx n).le) _),
      ← ENNReal.ofReal_mul (sq_nonneg _)]
    apply le_of_eq
    congr 1
    rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2) (hx n).le]
    ring

/-- The power estimate supplies a finite bound for every grid scale. -/
theorem exists_finite_separated_grid_cost_bound_of_power_bound
    (μ : Measure Path2) (direction C α d p A : ℝ) (k : ℕ) (β : ℝ≥0)
    (hslack : 2 < (β : ℝ) + α * (p + 2))
    (hP : ∀ n : ℕ, ∀ i j : Fin (n.factorial ^ 6),
      d < (j.val : ℝ) / (n.factorial ^ 6 : ℕ) -
          (i.val : ℝ) / (n.factorial ^ 6 : ℕ) →
      μ (factorialConeGridEvent direction C α k n i j) ≤
        ENNReal.ofReal (A * (factorialGridMesh n ^ α) ^ (p + 2))) :
    ∃ K : ℝ≥0∞, K ≠ ∞ ∧ ∀ n : ℕ,
      (∑ ij : Fin (n.factorial ^ 6) × Fin (n.factorial ^ 6),
        if d < (ij.2.val : ℝ) / (n.factorial ^ 6 : ℕ) -
            (ij.1.val : ℝ) / (n.factorial ^ 6 : ℕ) then
          Metric.ediam (factorialGridNeighborhood n ij.1 ij.2) ^ (β : ℝ) *
            μ (factorialConeGridEvent direction C α k n ij.1 ij.2)
        else 0) ≤ K := by
  apply exists_finite_bound_of_tendsto_zero
  · intro n
    apply ne_of_lt
    refine lt_of_le_of_lt (separated_grid_cost_le_of_uniform_probability μ direction C α d k n β _ (hP n)) ?_
    exact ENNReal.mul_lt_top (ENNReal.pow_lt_top (ENNReal.natCast_lt_top _))
      (ENNReal.mul_lt_top (ENNReal.rpow_lt_top_of_nonneg β.coe_nonneg ENNReal.ofReal_ne_top)
        ENNReal.ofReal_lt_top)
  · exact tendsto_separated_grid_cost_of_power_bound μ direction C α d p A k β hslack hP

end LatticeProb.CorrelatedBM
