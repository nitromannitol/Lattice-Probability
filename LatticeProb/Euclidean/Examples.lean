module

public import LatticeProb.Euclidean.Asymptotic
public import LatticeProb.Euclidean.Estimates
public import LatticeProb.Euclidean.Shell
public import LatticeProb.Euclidean.Summability

@[expose] public section

/-!
# Lawful instances in dimensions one and two

The generic theorems of the Euclidean chain are applied in dimensions `d = 1` and `d = 2`, and the
objects they involve are checked to be nonzero: the unit-ball volume takes its known value (`2`
and `π`), the scaled unit-ball index set contains a nonzero integer point, the leading coefficient
`d · unitBallVolume d` of the critical asymptotic is nonzero, and the radial error series and the
exterior series are summable by the generic theorems, not by a junk value of `tsum`.  No hypothesis
is used beyond the dimension and the scale stated on each declaration.
-/

noncomputable section

namespace LatticeProb.Euclidean.Examples

open LatticeProb.Euclidean.Lattice LatticeProb.Euclidean.Shell
open LatticeProb.Euclidean.Summability LatticeProb.Euclidean.Estimates
open LatticeProb.Euclidean.Asymptotic

/-- A real vector whose squared coordinates sum to at most one has Euclidean radius at most one. -/
theorem radius_le_one_of_sum_le_one {d : ℕ} {v : Fin d → ℝ} (h : ∑ k, (v k) ^ 2 ≤ 1) :
    radius v ≤ 1 :=
  (Real.sqrt_le_sqrt h).trans Real.sqrt_one.le

/-- The unit-ball volume in dimension one is `2`. -/
theorem unitBallVolume_one : unitBallVolume 1 = 2 := by
  have hpi : 0 < Real.sqrt Real.pi := Real.sqrt_pos.mpr Real.pi_pos
  have hG : Real.Gamma (1 / 2 + 1) = 1 / 2 * Real.sqrt Real.pi := by
    rw [Real.Gamma_add_one (by norm_num), Real.Gamma_one_half_eq]
  have e1 : ((1 : ℕ) : ℝ) / 2 + 1 = 1 / 2 + 1 := by norm_num
  unfold unitBallVolume
  rw [e1, hG, div_eq_iff (mul_ne_zero (by norm_num) hpi.ne')]
  ring

/-- The unit-ball volume in dimension two is `π`. -/
theorem unitBallVolume_two : unitBallVolume 2 = Real.pi := by
  have e2 : ((2 : ℕ) : ℝ) / 2 + 1 = 2 := by norm_num
  unfold unitBallVolume
  rw [e2, Real.Gamma_two, div_one, Real.sq_sqrt Real.pi_pos.le]

/-- In dimension one the nonzero index `1` lies in the unit-ball index set at scale `1/2`. -/
theorem one_mem_unitBallIndices_dim_one :
    (fun _ : Fin 1 => (1 : ℤ)) ∈ unitBallIndices 1 (1 / 2) := by
  refine (mem_unitBallIndices (by norm_num : (0 : ℝ) < 1 / 2) _).mpr ⟨fun h => ?_, ?_⟩
  · exact one_ne_zero (congrFun h 0)
  · exact radius_le_one_of_sum_le_one (by norm_num [physical, Fin.sum_univ_one])

/-- In dimension two the nonzero index `(1, 1)` lies in the unit-ball index set at scale `1/2`. -/
theorem one_mem_unitBallIndices_dim_two :
    (fun _ : Fin 2 => (1 : ℤ)) ∈ unitBallIndices 2 (1 / 2) := by
  refine (mem_unitBallIndices (by norm_num : (0 : ℝ) < 1 / 2) _).mpr ⟨fun h => ?_, ?_⟩
  · exact one_ne_zero (congrFun h 0)
  · exact radius_le_one_of_sum_le_one (by norm_num [physical, Fin.sum_univ_two])

/-- The radial error series over the nonzero integer points in dimension one is summable. -/
theorem radialError_summable_dim_one :
    Summable (fun w : {w : Site 1 // w ≠ 0} =>
      Real.rpow (radius (physical 1 w.val)) (-((1 : ℕ) : ℝ) - 1)) :=
  nonzero_radial_error_summable_real 1 le_rfl

/-- The radial error series over the nonzero integer points in dimension two is summable. -/
theorem radialError_summable_dim_two :
    Summable (fun w : {w : Site 2 // w ≠ 0} =>
      Real.rpow (radius (physical 1 w.val)) (-((2 : ℕ) : ℝ) - 1)) :=
  nonzero_radial_error_summable_real 2 (by norm_num)

/-- In dimension one, with exponent `2 > 1`, the exterior indicator series is summable at every
scale `ε ∈ (0,1)`: the summability comes from `exterior_rpow_sum_bound`. -/
theorem exterior_summable_dim_one (ε : ℝ) (hε : ε ∈ Set.Ioo (0 : ℝ) 1) :
    Summable (fun z : Site 1 =>
      if 1 ≤ radius (physical ε z) then (radius (physical ε z)) ^ (-(2 : ℝ)) else 0) := by
  obtain ⟨_, _, h⟩ := exterior_rpow_sum_bound 1 le_rfl 2 (by norm_num)
  exact (h ε hε).1

/-- In dimension two, with exponent `1 < 2`, the scaled radial sum is bounded uniformly in
`ε ∈ (0,1)`, with the constant of the regime `α < d`. -/
theorem upper_bound_dim_two :
    ∃ C : ℝ, 0 < C ∧ ∀ ε : ℝ, ε ∈ Set.Ioo (0 : ℝ) 1 →
      ε ^ 2 * (∑ z ∈ unitBallIndices 2 ε, (radius (physical ε z)) ^ (-(1 : ℝ))) ≤ C := by
  obtain ⟨C, hC, h⟩ := rpow_sum_upper_bound 2 (by norm_num) 1 (by norm_num)
  refine ⟨C, hC, fun ε hε => ?_⟩
  have hd := h ε hε
  rw [if_pos (show (1 : ℝ) < ((2 : ℕ) : ℝ) by norm_num)] at hd
  exact hd

/-- The critical lattice sum in dimension one: for every `R ≥ 2` the sum over the nonzero integer
points with `|z| ≤ R` of `|z|^{-1}` is within `K` of `2 log R`, with `2 = 1 · unitBallVolume 1`. -/
theorem critical_sum_asymp_dim_one :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ R : ℝ, 2 ≤ R →
      |(∑ z ∈ unitBallIndices 1 (1 / R), Real.rpow (radius (physical 1 z)) (-((1 : ℕ) : ℝ)))
        - 2 * Real.log R| ≤ K := by
  obtain ⟨K, hK0, hK⟩ := shell_sum_asymp (d := 1) le_rfl
  exact ⟨K, hK0, fun R hR => by simpa [unitBallVolume_one] using hK R hR⟩

/-- **The planar critical lattice sum.** For every `R ≥ 2` the sum over the nonzero integer
points with `|z| ≤ R` of `|z|^{-2}` is within `K` of `2π log R`, with
`2π = 2 · unitBallVolume 2`. -/
theorem critical_sum_asymp_dim_two :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ R : ℝ, 2 ≤ R →
      |(∑ z ∈ unitBallIndices 2 (1 / R), Real.rpow (radius (physical 1 z)) (-((2 : ℕ) : ℝ)))
        - 2 * Real.pi * Real.log R| ≤ K := by
  obtain ⟨K, hK0, hK⟩ := shell_sum_asymp (d := 2) (by norm_num)
  exact ⟨K, hK0, fun R hR => by simpa [unitBallVolume_two] using hK R hR⟩

end LatticeProb.Euclidean.Examples
