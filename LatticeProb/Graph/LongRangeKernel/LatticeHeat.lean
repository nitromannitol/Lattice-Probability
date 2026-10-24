import LatticeProb.Graph.LongRangeKernel.Lattice
import LatticeProb.Walk.SRW

/-!
# Heat density of the reference lattice

The counting-measure heat density of the normalized lattice is the simple random walk
kernel evaluated at the displacement between its endpoints.
-/

namespace LatticeProb.Graph.LongRangeKernel

open LatticeProb
open scoped ENNReal

noncomputable section

variable {d : ℕ}

/-- Reflection about a fixed endpoint converts the lattice average to a displacement average. -/
theorem walkOp_reflect (f : Site d → ℝ) (x y : Site d) :
    LatticeProb.walkOp (fun z => f (y - z)) x =
      LatticeProb.walkOp f (y - x) := by
  unfold LatticeProb.walkOp nbrSum
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  dsimp only
  rw [show y - (x + unit i) = (y - x) - unit i by abel,
    show y - (x - unit i) = (y - x) + unit i by abel]
  exact add_comm _ _

/-- The normalized lattice heat density is the simple random walk displacement kernel. -/
theorem weightedLattice_heat_eq (hd : 0 < d) (n : ℕ) (x y : Site d) :
    (weightedLattice d hd).heat n x y = ENNReal.ofReal (srwHeat d n (y - x)) := by
  classical
  induction n generalizing x y with
  | zero =>
    simp only [WeightedGraph.heat, densityPower, identityDensity, weightedLattice_mass,
      ENNReal.coe_one, inv_one, srwHeat_zero, sub_eq_zero]
    by_cases h : x = y <;> simp [h, eq_comm]
  | succ n ih =>
    change (∑' z, (weightedLattice d hd).referenceDensity x z *
      (weightedLattice d hd).heat n z y *
      ((weightedLattice d hd).mass z : ℝ≥0∞)) = _
    simp_rw [weightedLattice_referenceDensity, weightedLattice_mass,
      ENNReal.coe_one, mul_one, ih]
    rw [tsum_eq_sum (s := (lattice d).neighborFinset x)]
    · have hsum : (∑ z ∈ (lattice d).neighborFinset x,
          (if (lattice d).Adj x z then (2 * (d : ℝ≥0∞))⁻¹ else 0) *
            ENNReal.ofReal (srwHeat d n (y - z))) =
          ENNReal.ofReal (LatticeProb.Graph.walkOp (lattice d)
            (fun z => srwHeat d n (y - z)) x) := by
        unfold LatticeProb.Graph.walkOp
        rw [ENNReal.ofReal_div_of_pos (by
          rw [LatticeProb.Graph.Zd.degree_eq]
          exact_mod_cast (by omega : 0 < 2 * d)),
          ENNReal.ofReal_sum_of_nonneg (fun z _ => srwHeat_nonneg n (y - z)),
          LatticeProb.Graph.Zd.degree_eq]
        push_cast
        rw [div_eq_mul_inv, Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro z hz
        rw [if_pos (((lattice d).mem_neighborFinset x z).mp hz)]
        rw [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2)]
        norm_num only [ENNReal.ofReal_ofNat, ENNReal.ofReal_natCast]
        exact mul_comm _ _
      rw [hsum, LatticeProb.Graph.Zd.walkOp_eq, walkOp_reflect, srwHeat_succ]
    · intro z hz
      rw [if_neg (fun h => hz (((lattice d).mem_neighborFinset x z).mpr h)), zero_mul]

end

end LatticeProb.Graph.LongRangeKernel
