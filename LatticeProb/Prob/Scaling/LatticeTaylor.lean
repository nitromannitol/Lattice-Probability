/- Coordinate rescaling and symmetric second differences for the lattice walk operator.

Moved from Parking-Sharpness.
-/
import LatticeProb.Site

open LatticeProb
noncomputable section
namespace LatticeProb.Scaling.LatticeTaylor
variable {d : ℕ}

/-- Rescaling a positive lattice step changes one real coordinate by the mesh size. -/
theorem rescale_add_unit (y : Site d) (i : Fin d) (R : ℝ) :
    (fun j => ((y + unit i) j : ℝ) / R) =
      Function.update (fun j => (y j : ℝ) / R) i ((y i : ℝ) / R + 1 / R) := by
  funext j
  by_cases h : j = i
  · subst j
    simp [unit, add_div]
  · simp [unit, h]

/-- Rescaling a negative lattice step changes one real coordinate by the mesh size. -/
theorem rescale_sub_unit (y : Site d) (i : Fin d) (R : ℝ) :
    (fun j => ((y - unit i) j : ℝ) / R) =
      Function.update (fun j => (y j : ℝ) / R) i ((y i : ℝ) / R - 1 / R) := by
  funext j
  by_cases h : j = i
  · subst j
    simp [unit, sub_div]
  · simp [unit, h]

/-- The walk generator is the normalized sum of symmetric second differences. -/
theorem walkOp_sub_eq_sum (hd : 1 ≤ d) (f : Site d → ℝ) (y : Site d) :
    walkOp f y - f y =
      (∑ i : Fin d, (f (y + unit i) + f (y - unit i) - 2 * f y)) / (2 * d) := by
  have hd0 : (d : ℝ) ≠ 0 := by exact_mod_cast (by omega : d ≠ 0)
  simp only [walkOp, nbrSum, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul]
  field_simp

end LatticeProb.Scaling.LatticeTaylor
end
