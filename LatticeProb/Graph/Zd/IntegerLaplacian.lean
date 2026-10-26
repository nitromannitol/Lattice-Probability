import LatticeProb.Prob.Percolation.LatticeBondModel
import Mathlib.Data.Finset.Max
import Mathlib.Algebra.Group.Subgroup.Finite

/-!
# Integer values from a finitely supported integer lattice Laplacian

In every positive dimension, a finitely supported real function with integer-valued
unnormalized nearest-neighbor Laplacian is integer-valued. A noninteger site maximal in
one coordinate would be the unique noninteger neighbor of the site immediately above it.
-/

namespace LatticeProb.Graph.Zd

open LatticeProb Percolation

variable {d : ℕ}

/-- A neighbor of the site just above `x` is either `x` or strictly above `x`. -/
theorem neighbor_above_eq_or_lt (i : Fin d) (x z : Fin d → ℤ)
    (hz : (nearestNeighborGraph d).Adj (x + unit i) z) :
    z = x ∨ x i < z i := by
  obtain ⟨j, hj | hj⟩ := adj_iff.mp hz
  · right
    rw [hj]
    by_cases hji : j = i
    · subst j
      simp only [Pi.add_apply, unit, Pi.single_eq_same]
      omega
    · simp only [Pi.add_apply, unit, Pi.single_eq_same, Pi.single_eq_of_ne (Ne.symm hji)]
      omega
  · by_cases hji : j = i
    · subst j
      left
      rw [hj, add_sub_cancel_right]
    · right
      rw [hj]
      simp only [Pi.add_apply, Pi.sub_apply, unit, Pi.single_eq_same,
        Pi.single_eq_of_ne (Ne.symm hji)]
      omega

/-- Finite support and an integer-valued full lattice Laplacian force integer values,
provided the dimension is positive. -/
theorem integer_values_of_finite_support_integer_laplacian (hd : 0 < d)
    (u : (Fin d → ℤ) → ℝ) (hs : (Function.support u).Finite)
    (hΔ : ∀ x, ∃ n : ℤ, laplacian (nearestNeighborGraph d) u x = (n : ℝ)) :
    ∀ x, ∃ n : ℤ, u x = (n : ℝ) := by
  classical
  let I : AddSubgroup ℝ := (Int.castAddHom ℝ).range
  have memI (r : ℝ) : r ∈ I ↔ ∃ n : ℤ, r = (n : ℝ) := by
    exact ⟨fun ⟨n, hn⟩ => ⟨n, hn.symm⟩, fun ⟨n, hn⟩ => ⟨n, hn.symm⟩⟩
  have hbad : {x | u x ∉ I}.Finite := hs.subset (by
    intro x hx hzero
    exact hx (hzero ▸ I.zero_mem))
  intro a
  by_contra ha
  have haI : u a ∉ I := fun h => ha ((memI _).mp h)
  let B := hbad.toFinset
  let i : Fin d := ⟨0, hd⟩
  obtain ⟨x, hx, hmax⟩ := B.exists_max_image (fun x => x i)
    ⟨a, hbad.mem_toFinset.mpr haI⟩
  have hxI : u x ∉ I := hbad.mem_toFinset.mp hx
  have above (z : Fin d → ℤ) (hz : x i < z i) : u z ∈ I := by
    by_contra hzI
    exact (not_le_of_gt hz) (hmax z (hbad.mem_toFinset.mpr hzI))
  let y := x + unit i
  have hy : u y ∈ I := above y (by
    dsimp [y]
    simp only [unit, Pi.single_eq_same]
    omega)
  have hxy : x ∈ (nearestNeighborGraph d).neighborFinset y := by
    apply (SimpleGraph.mem_neighborFinset _ _ _).mpr
    exact adj_iff.mpr ⟨i, Or.inr (by dsimp [y]; abel)⟩
  have hsum : (∑ z ∈ ((nearestNeighborGraph d).neighborFinset y).erase x,
      (u z - u y)) ∈ I := by
    apply I.sum_mem
    intro z hz
    obtain ⟨hzx, hzy⟩ := Finset.mem_erase.mp hz
    have hzadj := (SimpleGraph.mem_neighborFinset _ _ _).mp hzy
    have hzabove := (neighbor_above_eq_or_lt i x z hzadj).resolve_left hzx
    exact I.sub_mem (above z hzabove) hy
  have htotal : laplacian (nearestNeighborGraph d) u y ∈ I := (memI _).mpr (hΔ y)
  have heq := Finset.sum_erase_add ((nearestNeighborGraph d).neighborFinset y)
    (fun z => u z - u y) hxy
  change _ = laplacian (nearestNeighborGraph d) u y at heq
  have hterm : u x - u y ∈ I := by
    have hm := I.sub_mem htotal hsum
    rw [← heq] at hm
    simpa only [add_sub_cancel_left] using hm
  exact hxI (by simpa only [sub_add_cancel] using I.add_mem hterm hy)

end LatticeProb.Graph.Zd
