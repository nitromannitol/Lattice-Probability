import LatticeProb.External.FeyDenBoerRedigCubicalCluster
import LatticeProb.Sandpile.RadiusConsequences
import LatticeProb.Sandpile.FdBR.Stabilize
import LatticeProb.Sandpile.FdBR.CubeSupport
import LatticeProb.Sandpile.FdBR.RadiusBound

/-!
# The cubical cluster of Fey-den Boer and Redig, proved

The proposition `LatticeProb.External.FeyDenBoerRedigCubicalCluster` holds. Its witness is the
parallel toppling odometer `podo s0`, which is a legal toppling procedure. The time `T` and the
stability of the terminal configuration come from `fdbr_podo_stabilizes`. The terminal positive
support is finite, so it is the integer cube of `fdbr_support_eq_cube`, and the radius bound is
`fdbr_radius_bound` applied to `podo s0 T`.  Consequently the terminal cube of the parallel
process, `LatticeProb.Sandpile.fdbr_parallel_terminal`, holds without its hypothesis
(`LatticeProb.Sandpile.fdbr_parallel_terminal_unconditional`).
-/

namespace LatticeProb.External

open LatticeProb LatticeProb.Sandpile

/-- **The cubical cluster of Fey-den Boer and Redig holds**: for `d ≥ 2` and `N ≥ 2`, the parallel
odometer from the background `2d - 2` with `N` extra chips at the origin is legal, eventually
constant, stable at its terminal time, has the integer cube as terminal positive support, and
satisfies the lower radius bound. -/
theorem feyDenBoerRedigCubicalCluster_holds : FeyDenBoerRedigCubicalCluster := by
  intro d hd N hN s0 hs0
  have hd1 : 1 ≤ d := by omega
  obtain ⟨T, hconst, hstab, K, hK⟩ := fdbr_podo_stabilizes hd1 N s0 hs0
  have hfin : {x : Site d | 0 < podo s0 T x}.Finite := by
    refine Set.Finite.subset (Set.finite_Icc (fun _ => -(K : ℤ)) (fun _ => (K : ℤ))) ?_
    intro x hx
    have hx0 : 0 < podo s0 T x := hx
    have hlt : supNormNat x < K := not_le.mp fun h => hx0.ne' (hK x h)
    have habs : ∀ i, |x i| ≤ (K : ℤ) := fun i => by
      have hle : (x i).natAbs ≤ supNormNat x :=
        Finset.le_sup (f := fun i => (x i).natAbs) (Finset.mem_univ i)
      rw [Int.abs_eq_natAbs]
      exact_mod_cast hle.trans hlt.le
    exact Set.mem_Icc.mpr ⟨fun i => (abs_le.mp (habs i)).1, fun i => (abs_le.mp (habs i)).2⟩
  obtain ⟨r, hr⟩ := fdbr_support_eq_cube hd1 hN s0 hs0 T hstab hfin
  exact ⟨podo s0, T, podo_isLegal s0, hconst, hstab, r, hr,
    fdbr_radius_bound hd1 N s0 hs0 (podo s0 T) (fun x => (podo_isLegal s0).nonneg T x) r hr hstab⟩

end LatticeProb.External

namespace LatticeProb.Sandpile

/-- **Terminal cube of the parallel process**, with no hypothesis.  For the background `2d - 2`
with `N ≥ 2` extra chips at the origin, the parallel odometer `podo s0` is globally
stabilizable, and at every time `T` after which it no longer changes its positive-odometer
support is the integer cube `{x : max_i |x_i| ≤ r}` for a natural radius `r` with
`((N + 2d - 2)^(1/d) - 3) / 2 ≤ r`. -/
theorem fdbr_parallel_terminal_unconditional (d : ℕ) (hd : 2 ≤ d) (N : ℕ) (hN : 2 ≤ N)
    (s0 : Site d → ℤ)
    (hs0 : ∀ x : Site d, s0 x = (2 * (d : ℤ) - 2) + (N : ℤ) * dirac (0 : Site d) x) :
    Stabilizable s0 ∧ ∃ r : ℕ,
      (∀ T : ℕ, (∀ t : ℕ, T ≤ t → podo s0 t = podo s0 T) →
        {x : Site d | 0 < podo s0 T x} = {x : Site d | ∀ i : Fin d, |x i| ≤ (r : ℤ)}) ∧
      ((((N : ℝ) + 2 * (d : ℝ) - 2) ^ (1 / (d : ℝ)) - 3) / 2 ≤ (r : ℝ)) :=
  fdbr_parallel_terminal LatticeProb.External.feyDenBoerRedigCubicalCluster_holds d hd N hN s0 hs0

end LatticeProb.Sandpile
