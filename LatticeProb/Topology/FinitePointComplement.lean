/-
The complement of finitely many points in the real plane is path connected.
The proof specializes the countable-complement theorem to the rank-two product space.
-/
import Mathlib.Analysis.Normed.Module.Connected
import Mathlib.LinearAlgebra.Dimension.Constructions
namespace LatticeProb.PlaneTopology

/-- The real plane has dimension strictly greater than one. -/
theorem one_lt_rank_plane : 1 < Module.rank ℝ (ℝ × ℝ) := by
  rw [rank_prod']
  simp only [CommSemiring.rank_self]
  norm_num

/-- **Finite point removal.** Removing any finite set of real plane points leaves a
path connected set, without assumptions on the locations or their distinctness. -/
theorem isPathConnected_compl_of_finite {s : Set (ℝ × ℝ)} (hs : s.Finite) :
    IsPathConnected sᶜ :=
  hs.countable.isPathConnected_compl_of_one_lt_rank one_lt_rank_plane

/-- The plane with the positions of any finite family removed is path connected. -/
theorem isPathConnected_compl_range {ι : Type*} [Finite ι] (p : ι → ℝ × ℝ) :
    IsPathConnected (Set.range p)ᶜ :=
  isPathConnected_compl_of_finite (Set.finite_range p)

end LatticeProb.PlaneTopology
