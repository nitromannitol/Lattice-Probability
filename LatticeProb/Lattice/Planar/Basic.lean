/- Adapted from nitromannitol/rotor-23, Apache-2.0; copyright 2026 Ahmed Bou-Rabee and Yuval Peres. -/
import Mathlib

namespace LatticeProb.Lattice.Planar

/-- A site of the square lattice `ℤ²`. -/
abbrev Site := ℤ × ℤ

/-- A direction out of a site; equivalently the directed edge it names.  The
numbering is the paper's clockwise order `N, E, S, W`. -/
abbrev Dir := Fin 4

/-- The unit step `N, E, S, W` in direction `a`. -/
def dirVec (a : Dir) : Site := ![((0 : ℤ), (1 : ℤ)), (1, 0), (0, -1), (-1, 0)] a

end LatticeProb.Lattice.Planar
