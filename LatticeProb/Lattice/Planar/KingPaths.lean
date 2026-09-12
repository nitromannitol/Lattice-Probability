/- Adapted from nitromannitol/rotor-23, Apache-2.0; copyright 2026 Ahmed Bou-Rabee and Yuval Peres. -/
import LatticeProb.Lattice.Planar.BlockGeom

open Finset

namespace LatticeProb.Lattice.Planar

/-- A king step: a move to a different point with each coordinate changing by at most one. -/
def KingStep (a b : ℤ × ℤ) : Prop := a ≠ b ∧ linf (b - a) ≤ 1

end LatticeProb.Lattice.Planar
