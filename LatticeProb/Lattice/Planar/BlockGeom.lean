/- Adapted from nitromannitol/rotor-23, Apache-2.0; copyright 2026 Ahmed Bou-Rabee and Yuval Peres. -/
import Mathlib

open Filter Topology

namespace LatticeProb.Lattice.Planar

/-- The `ℓ^∞` norm on `ℤ²` as an integer. -/
def linf (z : ℤ × ℤ) : ℤ := max |z.1| |z.2|

end LatticeProb.Lattice.Planar
