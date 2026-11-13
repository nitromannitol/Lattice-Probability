import LatticeProb.Vendor.FormalMathPercolation.Literature.KestenTheoremProofs
import LatticeProb.Vendor.FormalMathPercolation.Literature.SharpnessDCTProofs
import LatticeProb.Vendor.FormalMathPercolation.Literature.BondPercolationSymmetry

/-!
# Percolation on `ℤ^d`: Kesten's theorem and sharpness of the phase transition

Vendored copy of the part of the `Percolation` library of `anthropics/formal-math`
(commit `795efb86f191735c5481675763537cfb4ff37e55`, subdirectory `percolation`, Apache License 2.0)
that is needed for

* `Percolation.Literature.kesten_criticalProb_Z2_holds`: the critical probability of bond
  percolation on `ℤ²` is `1/2`;
* `Percolation.Literature.DCT16.perc_sharpness_holds`: sharpness of the phase transition for Bernoulli
  bond percolation on `ℤ^d`, `d ≥ 2`;
* `Percolation.Literature.setBernoulli_map_relabel`: invariance of the law of Bernoulli bond
  percolation under relabelling the pairs of vertices along an equivalence.

The files below `Vendor/FormalMathPercolation/` are the original sources with the module paths of
their `import` lines rewritten; `LICENSE` and `NOTICE` of the original are kept in that directory.
-/
