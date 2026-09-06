# Lattice-Probability

A Lean 4 library for probability on the lattice `ℤ^d`, shared by the
formalizations of Ahmed Bou-Rabee's papers.  It collects the objects those
papers have in common so that each formalization can import them rather than
define its own: sites and the nearest-neighbour graph, the simple random walk
operator, i.i.d. fields, and site-indexed instruction stacks.

## Layout

```text
LatticeProb/Site.lean               sites, unit vectors, the lattice graph, the walk operator, boxes, components
LatticeProb/IID.lean                i.i.d. fields, instruction stacks and arrival counts
LatticeProb/Rank.lean               ranking a finite set by an injective key
LatticeProb/ParticleHole.lean       the particle-hole process: driver, state, one round
LatticeProb/ParticleHoleLemmas.lean the leaf facts about that process
LatticeProb/Walk/Basic.lean         paths on the lattice: directions, positions, ranges, edges
LatticeProb/Walk/Path.lean          path facts and the law of the first n steps of the walk
LatticeProb/Walk/Lazy.lean          the lazy walk operator Q and the truncated Green function
LatticeProb/Walk/OneDim.lean        the one-dimensional lazy kernel
LatticeProb/Walk/SRW.lean           the simple random walk kernel, its support and parity
LatticeProb/Walk/OneDimGauss.lean   the Gaussian bound on the one-dimensional lazy kernel
LatticeProb/Walk/SRWOneDim.lean     the one-dimensional simple kernel against the lazy one
LatticeProb/Walk/SRWDecomp.lean     the coordinate decomposition of the simple kernel
LatticeProb/Walk/SRWGauss.lean      the ingredients of the Gaussian bound on the lattice
LatticeProb/Walk/S1Gauss.lean       the Gaussian bound on the one-dimensional simple kernel
LatticeProb/Walk/SRWSup.lean        the sup bound on the simple kernel
LatticeProb/Walk/SRWGreenSup.lean   the truncated Green function of the simple walk by dimension
LatticeProb/Walk/SRWGaussBound.lean the Gaussian upper bound on the simple kernel
LatticeProb/Walk/SchedExtra.lean    the sharper schedule average behind the gradient bound
LatticeProb/Walk/P1Grad.lean        the gradient of the one-dimensional lazy kernel
LatticeProb/Walk/LazyGrad.lean      the gradient of the lazy kernel on the lattice
LatticeProb/Walk/Decomp.lean        the coordinate decomposition of the r-step kernel
LatticeProb/Walk/Moment.lean        moments of the coordinate visit counts
LatticeProb/Walk/LazyBox.lean       the r-step kernel on a box
LatticeProb/Walk/Series.lean        the three series bounds
LatticeProb/Walk/GreenBounds.lean   the sup, oscillation and total variation bounds
LatticeProb/Walk/Green.lean         G_n(0,0) is of order sqrt n, log n, or bounded
LatticeProb/Walk/Poisson.lean       the Poisson equation for the truncated Green function
LatticeProb/Walk/RangeBox.lean      the range of a path fits in a box
LatticeProb/Walk/Infinite.lean      the walk on infinite paths, and the finite marginals
LatticeProb/Walk/Dirichlet.lean     the Dirichlet Laplacian, mean exit times, effective resistance
LatticeProb/Walk/Harmonic.lean      the maximum principle, the Green function, one-point insertion
LatticeProb/Walk/Energy.lean        the Dirichlet energy and the Thomson resistance comparison
LatticeProb/Walk/BoxAverage.lean    the discrete Poincare inequality and the bound on T(A)
LatticeProb/Walk/ExitTime.lean      the exit time bounds for a finite set
LatticeProb/Walk/ExitBox.lean       the exit time of a box of radius r is of order r squared
LatticeProb/Prob/Catalog.lean       Mathlib's probability theorems under this library's names
LatticeProb/Prob/Harris.lean        the Harris inequality for product measures
LatticeProb/Prob/HarrisVariants.lean  decreasing, mixed, and locally monotone forms
LatticeProb/Prob/ZeroOne.lean       the ergodic zero-one law for coordinate shifts
LatticeProb/Prob/Translation.lean   translation-invariant events of an i.i.d. field on the lattice
LatticeProb/Prob/HewittSavage.lean  the Hewitt-Savage zero-one law for exchangeable events
LatticeProb/Prob/HarrisCube.lean    the Harris inequality on the discrete and continuous cubes
LatticeProb/Prob/BK.lean            the van den Berg-Kesten inequality on the finite cube
LatticeProb/Prob/InfinitePiSplit.lean  the head-tail decomposition of a product over the naturals
LatticeProb/Prob/Coordinate.lean    one coordinate of an infinite product, against the rest
LatticeProb/Prob/MaximalErgodic.lean  the maximal ergodic theorem
LatticeProb/Prob/Birkhoff.lean      the pointwise ergodic theorem
LatticeProb/Prob/Kingman.lean       the subadditive ergodic theorem
LatticeProb/Prob/SubGaussian.lean   sub-Gaussian behaviour on a range, and its Bernstein tail
LatticeProb/Prob/EfronStein.lean    the exponential Efron-Stein inequality on a product measure
LatticeProb/Prob/WeightedConc.lean  weighted exponential concentration and its tail
LatticeProb/Walk/Markov.lean        the Markov property at a fixed time and at a bounded stopping time
LatticeProb/Graph/                  the divisible sandpile and the walk on a general graph, and the
                                    random-walk (optimal-stopping) representation of the odometer,
                                    with its specializations to the lattice
```

## Attribution

Three files under `LatticeProb/Prob/` are adapted from an Apache-2.0 licensed
library; see `NOTICE`.

## Build

```sh
lake exe cache get
lake build
```

The library is pinned to the Mathlib revision in `lake-manifest.json`; the
formalizations that depend on it use the same pin.
