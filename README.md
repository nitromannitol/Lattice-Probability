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
LatticeProb/Walk/GaussSeries.lean   summing a Gaussian kernel bound over time
LatticeProb/Walk/GreenIdentity.lean the lazy Green function is twice the simple one
LatticeProb/Walk/SimpleTransfer.lean  the Green function of the simple walk
LatticeProb/Walk/GRGrad.lean        the Green gradient bound, for both walks
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
LatticeProb/Prob/Ottaviani.lean     Ottaviani's maximal inequality, as a first passage decomposition
LatticeProb/Prob/BrownianMax.lean   the Gaussian maximal estimate for Brownian motion: the tail of the
                                    largest displacement before a time, by Ottaviani's inequality on a
                                    dyadic grid
LatticeProb/Prob/BrownianExit.lean  Brownian motion on R^d with generator Delta/(2d), and the Gaussian
                                    tail of the time at which it leaves a ball, for every positive
                                    radius and for the closed ball as well as the open one
LatticeProb/Prob/NetApprox.lean     the partition of unity attached to a finite set of points of a
                                    metric space, and the interpolation of a function by its values
                                    on that set
LatticeProb/Prob/FddTight.lean      from the finite-dimensional laws and equicontinuity in probability
                                    to the expectation of a bounded uniformly continuous functional
                                    of the whole path
LatticeProb/Prob/BrownianMarkov.lean  restarting Brownian motion at a deterministic time, its natural
                                    filtration, the event of having left a ball as an event of the
                                    past, and the strong Markov property at a stopping time as a
                                    stated property
LatticeProb/Prob/IndepPi.lean       independent pairs give independent families: the supremum of one
                                    half of a family of independent pairs is independent of the
                                    supremum of the other half
LatticeProb/Prob/StoppingDyadic.lean  the dyadic approximation of a stopping time from above, its
                                    countably many values and its convergence
LatticeProb/Prob/BrownianPathLaw.lean  the law of a pre-Brownian motion on path space, and the
                                    invariance of the law of the increments under restarting at a
                                    deterministic time
LatticeProb/Prob/BrownianStrongMarkov.lean  the strong Markov property of Brownian motion on
                                    R^d: the increments after a stopping time have the law of the
                                    centred motion and are independent of the past
LatticeProb/Prob/BrownianRestartIntegral.lean  the strong Markov property as a change of the
                                    restarted path for a fresh motion inside an expectation
LatticeProb/Prob/BrownianExitTime.lean  the exit time of a ball, its stopping-time property, and
                                    the exit time stopped at a horizon
LatticeProb/Prob/BrownianContAll.lean  Kolmogorov-Chentsov on the half line with every path
                                    continuous, and a Brownian motion on R^d that has it
LatticeProb/Prob/RegularVariation.lean  regular variation at infinity and Potter's bounds for a
                                    monotone regularly varying function
LatticeProb/Prob/Karamata.lean      Karamata's theorem for the integrated tail, and the layer cake
                                    identity that makes it a statement about a law
LatticeProb/Prob/KaramataOrigin.lean  Karamata's theorem for the integral from the origin of a
                                    regularly varying function of index above -1, and the limit
                                    of the tail against the integrated reciprocal of the
                                    integrated tail
LatticeProb/Prob/Freedman.lean      Freedman's inequality for a martingale with bounded increments,
                                    through the exponential supermartingale
LatticeProb/Prob/Moments.lean       the second and fourth moment of an independent centred sum
LatticeProb/Prob/VonBahrEsseenSum.lean  the von Bahr-Esseen inequality: the p-th moment bound
                                    for an independent centred sum (1 ≤ p ≤ 2) and its tail bound
LatticeProb/Network/                electrical networks on a locally finite graph: the Dirichlet
                                    energy and form, harmonic functions, the killed Green function
                                    as a voltage, the maximum and Dirichlet principles, Rayleigh
                                    monotonicity, Thomson's principle and the Nash-Williams bound
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
