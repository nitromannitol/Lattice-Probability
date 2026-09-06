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
LatticeProb/Walk/                   simple and lazy random walk on the lattice
LatticeProb/Prob/                   the general probability facts the papers cite
LatticeProb/External/               statements taken from the literature, as explicit hypotheses
```

## Build

```sh
lake exe cache get
lake build
```

The library is pinned to the Mathlib revision in `lake-manifest.json`; the
formalizations that depend on it use the same pin.
