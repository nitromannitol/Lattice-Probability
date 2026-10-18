import LatticeProb.Sandpile.LeastAction

/-!
# Cubical toppling clusters on the background `2d - 2`

The lower-radius part of Theorem 4.1 of A. Fey-den Boer and F. Redig,
*Limiting shapes for deterministic centrally seeded growth models*,
[arXiv:math/0702450v2](https://arxiv.org/abs/math/0702450v2), printed p. 7.
Section 2 uses total origin height `n` and background height `h` elsewhere. Here
`h = 2d - 2` and `N` counts extra chips, so `n = N + h`. A site topples at height `2d`.

This proposition retains the cubical toppled support and its lower-radius bound,
restricted to `d >= 2` and `N >= 2`. The proof on pp. 8-9 constructs integer radii
starting at zero and increasing by zero or one. A legal procedure starts with zero
odometer, stabilizes in finite time and has stable terminal configuration. Its terminal
positive-odometer support is the integer cube. The upper-radius and particle-cluster
conclusions are omitted. This is a cited input; no proof is asserted by its definition.
-/

namespace LatticeProb.External

open LatticeProb LatticeProb.Sandpile

/-- The cubical toppled-support and lower-radius conclusion of Fey-den Boer and Redig,
Theorem 4.1, with total origin height `N + 2d - 2`. -/
def FeyDenBoerRedigCubicalCluster : Prop :=
  ∀ d : ℕ, 2 ≤ d → ∀ N : ℕ, 2 ≤ N → ∀ s0 : Site d → ℤ,
    (∀ x : Site d, s0 x = (2 * (d : ℤ) - 2) + (N : ℤ) * dirac (0 : Site d) x) →
      ∃ u : ℕ → Site d → ℤ, ∃ T : ℕ,
        IsLegalToppling s0 u ∧
        (∀ t : ℕ, T ≤ t → u t = u T) ∧
        (∀ x : Site d, s0 x + lap (u T) x < 2 * (d : ℤ)) ∧
        ∃ r : ℕ,
          {x : Site d | 0 < u T x} = {x : Site d | ∀ i : Fin d, |x i| ≤ (r : ℤ)} ∧
          ((((N : ℝ) + 2 * (d : ℝ) - 2) ^ (1 / (d : ℝ)) - 3) / 2 ≤ (r : ℝ))

end LatticeProb.External
