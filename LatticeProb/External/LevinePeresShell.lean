import LatticeProb.Sandpile.Toppling
import LatticeProb.Sandpile.FLP.Basic
import LatticeProb.Walk.Ball

/-!
# The shell bound of Levine and Peres

Theorem 4.1 of L. Levine and Y. Peres, *Strong spherical asymptotics for rotor-router
aggregation and the divisible sandpile*, Potential Anal. 30 (2009), 1–27,
[arXiv:0704.0688](https://arxiv.org/abs/0704.0688), with background height `h = d - 1`, as
quoted by A. Fey, L. Levine and Y. Peres, *Growth rates and explosions in sandpiles*,
[arXiv:0901.3805v2](https://arxiv.org/abs/0901.3805v2), Section 3.1: for every `ε ∈ (0, 1)`
there is a constant `c`, independent of `n`, such that the odometer of the pile
`(d - 1) + n δ₀` is at most `c` on the shell `c'₁ r - 1 < |x| ≤ c'₁ r`, where
`r = (n / ω_d)^{1/d}`, `c'₁ = (1 - ε)^{-1/d}` and `ω_d` is the volume of the Euclidean unit
ball. Levine and Peres count the chips emitted at a site, `2d` per toppling, so their constant
`c'₂` corresponds to `c = c'₂ / 2d` here.

The printed claim bounds the abelian odometer. The parallel odometer `podo t` stays below it at
every time `t` by the least action principle, so the statement below, phrased with `podo`,
follows from the printed one. This is a cited input; no proof is asserted by its definition.
-/

namespace LatticeProb.External

open LatticeProb LatticeProb.Sandpile

/-- The shell bound of Levine and Peres, Theorem 4.1, for the background height `d - 1`: the
parallel odometer of `(d - 1) + n δ₀` is bounded, uniformly in `n` and in time, on the shell
`c'₁ r - 1 < |x| ≤ c'₁ r` with `r = (n / ω_d)^{1/d}` and `c'₁ = (1 - ε)^{-1/d}`. -/
def LevinePeresShellBound : Prop :=
  ∀ d : ℕ, 2 ≤ d → ∀ ε : ℝ, 0 < ε → ε < 1 → ∃ c : ℕ, ∀ n : ℕ, 1 ≤ n → ∀ x : Site d,
    (1 - ε) ^ (-(1 / (d : ℝ))) * ((n : ℝ) / FLP.omegaD d) ^ (1 / (d : ℝ)) - 1 <
        LatticeProb.euclidNorm x →
    LatticeProb.euclidNorm x ≤
        (1 - ε) ^ (-(1 / (d : ℝ))) * ((n : ℝ) / FLP.omegaD d) ^ (1 / (d : ℝ)) →
    ∀ t : ℕ, podo (fun y : Site d => ((d : ℤ) - 1) + (n : ℤ) * dirac 0 y) t x ≤ c

end LatticeProb.External
