import LatticeProb.Sandpile.Toppling

/-!
# The radius bound of Fey, Levine and Peres

Theorem 1.1 of A. Fey, L. Levine and Y. Peres, *Growth rates and explosions in sandpiles*,
[arXiv:0901.3805v2](https://arxiv.org/abs/0901.3805v2), printed p. 4.
For `d <= h <= 2d - 2`, the sites that topple from the pile `h + n delta_0` eventually lie
in the cube of radius `((d + eps) / (2d - 1 - h)) * (n / omega_d)^(1/d)`, for every
`eps > 0`. The threshold in `n` may depend on `d`, `h` and `eps`.

Section 2, pp. 5-6, includes the discrete parallel toppling procedure. The toppled set
here therefore uses positive parallel odometer at some finite time. `omega_d` is the
Lebesgue volume of the Euclidean unit ball. This is a cited input; no proof is asserted
by its definition.
-/

namespace LatticeProb.External

open LatticeProb LatticeProb.Sandpile MeasureTheory

/-- The eventual outer-radius bound in Fey, Levine and Peres, Theorem 1.1, for every
positive `eps` and background height `d <= h <= 2d - 2`. -/
def FeyLevinePeresRadius : Prop :=
  ∀ d : ℕ, ∀ h : ℤ, (d : ℤ) ≤ h → h ≤ 2 * (d : ℤ) - 2 →
    ∀ ε : ℝ, 0 < ε →
      ∃ n0 : ℕ, ∀ n : ℕ, n0 ≤ n →
        {x : Site d | ∃ t : ℕ, 0 < podo (fun y : Site d => h + (n : ℤ) * dirac (0 : Site d) y) t x} ⊆
          {x : Site d | ∀ i : Fin d, |(x i : ℝ)| ≤
            (((d : ℝ) + ε) / (2 * (d : ℝ) - 1 - (h : ℝ))) *
              (((n : ℝ) / (volume (Metric.ball (0 : EuclideanSpace ℝ (Fin d)) 1)).toReal) ^
                (1 / (d : ℝ)))}

end LatticeProb.External
