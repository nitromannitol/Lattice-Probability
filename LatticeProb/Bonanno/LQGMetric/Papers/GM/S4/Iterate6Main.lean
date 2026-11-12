/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.GM.S4.Iterate6Main at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S4.Iterate6Pair
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S4.Iterate6L411
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S4.Iterate5Chain
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S2.Geodesics
import LatticeProb.Bonanno.LQGMetric.Papers.DG.XiQBound
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S4.L47MeasC

/-!
# `T4_2PairOne` and GM Theorem 4.2, modulo Proposition 4.12 (P2-M2K6)

Source: GM = `literature/src/1905.00383/uniqueness-final.tex`, proof of Theorem 4.2 (l. 1611–1613,
2437–2446): Lemma 4.11 (the regularity event `ℰ_𝕣`, l. 1979–1990), Proposition 4.12 (`GMP4_12`,
taken as a hypothesis: P2-M2J2e), Proposition 4.17 / Lemma 4.21 (`gm_T42_pairU`).

* `GMP4_12`: GM Proposition 4.12 for every weak LQG metric, valid CONF parameters, Hölder
  exponents `0 < χ < ξ(Q−2)`, `χ' > ξ(Q+2)` and constant-invariant geodesic selector.
* `gm_T4_2PairOne`: `T4_2PairOne` (D89), and `gm_T4_2 : T4_2` through `gm_T4_2_of_pairOne`.

Choices (GM l. 1611–1613, 2437–2446): `χ = ξ(Q−2)/2`, `χ' = ξ(Q+2) + 1`; `β, θ` from P4.12;
`ν_* = β/8`, `ζ = β/4` (so `4ν + ζ < β`); `ℓ_reg = ℓ/4` (pairs with `|𝕫 − 𝕨| ≥ ℓ R = 4ℓ_reg R`);
`p = max(1 − η, 1/2)` in Lemma 4.11 and `a ≤ ℓ/4`; the events `E'_r(z) = E_r(z)` for `r ∈ ℛ`,
`= DistC` otherwise, and the radii `r'^ε_k(𝕣) = (𝕣/R) r^ε_k` (`ε ≤ ε₀`), `= ε𝕣` otherwise, so that
the `∀ 𝕣` hypotheses of Lemma 4.11 and Proposition 4.12 hold (only `𝕣 = R` is used); the
probability space is completed (D70) and the field normalized by `h(ψ₀) = 0` with a far test
function `ψ₀` (`gm_exists_farTest`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory MeasurableSpace Set Filter Metric Topology
open LQGMetric.Blueprint
open scoped ENNReal

namespace LQGMetric.GM

theorem gm_Q_sub_two_pos {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) : 0 < Q γ - 2 := by
  unfold Q
  have : 2 / γ + γ / 2 - 2 = (2 - γ) ^ 2 / (2 * γ) := by field_simp; ring
  rw [this]
  have : 0 < 2 - γ := by linarith
  positivity

end LQGMetric.GM
