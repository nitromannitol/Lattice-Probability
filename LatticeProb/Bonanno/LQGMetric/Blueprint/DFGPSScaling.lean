/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Blueprint.DFGPSScaling at commit fdb5cad; only the module paths of local imports are changed.
   Declarations, examples and checks that the copied results do not use are omitted. -/
import LatticeProb.Bonanno.LQGMetric.Statement.LQGMetric

/-!
# Blueprint: DFGPS Theorem 1.5 (optimal scaling of the constants 𝔠_r)

Source: Dubédat–Falconet–Gwynne–Pfeffer–Sun, *Weak LQG metrics and Liouville first passage
percolation*, arXiv:1905.00380 (DFGPS), `literature/src/1905.00380/lqg-metric-estimates-final.tex`,
l. 426–436 (standing assumption l. 426: "we assume that D is a weak γ-LQG metric and h is a
whole-plane GFF"; weak γ-LQG metrics are defined for γ ∈ (0,2), l. 323):

> **Theorem 1.5.** Let ξ be as in (1.1) and let Q = 2/γ + γ/2. Then for r > 0, the scaling
> constants satisfy 𝔠_{δr}/𝔠_r = δ^{ξQ + o_δ(1)} as δ → 0, at a rate which is uniform over all
> r > 0.

Cited by GM l. 452–456 as (1.13) ("for any weak γ-LQG metric … uniformly over all r > 0") and
used in the proof of GM Lemma 1.10 (l. 529) for the constants `𝔠_r = r^{−α}` produced there, so the
Prop is stated for **every** family `c` with which `D` is a weak metric (GM_A D-3; GM_A S1.13).

Reading of "= δ^{ξQ + o_δ(1)} as δ → 0, uniformly over r > 0" (blueprint/M1.md §1, proposed
DEVIATIONS entry BP-M1-1): for every `ζ > 0` there is `δ₀ > 0` such that for all `δ ∈ (0, δ₀)` and
all `r > 0`, `δ^{ξQ+ζ} ≤ 𝔠_{δr}/𝔠_r ≤ δ^{ξQ−ζ}`. This is the reading of DFGPS's own proof
(l. 1659–1723: "𝔠_{δ𝕣} ≤ δ^{ξQ − o_δ(1)} 𝔠_𝕣 … uniformly in 𝕣") and of the consumer GM l. 529.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal

namespace LQGMetric.Blueprint

/-- **DFGPS Theorem 1.5** (DFGPS l. 429–436): for `γ ∈ (0,2)` and every weak γ-LQG metric `D`
with scaling constants `c`, `c(δr)/c(r) = δ^{ξQ + o_δ(1)}` as `δ → 0`, uniformly in `r > 0`:
for every `ζ > 0` there is `δ₀ > 0` with `δ^{ξQ+ζ} ≤ c(δr)/c(r) ≤ δ^{ξQ−ζ}` for all
`δ ∈ (0, δ₀)` and `r > 0` (`ξ = xiGamma γ`, `Q = Q γ`). -/
def DFGPSScaling : Prop :=
  ∀ γ : ℝ, 0 < γ → γ < 2 → ∀ (D : DistC → ContMetric) (c : ℝ → ℝ), IsWeakLQGMetric γ D c →
    ∀ ζ : ℝ, 0 < ζ → ∃ δ₀ : ℝ, 0 < δ₀ ∧ ∀ δ ∈ Ioo (0 : ℝ) δ₀, ∀ r : ℝ, 0 < r →
      δ ^ (xiGamma γ * Q γ + ζ) ≤ c (δ * r) / c r ∧
        c (δ * r) / c r ≤ δ ^ (xiGamma γ * Q γ - ζ)

end LQGMetric.Blueprint
