import LatticeProb.Prob.KingmanLinear.Defs
import LatticeProb.Prob.KingmanLinear.Restated
import LatticeProb.Prob.KingmanLinear.LinearSets
import LatticeProb.Prob.KingmanLinear.InducedFamily
import LatticeProb.Prob.KingmanLinear.Interpolation
import LatticeProb.Prob.KingmanLinear.FromInducedToAllTimes
import LatticeProb.Prob.KingmanLinear.LimitInvariant
import LatticeProb.Prob.KingmanLinear.MainTheorem

/-!
# Kingman's theorem under a linear bound, without integrability of `g 1`

Kingman's theorem for a nonnegative subadditive family with an almost-sure linear bound and a
Lipschitz-in-time control, without integrability of `g 1`.

For `T` preserving a probability measure `μ`, `g : ℕ → Ω → ℝ` nonnegative, measurable,
subadditive along `T` (`g (m+n) x ≤ g m x + g n (T^[m] x)`), with an a.e. linear bound
`g n x ≤ C n + K` and a Lipschitz-in-time control on dyadic windows, the ratios `g n x / n`
converge a.e. to a constant `L` (`ae_tendsto_div_of_linear`).

This file only imports its children, one per proof stage, under `LatticeProb/Prob/KingmanLinear/`.

## Route

* Shared definitions (`Defs`): `A_k = {x | ∀ n, g n x ≤ C n + k}` (`linSet`), the induced family's
  return-time Birkhoff sum `retSum`, and the induced family `indG` itself.
* Restated from `induced-map`, `kac`, `invariance` (`Restated`): measurability and invariance
  facts about the first-return map, kept under their own names for a self-contained argument.
* 1. The sets `A_k` (`LinearSets`): `A_k` is measurable and the `A_k` exhaust `Ω` a.e.
* 2. The induced family (`InducedFamily`): on `A = A_k` with first-return map `S` and return time
  `r`, `G j x = g (R j x) x` is subadditive along `S`, measurable, and `G 1` is integrable on
  `A_k` (Kac's lemma). The library's Kingman theorem `LatticeProb.ae_tendsto_div` for `S` on
  `μ.restrict A_k` gives `G j / j → Λ` a.e. on `A_k`; the library's Birkhoff theorem
  `LatticeProb.ae_tendsto_bAvg` for `r` gives `R j / j → ρ`.
* 3. Deterministic interpolation (`Interpolation`, pure real analysis): `R` is strictly increasing
  with `R 0 = 0`, `ρ ≥ 1`, `g (R j) / R j → Λ / ρ`, `(R (j+1) - R j) / R j → 0`, and the Lipschitz
  control gives `g n / n → Λ / ρ` along all `n`.
* 4. From the induced family to all times (`FromInducedToAllTimes`): assembles stages 1-3 into
  a.e. convergence of `g n x / n` on all of `Ω`.
* 5. The limit is invariant, hence constant (`LimitInvariant`): the limit `ℓ` (written as the
  `limsup`, measurable by `Measurable.limsup`) satisfies `ℓ ≤ ℓ ∘ T` a.e. (from
  `g (n+1) x ≤ g 1 x + g n (T x)`), so by `ae_eq_const_of_ae_le_comp_real` it is a.e. constant.
* Main theorem (`MainTheorem`): assembles the five stages into `ae_tendsto_div_of_linear`.

-/
