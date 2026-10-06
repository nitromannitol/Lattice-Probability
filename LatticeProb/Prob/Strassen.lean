import LatticeProb.Prob.Strassen.Defs
import LatticeProb.Prob.Strassen.OrderBasics
import LatticeProb.Prob.Strassen.HallPoset
import LatticeProb.Prob.Strassen.Rounding
import LatticeProb.Prob.Strassen.MarginalWeights
import LatticeProb.Prob.Strassen.DiscreteCoupling
import LatticeProb.Prob.Strassen.LevelCoupling
import LatticeProb.Prob.Strassen.LimitPassage
import LatticeProb.Prob.Strassen.Converse

/-!
# Strassen's coupling theorem

Strassen's coupling theorem for `{0,1}`-valued fields on a countable set. `IsIncreasingSet A`
says that `A` is closed under increasing a `{0,1}`-valued field coordinatewise.
`exists_monotone_coupling` (Strassen's theorem, in the domination form used by the percolation
literature) states: if `μ` and `ν` are probability measures on `S → Bool` for a countable `S` and
every measurable increasing event is at least as likely under `μ` as under `ν`, then there is a
probability measure `π` on the product with first marginal `μ`, second marginal `ν`, and
`p.2 ≤ p.1` for `π`-almost every `p`. `domination_of_monotone_coupling` is the converse.

This file only imports its children, one per proof stage, under `LatticeProb/Prob/Strassen/`.

## Route

No Kolmogorov extension, no LP duality: Mathlib has Farkas only for closed cones and no
closedness of finitely generated cones, so the finite stage goes through Hall instead.

* Shared definitions (`Defs`): `IsIncreasingSet` and `couplingSupport`.
* 0. Order basics (`OrderBasics`).
* A. Integer Strassen on a finite poset `P` via Hall (`HallPoset`,
  `Fintype.all_card_le_filter_rel_iff_exists_injective`) on "copies" `Σ y, Fin (n y)` → `Σ x, Fin
  (m x)`; up-set domination is Hall's condition.
* B. Rounding with denominator `D` (`Rounding`): the small law is rounded down (excess to `⊥`),
  the large law rounded up (excess to `⊤`); this preserves up-set domination exactly and errs by
  at most `|P|/D` per set.
* C. Weights of the finite-dimensional marginals on `P_F = (F → Bool)`, `F : Finset S`
  (`MarginalWeights`).
* D. The discrete coupling on `(S → Bool)²` (`DiscreteCoupling`, extend by `false` off `F`),
  supported on `{p.2 ≤ p.1}`.
* E. Level-`N` coupling with `F_N ↑ S`, `D_N = (N+1)|P_{F_N}|` (`LevelCoupling`): cylinder
  marginals within `1/(N+1)`.
* F. Limit (`LimitPassage`): `ProbabilityMeasure ((S → Bool)²)` is compact (Mathlib
  `instCompactSpaceProbabilityMeasure`, Prokhorov); take a limit along an ultrafilter `≤ atTop`;
  the closed support set passes by portmanteau
  (`ProbabilityMeasure.limsup_measure_closed_le_of_tendsto`), clopen cylinder masses pass by
  `ProbabilityMeasure.tendsto_measure_of_null_frontier_of_tendsto`, and cylinders form a
  generating π-system (`generateFrom_measurableCylinders`, `isPiSystem_measurableCylinders`).
* Converse (`Converse`): the easy direction, `domination_of_monotone_coupling`.

-/
