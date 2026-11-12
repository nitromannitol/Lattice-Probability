/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.LM.T1_7D1 at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.LM.C1_8

/-!
# LM Theorem 1.7: the repaired Step 2–3 (decision D107, task P2-DEC107)

Gwynne–Miller, *Local metrics of the Gaussian free field* (arXiv:1905.00379,
`local-metrics-final.tex`), Theorem 1.7 (l. 306–311), proof l. 1000–1089. LM's Step 3 (l. 1075–1084)
has the gap G1 (blueprint/LocalMetrics.md, notes R3): the near-geodesics `P = P_ε` of `D(·,·;V)`
vary with `ε` and (5.18) compares with `D` instead of `D(·,·;V)`, so no uniform modulus is
available near `∂V`. Decision D107 (decisions/DEC-107.md): keep `U = ℂ`, `V = B_n := B_n(0)` and
LM's Efron–Stein set-up (Step 1, l. 1011–1026) and Step 2 (l. 1030–1055) verbatim, and replace
Step 3 by the **product bound**: besides LM's near-geodesic `P'` of `D(·,·;B_n)` (slack `ε³`), take
an auxiliary near-geodesic `P` of `D(·,·;B_{n−1})` (slack `ε³`); for each square `S`,
`A(S) := (D^S(z,w;B_n) − D(z,w;B_n))_+` satisfies both LM's bound `A(S) ≤ b₂(S) := C² len(P'∩S;D)
+ ε³` (l. 1052–1055) and `A(S) ≤ b₁(S) := η_n + ε³ + (C² − 1) len(P∩S;D)`, where
`η_n := D(z,w;B_{n−1}) − D(z,w;B_n)`; `sup_S b₁(S) → C² η_n` as `ε → 0` because `P ⊂ B_{n−1}` stays
away from `∂B_n` (LM's modulus argument, l. 1079–1081, now valid), and `∑_S b₂(S) ≤ C² D(z,w;B_n)
+ C²ε³ + ε³ #𝒮 → C² D(z,w;B_n)`. Hence `∑_S A(S)² ≤ sup_S b₁ · ∑_S b₂` (`t17_sum_sq_le` below)
gives `Var[D(z,w;B_n) | h, θ] ≤ C⁴ E[η_n D(z,w;B_n) | h, θ]`, which tends to `0` as `n → ∞`
(bounded convergence, LM Lemma 5.1), instead of LM's conclusion for a fixed `V`.

This file holds the deterministic inequalities of the repair and the exact open node
`LMT17VarNode` (the per-`n` variance bound); `lmThm1_7_of_varNode` (packet P-LIM of DEC-107) will
derive `LMThm1_7` from it.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal

namespace LQGMetric.LM

open Blueprint

/-! ## The product bound (DEC-107 §3, step (iv)) -/

/-- the positive part `(x)_+ = max x 0` of a difference is bounded by any upper bound of the
difference that is nonnegative (used for `A(S) ≤ b₁(S)` and `A(S) ≤ b₂(S)`). -/
theorem t17_posPart_le {x y b : ℝ} (hxy : x ≤ y + b) (hb : 0 ≤ b) : max (x - y) 0 ≤ b :=
  max_le (by linarith) hb

/-! ## The exact open node -/

end LQGMetric.LM
