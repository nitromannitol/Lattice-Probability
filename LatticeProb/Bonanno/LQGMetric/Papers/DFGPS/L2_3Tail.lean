/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DFGPS.L2_3Tail at commit fdb5cad; only the module paths of local imports are changed.
   Declarations, examples and checks that the copied results do not use are omitted. -/
import LatticeProb.Bonanno.LQGMetric.Field.CircleAvgBridge
import LatticeProb.Bonanno.LQGMetric.Gaussian.SupTailField
import LatticeProb.Bonanno.LQGMetric.Gaussian.FerniqueFinite

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
Dubédat–Falconet–Gwynne–Pfeffer–Sun, *Weak LQG metrics and Liouville first passage percolation*
(arXiv:1905.00380, `lqg-metric-estimates-final.tex`, "T"), proof of Lemma 2.3 (`lem-gff-tail`),
T:751–781. Let `H` be a jointly continuous version of the circle-average process
`(r, z) ↦ h_r(z)` of a whole-plane GFF `h` (DS arXiv:0808.1560 Prop. 3.1; here
`CircleAvg.exists_continuous_version_circleAvg`).

* `blk_tail` (T:757–768, (eqn-gff-sup0)/(eqn-gff-sup-k)): for each `k`, the field
  `(r, z) ↦ H(2^k r, z) − H(2^k, 0)`, `r ∈ [1/2, 1]`, `|z| ≤ R`, satisfies
  `P(sup |·| ≥ M + u) ≤ 2 exp(−u²/(2σ²))` with `M`, `σ` depending only on `R`.
  The paper gets the `k`-uniformity from the scale invariance of the law of `h` modulo additive
  constants and the bound from Borell–TIS (AT Thm 2.1.1); we use Borell–TIS
  (`SupTail.tail_iSup_abs_le`, Adler–Taylor Thm 2.1.1) with the chaining bound for `E sup`
  (`SupTail.integral_iSup_family_le`) and check the `k`-uniformity directly on the
  (scale-invariant) covariance bound `incCov_self_le` (DEVIATIONS: DEV-DFGPS-2, DEV-DFGPS-B2a).
  We also subtract `H(2^k, 0)` instead of `H(r, 0)` (so that the radial part is a single
  Gaussian per block; see `pt_tail`).
* `pt_tail` (T:779, "t ↦ h_{e^t}(0) is a standard Brownian motion"): `H(2^k, 0) − H(1, 0)` is
  centered Gaussian with variance `k log 2`, hence `P(|·| ≥ u) ≤ 2 exp(−u²/(2(k+1)))`.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set Metric

namespace LQGMetric.DFGPS

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {h : Ω → DistC}

/-- `H` is a jointly continuous version of the circle-average process `(r, z) ↦ h_r(z)` of `h`
(continuous on `(0, ∞) × ℂ` for every `ω`, and `H r z = h_r(z)` a.s. for each `r > 0`, `z`). -/
structure IsCircleAvgVersion (h : Ω → DistC) (P : Measure Ω) (H : ℝ → ℂ → Ω → ℝ) : Prop where
  cont : ∀ ω, ContinuousOn (fun p : ℝ × ℂ => H p.1 p.2 ω) (Ioi 0 ×ˢ univ)
  ae_eq : ∀ r, 0 < r → ∀ z, (fun ω => H r z ω) =ᵐ[P] fun ω => circleAvg (h ω) r z

variable {H : ℝ → ℂ → Ω → ℝ}

/-! ## The block field -/

variable (R : NNReal) (k : ℕ)

/-! ## The radial part at the centre -/

end LQGMetric.DFGPS
