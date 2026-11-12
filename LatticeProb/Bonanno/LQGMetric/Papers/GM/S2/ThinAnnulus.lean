/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.GM.S2.ThinAnnulus at commit fdb5cad; only the module paths of local imports are changed.
   Declarations, examples and checks that the copied results do not use are omitted. -/
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S2.TightA
import LatticeProb.Bonanno.LQGMetric.Blueprint.DFGPSEstimates
import LatticeProb.Bonanno.LQGMetric.Blueprint.M2Defs
import LatticeProb.Bonanno.LQGMetric.Metric.InternalOps
import LatticeProb.Bonanno.LQGMetric.Metric.InternalC

/-!
# GM Lemma 2.11: internal distances across a thin annulus are large (task P2-M2C, WP-M2c)

GM (arXiv:1905.00383v3, `uniqueness-final.tex` l. 1062–1072), Lemma 2.11 (`lem-attained-long`):
for `S > s > 0` and `p ∈ (0,1)` there is `α_* ∈ (1/2, 1)` such that for `α ∈ [α_*, 1)`, every
`z` and `𝕣 > 0`, with probability `≥ p`, every `u, v ∈ A_{α𝕣,𝕣}(z)` with
`D_h(u,v) ≥ s 𝔠_𝕣 e^{ξ h_𝕣(z)}` have `D_h(u,v; A_{α𝕣,𝕣}(z)) ≥ S 𝔠_𝕣 e^{ξ h_𝕣(z)}`.

GM's proof (l. 1067–1071), followed here:
* "By Weyl scaling … the event does not depend on the additive constant; by translation invariance
  … the probability does not depend on `z`": we pass to the normalized translated field
  `h' = h(· + z) − h_1(z)` (Axiom IV′, `IsWeakLQGMetric.translation`; Axiom III,
  `IsWeakLQGMetric.ae_dist_addConst`; `CircleAvg.ae_circleAvg_addConst`), and transport internal
  metrics by `internal_translate_eq` (LM S-int (d), `internalEDist_image_of_edist_eq`).
* "By Axiom V we find `b = b(s)` such that w.p. `≥ 1 − (1−p)/2` any `u, v ∈ B_𝕣` with
  `D_h(u,v) ≥ s 𝔠_𝕣 e^{ξh_𝕣}` have `|u − v| ≥ b𝕣`": the proved GM.S2.4b, `Tight.gm_S2_4b`
  (task P2-TIGHT), used instead of the Blueprint Prop `GMS2_4b`.
* "Combining with Lemma 2.10 (`ε = 1 − α`, `L = ∂𝔻`)": `Blueprint.DFGPSProp4_1` (DFGPS Prop 4.1,
  = GM Lemma 2.10) with the exponent made negative through `Blueprint.GMXiQBound` (GM l. 1056).
  Since DFGPS's `ε₀` may depend on the probability space, it is applied once to the canonical
  normalized GFF `(DistC, μ, id)` and transferred to any field by `Measure.le_map_apply`
  (no measurability of the event is needed).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal

namespace LQGMetric.GM
open Blueprint MetricGeometry

/-- `ξ = γ/d_γ > 0` for `γ > 0` (both branches of `chiDZZ` are positive). -/
lemma xiGamma_pos {γ : ℝ} (hγ : 0 < γ) : 0 < xiGamma γ := by
  have hχ : 0 < chiDZZ γ := by
    unfold chiDZZ
    split_ifs with h
    · exact h.choose_spec.1
    · norm_num
  exact div_pos hγ (div_pos two_pos hχ)

end LQGMetric.GM
