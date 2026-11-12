/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DG.S3P16C at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DG.S3P16B

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# DG Proposition 3.16, upper bound, in DG L3.7's coupling (task P2-DG316)

Source: Ding–Gwynne arXiv:1807.01072, `metric-comparison-final.tex`, proof of Prop 3.16
(DG:1445–1456). DG couple `ĥ` and `h^{𝕊(1)}` by Lemma 3.7 so that (eqn-use-circle-avg-approx)
`|h^{𝕊(1)}_δ(z) − ĥ_δ(w)| ≤ (ζ/2ξ) log δ⁻¹` for `|z − w| ≤ 4δ`; the upper bound only needs the
pairs at distance `≤ δ` (the polygon of `p16_upper_det` stays in the squares), so Lemma 3.7 with
`C = 1` suffices, and the failure probability is superpolynomially small. The factor `2` of
`p16_upper_det` is absorbed for small `δ` ("up to a deterministic constant factor which can be
ignored by slightly shrinking `ζ`").

* `p16_upper_of_lem37`: from `Blueprint.DGLem3_7`, in its coupling, for every `ζ ∈ (0,1)`,
  `ξ > 0`, `p > 0`, with probability `≥ 1 − K δ^p`, for all `z, w ∈ 𝕊`,
  `D^δ_{h^{𝕊(1)}}(z,w;𝕊) ≤ δ^{−ζ} D̂^δ_{ĥ}(z,w;𝕊)`.
-/

noncomputable section

open MeasureTheory Set

namespace LQGMetric.DG

open Blueprint

lemma p16_dgApprox_nonneg (ξ δ : ℝ) (hδ : 0 ≤ δ) (φ : ℂ → ℝ) (z w : ℂ) :
    0 ≤ dgApproxLFPP ξ δ φ z w :=
  Real.iInf_nonneg fun L => List.sum_nonneg fun x hx => by
    obtain ⟨k, -, rfl⟩ := List.mem_map.1 hx; positivity

/-- `2 e^{ξ η log δ⁻¹} ≤ δ^{−ζ}` once `ξ η ≤ ζ/2` and `log δ⁻¹ ≥ 2 log 2 / ζ` -/
lemma p16_const {δ ξ η ζ : ℝ} (hδ0 : 0 < δ) (hζ : 0 < ζ) (hξη : ξ * η ≤ ζ / 2)
    (hL : 2 * Real.log 2 / ζ ≤ Real.log δ⁻¹) (hL0 : 0 ≤ Real.log δ⁻¹) :
    2 * Real.exp (ξ * (η * Real.log δ⁻¹)) ≤ δ ^ (-ζ) := by
  have e : δ ^ (-ζ) = Real.exp (ζ * Real.log δ⁻¹) := by
    rw [Real.rpow_def_of_pos hδ0, Real.log_inv]; ring_nf
  rw [e, show (2 : ℝ) = Real.exp (Real.log 2) from (Real.exp_log two_pos).symm, ← Real.exp_add]
  refine Real.exp_le_exp.2 ?_
  rw [div_le_iff₀ hζ] at hL
  nlinarith

end LQGMetric.DG
