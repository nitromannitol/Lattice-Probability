/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DFGPS.L2_8GffPos at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DFGPS.L2_8GffSq
import Mathlib.MeasureTheory.Measure.Prokhorov

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# Limits of the zero-boundary LFPP metrics on `[0,1]²` are positive off the diagonal
(DFGPS Lemma 2.8, step (a1), T:879–881)

DFGPS (arXiv:1905.00380, `lqg-metric-estimates-final.tex` T:879–881): "It is shown in
[DDDF, Theorem 1] (see also [DDDF, Section 6.1]) that … the internal metrics
`λ_ε⁻¹ D^ε_{h̊}(·,·;[0,1]²)` are tight … and any subsequential limit of these laws is supported
on length metrics which induce the Euclidean topology on `[0,1]²`." DDDF Theorem 1 (2)
(`Blueprint.DDDFThm1_2`) states only the tightness; DDDF §6.1 (DD:1498–1510) derives Theorem 1 (2)
from Theorem 1 (1) through the coupling of Proposition 29 (`Blueprint.DDDFProp29`):
`‖φ_t − p_{t/2} * h̊‖_U` has Gaussian tails uniformly in `t`, so the two normalized metrics are
bi-Lipschitz with a tight family of constants `e^{|ξ| ‖φ_t − p_{t/2}*h̊‖_U}`, and the limits of
`λ_{√t}⁻¹ e^{ξφ_{√t}} ds` are bi-Hölder (Theorem 1 (1), `Blueprint.DDDFThm1_1`), hence positive
off the diagonal. We formalize this transfer at the level of laws
(`ae_posOffDiag_of_dominated`, `L2_8LimPos.lean`): the coupling of Prop. 29 lives on its own
probability space for each `t`, and the laws are transported by `map_pathC_heat_eq` and
`map_pathC_phiVer_eq` (`L2_8GffLaw*.lean`).

Main result: `zb_lim_posOffDiag`.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set Metric
open scoped NNReal ENNReal

namespace LQGMetric.DFGPS

open Blueprint WhiteNoise DDDF LFPP

lemma isPosOffDiag_of_isBiHolderSq {d : C(closedUnitSquare × closedUnitSquare, ℝ)}
    (hd : IsBiHolderSq d) : IsPosOffDiag d := by
  obtain ⟨c, C, α, β, hc, -, -, -, h⟩ := hd
  intro x y hxy
  have hne : (x : ℂ) - y ≠ 0 := sub_ne_zero.2 fun h => hxy (Subtype.ext h)
  exact lt_of_lt_of_le (mul_pos hc (Real.rpow_pos_of_pos (norm_pos_iff.2 hne) _)) (h x y).1

lemma exists_gauss_tail_le {C c ζ : ℝ} (hc : 0 < c) (hζ : 0 < ζ) :
    ∃ x : ℝ, 0 < x ∧ C * Real.exp (-c * x ^ 2) ≤ ζ := by
  have h1 : Tendsto (fun x : ℝ => c * x ^ 2) atTop atTop :=
    (tendsto_pow_atTop two_ne_zero).const_mul_atTop hc
  have h2 : Tendsto (fun x : ℝ => C * Real.exp (-c * x ^ 2)) atTop (𝓝 (C * 0)) := by
    refine (Real.tendsto_exp_neg_atTop_nhds_zero.comp h1).const_mul C |>.congr fun x => ?_
    simp [Function.comp, neg_mul]
  rw [mul_zero] at h2
  obtain ⟨x, hx1, hx2⟩ := ((h2.eventually (gt_mem_nhds hζ)).and (eventually_gt_atTop 0)).exists
  exact ⟨x, hx2, hx1.le⟩

end LQGMetric.DFGPS
