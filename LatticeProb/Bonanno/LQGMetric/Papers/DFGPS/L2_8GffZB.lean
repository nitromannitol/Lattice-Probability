/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DFGPS.L2_8GffZB at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DFGPS.L2_8GffPos

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# DFGPS Lemma 2.8, the zero-boundary step on `(-1,2)²` (T:877–881)

DFGPS (arXiv:1905.00380, `lqg-metric-estimates-final.tex` T:877–881): `h̊` is a zero-boundary GFF
on `V = (-1,2)²`; with `h̊*_ε = h̊ * p_{ε²/2}`, "there are constants `λ_ε` such that the internal
metrics `λ_ε⁻¹ D^ε_{h̊}(·,·;[0,1]²)` are tight … and any subsequential limit … induce[s] the
Euclidean topology on `[0,1]²`" ([DDDF, Theorem 1] and [DDDF, §6.1]).

`zb_step`: for the extended zero-boundary GFF `Xh` on `sqOpens (-1) 3 = (-1,2)²` there is a
continuous version `Y δ` of `p_{δ/2} * h̊` (`exists_heat_contVersion_sq`) for every `δ ∈ (0,1)`
such that the laws of `λ_{√δ}⁻¹ e^{ξ Y δ} ds` on `[0,1]²` are tight (`Blueprint.DDDFThm1_2`) and
every limit along `δ_n → 0` is a.s. positive off the diagonal (`zb_lim_posOffDiag`, with
`U = (-1/2, 3/2)²` in DDDF Prop 29). (With `δ = ε²`, `λ_{√δ} = λ_ε` and `Y δ = h̊*_ε`.)
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set Metric
open scoped NNReal ENNReal

namespace LQGMetric.DFGPS

open Blueprint WhiteNoise DDDF LFPP HeatSq

lemma closure_sqOpen_subset (a L : ℝ) :
    closure (sqOpen a L) ⊆ {z : ℂ | a ≤ z.re ∧ z.re ≤ a + L ∧ a ≤ z.im ∧ z.im ≤ a + L} := by
  refine closure_minimal (fun z hz => ⟨hz.1.le, hz.2.1.le, hz.2.2.1.le, hz.2.2.2.le⟩) ?_
  have e : {z : ℂ | a ≤ z.re ∧ z.re ≤ a + L ∧ a ≤ z.im ∧ z.im ≤ a + L} =
      (Complex.re ⁻¹' Icc a (a + L)) ∩ (Complex.im ⁻¹' Icc a (a + L)) := by
    ext z; simp only [mem_ofPred_eq, mem_inter_iff, mem_preimage, mem_Icc]; tauto
  rw [e]
  exact (isClosed_Icc.preimage Complex.continuous_re).inter
    (isClosed_Icc.preimage Complex.continuous_im)

end LQGMetric.DFGPS
