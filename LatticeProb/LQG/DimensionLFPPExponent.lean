import LatticeProb.Bonanno.LQGMetric.Assembly.MainFinal
import LatticeProb.Bonanno.LQGMetric.Papers.DG.Adapter
import LatticeProb.Bonanno.LQGMetric.Papers.DG.XiQBound
import LatticeProb.Bonanno.LQGMetric.Papers.DG.S3Wire3
import LatticeProb.Bonanno.LQGMetric.Papers.DG.S3L37Q1
import LatticeProb.Bonanno.LQGMetric.Papers.DG.S3P16D3
import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.S5L53W1

/-!
# The LFPP distance exponent at `ξ = γ / d_γ`

Ding-Gwynne (*The fractal dimension of Liouville quantum gravity: universality, monotonicity, and
bounds*, arXiv:1807.01072, Theorem 1.5) relate Liouville first passage percolation at parameter `ξ` to
`γ`-LQG: for `γ ∈ (0, 2)`, `d_γ` the dimension of `γ`-LQG and `ξ = γ / d_γ`, the LFPP distance between
the boundary arcs of the unit square, built from the circle-average process `h_ε` of a whole-plane GFF,
is `ε^{1 - ξ Q + o(1)}` with `Q = 2/γ + γ/2`.

This file records the theorem with no hypothesis (`dgThm1_5_holds`), assembled from the Ding-Gwynne and
Ding-Zeitouni-Zhang estimates of the library, and its form as an LFPP exponent: for every circle-average
process of the whole-plane GFF, `log L_ε / log ε → 1 - ξ_γ Q_γ` in probability
(`isLFPPExponent_xiGamma`).
-/

open MeasureTheory

noncomputable section

namespace LatticeProb.LQG

/-- **Ding-Gwynne, Theorem 1.5** (arXiv:1807.01072): for `γ ∈ (0, 2)` and `ξ = γ / d_γ`, the LFPP
distances of the circle-average process of a whole-plane GFF satisfy the upper and lower exponent bounds
with exponent `1 - 2/d_γ - γ²/(2 d_γ)`. -/
theorem dgThm1_5_holds : LQGMetric.DG.DGThm1_5 :=
  have hD : LQGMetric.DG.DZZInputsDGForm := LQGMetric.DG.dzzInputsDGForm_of
    (LQGMetric.DZZ.dzzInputsDG_of_exp
      (LQGMetric.DZZ.dzzLem53ExpAll_of_hbadB LQGMetric.l53HbadBAll_proved))
  LQGMetric.DG.wire_dgThm1_5_of LQGMetric.DG.L37Q.dgLem3_7
    (LQGMetric.DG.dgProp3_16_of_lem37 LQGMetric.DG.L37Q.dgLem3_7) hD

/-- The LFPP exponent at `ξ_γ = γ / d_γ`: for `γ ∈ (0, 2)` and every circle-average process `h_ε` of a
whole-plane GFF, `log L_ε / log ε → 1 - ξ_γ Q_γ` in probability, where `L_ε` is the LFPP left-right
crossing distance of the unit square at parameter `ξ_γ`. -/
theorem isLFPPExponent_xiGamma {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2)
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} {hc : ℝ → ℂ → Ω → ℝ}
    (hG : LQGDimension.IsGFFCircleAverage hc P) :
    LQGDimension.IsLFPPExponent hc P (LQGMetric.xiGamma γ)
      (1 - LQGMetric.xiGamma γ * LQGMetric.Q γ) := by
  rw [LQGMetric.DG.xiGamma_mul_Q hγ, sub_sub_cancel]
  exact LQGMetric.DG.isLFPPExponent_of_dgThm1_5 dgThm1_5_holds hγ hγ2 hG

end LatticeProb.LQG
