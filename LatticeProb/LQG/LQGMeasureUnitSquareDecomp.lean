import LatticeProb.LQG.VagueLimitExpShift
import LatticeProb.LQG.VagueLimitAreaApprox
import LatticeProb.LQG.CircleUnifUniform
import LatticeProb.LQG.CircleAvgDecompUnitSquare
import LatticeProb.LQG.LQGLimitRestrictIdentify
import LatticeProb.Bonanno.QuantumZipper.Proofs.LQG.AtomlessUncond

/-!
# The LQG measure of the whole-plane GFF on the unit square

For the whole-plane GFF `h₀` of a white noise `W`, normalized by its unit-circle average, and a
box `B` at distance `≥ 1/10` from the boundary of the unit square `𝕍`: almost surely, on the
interior of `B`, the circle-average approximations of the `γ`-LQG measure of `h₀ − h₀_1(0)`
converge vaguely to `e^{γ Y} μ_{h^𝕍}`, where `μ_{h^𝕍}` is the `γ`-LQG measure of the
white-noise zero-boundary GFF of `𝕍` and `Y` is the continuous modification of
`h₀ − h₀_1(0) − h^𝕍` on `B`. Consequently every dyadic LQG limit of `h₀ − h₀_1(0)` restricts to
`e^{γ Y} μ_{h^𝕍}` on the interior of `B`.
-/

open MeasureTheory Filter Topology Set

namespace LQGMetric

open QuantumZipper GMCIdent3 GMCIdent WhiteNoise

/-- **Domain Markov decomposition of the LQG measure on the unit square, vague form.** -/
theorem _root_.LatticeProb.LQG.ae_isVagueLimitOn_interior_withDensity_exp
    {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω'] {P : Measure Ω}
    [IsProbabilityMeasure P] {P' : Measure Ω'} [IsProbabilityMeasure P']
    {X : Ω' → Measure ℂ → ℝ} (hX : IsZeroBoundaryGFFOn openSquare X P')
    {W : WNSpace → Ω → ℝ} (hW : IsWhiteNoise P W) {h₀ : Ω → DistC} (hm : Measurable h₀)
    {B : Set ℂ} (hB : ∀ z ∈ B, Metric.ball z (1 / 10) ⊆ openSquare)
    {Y : ℂ → Ω → ℝ} (hYc : ∀ ω, Continuous fun z => Y z ω) (hYm : ∀ z, Measurable (Y z))
    (hF : ∀ (z : ℂ) (r : ℝ), 0 < r → Metric.closedBall z r ⊆ B →
      (fun ω => ∫ x, Y x ω ∂(circleUnif z r)) =ᵐ[P] fun ω =>
        LQGMetric.circleAvg (h₀ ω) r z - LQGMetric.circleAvg (h₀ ω) 1 0 -
          Real.sqrt Real.pi * W (measKerL2 openSquare (Ioi 0) (circleUnif z r)) ω)
    {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) :
    ∀ᵐ ω ∂P, IsVagueLimitOn (interior B)
      (fun k => volume.withDensity fun z => ENNReal.ofReal (radius k ^ (γ ^ 2 / 2) *
        Real.exp (γ * (LQGMetric.circleAvg (h₀ ω) (radius k) z -
          LQGMetric.circleAvg (h₀ ω) 1 0))))
      (((qAreaMeasureOn γ (GMCIdent3.wnField W ω) openSquare).restrict (interior B)).withDensity
        fun z => ENNReal.ofReal (Real.exp (γ * Y z ω))) := by
  have hBsq : interior B ⊆ openSquare := fun z hz =>
    hB z (interior_subset hz) (Metric.mem_ball_self (by norm_num))
  filter_upwards [LatticeProb.LQG.ae_isVagueLimitOn_withDensity_avgReg_wnField hX hW hγ hγ2,
    LatticeProb.LQG.ae_circleAvg_sub_eq_avgReg_add_integral hX hW hm hB hYc hYm hF]
    with ω hx hab
  have hsec : ∀ F : Ω → ℂ → ℝ, (Measurable fun q : Ω × ℂ => F q.1 q.2) → Measurable (F ω) :=
    fun F hF => hF.comp ((measurable_const : Measurable fun _ : ℂ => ω).prodMk measurable_id)
  exact LatticeProb.LQG.isVagueLimitOn_withDensity_exp_of_shift isOpen_interior
    (c := fun k => radius k ^ (γ ^ 2 / 2)) (fun k => Real.rpow_nonneg (radius_pos k).le _)
    (a := fun k z => avgReg (GMCIdent3.wnField W ω) k z)
    (b := fun k z => LQGMetric.circleAvg (h₀ ω) (radius k) z - LQGMetric.circleAvg (h₀ ω) 1 0)
    (fun k => hsec (fun ω z => avgReg (GMCIdent3.wnField W ω) k z)
      (LatticeProb.LQG.measurable_avgReg_wnField hW k))
    (fun k => hsec (fun ω z => LQGMetric.circleAvg (h₀ ω) (radius k) z -
        LQGMetric.circleAvg (h₀ ω) 1 0)
      (LatticeProb.LQG.measurable_circleAvg_sub_circleAvg hm _))
    (AtomlessUncond.isVagueLimitOn_restrict isOpen_interior hBsq hx)
    (g := fun z => Y z ω) (hYc ω).measurable (hYc ω).continuousOn
    (ψ := fun k z => ∫ x, Y x ω ∂(circleUnif z (radius k)))
    (fun k => hsec (fun ω z => ∫ x, Y x ω ∂(circleUnif z (radius k)))
      (LatticeProb.LQG.measurable_integral_circleUnif hYc hYm _))
    (fun K hK _ => LatticeProb.LQG.tendstoUniformlyOn_integral_circleUnif (hYc ω) hK)
    (fun K hK hKU => hab K hK hKU)

/-- **Domain Markov decomposition of the LQG measure on the unit square.** Almost surely, every
dyadic LQG limit `m` of `h₀ − h₀_1(0)` (with circle averages `h_ε` agreeing at the dyadic scales,
Lebesgue-almost everywhere, with those of `h₀ − h₀_1(0)`) restricts on the interior of `B` to
`e^{γ Y} μ_{h^𝕍}`. -/
theorem _root_.LatticeProb.LQG.ae_restrict_eq_withDensity_of_isLQGLimit
    {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω'] {P : Measure Ω}
    [IsProbabilityMeasure P] {P' : Measure Ω'} [IsProbabilityMeasure P']
    {X : Ω' → Measure ℂ → ℝ} (hX : IsZeroBoundaryGFFOn openSquare X P')
    {W : WNSpace → Ω → ℝ} (hW : IsWhiteNoise P W) {h₀ : Ω → DistC} (hm : Measurable h₀)
    {B : Set ℂ} (hB : ∀ z ∈ B, Metric.ball z (1 / 10) ⊆ openSquare)
    {Y : ℂ → Ω → ℝ} (hYc : ∀ ω, Continuous fun z => Y z ω) (hYm : ∀ z, Measurable (Y z))
    (hF : ∀ (z : ℂ) (r : ℝ), 0 < r → Metric.closedBall z r ⊆ B →
      (fun ω => ∫ x, Y x ω ∂(circleUnif z r)) =ᵐ[P] fun ω =>
        LQGMetric.circleAvg (h₀ ω) r z - LQGMetric.circleAvg (h₀ ω) 1 0 -
          Real.sqrt Real.pi * W (measKerL2 openSquare (Ioi 0) (circleUnif z r)) ω)
    {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) {hε : Ω → ℝ → ℂ → ℝ} {m : Ω → Measure ℂ}
    (hlim : ∀ᵐ ω ∂P, LatticeProb.LQG.IsLQGLimit γ (hε ω) (m ω))
    (hcirc : ∀ᵐ ω ∂P, ∀ k, hε ω (LatticeProb.LQG.dyadicScale k) =ᵐ[volume] fun z =>
      LQGMetric.circleAvg (h₀ ω) (radius k) z - LQGMetric.circleAvg (h₀ ω) 1 0) :
    ∀ᵐ ω ∂P, (m ω).restrict (interior B) =
      ((qAreaMeasureOn γ (GMCIdent3.wnField W ω) openSquare).restrict (interior B)).withDensity
        fun z => ENNReal.ofReal (Real.exp (γ * Y z ω)) := by
  filter_upwards [hlim, hcirc, LatticeProb.LQG.ae_isVagueLimitOn_interior_withDensity_exp hX hW
    hm hB hYc hYm hF hγ hγ2] with ω h1 h2 h3
  exact h1.restrict_eq_of_isVagueLimitOn isOpen_interior h2 h3

end LQGMetric
