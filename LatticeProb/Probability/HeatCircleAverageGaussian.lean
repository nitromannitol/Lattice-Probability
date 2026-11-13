import LatticeProb.Bonanno.LQGMetric.Field.HeatMollifyPoint
import LatticeProb.Bonanno.LQGMetric.Field.CircleAvgRate
import LatticeProb.Bonanno.LQGMetric.Field.CircleAvgGaussLim
import LatticeProb.Bonanno.LQGMetric.Field.CircleAvgIndep
import LatticeProb.Bonanno.LQGMetric.Field.MeasurableAvg

/-!
# Heat-kernel mollification minus circle average of a whole-plane GFF is centered Gaussian

Let `h` be a whole-plane Gaussian free field, defined modulo a global additive constant
(`LQGMetric.IsWholePlaneGFF`: only the pairings with mean-zero test functions are prescribed).
The heat-kernel mollification `h*_ε(z) = (h * p_{ε²/2})(z)` and the circle average `h_ε(z)`
both integrate `h` against a probability density, so their difference does not see the
additive constant. We show that for fixed `ε > 0` and `z`, the law of `h*_ε(z) - h_ε(z)` is a
centered Gaussian `N(0, V)`, and that `(ε, z) ↦ h*_ε(z) - h_ε(z)` is a centered Gaussian
process (`isGaussianProcess_heatMollify_sub_circleAvg`).

Proof. With `χ_n` the smooth cutoffs and `ψ_{n,z,ε}` the mollified uniform measure on
`∂B_ε(z)`, the test function `p_{ε²/2}(z,·) χ_n - (∫ p_{ε²/2}(z,·) χ_n) ψ_{n,z,ε}` has mean
zero, so its pairing with `h` is a centered Gaussian. As `n → ∞` the pairings converge almost
surely to `h*_ε(z) - h_ε(z)`: the truncated heat pairings converge to `h*_ε(z)`, the mollified
circle averages converge to `h_ε(z)`, and the total mass of the truncated heat kernel tends
to one (dominated convergence). Almost sure limits of centered Gaussians are centered Gaussian.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set

namespace LQGMetric
namespace HeatCircle

open CircleAvg

/-- The total mass of the truncated heat kernel `p_s(z,·) χ_n` tends to one. -/
lemma tendsto_integral_heatTrunc {s : ℝ} (hs : 0 < s) (z : ℂ) :
    Tendsto (fun n : ℕ => ∫ w, heatTrunc s z n w) atTop (𝓝 1) := by
  rw [← integral_heatKernel s hs z]
  have hint : Integrable (heatKernel s z) := by
    by_contra hni
    have h0 := integral_undef hni
    rw [integral_heatKernel s hs z] at h0
    exact one_ne_zero h0
  refine tendsto_integral_of_dominated_convergence (heatKernel s z)
    (fun n => (heatTrunc s z n).continuous.aestronglyMeasurable) hint (fun n => ?_) ?_
  · refine Eventually.of_forall fun w => ?_
    have hk := heatKernel_nonneg s hs.le z w
    rw [heatTrunc_apply, norm_mul, Real.norm_of_nonneg hk,
      Real.norm_of_nonneg (cutoff n).nonneg]
    exact mul_le_of_le_one_right hk (cutoff n).le_one
  · refine Eventually.of_forall fun w => ?_
    refine tendsto_atTop_of_eventually_const (i₀ := ⌈‖w‖⌉₊) fun n hn => ?_
    have h1 : (cutoff n : ℂ → ℝ) w = 1 := (cutoff n).one_of_mem_closedBall (by
      rw [Metric.mem_closedBall, dist_zero_right]
      show ‖w‖ ≤ (n : ℝ) + 1
      have := (Nat.le_ceil ‖w‖).trans (Nat.cast_le.mpr hn)
      linarith)
    rw [heatTrunc_apply, h1, mul_one]

/-- The mean-zero test function `p_s(z,·) χ_n − (∫ p_s(z,·) χ_n) ψ_{n,z,r}`. -/
def heatCircDiff (s : ℝ) (z : ℂ) (r : ℝ) (n : ℕ) : TestC0 :=
  ⟨heatTrunc s z n - (∫ w, heatTrunc s z n w) • circBump n z r, by
    show ∫ x, (heatTrunc s z n x - (∫ w, heatTrunc s z n w) * circBump n z r x) = 0
    rw [integral_sub (integrable_testC _) ((integrable_testC _).const_mul _),
      integral_const_mul, integral_circBump, mul_one, sub_self]⟩

lemma pair_heatCircDiff (g : DistC) (s : ℝ) (z : ℂ) (r : ℝ) (n : ℕ) :
    g (heatCircDiff s z r n).1 =
      g (heatTrunc s z n) - (∫ w, heatTrunc s z n w) * mollAvg g n z r := by
  show g (heatTrunc s z n - (∫ w, heatTrunc s z n w) • circBump n z r) = _
  rw [map_sub, map_smul, smul_eq_mul, mollAvg_eq]

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {h : Ω → DistC}

/-- Almost surely, the pairings of `h` with the mean-zero test functions `heatCircDiff`
converge to `h*_ε(z) − h_ε(z)`. -/
theorem ae_tendsto_pair_heatCircDiff (hh : IsWholePlaneGFF h P) {ε : ℝ} (hε : 0 < ε)
    (z : ℂ) :
    ∀ᵐ ω ∂P, Tendsto (fun n => h ω (heatCircDiff (ε ^ 2 / 2) z ε n).1) atTop
      (𝓝 (heatMollify ε (h ω) z - circleAvg (h ω) ε z)) := by
  have hs : 0 < ε ^ 2 / 2 := by positivity
  filter_upwards [hh.ae_tendsto_heatMollify ε hε.ne' z, ae_tendsto_mollAvg hh z hε]
    with ω h1 h2
  obtain ⟨a, ha⟩ := h2
  rw [circleAvg_eq_of_tendsto ha]
  have hlim := h1.sub ((tendsto_integral_heatTrunc hs z).mul ha)
  rw [one_mul] at hlim
  exact hlim.congr fun n => (pair_heatCircDiff (h ω) _ z ε n).symm

/-- **Gaussianity of the heat-versus-circle difference.** For a whole-plane GFF, `ε > 0` and
`z ∈ ℂ`, the random variable `h*_ε(z) − h_ε(z)` has a centered Gaussian law `N(0, V)`. -/
theorem exists_gaussianReal_heatMollify_sub_circleAvg [IsProbabilityMeasure P]
    (hh : IsWholePlaneGFF h P) {ε : ℝ} (hε : 0 < ε) (z : ℂ) :
    ∃ V : NNReal,
      P.map (fun ω => heatMollify ε (h ω) z - circleAvg (h ω) ε z) = gaussianReal 0 V := by
  set Y : ℕ → Ω → ℝ := fun n ω => h ω (heatCircDiff (ε ^ 2 / 2) z ε n).1 with hY
  have hG : ∀ n, HasGaussianLaw (Y n) P := fun n =>
    hh.gaussian.hasGaussianLaw_eval (heatCircDiff (ε ^ 2 / 2) z ε n)
  have hYm : ∀ n, AEMeasurable (Y n) P := fun n => (hG n).aemeasurable
  have hlaw : ∀ n, P.map (Y n) = gaussianReal 0 (Var[Y n; P]).toNNReal := by
    intro n
    have hc : P[Y n] = 0 := hh.centered _
    rw [(hG n).map_eq_gaussianReal, hc]
  have hlim := ae_tendsto_pair_heatCircDiff hh hε z
  have hZ := aemeasurable_of_tendsto_metrizable_ae' hYm hlim
  obtain ⟨V, -, hV⟩ := exists_gaussianReal_of_ae_tendsto hYm hZ hlaw hlim
  exact ⟨V, hV⟩

/-- The heat-versus-circle difference `ω ↦ h*_ε(z) − h_ε(z)` is measurable. -/
theorem measurable_heatMollify_sub_circleAvg (hh : IsWholePlaneGFF h P) (ε : ℝ) (z : ℂ) :
    Measurable fun ω => heatMollify ε (h ω) z - circleAvg (h ω) ε z :=
  ((measurable_heatMollify_left ε z).comp hh.measurable).sub
    ((measurable_circleAvg_left ε z).comp hh.measurable)

/-- **Joint Gaussianity.** For a whole-plane GFF, the field
`(ε, z) ↦ h*_ε(z) − h_ε(z)` indexed by `ε > 0` and `z ∈ ℂ` is a centered Gaussian process:
it is the almost sure limit, coordinatewise, of the Gaussian process of pairings of `h` with
the mean-zero test functions `heatCircDiff`. -/
theorem isGaussianProcess_heatMollify_sub_circleAvg [IsProbabilityMeasure P]
    (hh : IsWholePlaneGFF h P) :
    IsGaussianProcess (fun (p : Ioi (0 : ℝ) × ℂ) (ω : Ω) =>
      heatMollify (p.1 : ℝ) (h ω) p.2 - circleAvg (h ω) (p.1 : ℝ) p.2) P :=
  CircleAvgIndep.isGaussianProcess_of_ae_tendsto
    (Yn := fun n (p : Ioi (0 : ℝ) × ℂ) ω =>
      h ω (heatCircDiff ((p.1 : ℝ) ^ 2 / 2) p.2 (p.1 : ℝ) n).1)
    (fun n => hh.gaussian.comp_right
      (fun p : Ioi (0 : ℝ) × ℂ => heatCircDiff ((p.1 : ℝ) ^ 2 / 2) p.2 (p.1 : ℝ) n))
    (fun _ _ => hh.centered _)
    (fun p => measurable_heatMollify_sub_circleAvg hh (p.1 : ℝ) p.2)
    (fun p => ae_tendsto_pair_heatCircDiff hh (mem_Ioi.1 p.1.2) p.2)

end HeatCircle
end LQGMetric
