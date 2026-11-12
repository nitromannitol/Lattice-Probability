/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module MatedCRTHarmonic.MoTPort.Foundations.ConeArea5 at commit fdb5cad; only the module paths of local imports are changed.
   Declarations, examples and checks that the copied results do not use are omitted. -/
/- Provenance: ported from an earlier mating-of-trees formalization; only imports and namespace names were changed. -/
import LatticeProb.Bonanno.MatedCRTHarmonic.MoTPort.Foundations.ConeArea4I
import Mathlib.Analysis.SpecialFunctions.Integrals.PosLogEqCircleAverage

/-!
# Cone area, part 10: the log-singular comparison (deterministic)

If `g` is continuous on `ℂ \ {0}` and `g(w) ≤ c(−log|w|) + C` on the punctured disc `B(0,ρ)`,
then on `B(0,δ)` (with `δ + 2^{-k} ≤ ρ`) the approximations of `x + g` are dominated by
`e^{γC}` times the approximations of `x` weighted by `max(|z|, 2^{-k})^{−γc}` (QZ
`AtomlessUncond.logFactorA` at the centre `0`):

* `circleAverage_logBound`: `⨍_{∂B(z,r)} (c(−log|w|) + C) = c(−log max(|z|,r)) + C` (mathlib
  `circleAverage_log_norm_sub_const_eq_log_radius_add_posLog`, Jensen's formula for `log|·|`);
* `areaApproxC_add_ofFunC_ball_le`: the comparison of the approximations;
* **`tight_add_ofFunC`**: tightness at `0` of the weighted approximations of `x` gives tightness
  at `0` of the approximations of `x + g`.

This is the whole-plane analogue of QZ `AreaNoAtom.areaApprox_add_logPotC_add_ofFun_apply` (the
interior log singularity `α(−log|·−z|)` plus a continuous function), with the circle average of
the added function bounded instead of computed. The comparison and tightness steps are proved by elementary estimates.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set Metric
open scoped ENNReal

namespace MatedCRTHarmonic.MoTPort
namespace ConeArea5

open QuantumZipper LQGMetric

/-- **Jensen's formula for the log bound**: `⨍_{∂B(z,r)} (c(−log|w|) + C) = c(−log max(|z|,r)) + C` -/
lemma circleAverage_logBound (c C : ℝ) (z : ℂ) {r : ℝ} (hr : 0 < r) :
    Real.circleAverage (fun w : ℂ => c * -Real.log ‖w‖ + C) z r =
      c * -Real.log (max ‖z‖ r) + C := by
  have h1 := circleAverage_log_norm_sub_const_eq_log_radius_add_posLog (a := (0 : ℂ)) (c := z)
    hr.ne'
  simp only [sub_zero] at h1
  have h2 : Real.log r + Real.posLog (r⁻¹ * ‖z‖) = Real.log (max ‖z‖ r) := by
    rw [Real.posLog_eq_log_max_one (by positivity), ← Real.log_mul hr.ne'
      (by positivity : max 1 (r⁻¹ * ‖z‖) ≠ 0)]
    congr 1
    rw [mul_max_of_nonneg _ _ hr.le, mul_one, ← mul_assoc, mul_inv_cancel₀ hr.ne', one_mul,
      max_comm]
  have e : (fun w : ℂ => c * -Real.log ‖w‖ + C) =
      fun w => ((-c) • fun w : ℂ => Real.log ‖w - 0‖) w + C := by
    funext w; simp only [Pi.smul_apply, smul_eq_mul, sub_zero]; ring
  have hi : CircleIntegrable ((-c) • fun w : ℂ => Real.log ‖w - 0‖) z r :=
    (circleIntegrable_log_norm_sub_const r).const_smul
  rw [e, Real.circleAverage_fun_add hi (circleIntegrable_const C z r), Real.circleAverage_smul,
    Real.circleAverage_const]
  simp only [sub_zero] at h1 ⊢
  rw [smul_eq_mul, h1, h2]
  ring

/-- the weight `max(2^{-k},|w|)^{−γc}` written through `exp` -/
lemma exp_logBound_eq {γ c C : ℝ} {z : ℂ} {k : ℕ} :
    Real.exp (γ * (c * -Real.log (max ‖z‖ (radius k)) + C)) =
      Real.exp (γ * C) * AtomlessUncond.logFactorA γ c 0 k z := by
  have hm : 0 < max (radius k) ‖z - 0‖ := lt_max_of_lt_left (QuantumZipper.radius_pos k)
  unfold AtomlessUncond.logFactorA
  rw [Real.rpow_def_of_pos hm, ← Real.exp_add, sub_zero, max_comm]
  congr 1
  ring

/-- **the comparison of the approximations near the log singularity** -/
theorem areaApproxC_add_ofFunC_ball_le {γ c C ρ δ : ℝ} (hγ : 0 < γ) {x : Field}
    (hc : ConeArea.HasCircleAvgs x) {g : ℂ → ℝ} (hgl : LocallyIntegrable g volume)
    (hg : ContinuousOn g (univ \ {0}))
    (hgb : ∀ w : ℂ, w ≠ 0 → ‖w‖ < ρ → g w ≤ c * -Real.log ‖w‖ + C) {k : ℕ}
    (hk : δ + radius k ≤ ρ) :
    areaApproxC γ (x + ofFunC g) k (ball 0 δ) ≤ ENNReal.ofReal (Real.exp (γ * C)) *
      (areaApproxC γ x k).withDensity
        (fun w => ENNReal.ofReal (AtomlessUncond.logFactorA γ c 0 k w)) (ball 0 δ) := by
  have hrk := QuantumZipper.radius_pos k
  have hUo : IsOpen (univ \ {(0 : ℂ)}) := isOpen_univ.sdiff isClosed_singleton
  have hm1 : Measurable fun z : ℂ => ENNReal.ofReal (radius k ^ (γ ^ 2 / 2) *
      Real.exp (γ * circleAvg x (radius k) z)) :=
    ENNReal.measurable_ofReal.comp ((Real.measurable_exp.comp
      ((ConeArea3.measurable_circleAvg_center x _).const_mul γ)).const_mul _)
  have hm2 : Measurable fun w : ℂ => ENNReal.ofReal (AtomlessUncond.logFactorA γ c 0 k w) :=
    ENNReal.measurable_ofReal.comp (AtomlessUncond.continuous_logFactorA γ c 0 k).measurable
  unfold areaApproxC
  rw [← withDensity_mul _ hm1 hm2, withDensity_apply _ measurableSet_ball,
    withDensity_apply _ measurableSet_ball, ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  have hsph : ∀ᵐ z ∂(volume : Measure ℂ), z ∉ sphere (0 : ℂ) (radius k) :=
    compl_mem_ae_iff.2 (Measure.addHaar_sphere volume 0 _)
  refine lintegral_mono_ae ?_
  filter_upwards [ae_restrict_of_ae (hc k), ae_restrict_of_ae hsph,
    ae_restrict_mem measurableSet_ball] with z ⟨a, ha⟩ hzs hzb
  have hzb' : ‖z‖ < δ := by simpa [mem_ball, dist_zero_right] using hzb
  have hs : sphere z (radius k) ⊆ univ \ {0} := fun w hw => ⟨mem_univ _, fun h0 => by
    rw [mem_singleton_iff] at h0
    rw [h0, mem_sphere, dist_comm] at hw
    exact hzs (by rw [mem_sphere]; exact hw)⟩
  have hsρ : ∀ w ∈ sphere z |radius k|, w ≠ 0 ∧ ‖w‖ < ρ := fun w hw => by
    rw [abs_of_pos hrk] at hw
    refine ⟨fun h0 => (hs hw).2 h0, ?_⟩
    rw [mem_sphere, dist_eq_norm] at hw
    have := norm_add_le z (w - z)
    simp only [add_sub_cancel] at this
    linarith
  rw [ConeArea3.circleAvg_add_ofFunC hgl hUo hg hrk hs ha]
  have hbound : Real.circleAverage g z (radius k) ≤
      c * -Real.log (max ‖z‖ (radius k)) + C := by
    rw [← circleAverage_logBound c C z hrk]
    have hcs : ContinuousOn (fun w : ℂ => c * -Real.log ‖w‖ + C) (sphere z |radius k|) :=
      ((continuousOn_const.mul (Real.continuousOn_log.comp continuous_norm.continuousOn
        fun w hw => by simpa [norm_eq_zero] using (hsρ w hw).1).neg).add continuousOn_const)
    refine Real.circleAverage_mono ?_ hcs.circleIntegrable' fun w hw =>
      hgb w (hsρ w hw).1 (hsρ w hw).2
    exact (hg.mono (by rw [abs_of_pos hrk]; exact hs)).circleIntegrable'
  simp only [Pi.mul_apply]
  have hA0 : 0 ≤ radius k ^ (γ ^ 2 / 2) * Real.exp (γ * circleAvg x (radius k) z) := by positivity
  rw [← ENNReal.ofReal_mul hA0, ← ENNReal.ofReal_mul (Real.exp_pos _).le]
  refine ENNReal.ofReal_le_ofReal ?_
  have he : Real.exp (γ * (circleAvg x (radius k) z + Real.circleAverage g z (radius k))) ≤
      Real.exp (γ * circleAvg x (radius k) z) *
        (Real.exp (γ * C) * AtomlessUncond.logFactorA γ c 0 k z) := by
    rw [← exp_logBound_eq, ← Real.exp_add]
    exact Real.exp_le_exp.2 (by nlinarith)
  have hr0 : 0 ≤ radius k ^ (γ ^ 2 / 2) := by positivity
  calc radius k ^ (γ ^ 2 / 2) *
        Real.exp (γ * (circleAvg x (radius k) z + Real.circleAverage g z (radius k)))
      ≤ radius k ^ (γ ^ 2 / 2) * (Real.exp (γ * circleAvg x (radius k) z) *
        (Real.exp (γ * C) * AtomlessUncond.logFactorA γ c 0 k z)) :=
        mul_le_mul_of_nonneg_left he hr0
    _ = _ := by ring

/-- **tightness at `0` transfers from the weighted approximations of `x` to those of `x + g`** -/
theorem tight_add_ofFunC {γ c C ρ : ℝ} (hγ : 0 < γ) (hρ : 0 < ρ) {x : Field}
    (hc : ConeArea.HasCircleAvgs x) {g : ℂ → ℝ} (hgl : LocallyIntegrable g volume)
    (hg : ContinuousOn g (univ \ {0}))
    (hgb : ∀ w : ℂ, w ≠ 0 → ‖w‖ < ρ → g w ≤ c * -Real.log ‖w‖ + C)
    (htight : ∀ ε : ℝ, 0 < ε → ∃ δ > 0, ∀ᶠ k in atTop, (areaApproxC γ x k).withDensity
        (fun w => ENNReal.ofReal (AtomlessUncond.logFactorA γ c 0 k w)) (ball 0 δ) ≤
          ENNReal.ofReal ε) :
    ∀ ε : ℝ, 0 < ε → ∃ δ > 0, ∀ᶠ k in atTop,
      areaApproxC γ (x + ofFunC g) k (ball 0 δ) ≤ ENNReal.ofReal ε := by
  intro ε hε
  set E := Real.exp (γ * C) with hE
  have hE0 : 0 < E := Real.exp_pos _
  obtain ⟨δ, hδ, hev⟩ := htight (ε / E) (div_pos hε hE0)
  refine ⟨min δ (ρ / 2), lt_min hδ (half_pos hρ), ?_⟩
  have hr : Tendsto radius atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
  filter_upwards [hev, hr.eventually (ge_mem_nhds (half_pos hρ))] with k hk hrk
  have hk' : min δ (ρ / 2) + radius k ≤ ρ := by linarith [min_le_right δ (ρ / 2)]
  refine (areaApproxC_add_ofFunC_ball_le hγ hc hgl hg hgb hk').trans ?_
  calc ENNReal.ofReal E * (areaApproxC γ x k).withDensity
        (fun w => ENNReal.ofReal (AtomlessUncond.logFactorA γ c 0 k w)) (ball 0 (min δ (ρ / 2)))
      ≤ ENNReal.ofReal E * ENNReal.ofReal (ε / E) :=
        by gcongr; exact (measure_mono (ball_subset_ball (min_le_left _ _))).trans hk
    _ = ENNReal.ofReal ε := by
        rw [← ENNReal.ofReal_mul hE0.le, mul_div_cancel₀ _ hE0.ne']

end ConeArea5
end MatedCRTHarmonic.MoTPort
