/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Field.CircleAvgProc at commit 31e7483; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Field.CircleAvgCov
import LatticeProb.Bonanno.LQGMetric.Field.CircleAvgGaussLim

/-!
# The circle-average increments of a whole-plane GFF: law and covariance

For a whole-plane GFF `h` and radii `r, s > 0`, the increment `h_r(z) − h_s(w)` is centered
Gaussian with variance `incCov z r w s z r w s` (`map_cInc`), and the covariance of two
increments is `incCov` (`covariance_cInc`); this is Duplantier–Sheffield's circle-average
covariance (arXiv:0808.1560 §3.1). In particular `Var(h_r(z) − h_1(z)) = |log r|`
(`variance_cInc_one`), the Brownian-motion normalization (DS Prop. 3.3 / GM l. 223).
Proof: a.s. limits (`ae_tendsto_mollAvg`) of the Gaussian mollified increments, whose
covariances converge (`tendsto_logCov_circDiff`), with `exists_gaussianReal_of_ae_tendsto`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set Metric
open scoped Real

namespace LQGMetric
namespace CircleAvg

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {h : Ω → DistC}

/-- the mollified increment at level `n` -/
def mInc (h : Ω → DistC) (n : ℕ) (r : ℝ) (z : ℂ) (s : ℝ) (w : ℂ) (ω : Ω) : ℝ :=
  mollAvg (h ω) n z r - mollAvg (h ω) n w s

/-- the circle-average increment `h_r(z) − h_s(w)` -/
def cInc (h : Ω → DistC) (r : ℝ) (z : ℂ) (s : ℝ) (w : ℂ) (ω : Ω) : ℝ :=
  circleAvg (h ω) r z - circleAvg (h ω) s w

lemma ae_tendsto_mInc (hh : IsWholePlaneGFF h P) {r s : ℝ} (hr : 0 < r) (hs : 0 < s)
    (z w : ℂ) :
    ∀ᵐ ω ∂P, Tendsto (fun n => mInc h n r z s w ω) atTop (𝓝 (cInc h r z s w ω)) := by
  filter_upwards [ae_tendsto_mollAvg hh z hr, ae_tendsto_mollAvg hh w hs] with ω ⟨a, ha⟩ ⟨b, hb⟩
  simp only [mInc, cInc, circleAvg_eq_of_tendsto ha, circleAvg_eq_of_tendsto hb]
  exact ha.sub hb

lemma measurable_cInc (hh : IsWholePlaneGFF h P) (r : ℝ) (z : ℂ) (s : ℝ) (w : ℂ) :
    Measurable (cInc h r z s w) :=
  ((measurable_circleAvg_left r z).comp hh.measurable).sub
    ((measurable_circleAvg_left s w).comp hh.measurable)

lemma logCov_circDiff_nonneg (hh : IsWholePlaneGFF h P) (φ : TestC0) :
    0 ≤ logCov φ.1 φ.1 := by
  rw [← (integral_sq_pair hh φ).2]
  exact integral_nonneg fun _ => sq_nonneg _

lemma map_mInc (hh : IsWholePlaneGFF h P) (n : ℕ) (r : ℝ) (z : ℂ) (s : ℝ) (w : ℂ) :
    P.map (mInc h n r z s w) =
      gaussianReal 0 (logCov (circDiff n z r n w s).1 (circDiff n z r n w s).1).toNNReal := by
  have hG := hasGaussianLaw_mollAvg_sub hh n z r n w s
  rw [show mInc h n r z s w = fun ω => mollAvg (h ω) n z r - mollAvg (h ω) n w s from rfl,
    hG.map_eq_gaussianReal, integral_mollAvg_sub hh, ← covariance_self hG.aemeasurable,
    covariance_mollAvg_sub hh]

lemma gaussianReal_facts {Z : Ω → ℝ} (hZ : AEMeasurable Z P) {v : NNReal}
    (hl : P.map Z = gaussianReal 0 v) : Var[Z; P] = v ∧ MemLp Z 2 P := by
  have : IsGaussian (P.map Z) := by rw [hl]; infer_instance
  have hG : HasGaussianLaw Z P := IsGaussian.hasGaussianLaw hZ
  refine ⟨?_, hG.memLp_two⟩
  have := variance_map (X := id) (μ := P) aemeasurable_id hZ
  rw [hl, variance_id_gaussianReal] at this
  exact this.symm

/-- **Law of a circle-average increment.** -/
theorem map_cInc (hh : IsWholePlaneGFF h P) {r s : ℝ} (hr : 0 < r) (hs : 0 < s) (z w : ℂ) :
    P.map (cInc h r z s w) = gaussianReal 0 (incCov z r w s z r w s).toNNReal ∧
      Var[cInc h r z s w; P] = incCov z r w s z r w s := by
  have := hh.gaussian.isProbabilityMeasure
  obtain ⟨V, hV, hmap⟩ := exists_gaussianReal_of_ae_tendsto
    (fun n => (hasGaussianLaw_mollAvg_sub hh n z r n w s).aemeasurable)
    (measurable_cInc hh r z s w).aemeasurable (fun n => map_mInc hh n r z s w)
    (ae_tendsto_mInc hh hr hs z w)
  have hL := tendsto_logCov_circDiff hr hs hr hs z w z w
  have hT : Tendsto (fun n =>
      ((logCov (circDiff n z r n w s).1 (circDiff n z r n w s).1).toNNReal : ℝ)) atTop
      (𝓝 ((incCov z r w s z r w s).toNNReal : ℝ)) :=
    (NNReal.continuous_coe.tendsto _).comp ((continuous_real_toNNReal.tendsto _).comp hL)
  have hVeq : V = (incCov z r w s z r w s).toNNReal :=
    NNReal.coe_injective (tendsto_nhds_unique hV hT)
  have hnn : 0 ≤ incCov z r w s z r w s :=
    ge_of_tendsto' hL fun n => logCov_circDiff_nonneg hh _
  rw [hVeq] at hmap
  refine ⟨hmap, ?_⟩
  rw [(gaussianReal_facts (measurable_cInc hh r z s w).aemeasurable hmap).1,
    Real.coe_toNNReal _ hnn]

/-- **Covariance of circle-average increments** (DS §3.1). -/
theorem covariance_cInc (hh : IsWholePlaneGFF h P) {r s r' s' : ℝ} (hr : 0 < r) (hs : 0 < s)
    (hr' : 0 < r') (hs' : 0 < s') (z w z' w' : ℂ) :
    cov[cInc h r z s w, cInc h r' z' s' w'; P] = incCov z r w s z' r' w' s' := by
  have := hh.gaussian.isProbabilityMeasure
  set A := cInc h r z s w
  set B := cInc h r' z' s' w'
  have hGP := isGaussianProcess_mollAvg_sub hh
  -- the mollified sums
  set Y : ℕ → Ω → ℝ := fun n ω => mInc h n r z s w ω + mInc h n r' z' s' w' ω
  have hGY : ∀ n, HasGaussianLaw (Y n) P := fun n =>
    hGP.hasGaussianLaw_fun_add (s := ((n, z, r), (n, w, s))) (t := ((n, z', r'), (n, w', s')))
  have hGA : ∀ n, HasGaussianLaw (mInc h n r z s w) P := fun n =>
    hasGaussianLaw_mollAvg_sub hh n z r n w s
  have hGB : ∀ n, HasGaussianLaw (mInc h n r' z' s' w') P := fun n =>
    hasGaussianLaw_mollAvg_sub hh n z' r' n w' s'
  have hmeanY : ∀ n, P[Y n] = 0 := by
    intro n
    simp only [Y]
    rw [integral_add (hGA n).integrable (hGB n).integrable]
    simp only [mInc]
    rw [integral_mollAvg_sub hh, integral_mollAvg_sub hh, add_zero]
  have hvarY : ∀ n, Var[Y n; P] =
      logCov (circDiff n z r n w s).1 (circDiff n z r n w s).1 +
        2 * logCov (circDiff n z r n w s).1 (circDiff n z' r' n w' s').1 +
          logCov (circDiff n z' r' n w' s').1 (circDiff n z' r' n w' s').1 := by
    intro n
    have := variance_add (hGA n).memLp_two (hGB n).memLp_two
    simp only [Y]
    rw [show (fun ω => mInc h n r z s w ω + mInc h n r' z' s' w' ω) =
      mInc h n r z s w + mInc h n r' z' s' w' from rfl, this,
      ← covariance_self (hGA n).aemeasurable, ← covariance_self (hGB n).aemeasurable]
    have e1 : cov[mInc h n r z s w, mInc h n r z s w; P] =
        logCov (circDiff n z r n w s).1 (circDiff n z r n w s).1 :=
      covariance_mollAvg_sub hh n z r n w s n z r n w s
    have e2 : cov[mInc h n r z s w, mInc h n r' z' s' w'; P] =
        logCov (circDiff n z r n w s).1 (circDiff n z' r' n w' s').1 :=
      covariance_mollAvg_sub hh n z r n w s n z' r' n w' s'
    have e3 : cov[mInc h n r' z' s' w', mInc h n r' z' s' w'; P] =
        logCov (circDiff n z' r' n w' s').1 (circDiff n z' r' n w' s').1 :=
      covariance_mollAvg_sub hh n z' r' n w' s' n z' r' n w' s'
    rw [e1, e2, e3]
  have hmapY : ∀ n, P.map (Y n) = gaussianReal 0 (Var[Y n; P]).toNNReal := by
    intro n
    rw [(hGY n).map_eq_gaussianReal, hmeanY]
  have hlimY : ∀ᵐ ω ∂P, Tendsto (fun n => Y n ω) atTop (𝓝 (A ω + B ω)) := by
    filter_upwards [ae_tendsto_mInc hh hr hs z w, ae_tendsto_mInc hh hr' hs' z' w'] with ω h1 h2
    exact h1.add h2
  obtain ⟨V, hV, hmap⟩ := exists_gaussianReal_of_ae_tendsto (fun n => (hGY n).aemeasurable)
    ((measurable_cInc hh r z s w).add (measurable_cInc hh r' z' s' w')).aemeasurable hmapY hlimY
  have hT : Tendsto (fun n => ((Var[Y n; P]).toNNReal : ℝ)) atTop
      (𝓝 (incCov z r w s z r w s + 2 * incCov z r w s z' r' w' s' +
        incCov z' r' w' s' z' r' w' s')) := by
    refine (((tendsto_logCov_circDiff hr hs hr hs z w z w).add
      ((tendsto_logCov_circDiff hr hs hr' hs' z w z' w').const_mul 2)).add
      (tendsto_logCov_circDiff hr' hs' hr' hs' z' w' z' w')).congr fun n => ?_
    rw [Real.coe_toNNReal _ (variance_nonneg _ _), hvarY]
  have hVeq := tendsto_nhds_unique hV hT
  have hAB := (gaussianReal_facts ((measurable_cInc hh r z s w).add
    (measurable_cInc hh r' z' s' w')).aemeasurable hmap).1
  rw [hVeq] at hAB
  obtain ⟨hA, hAm⟩ := gaussianReal_facts (measurable_cInc hh r z s w).aemeasurable
    (map_cInc hh hr hs z w).1
  obtain ⟨hB, hBm⟩ := gaussianReal_facts (measurable_cInc hh r' z' s' w').aemeasurable
    (map_cInc hh hr' hs' z' w').1
  have hsum := variance_add hAm hBm
  rw [hAB, (map_cInc hh hr hs z w).2, (map_cInc hh hr' hs' z' w').2] at hsum
  linarith

lemma circCov_center (z : ℂ) {r : ℝ} (hr : 0 < r) (s : ℝ) (hs : 0 < s) :
    circCov z r z s = Real.log s + Real.posLog (s⁻¹ * r) := by
  refine Real.circleAverage_const_on_circle fun x hx => ?_
  rw [circLog_eq hs.ne', mem_sphere_iff_norm, abs_of_pos hr] at *
  rw [norm_sub_rev, hx]

/-- **`Var(h_r(z) − h_1(z)) = |log r|`.** -/
theorem variance_cInc_one (hh : IsWholePlaneGFF h P) {r : ℝ} (hr : 0 < r) (z : ℂ) :
    Var[cInc h r z 1 z; P] = |Real.log r| := by
  rw [(map_cInc hh hr one_pos z z).2, incCov, circCov_center z hr r hr,
    circCov_center z hr 1 one_pos, circCov_center z one_pos r hr,
    circCov_center z one_pos 1 one_pos, Real.abs_log_eq_posLog_add_posLog_inv,
    inv_mul_cancel₀ hr.ne', inv_one, one_mul, mul_one, Real.log_one]
  have h1 : Real.posLog 1 = 0 := by simp [Real.posLog_apply]
  linarith

end CircleAvg
end LQGMetric
