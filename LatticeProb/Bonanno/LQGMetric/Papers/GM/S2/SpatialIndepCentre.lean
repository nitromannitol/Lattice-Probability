/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.GM.S2.SpatialIndepCentre at commit 31e7483; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S2.SpatialIndepMoment
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S3.DeterministicLaw
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S2.TightLaw
import LatticeProb.Bonanno.LQGMetric.Field.CircleAvgRate
import LatticeProb.Bonanno.LQGMetric.Field.ExistGFF
import LatticeProb.Bonanno.LQGMetric.Field.ZeroBoundaryAffine

/-!
# GM Lemma 2.7: tightness of the centring offset, uniformly in the centre

The centring constant of GM's recentred field is `h_{1+s}(z)` (GM l. 967, 979). With the
mean value property, `𝔥(z) − h_{1+s}(z) = (h(ψ_z) − h̊(ψ_z))/∫ψ − h_{1+s}(z)`; the first part
`offsetFun δ R z h = h(ψ_z)/∫ψ − h_R(z)` is a functional of `h` modulo additive constants whose
law does not depend on `z` nor on the probability space (translation invariance
`IsWholePlaneGFF.affineComp`, `Tight.circleAvg_affineComp_one`, and uniqueness of the law modulo
constants `GM.prob_eq_of_ae_addConst_iff`, as in GM l. 985–986). Hence it is tight uniformly
(`exists_offset_bound`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set Metric
open scoped ENNReal

namespace LQGMetric.GM

open QuantumZipper TopologicalSpace

/-- `h(ψ_z)/∫ψ − h_R(z)` -/
def offsetFun {δ : ℝ} (hδ : 0 ≤ δ) (R : ℝ) (z : ℂ) (T : DistC) : ℝ :=
  T (radBump δ hδ z) / (∫ y, radProf δ y) - circleAvg T R z

lemma measurable_offsetFun {δ : ℝ} (hδ : 0 ≤ δ) (R : ℝ) (z : ℂ) :
    Measurable (offsetFun hδ R z) :=
  ((measurable_distOn_apply _).div_const _).sub (measurable_circleAvg_left R z)

lemma offsetFun_affineComp {δ : ℝ} (hδ : 0 ≤ δ) (R : ℝ) (z : ℂ) (T : DistC) :
    offsetFun hδ R 0 (affineComp 1 z T) = offsetFun hδ R z T := by
  unfold offsetFun
  rw [Tight.circleAvg_affineComp_one, GFFInv.affineComp_apply]
  congr 2
  rw [one_pow, inv_one, one_mul]
  congr 1
  ext x
  rw [testAffinePull_apply 1 z one_ne_zero, radBump_apply, radBump_apply]
  simp

lemma offsetFun_addConst {δ : ℝ} (hδ : 0 < δ) (R : ℝ) {T : DistC}
    (hT : ∀ c, circleAvg (addConst T c) R 0 = circleAvg T R 0 + c) (a : ℝ) :
    offsetFun hδ.le R 0 (addConst T a) = offsetFun hδ.le R 0 T := by
  unfold offsetFun
  have hI := integral_radProf_pos hδ
  rw [hT, GFFInv.addConst_apply, integral_radBump]
  field_simp
  ring

/-- **uniform tightness of the offset** -/
theorem exists_offset_bound {δ R : ℝ} (hδ : 0 < δ) (hR : 0 < R) {ε : ℝ} (hε : 0 < ε) :
    ∃ A : ℝ, 0 < A ∧ ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      (h : Ω → DistC), IsWholePlaneGFF h P → ∀ z : ℂ,
        P {ω | A < |offsetFun hδ.le R z (h ω)|} ≤ ENNReal.ofReal ε := by
  obtain ⟨Ω₀, _, P₀, h₀, hP₀, hh₀⟩ := GFFExist.exists_wholePlaneGFF
  set S : ℕ → Set DistC := fun n => {T | (n + 1 : ℝ) < |offsetFun hδ.le R 0 T|} with hS
  have hSm : ∀ n, MeasurableSet (S n) := fun n =>
    measurableSet_lt measurable_const (continuous_abs.measurable.comp (measurable_offsetFun hδ.le R 0))
  have hanti : Antitone fun n => h₀ ⁻¹' S n := by
    intro m n hmn T hT
    simp only [hS, mem_preimage, mem_ofPred_eq] at hT ⊢
    have : (m : ℝ) ≤ n := by exact_mod_cast hmn
    linarith
  have hinter : (⋂ n, h₀ ⁻¹' S n) = ∅ := by
    ext ω
    simp only [hS, mem_iInter, mem_preimage, mem_ofPred_eq, mem_empty_iff_false, iff_false,
      not_forall, not_lt]
    obtain ⟨n, hn⟩ := exists_nat_gt |offsetFun hδ.le R 0 (h₀ ω)|
    exact ⟨n, by linarith⟩
  have ht := tendsto_measure_iInter_atTop (μ := P₀)
    (fun n => (hh₀.measurable (hSm n)).nullMeasurableSet) hanti ⟨0, measure_ne_top _ _⟩
  rw [hinter, measure_empty] at ht
  obtain ⟨n, hn⟩ := (ht.eventually (Iic_mem_nhds (ENNReal.ofReal_pos.2 hε))).exists
  refine ⟨n + 1, by positivity, fun {Ω} _ P _ h hh z => ?_⟩
  have hh' := hh.affineComp one_pos z
  have e : {ω | (n + 1 : ℝ) < |offsetFun hδ.le R z (h ω)|} =
      (fun ω => affineComp 1 z (h ω)) ⁻¹' S n := by
    ext ω; simp [hS, offsetFun_affineComp]
  rw [e, prob_eq_of_ae_addConst_iff hh' hh₀ (hSm n) ?_ ?_]
  · exact hn
  · filter_upwards [CircleAvg.ae_circleAvg_addConst hh' 0 hR] with ω hω a
    simp only [hS, mem_ofPred_eq, offsetFun_addConst hδ R hω]
  · filter_upwards [CircleAvg.ae_circleAvg_addConst hh₀ 0 hR] with ω hω a
    simp only [hS, mem_ofPred_eq, offsetFun_addConst hδ R hω]

/-- the radial bump as a test function on `B(z,R)` (`δ < R`) -/
def radBumpOn {δ R : ℝ} (hδ : 0 < δ) (hδR : δ < R) (z : ℂ) : TestOn (Blueprint.ballO z R) :=
  ⟨radBump δ hδ.le z, (radBump δ hδ.le z).contDiff, (radBump δ hδ.le z).hasCompactSupport, by
    refine (closure_minimal (fun x hx => ?_) isClosed_closedBall).trans
      (closedBall_subset_ball hδR)
    by_contra hx'
    rw [mem_closedBall, dist_eq_norm, not_le] at hx'
    exact hx (radProf_eq_zero hδ.le hx'.le)⟩

/-- the variance of a zero-boundary GFF on `B(0,R)` paired with `ψ_0` -/
def zbVar {δ R : ℝ} (hδ : 0 < δ) (_hδR : δ < R) : ℝ :=
  zeroGFFTestCov (Metric.ball (0 : ℂ) R) (radBump δ hδ.le 0) (radBump δ hδ.le 0)

/-- translation invariance of the zero-boundary covariance of `ψ_z` on `B(z,R)` -/
lemma zeroGFFTestCov_radBump {δ R : ℝ} (hδ : 0 < δ) (hδR : δ < R) (z : ℂ) :
    zeroGFFTestCov (Metric.ball z R) (radBump δ hδ.le z) (radBump δ hδ.le z) = zbVar hδ hδR := by
  have h := zeroGFFTestCov_affine (z := z) one_ne_zero (radBumpOn hδ hδR 0) (radBumpOn hδ hδR 0)
  rw [one_pow, one_mul] at h
  have hset : ((affOpens 1 z (Blueprint.ballO 0 R) : Opens ℂ) : Set ℂ) = Metric.ball z R := by
    ext x
    show affMap 1 z x ∈ Metric.ball (0 : ℂ) R ↔ _
    simp [affMap, mem_ball, dist_eq_norm, sub_eq_add_neg]
  have hfun : ((zbPull 1 z one_ne_zero (radBumpOn hδ hδR 0) : TestOn _) : ℂ → ℝ) =
      radBump δ hδ.le z := by
    funext x
    rw [zbPull_apply]
    show radProf δ (affMap 1 z x - 0) = radProf δ (x - z)
    simp [affMap, sub_eq_add_neg]
  rw [hset, hfun] at h
  exact h

/-- **Chebyshev for the zero-boundary pairing**, uniform in `z` -/
theorem prob_zbPair_ge_le {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {δ R : ℝ} (hδ : 0 < δ) (hδR : δ < R) {z : ℂ} {hz : Ω → DistC}
    (hzb : IsZeroBoundaryGFF (Blueprint.ballO z R)
      (fun ω => restrictTo (Blueprint.ballO z R) (hz ω)) P) {t : ℝ} (ht : 0 < t) :
    P {ω | t ≤ |hz ω (radBump δ hδ.le z)|} ≤ ENNReal.ofReal (zbVar hδ hδR / t ^ 2) := by
  set ψ := radBumpOn hδ hδR z
  have e : (fun ω => hz ω (radBump δ hδ.le z)) = fun ω => restrictTo (Blueprint.ballO z R) (hz ω) ψ := by
    funext ω
    show hz ω _ = hz ω (TestFunction.monoCLM ℝ ψ)
    congr 1; ext x; simp [TestFunction.monoCLM_apply, ψ, radBumpOn]; rfl
  have hL : MemLp (fun ω => restrictTo (Blueprint.ballO z R) (hz ω) ψ) 2 P :=
    (hzb.process.gaussian.hasGaussianLaw_eval ψ).memLp_two
  have h0 := hzb.process.centered ψ
  have hv : variance (fun ω => restrictTo (Blueprint.ballO z R) (hz ω) ψ) P = zbVar hδ hδR := by
    rw [← covariance_self hL.aemeasurable, hzb.process.covariance_eq]
    exact zeroGFFTestCov_radBump hδ hδR z
  have := meas_ge_le_variance_div_sq hL ht
  rw [hv, h0] at this
  have e2 : {ω | t ≤ |hz ω (radBump δ hδ.le z)|} =
      {ω | t ≤ |restrictTo (Blueprint.ballO z R) (hz ω) ψ - 0|} := by
    ext ω
    show t ≤ |hz ω (radBump δ hδ.le z)| ↔ t ≤ |restrictTo (Blueprint.ballO z R) (hz ω) ψ - 0|
    rw [sub_zero, show hz ω (radBump δ hδ.le z) = _ from congrFun e ω]
  rw [e2]; exact this

end LQGMetric.GM
