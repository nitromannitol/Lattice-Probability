/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module MatedCRTHarmonic.IGLaw.CircleAvgCovariance at commit fdb5cad; only the module paths of local imports are changed.
   Declarations, examples and checks that the copied results do not use are omitted. -/
import LatticeProb.Bonanno.MatedCRTHarmonic.IGLaw.OInterfaces
import LatticeProb.Bonanno.MatedCRTHarmonic.LQGCoord.ScaleKolm
import LatticeProb.Bonanno.MatedCRTHarmonic.LQGCoord.Transform

/-!
# Covariance of the whole-plane GFF circle-average process

The chosen smooth bump in LQGMetric need not be radial. Rotation covariance is therefore
proved by comparing its rotated and unrotated circle mollifiers in the mean-zero GFF pairing.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set Metric
open scoped Distributions Real

namespace MatedCRTHarmonic.IGLaw

open LQGMetric LQGMetric.CircleAvg

private def rotTest (θ : ℝ) (φ : TestC) : TestC :=
  MatedCRTHarmonic.MoTPort.FieldOps.testPullCLE
    (rotation (Circle.exp (-θ))).toContinuousLinearEquiv φ

private lemma rotTest_apply (θ : ℝ) (φ : TestC) (x : ℂ) :
    rotTest θ φ x = φ (rotation (Circle.exp (-θ)) x) := rfl

private lemma integral_rotTest (θ : ℝ) (φ : TestC) :
    ∫ x, rotTest θ φ x = ∫ x, φ x := by
  let R := rotation (Circle.exp (-θ))
  have h := R.measurePreserving.integral_comp R.toHomeomorph.measurableEmbedding
    (fun x : ℂ => φ x)
  exact h

private lemma logPot_rotTest (θ : ℝ) (φ : TestC) (x : ℂ) :
    logPot (rotTest θ φ) x = logPot φ (rotation (Circle.exp (-θ)) x) := by
  let R := rotation (Circle.exp (-θ))
  have h := R.measurePreserving.integral_comp R.toHomeomorph.measurableEmbedding
    (fun y : ℂ => -Real.log ‖R x - y‖ * φ y)
  unfold logPot
  calc
    (∫ y, -Real.log ‖x - y‖ * rotTest θ φ y) =
        ∫ y, -Real.log ‖R x - R y‖ * φ (R y) := by
          apply integral_congr_ae
          filter_upwards [] with y
          rw [← R.map_sub, R.norm_map]
          rfl
    _ = ∫ y, -Real.log ‖R x - y‖ * φ y := h

private lemma rotTest_integral_one (θ : ℝ) (n : ℕ) (w : ℂ) (ρ : ℝ) :
    ∫ x, rotTest θ (circBump n w ρ) x = 1 := by
  rw [integral_rotTest, integral_circBump]

private lemma rot_center (θ : ℝ) (w : ℂ) :
    rotation (Circle.exp (-θ)) (Complex.exp (θ * Complex.I) * w) = w := by
  simp only [rotation_apply]
  change Complex.exp (((-θ : ℝ) : ℂ) * Complex.I) *
    (Complex.exp (((θ : ℝ) : ℂ) * Complex.I) * w) = w
  rw [← mul_assoc, ← Complex.exp_add]
  have : (((-θ : ℝ) : ℂ) * Complex.I + (((θ : ℝ) : ℂ) * Complex.I)) = 0 := by
    push_cast
    ring
  rw [this, Complex.exp_zero, one_mul]

private lemma circLog_rot (θ : ℝ) {ρ : ℝ} (hρ : 0 < ρ) (w x : ℂ) :
    circLog w ρ (rotation (Circle.exp (-θ)) x) =
      circLog (Complex.exp (θ * Complex.I) * w) ρ x := by
  let R := rotation (Circle.exp (-θ))
  have hnorm : ‖w - R x‖ = ‖Complex.exp (θ * Complex.I) * w - x‖ := by
    calc
      ‖w - R x‖ = ‖R (Complex.exp (θ * Complex.I) * w) - R x‖ := by
        rw [rot_center θ w]
      _ = ‖Complex.exp (θ * Complex.I) * w - x‖ := by
        rw [← R.map_sub, R.norm_map]
  rw [circLog_eq hρ.ne', circLog_eq hρ.ne']
  rw [hnorm]

private lemma abs_logPot_circBump_add_le {ρ : ℝ} (hρ : 0 < ρ)
    (n : ℕ) (w x : ℂ) :
    |logPot (circBump n w ρ) x + circLog w ρ x| ≤ (2 : ℝ)⁻¹ ^ n / ρ := by
  rw [logPot_circBump]
  simpa only [neg_add_eq_sub, abs_sub_comm, abs_neg] using
    abs_integral_bump_circLog_sub_le hρ n w x

private lemma abs_logPot_rotBump_add_le (θ : ℝ) {ρ : ℝ} (hρ : 0 < ρ)
    (n : ℕ) (w x : ℂ) :
    |logPot (rotTest θ (circBump n w ρ)) x +
      circLog (Complex.exp (θ * Complex.I) * w) ρ x| ≤ (2 : ℝ)⁻¹ ^ n / ρ := by
  rw [logPot_rotTest, ← circLog_rot θ hρ]
  exact abs_logPot_circBump_add_le hρ n w _

private def rotDiff (n : ℕ) (θ : ℝ) (w : ℂ) (ρ : ℝ) : TestC0 :=
  ⟨rotTest θ (circBump n w ρ) -
      circBump n (Complex.exp (θ * Complex.I) * w) ρ, by
    change ∫ x, (rotTest θ (circBump n w ρ) x -
      circBump n (Complex.exp (θ * Complex.I) * w) ρ x) = 0
    rw [integral_sub (integrable_testC _) (integrable_testC _),
      rotTest_integral_one, integral_circBump, sub_self]⟩

private lemma abs_logPot_rotDiff_le (n : ℕ) (θ : ℝ) {ρ : ℝ} (hρ : 0 < ρ)
    (w x : ℂ) :
    |logPot (rotDiff n θ w ρ).1 x| ≤ 2 * ((2 : ℝ)⁻¹ ^ n / ρ) := by
  let g := circLog (Complex.exp (θ * Complex.I) * w) ρ x
  have h₁ := abs_logPot_rotBump_add_le θ hρ n w x
  have h₂ := abs_logPot_circBump_add_le hρ n (Complex.exp (θ * Complex.I) * w) x
  have hsub := abs_sub (logPot (rotTest θ (circBump n w ρ)) x + g)
    (logPot (circBump n (Complex.exp (θ * Complex.I) * w) ρ) x + g)
  simp only [rotDiff, logPot_sub]
  have heq : logPot (rotTest θ (circBump n w ρ)) x -
      logPot (circBump n (Complex.exp (θ * Complex.I) * w) ρ) x =
      (logPot (rotTest θ (circBump n w ρ)) x + g) -
      (logPot (circBump n (Complex.exp (θ * Complex.I) * w) ρ) x + g) := by ring
  rw [heq]
  linarith only [hsub, h₁, h₂]

private lemma rotTest_circBump_nonneg (n : ℕ) (θ : ℝ) (w : ℂ) (ρ : ℝ) (x : ℂ) :
    0 ≤ rotTest θ (circBump n w ρ) x := by
  rw [rotTest_apply]
  exact circBump_nonneg n w ρ _

private theorem logCov_rotDiff_le (n : ℕ) (θ : ℝ) {ρ : ℝ} (hρ : 0 < ρ)
    (w : ℂ) :
    logCov (rotDiff n θ w ρ).1 (rotDiff n θ w ρ).1 ≤
      4 * ((2 : ℝ)⁻¹ ^ n / ρ) := by
  set D := rotDiff n θ w ρ
  set A := rotTest θ (circBump n w ρ)
  set B := circBump n (Complex.exp (θ * Complex.I) * w) ρ
  set c := 2 * ((2 : ℝ)⁻¹ ^ n / ρ)
  rw [logCov_eq_integral_logPot]
  have hD : ∀ x, |D.1 x| ≤ A x + B x := by
    intro x
    show |A x - B x| ≤ _
    refine (abs_sub _ _).trans (le_of_eq ?_)
    rw [abs_of_nonneg (rotTest_circBump_nonneg n θ w ρ x),
      abs_of_nonneg (circBump_nonneg n _ ρ x)]
  have hb : ∀ x, ‖D.1 x * logPot D.1 x‖ ≤ (A x + B x) * c := by
    intro x
    rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs]
    exact mul_le_mul (hD x) (abs_logPot_rotDiff_le n θ hρ w x)
      (abs_nonneg _) (add_nonneg (rotTest_circBump_nonneg n θ w ρ x)
        (circBump_nonneg n _ ρ x))
  have hint : Integrable fun x => (A x + B x) * c :=
    ((integrable_testC _).add (integrable_testC _)).mul_const c
  have hle := (le_abs_self _).trans ((Real.norm_eq_abs _).symm.le.trans
    (norm_integral_le_of_norm_le hint (Eventually.of_forall hb)))
  refine hle.trans (le_of_eq ?_)
  rw [integral_mul_const, integral_add (integrable_testC _) (integrable_testC _),
    rotTest_integral_one, integral_circBump]
  simp only [c]
  ring

/-- At one circle, the two mollifier sequences have the same almost-sure limit. -/
theorem rotCircleAvgCovariance_fixed {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {h : Ω → DistC} (hh : IsWholePlaneGFF h P) (θ : ℝ) {ρ : ℝ} (hρ : 0 < ρ)
    (w : ℂ) :
    ∀ᵐ ω ∂P, circleAvg (MatedCRTHarmonic.MoTPort.rotateField θ (h ω)) ρ w =
      circleAvg (h ω) ρ (Complex.exp (θ * Complex.I) * w) := by
  have := hh.gaussian.isProbabilityMeasure
  have hE : ∀ᵐ ω ∂P,
      Tendsto (fun n => h ω (rotDiff n θ w ρ).1) atTop (𝓝 0) :=
    ae_tendsto_zero_of_sq_le (C := 4 / ρ) (q := (2 : ℝ)⁻¹)
      (fun n => (integral_sq_pair hh _).1) (by norm_num) (by norm_num)
      (fun n => by
        calc
          (∫ ω, h ω (rotDiff n θ w ρ).1 ^ 2 ∂P) =
              logCov (rotDiff n θ w ρ).1 (rotDiff n θ w ρ).1 :=
            (integral_sq_pair hh _).2
          _ ≤ 4 * ((2 : ℝ)⁻¹ ^ n / ρ) := logCov_rotDiff_le n θ hρ w
          _ = (4 / ρ) * (2 : ℝ)⁻¹ ^ n := by ring)
  have hhr := MatedCRTHarmonic.IGLaw.IsWholePlaneGFF.rotateField hh θ
  filter_upwards [ae_tendsto_mollAvg hhr w hρ,
    ae_tendsto_mollAvg hh (Complex.exp (θ * Complex.I) * w) hρ,
    hE] with ω ⟨a, ha⟩ ⟨b, hb⟩ hω
  rw [circleAvg_eq_of_tendsto ha, circleAvg_eq_of_tendsto hb]
  have hd : Tendsto (fun n =>
      mollAvg (MatedCRTHarmonic.MoTPort.rotateField θ (h ω)) n w ρ -
        mollAvg (h ω) n (Complex.exp (θ * Complex.I) * w) ρ)
      atTop (𝓝 0) := by
    refine hω.congr fun n => ?_
    rw [mollAvg_eq, mollAvg_eq]
    change h ω (rotTest θ (circBump n w ρ) -
      circBump n (Complex.exp (θ * Complex.I) * w) ρ) = _
    rw [map_sub]
    rfl
  have he := tendsto_nhds_unique (ha.sub hb) hd
  linarith

private lemma continuous_circleParam : Continuous fun q : Fin 4 → ℝ =>
    (MatedCRTHarmonic.LQGCoord.kR q, MatedCRTHarmonic.LQGCoord.kW q) := by
  unfold MatedCRTHarmonic.LQGCoord.kR MatedCRTHarmonic.LQGCoord.kW
  refine (Real.continuous_exp.comp (continuous_apply 3)).prodMk ?_
  have e : (fun q : Fin 4 → ℝ => (⟨q 1, q 2⟩ : ℂ)) =
      fun q => (q 1 : ℂ) + (q 2 : ℂ) * Complex.I := by
    funext q
    exact Complex.mk_eq_add_mul_I _ _
  rw [e]
  fun_prop

private lemma continuous_circleParamR (R : ℂ) : Continuous fun q : Fin 4 → ℝ =>
    (MatedCRTHarmonic.LQGCoord.kR q, R * MatedCRTHarmonic.LQGCoord.kW q) :=
  continuous_circleParam.fst.prodMk (continuous_const.mul continuous_circleParam.snd)

private lemma circleProc_ext_rotation (R : ℂ) (f g : ℝ → ℂ → ℝ)
    (hf : ContinuousOn (fun p : ℝ × ℂ => f p.1 p.2) (Ioi 0 ×ˢ univ))
    (hg : ContinuousOn (fun p : ℝ × ℂ => g p.1 p.2) (Ioi 0 ×ˢ univ))
    (hc : ∀ q : MatedCRTHarmonic.LQGCoord.kDense,
      f (MatedCRTHarmonic.LQGCoord.kR q.1) (MatedCRTHarmonic.LQGCoord.kW q.1) =
      g (MatedCRTHarmonic.LQGCoord.kR q.1) (R * MatedCRTHarmonic.LQGCoord.kW q.1)) :
    ∀ ρ : ℝ, 0 < ρ → ∀ w : ℂ, f ρ w = g ρ (R * w) := by
  let E : Set (Fin 4 → ℝ) := {q | q 0 ≠ 0}
  have hleft : ContinuousOn (fun q : Fin 4 → ℝ =>
      f (MatedCRTHarmonic.LQGCoord.kR q) (MatedCRTHarmonic.LQGCoord.kW q)) E :=
    hf.comp continuous_circleParam.continuousOn (fun q _ =>
      ⟨MatedCRTHarmonic.LQGCoord.kR_pos q, mem_univ _⟩)
  have hright : ContinuousOn (fun q : Fin 4 → ℝ =>
      g (MatedCRTHarmonic.LQGCoord.kR q)
        (R * MatedCRTHarmonic.LQGCoord.kW q)) E :=
    hg.comp (continuous_circleParamR R).continuousOn (fun q _ =>
      ⟨MatedCRTHarmonic.LQGCoord.kR_pos q, mem_univ _⟩)
  have heq : EqOn (fun q : Fin 4 → ℝ =>
      f (MatedCRTHarmonic.LQGCoord.kR q) (MatedCRTHarmonic.LQGCoord.kW q))
      (fun q => g (MatedCRTHarmonic.LQGCoord.kR q)
        (R * MatedCRTHarmonic.LQGCoord.kW q)) E := by
    refine EqOn.of_subset_closure (s := MatedCRTHarmonic.LQGCoord.kDense)
      (fun q hq => hc ⟨q, hq⟩) hleft hright
      (fun q hq => hq.1) MatedCRTHarmonic.LQGCoord.subset_closure_kDense
  intro ρ hρ w
  let q : Fin 4 → ℝ := ![1, w.re, w.im, Real.log ρ]
  have hq : q ∈ E := by simp [q, E]
  have hqr : MatedCRTHarmonic.LQGCoord.kR q = ρ := by
    simp [MatedCRTHarmonic.LQGCoord.kR, q, Real.exp_log hρ]
  have hqw : MatedCRTHarmonic.LQGCoord.kW q = w := by
    simp [MatedCRTHarmonic.LQGCoord.kW, q, Complex.eta]
  simpa only [hqr, hqw] using heq hq

/-- One event gives rotation covariance at every positive radius and every centre. -/
theorem rotCircleAvgCovarianceAll_holds : RotCircleAvgCovarianceAll := by
  intro Ω _ P h hh θ
  let R : ℂ := Complex.exp (θ * Complex.I)
  have hRgood := MatedCRTHarmonic.LQGCoord.ae_tendsto_mollAvgS_circleAvg
    (MatedCRTHarmonic.IGLaw.IsWholePlaneGFF.rotateField hh θ)
  have hgood := MatedCRTHarmonic.LQGCoord.ae_tendsto_mollAvgS_circleAvg hh
  have : Countable MatedCRTHarmonic.LQGCoord.kDense :=
    MatedCRTHarmonic.LQGCoord.kDense_countable.to_subtype
  have hcount : ∀ᵐ ω ∂P, ∀ q : MatedCRTHarmonic.LQGCoord.kDense,
      circleAvg (MatedCRTHarmonic.MoTPort.rotateField θ (h ω))
        (MatedCRTHarmonic.LQGCoord.kR q.1) (MatedCRTHarmonic.LQGCoord.kW q.1) =
      circleAvg (h ω) (MatedCRTHarmonic.LQGCoord.kR q.1)
        (R * MatedCRTHarmonic.LQGCoord.kW q.1) := by
    apply ae_all_iff.2
    intro q
    exact rotCircleAvgCovariance_fixed hh θ
      (MatedCRTHarmonic.LQGCoord.kR_pos q.1) (MatedCRTHarmonic.LQGCoord.kW q.1)
  filter_upwards [hRgood, hgood, hcount] with ω hrg hg hc
  exact circleProc_ext_rotation R _ _ hrg.1 hg.1 hc

/-- The fixed-circle form used for the curve-law invariance. -/
theorem rotCircleAvgCovariance_holds : RotCircleAvgCovariance :=
  rotCircleAvgCovariance_of_all rotCircleAvgCovarianceAll_holds

/-- Positive affine changes of coordinates act on all circle averages on one event. -/
theorem ae_circleAvg_affineComp_all {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {h : Ω → DistC} (hh : IsWholePlaneGFF h P) {s : ℝ} (hs : 0 < s) (b : ℂ) :
    ∀ᵐ ω ∂P, ∀ ρ : ℝ, 0 < ρ → ∀ w : ℂ,
      circleAvg (affineComp s b (h ω)) ρ w =
        circleAvg (h ω) (s * ρ) ((s : ℂ) * w + b) := by
  filter_upwards [MatedCRTHarmonic.LQGCoord.ae_tendsto_mollAvgS_circleAvg hh]
    with ω hω ρ hρ w
  have ht := hω.2 (s * ρ) (mul_pos hs hρ) ((s : ℂ) * w + b)
  simpa only [add_zero, LQGMetric.GFFLaw.addConst_zero'] using
    (MatedCRTHarmonic.LQGCoord.circleAvg_addConst_affineComp_of_tendsto hs 0 ht)

/-- The circle-average process of `h(s e^{iθ}·+b)` is the pullback of the process of `h`,
simultaneously for every positive radius and centre. -/
theorem ae_circleAvg_affineRotate_all {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    {h : Ω → DistC} (hh : IsWholePlaneGFF h P) (θ : ℝ) {s : ℝ} (hs : 0 < s) (b : ℂ) :
    ∀ᵐ ω ∂P, ∀ ρ : ℝ, 0 < ρ → ∀ w : ℂ,
      circleAvg (MatedCRTHarmonic.MoTPort.rotateField θ (affineComp s b (h ω))) ρ w =
        circleAvg (h ω) (s * ρ)
          ((s : ℂ) * Complex.exp (θ * Complex.I) * w + b) := by
  have haff : IsWholePlaneGFF (fun ω => affineComp s b (h ω)) P := hh.affineComp hs b
  have hrot : ∀ᵐ ω ∂P, ∀ ρ : ℝ, 0 < ρ → ∀ w : ℂ,
      circleAvg (MatedCRTHarmonic.MoTPort.rotateField θ (affineComp s b (h ω))) ρ w =
        circleAvg (affineComp s b (h ω)) ρ (Complex.exp (θ * Complex.I) * w) :=
    rotCircleAvgCovarianceAll_holds (P := P)
      (h := fun ω => affineComp s b (h ω)) haff θ
  filter_upwards [hrot, ae_circleAvg_affineComp_all hh hs b]
    with ω hrotω hscale ρ hρ w
  rw [hrotω ρ hρ w, hscale ρ hρ (Complex.exp (θ * Complex.I) * w)]
  congr 1
  ring

end MatedCRTHarmonic.IGLaw
