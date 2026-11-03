/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.LM.L3_4N1 at commit 31e7483; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.LM.L3_4Incr
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S2.SpatialIndepOsc

/-!
# LM Lemma 3.4, increment input: the oscillation functional and two Gaussian facts

Source: MQ arXiv:1812.03913 (`lqg_geodesics.tex`), proof of Lemma 4.4 (l. 633–657: the
oscillation of a harmonic function on a smaller ball is bounded by an average of
`|𝔥(y) − 𝔥(0)|`, then Jensen's inequality and the Gaussian law of `𝔥(y) − 𝔥(0)`), and Remark
eq. `(zero-boundary)` (l. 659–667, the same for the harmonic part of a zero-boundary GFF).

MQ average over a circle with the Poisson kernel; we average over a disc with the mean value
property (`GM.abs_sub_le_integral_of_harmonic`, as in `GM.prob_oscEv_le`), and we bound the
exponential moment (not the Gaussian-square moment), which is what LM Lemma 3.4 needs.

* `nestPhi` — `Φ(T) = ∫_{B̄_ρ(0)} |T(ψ_y − ψ_0)| dy` (`ψ_y = radBump δ y`), measurable in `T`.
* `osc_le_nestPhi` — if `T = d` on `B_1` with `d` harmonic, then
  `|d(u) − d(0)| ≤ oscC δ · Φ(T)` for `|u| < ρ − δ`, `ρ + δ < 1`.
* `lintegral_exp_le_of_indepFun` — `E e^X ≤ E e^{X+Z}` for `Z` independent of `X`, centred.
* `lintegral_exp_gauss` — `E e^{tY} = e^{t² Var Y/2}` for a centred Gaussian `Y`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Metric InnerProductSpace
open scoped ENNReal

namespace LQGMetric.LM

open Blueprint GM

/-- `Φ(T) = ∫_{B̄_ρ(0)} |T(ψ_y − ψ_0)| dy` -/
def nestPhi {δ : ℝ} (hδ : 0 ≤ δ) (ρ : ℝ) (T : DistC) : ℝ :=
  (∫⁻ y in closedBall (0 : ℂ) ρ, ENNReal.ofReal |T (radDiff hδ y 0).1|).toReal

lemma measurable_pair_radDiff {δ : ℝ} (hδ : 0 ≤ δ) :
    Measurable fun p : DistC × ℂ => p.1 (radDiff hδ p.2 0).1 := by
  have h1 := measurable_apply_radBump δ hδ
  have h2 : Measurable fun p : DistC × ℂ => p.1 (radBump δ hδ 0) :=
    h1.comp (measurable_fst.prodMk measurable_const)
  have : (fun p : DistC × ℂ => p.1 (radDiff hδ p.2 0).1) =
      fun p => p.1 (radBump δ hδ p.2) - p.1 (radBump δ hδ 0) := by
    funext p; simp only [radDiff, map_sub]
  rw [this]; exact h1.sub h2

lemma measurable_nestPhi {δ : ℝ} (hδ : 0 ≤ δ) (ρ : ℝ) : Measurable (nestPhi hδ ρ) :=
  (ENNReal.measurable_ofReal.comp (continuous_abs.measurable.comp
    (measurable_pair_radDiff hδ))).lintegral_prod_right'.ennreal_toReal

lemma continuous_pair_radDiff {δ : ℝ} (hδ : 0 ≤ δ) (T : DistC) :
    Continuous fun y => T (radDiff hδ y 0).1 := by
  have : (fun y => T (radDiff hδ y 0).1) = fun y => T (radBump δ hδ y) - T (radBump δ hδ 0) := by
    funext y; simp only [radDiff, map_sub]
  rw [this]
  exact ((map_continuous T).comp (continuous_radBump δ hδ)).sub continuous_const

lemma nestPhi_eq {δ : ℝ} (hδ : 0 ≤ δ) (ρ : ℝ) (T : DistC) :
    nestPhi hδ ρ T = ∫ y in closedBall (0 : ℂ) ρ, |T (radDiff hδ y 0).1| := by
  have hint : IntegrableOn (fun y => |T (radDiff hδ y 0).1|) (closedBall (0 : ℂ) ρ) :=
    (continuous_pair_radDiff hδ T).abs.continuousOn.integrableOn_compact (isCompact_closedBall _ _)
  rw [nestPhi, ← ofReal_integral_eq_lintegral_ofReal hint
    (Eventually.of_forall fun y => abs_nonneg _), ENNReal.toReal_ofReal
    (integral_nonneg fun y => abs_nonneg _)]

lemma nestPhi_nonneg {δ : ℝ} (hδ : 0 ≤ δ) (ρ : ℝ) (T : DistC) : 0 ≤ nestPhi hδ ρ T :=
  ENNReal.toReal_nonneg

/-- **Oscillation bound** (MQ l. 640–648, disc form): if `T = d` on `B_1(0)` with `d`
harmonic, then `|d(u) − d(0)| ≤ oscC δ · Φ(T)` for `|u| + δ ≤ ρ`, `ρ + δ < 1`. -/
theorem osc_le_nestPhi {δ ρ : ℝ} (hδ : 0 < δ) (hρ1 : ρ + δ < 1) {T : DistC} {d : ℂ → ℝ}
    (hd : HarmonicOnNhd d (ball (0 : ℂ) 1))
    (hrep : ∀ φ : TestOn (ballO 0 1), restrictTo (ballO 0 1) T φ = ∫ x, d x * φ x)
    {u : ℂ} (hu : ‖u‖ + δ ≤ ρ) : |d u - d 0| ≤ oscC δ * nestPhi hδ.le ρ T := by
  have hI := integral_radProf_pos hδ
  set I := ∫ y, radProf δ y
  have hρ : 0 ≤ ρ := by linarith [norm_nonneg u]
  have hgc : ∀ y ∈ closedBall (0 : ℂ) ρ, closedBall y δ ⊆ ((ballO 0 1 : TopologicalSpace.Opens ℂ) : Set ℂ) :=
    fun y hy w hw => by
      rw [mem_closedBall] at hy hw
      show w ∈ ball (0 : ℂ) 1
      rw [mem_ball]; linarith [dist_triangle w y 0]
  have hd' : HarmonicOnNhd d ((ballO 0 1 : TopologicalSpace.Opens ℂ) : Set ℂ) := hd
  have hval : ∀ y ∈ closedBall (0 : ℂ) ρ, |d y - d 0| = |T (radDiff hδ.le y 0).1| / I := by
    intro y hy
    have e1 := pair_radBump_of_harmonic (V := ballO 0 1) hd' hrep hδ (hgc y hy)
    have e2 := pair_radBump_of_harmonic (V := ballO 0 1) hd' hrep hδ
      (hgc 0 (mem_closedBall_self hρ))
    have : T (radDiff hδ.le y 0).1 = T (radBump δ hδ.le y) - T (radBump δ hδ.le 0) := by
      simp only [radDiff, map_sub]
    rw [this, e1, e2, ← sub_mul, abs_mul, abs_of_pos hI, mul_div_cancel_right₀ _ hI.ne']
  have hint : IntegrableOn (fun y => |T (radDiff hδ.le y 0).1|) (closedBall (0 : ℂ) ρ) :=
    (continuous_pair_radDiff hδ.le T).abs.continuousOn.integrableOn_compact
      (isCompact_closedBall _ _)
  have hub : closedBall u δ ⊆ closedBall (0 : ℂ) ρ := fun w hw => by
    rw [mem_closedBall] at hw ⊢
    have := dist_triangle w u 0
    rw [dist_zero_right, dist_zero_right] at this
    rw [dist_zero_right]
    linarith
  have hstep := abs_sub_le_integral_of_harmonic isOpen_ball hd hδ
    (hub.trans (closedBall_subset_ball (by linarith))) (d 0)
  have hmono : ∫ y in closedBall u δ, |d y - d 0| ≤
      ∫ y in closedBall (0 : ℂ) ρ, |T (radDiff hδ.le y 0).1| / I := by
    calc ∫ y in closedBall u δ, |d y - d 0|
          = ∫ y in closedBall u δ, |T (radDiff hδ.le y 0).1| / I :=
          setIntegral_congr_fun measurableSet_closedBall fun y hy => hval y (hub hy)
      _ ≤ _ := setIntegral_mono_set (hint.div_const I)
          (Eventually.of_forall fun y => div_nonneg (abs_nonneg _) hI.le)
          (Eventually.of_forall hub)
  rw [integral_div] at hmono
  rw [nestPhi_eq]
  calc |d u - d 0| ≤ expNegInvGlue (δ ^ 2) / I *
        ((∫ y in closedBall (0 : ℂ) ρ, |T (radDiff hδ.le y 0).1|) / I) :=
        hstep.trans (mul_le_mul_of_nonneg_left hmono (by
          have := expNegInvGlue.nonneg (δ ^ 2); positivity))
    _ = _ := by unfold oscC; ring

/-- **`E e^X ≤ E e^{X+Z}`** for `Z` independent of `X`, integrable and centred
(`E e^{X+Z} = E e^X · E e^Z` and `E e^Z ≥ e^{E Z} = 1` by Jensen). -/
theorem lintegral_exp_le_of_indepFun {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {X Z : Ω → ℝ} (hX : Measurable X) (hZ : Measurable Z)
    (hXZ : IndepFun X Z P) (hZi : Integrable Z P) (hZ0 : ∫ ω, Z ω ∂P = 0) :
    ∫⁻ ω, ENNReal.ofReal (Real.exp (X ω)) ∂P ≤
      ∫⁻ ω, ENNReal.ofReal (Real.exp (X ω + Z ω)) ∂P := by
  have hm : ∀ {f : Ω → ℝ}, Measurable f → Measurable fun ω => ENNReal.ofReal (Real.exp (f ω)) :=
    fun hf => ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp hf)
  have hind : IndepFun (fun ω => ENNReal.ofReal (Real.exp (X ω)))
      (fun ω => ENNReal.ofReal (Real.exp (Z ω))) P :=
    hXZ.comp (ENNReal.measurable_ofReal.comp Real.measurable_exp)
      (ENNReal.measurable_ofReal.comp Real.measurable_exp)
  have hprod : ∫⁻ ω, ENNReal.ofReal (Real.exp (X ω + Z ω)) ∂P =
      (∫⁻ ω, ENNReal.ofReal (Real.exp (X ω)) ∂P) * ∫⁻ ω, ENNReal.ofReal (Real.exp (Z ω)) ∂P := by
    rw [← lintegral_mul_eq_lintegral_mul_lintegral_of_indepFun (hm hX) (hm hZ) hind]
    congr 1; funext ω
    simp only [Pi.mul_apply, Real.exp_add]
    rw [ENNReal.ofReal_mul (Real.exp_pos _).le]
  have h1 : 1 ≤ ∫⁻ ω, ENNReal.ofReal (Real.exp (Z ω)) ∂P := by
    by_cases hi : Integrable (fun ω => Real.exp (Z ω)) P
    · rw [← ofReal_integral_eq_lintegral_ofReal hi
        (Eventually.of_forall fun ω => (Real.exp_pos _).le)]
      have hJ := ConvexOn.map_integral_le (s := univ) (g := Real.exp) convexOn_exp
        Real.continuous_exp.continuousOn isClosed_univ (Eventually.of_forall fun _ => mem_univ _)
        hZi hi
      rw [hZ0, Real.exp_zero] at hJ
      rw [← ENNReal.ofReal_one]
      exact ENNReal.ofReal_le_ofReal hJ
    · have : ∫⁻ ω, ENNReal.ofReal (Real.exp (Z ω)) ∂P = ∞ := by
        by_contra hne
        exact hi ⟨(Real.measurable_exp.comp hZ).aestronglyMeasurable, by
          rw [hasFiniteIntegral_iff_ofReal (Eventually.of_forall fun ω => (Real.exp_pos _).le)]
          exact lt_top_iff_ne_top.2 hne⟩
      rw [this]; exact le_top
  rw [hprod]
  calc ∫⁻ ω, ENNReal.ofReal (Real.exp (X ω)) ∂P
      = (∫⁻ ω, ENNReal.ofReal (Real.exp (X ω)) ∂P) * 1 := (mul_one _).symm
    _ ≤ _ := by gcongr

/-- **Gaussian exponential moment**: `E e^{tY} = e^{t² Var Y/2}` for a centred Gaussian `Y`. -/
theorem lintegral_exp_gauss {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {Y : Ω → ℝ} (hY : HasGaussianLaw Y P) (hY0 : ∫ ω, Y ω ∂P = 0)
    (t : ℝ) : ∫⁻ ω, ENNReal.ofReal (Real.exp (t * Y ω)) ∂P =
      ENNReal.ofReal (Real.exp (Var[Y; P] * t ^ 2 / 2)) := by
  have hlaw : HasLaw Y (gaussianReal 0 Var[Y; P].toNNReal) P :=
    ⟨hY.aemeasurable, by rw [hY.map_eq_gaussianReal, hY0]⟩
  have hmgf := mgf_gaussianReal hlaw t
  have hv : ((Var[Y; P].toNNReal : NNReal) : ℝ) = Var[Y; P] :=
    Real.coe_toNNReal _ (variance_nonneg _ _)
  rw [hv, zero_mul, zero_add] at hmgf
  have hi : Integrable (fun ω => Real.exp (t * Y ω)) P := by
    rw [← mgf_pos_iff, hmgf]; exact Real.exp_pos _
  rw [← ofReal_integral_eq_lintegral_ofReal hi
    (Eventually.of_forall fun ω => (Real.exp_pos _).le), ← hmgf]
  rfl

end LQGMetric.LM
