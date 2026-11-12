/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module MatedCRTHarmonic.LQGCoord.ScaleBump at commit fdb5cad; only the module paths of local imports are changed.
   Declarations, examples and checks that the copied results do not use are omitted. -/
import LatticeProb.Bonanno.LQGMetric.Field.CircleAvgKolm
import LatticeProb.Bonanno.LQGMetric.Field.CircleAvgAffine

/-!
# Mollifiers at an arbitrary scale and their circle averages

LQGMetric defines the circle average `circleAvg h r z` as
the limit of the circle averages of the mollified field `x ↦ h(ψ_{n,x})` along the **dyadic**
mollifier scales `2^{-n}` (`LQGMetric.circleAvg`). The field `h(r · + z)` sees the
mollifiers of `h` at the scales `r 2^{-n}`; to compare `circleAvg (affineComp r z h)` with
`circleAvg h` for **every** `r > 0` at once we need the mollified circle averages at an arbitrary
scale `s > 0`. This file sets up the deterministic objects:

* `bumpS s x = s⁻² ψ₀((· − x)/s)`, the mollifier at scale `s` (LQGMetric's `affTest s x ψ₀`,
  `ψ₀ = bumpTest 0 0`); `bumpS 2^{-n} x = bumpTest n x` (`bumpS_dyadic`), and the affine rule
  `h(r·+z)` paired with `bumpS s x` is `h` paired with `bumpS (rs) (rx + z)` (`affineComp_bumpS`);
* `circBumpS s w ρ`, the circle average of `x ↦ bumpS s x` over `∂B(w, ρ)` as a test function, with
  `⨍_{∂B(w,ρ)} T(bumpS s ·) = T(circBumpS s w ρ)` for every distribution `T`
  (`circleAverage_pairingS`, via LQGMetric's `TestIntegral.exists_testIntegral`);
* its log potential `logPot (circBumpS s w ρ) x = −∫ ψ₀(v) g_{w,ρ}(x − s v) dv`
  (`logPot_circBumpS'`) and the Lipschitz bound
  `|logPot Φ − logPot Φ'| ≤ (|s − s'| + |ρ − ρ'| + ‖w − w'‖)/min ρ ρ'`, hence the variance bound
  `logCov D D ≤ 2 (|s − s'| + |ρ − ρ'| + ‖w − w'‖)/min ρ ρ'` for `D = Φ − Φ'`
  (`logCov_circDiffS_le`).

The proofs copy LQGMetric's `CircleAvgPairing`, `CircleAvgVar` and `CircleAvgRate` with the
dyadic mollifier `bumpTest k 0` replaced by `bumpS s 0` (Duplantier–Sheffield arXiv:0808.1560
§3.1: the circle average is the pairing with the circle measure; the mollified version converges
to it with a rate linear in the mollifier scale).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Filter Topology Set Metric TopologicalSpace
open scoped Distributions BoundedContinuousFunction Real

namespace MatedCRTHarmonic.LQGCoord

open LQGMetric LQGMetric.CircleAvg LQGMetric.TestIntegral

/-! ## The mollifier at scale `s` -/

/-- The unit mollifier `ψ₀ = bumpTest 0 0` (normalized smooth bump with radii `1/2, 1`). -/
abbrev psi0 : TestC := bumpTest 0 0

/-- The mollifier at scale `s` centred at `x`: `y ↦ s⁻² ψ₀((y − x)/s)` (LQGMetric's `affTest`;
junk `0` for `s = 0`). -/
def bumpS (s : ℝ) (x : ℂ) : TestC := affTest s x psi0

lemma bumpS_apply {s : ℝ} (hs : s ≠ 0) (x y : ℂ) :
    bumpS s x y = (s ^ 2)⁻¹ * psi0 ((y - x) / s) := by
  simp [bumpS, affTest, testAffinePull_apply s x hs]

lemma bumpS_zero (x : ℂ) : bumpS 0 x = 0 := by
  ext y
  simp [bumpS, affTest, testAffinePull]

lemma psi0_eq_zero {v : ℂ} (hv : 1 ≤ ‖v‖) : psi0 v = 0 :=
  bumpTest_eq_zero 0 (by rwa [dist_zero_right])

lemma psi0_nonneg (v : ℂ) : 0 ≤ psi0 v := bumpTest_nonneg 0 0 v

lemma integral_psi0 : ∫ v, psi0 v = 1 := integral_bumpTest' 0 0

lemma bumpS_nonneg (s : ℝ) (x y : ℂ) : 0 ≤ bumpS s x y := by
  rcases eq_or_ne s 0 with rfl | hs
  · rw [bumpS_zero]; simp
  · rw [bumpS_apply hs]; exact mul_nonneg (by positivity) (psi0_nonneg _)

lemma bumpS_eq_zero (s : ℝ) {x y : ℂ} (h : |s| ≤ dist y x) : bumpS s x y = 0 := by
  rcases eq_or_ne s 0 with rfl | hs
  · rw [bumpS_zero]; simp
  · rw [bumpS_apply hs, psi0_eq_zero, mul_zero]
    rw [norm_div, Complex.norm_real, Real.norm_eq_abs, le_div_iff₀ (abs_pos.mpr hs), one_mul,
      ← dist_eq_norm]
    exact h

lemma integral_bumpS {s : ℝ} (hs : 0 < s) (x : ℂ) : ∫ y, bumpS s x y = 1 := by
  rw [bumpS, integral_affTest hs, integral_psi0]

/-- translation structure of the scale-`s` mollifiers -/
lemma bumpS_eq_sub (s : ℝ) (x y : ℂ) : bumpS s x y = bumpS s 0 (y - x) := by
  rcases eq_or_ne s 0 with rfl | hs
  · simp [bumpS_zero]
  · rw [bumpS_apply hs, bumpS_apply hs, sub_zero]

/-- The dyadic mollifiers are the scale-`2^{-n}` mollifiers. -/
lemma bumpS_dyadic (n : ℕ) (x : ℂ) : bumpS ((2 : ℝ)⁻¹ ^ n) x = bumpTest n x := by
  set s : ℝ := (2 : ℝ)⁻¹ ^ n with hs_def
  have hs : 0 < s := by positivity
  -- pointwise proportionality of the two unnormalized bumps
  have hbase : ∀ y, bumpAt n x y = bumpAt 0 0 ((y - x) / s) := by
    intro y
    rw [ContDiffBump.apply, ContDiffBump.apply]
    simp only [bumpAt, sub_zero]
    congr 1
    · rw [pow_succ]; field_simp; norm_num
    · simp only [Complex.real_smul, hs_def]
      push_cast
      field_simp
      ring
  have hI0 : 0 < ∫ v, bumpAt 0 0 v := (bumpAt 0 0).integral_pos
  have hprop : ∀ y, bumpS s x y = ((s ^ 2)⁻¹ / ∫ v, bumpAt 0 0 v) * bumpAt n x y := by
    intro y
    rw [bumpS_apply hs.ne', hbase, bumpTest_apply, ContDiffBump.normed_def]
    ring
  have hint : ∫ y, bumpS s x y = ((s ^ 2)⁻¹ / ∫ v, bumpAt 0 0 v) * ∫ y, bumpAt n x y := by
    simp_rw [hprop]
    rw [integral_const_mul]
  rw [integral_bumpS hs] at hint
  have hIn : 0 < ∫ y, bumpAt n x y := (bumpAt n x).integral_pos
  ext y
  rw [hprop, bumpTest_apply, ContDiffBump.normed_def]
  have hc : (s ^ 2)⁻¹ / ∫ v, bumpAt 0 0 v = 1 / ∫ y, bumpAt n x y := by
    field_simp at hint ⊢
    linarith
  rw [hc]
  ring

/-- **Affine rule.** `h(r·+z)` paired with `bumpS s x` is `h` paired with `bumpS (rs) (rx + z)`. -/
lemma affineComp_bumpS (g : DistC) {r s : ℝ} (hr : 0 < r) (hs : 0 < s) (z x : ℂ) :
    affineComp r z g (bumpS s x) = g (bumpS (r * s) ((r : ℂ) * x + z)) := by
  rw [affineComp]
  show (r ^ 2)⁻¹ * g (testAffinePull r z (bumpS s x)) = _
  rw [← smul_eq_mul, ← map_smul]
  congr 1
  ext y
  rw [bumpS_apply (mul_pos hr hs).ne']
  have hval : ((r ^ 2)⁻¹ • testAffinePull r z (bumpS s x)) y =
      (r ^ 2)⁻¹ * bumpS s x ((y - z) / r) := by
    simp [testAffinePull_apply r z hr.ne']
  rw [hval, bumpS_apply hs.ne']
  have hr' : (r : ℂ) ≠ 0 := by exact_mod_cast hr.ne'
  have hs' : (s : ℂ) ≠ 0 := by exact_mod_cast hs.ne'
  rw [show ((y - z) / (r : ℂ) - x) / (s : ℂ) = (y - ((r : ℂ) * x + z)) / ((r * s : ℝ) : ℂ) by
    push_cast; field_simp; ring]
  rw [mul_pow, mul_inv]
  ring

/-! ## Circle averages of the scale-`s` mollifiers as test functions -/

/-- the compact `closedBall w (|ρ| + |s|)` -/
def ballKS (w : ℂ) (ρ s : ℝ) : Compacts ℂ :=
  ⟨closedBall w (|ρ| + |s|), isCompact_closedBall _ _⟩

lemma support_bumpS_circle (s : ℝ) (w : ℂ) (ρ θ : ℝ) :
    Function.support (bumpS s (circleMap w ρ θ)) ⊆ (ballKS w ρ s : Set ℂ) := by
  intro y hy
  by_contra hK
  apply hy
  apply bumpS_eq_zero
  have h1 : |ρ| + |s| < dist y w := by simpa [ballKS] using hK
  have h2 : dist (circleMap w ρ θ) w = |ρ| := by simp [dist_eq_norm, circleMap_sub_center]
  linarith [dist_triangle y (circleMap w ρ θ) w]

/-- the curve `θ ↦ bumpS s (w + ρ e^{iθ})` in `𝓓_K` -/
def bumpCurveS (s : ℝ) (w : ℂ) (ρ : ℝ) (θ : ℝ) : 𝓓^{⊤}_{ballKS w ρ s}(ℂ, ℝ) :=
  ContDiffMapSupportedIn.of_support_subset (bumpS s (circleMap w ρ θ)).contDiff
    (support_bumpS_circle s w ρ θ)

lemma iteratedFDeriv_bumpS (s : ℝ) (x : ℂ) (i : ℕ) (y : ℂ) :
    iteratedFDeriv ℝ i (bumpS s x) y = iteratedFDeriv ℝ i (bumpS s 0) (y - x) := by
  have : (bumpS s x : ℂ → ℝ) = fun y => bumpS s 0 (y + -x) := by
    funext y; rw [bumpS_eq_sub, sub_eq_add_neg]
  rw [this, iteratedFDeriv_comp_add_right, sub_eq_add_neg]

lemma continuous_bumpCurveS (s : ℝ) (w : ℂ) (ρ : ℝ) : Continuous (bumpCurveS s w ρ) := by
  rw [ContDiffMapSupportedIn.continuous_iff_comp]
  intro i
  set G := iteratedFDeriv ℝ i (bumpS s 0 : ℂ → ℝ)
  have hGc : Continuous G := (bumpS s 0).contDiff.continuous_iteratedFDeriv
    (by exact_mod_cast le_top)
  have hGu : UniformContinuous G :=
    ((bumpS s 0).hasCompactSupport.iteratedFDeriv i).uniformContinuous_of_continuous hGc
  have hval : ∀ θ y, (ContDiffMapSupportedIn.structureMapCLM ℝ ⊤ i (bumpCurveS s w ρ θ)) y =
      G (y - circleMap w ρ θ) := by
    intro θ y
    rw [ContDiffMapSupportedIn.structureMapCLM_top_apply]
    exact iteratedFDeriv_bumpS s _ i y
  rw [Metric.continuous_iff]
  intro θ₀ ε hε
  obtain ⟨δ, hδ, hG⟩ := Metric.uniformContinuous_iff.mp hGu (ε / 2) (by positivity)
  obtain ⟨η, hη, hc⟩ := Metric.continuous_iff.mp (continuous_circleMap w ρ) θ₀ δ hδ
  refine ⟨η, hη, fun θ hθ => ?_⟩
  refine lt_of_le_of_lt ((BoundedContinuousFunction.dist_le (by positivity)).mpr fun y => ?_)
    (half_lt_self hε)
  simp only [Function.comp_apply, hval]
  refine (hG ?_).le
  rw [dist_eq_norm, sub_sub_sub_cancel_left, ← dist_eq_norm']
  exact hc θ hθ

lemma bumpCurveS_eq (s : ℝ) (w : ℂ) (ρ θ : ℝ) :
    TestFunction.ofSupportedIn (subset_univ _) (bumpCurveS s w ρ θ) =
      bumpS s (circleMap w ρ θ) := by
  ext y; rfl

lemma exists_circBumpS (s : ℝ) (w : ℂ) (ρ : ℝ) :
    ∃ I : 𝓓^{⊤}_{ballKS w ρ s}(ℂ, ℝ),
      (∀ y, I y = ∫ θ in (0 : ℝ)..2 * Real.pi, bumpCurveS s w ρ θ y) ∧
      ∀ T : 𝓓^{⊤}_{ballKS w ρ s}(ℂ, ℝ) →L[ℝ] ℝ,
        T I = ∫ θ in (0 : ℝ)..2 * Real.pi, T (bumpCurveS s w ρ θ) :=
  exists_testIntegral 0 (2 * Real.pi) (continuous_bumpCurveS s w ρ)

/-- `σ_{w,ρ} * ψ_s` as a test function: the circle average over `∂B(w, ρ)` of `x ↦ bumpS s x`. -/
def circBumpS (s : ℝ) (w : ℂ) (ρ : ℝ) : TestC :=
  (2 * Real.pi)⁻¹ • TestFunction.ofSupportedIn (subset_univ _) (exists_circBumpS s w ρ).choose

lemma circBumpS_apply (s : ℝ) (w : ℂ) (ρ : ℝ) (y : ℂ) :
    circBumpS s w ρ y = Real.circleAverage (fun x => bumpS s x y) w ρ := by
  rw [Real.circleAverage_def]
  show (2 * Real.pi)⁻¹ * (exists_circBumpS s w ρ).choose y = _
  rw [(exists_circBumpS s w ρ).choose_spec.1 y, smul_eq_mul]
  rfl

lemma comp_bumpCurveS (T : DistC) (s : ℝ) (w : ℂ) (ρ θ : ℝ) :
    (T.comp (TestFunction.ofSupportedInCLM ℝ (subset_univ _))) (bumpCurveS s w ρ θ) =
      T (bumpS s (circleMap w ρ θ)) := by
  show T (TestFunction.ofSupportedIn (subset_univ _) (bumpCurveS s w ρ θ)) = _
  rw [bumpCurveS_eq]

/-- **Circle averages of the scale-`s` mollified field are pairings.** -/
theorem circleAverage_pairingS (T : DistC) (s : ℝ) (w : ℂ) (ρ : ℝ) :
    Real.circleAverage (fun x => T (bumpS s x)) w ρ = T (circBumpS s w ρ) := by
  rw [circBumpS, map_smul, Real.circleAverage_def]
  have := (exists_circBumpS s w ρ).choose_spec.2
    (T.comp (TestFunction.ofSupportedInCLM ℝ (subset_univ _)))
  simp_rw [comp_bumpCurveS] at this
  rw [← this]
  rfl

lemma circBumpS_nonneg (s : ℝ) (w : ℂ) (ρ : ℝ) (y : ℂ) : 0 ≤ circBumpS s w ρ y := by
  rw [circBumpS_apply, Real.circleAverage_def]
  refine mul_nonneg (by positivity) (intervalIntegral.integral_nonneg (by positivity) ?_)
  intro θ _
  exact bumpS_nonneg _ _ _

lemma integral_circBumpS {s : ℝ} (hs : 0 < s) (w : ℂ) (ρ : ℝ) : ∫ y, circBumpS s w ρ y = 1 := by
  have h := circleAverage_pairingS (ofCont (ContinuousMap.const ℂ 1)) s w ρ
  simp only [ofCont_apply, ContinuousMap.const_apply, mul_one] at h
  simp_rw [integral_bumpS hs] at h
  rw [← h, Real.circleAverage_const]

/-- The mollified circle average of `T` at scale `s`: `⨍_{∂B(w,ρ)} T(bumpS s ·)`. -/
def mollAvgS (T : DistC) (s : ℝ) (w : ℂ) (ρ : ℝ) : ℝ :=
  Real.circleAverage (fun x => T (bumpS s x)) w ρ

lemma mollAvgS_eq (T : DistC) (s : ℝ) (w : ℂ) (ρ : ℝ) :
    mollAvgS T s w ρ = T (circBumpS s w ρ) :=
  circleAverage_pairingS T s w ρ

lemma mollAvgS_dyadic (T : DistC) (n : ℕ) (w : ℂ) (ρ : ℝ) :
    mollAvgS T ((2 : ℝ)⁻¹ ^ n) w ρ = mollAvg T n w ρ := by
  simp only [mollAvgS, mollAvg]
  simp_rw [bumpS_dyadic]

/-- **Affine rule for the mollified circle averages:** the dyadic mollified circle averages of
`h(r · + z)` at `(w, ρ)` are those of `h` at scale `r 2^{-n}` and at `(r w + z, r ρ)`. -/
lemma mollAvg_affineComp (g : DistC) {r : ℝ} (hr : 0 < r) (z : ℂ) (n : ℕ) (w : ℂ) (ρ : ℝ) :
    mollAvg (affineComp r z g) n w ρ =
      mollAvgS g (r * (2 : ℝ)⁻¹ ^ n) ((r : ℂ) * w + z) (r * ρ) := by
  rw [← mollAvgS_dyadic]
  simp only [mollAvgS, Real.circleAverage_def]
  congr 1
  refine intervalIntegral.integral_congr fun θ _ => ?_
  rw [affineComp_bumpS g hr (by positivity)]
  congr 2
  simp only [circleMap]
  push_cast
  ring

/-! ## Log potentials and the variance of differences -/

section Fubini

variable (s : ℝ) (w : ℂ) (ρ : ℝ) (x : ℂ)

/-- the angular measure on `(0, 2π]` -/
abbrev μθS : Measure ℝ := volume.restrict (Ioc 0 (2 * π))

lemma circBumpS_eq_integral (y : ℂ) :
    circBumpS s w ρ y = (2 * π)⁻¹ * ∫ θ, bumpS s 0 (y - circleMap w ρ θ) ∂μθS := by
  rw [circBumpS_apply, Real.circleAverage_def, smul_eq_mul,
    intervalIntegral.integral_of_le (by positivity)]
  simp_rw [bumpS_eq_sub s _ y]

/-- the integrand `(θ, y) ↦ −log|x − y| ψ_s(y − w − ρ e^{iθ})` -/
def fubFS (p : ℝ × ℂ) : ℝ := -Real.log ‖x - p.2‖ * bumpS s 0 (p.2 - circleMap w ρ p.1)

/-- the integrand `(θ, t) ↦ ψ_s(t) (−log|w + ρ e^{iθ} − (x − t)|)` -/
def fubGS (p : ℝ × ℂ) : ℝ := bumpS s 0 p.2 * -Real.log ‖circleMap w ρ p.1 - (x - p.2)‖

lemma fubGS_eq (θ : ℝ) (t : ℂ) :
    fubGS s w ρ x (θ, t) = fubFS s w ρ x (θ, t + circleMap w ρ θ) := by
  simp only [fubGS, fubFS, add_sub_cancel_right]
  rw [mul_comm]
  congr 3
  rw [← norm_neg]
  congr 1
  ring

lemma measurable_fubFS : Measurable (fubFS s w ρ x) := by
  unfold fubFS
  have h1 : Continuous (bumpS s 0 : ℂ → ℝ) := (bumpS s 0).continuous
  have h2 : Continuous fun p : ℝ × ℂ => p.2 - circleMap w ρ p.1 :=
    continuous_snd.sub ((continuous_circleMap w ρ).comp continuous_fst)
  exact ((Real.measurable_log.comp (measurable_const.sub measurable_snd).norm).neg).mul
    (h1.comp h2).measurable

lemma measurable_fubGS : Measurable (fubGS s w ρ x) := by
  unfold fubGS
  have h1 : Continuous (bumpS s 0 : ℂ → ℝ) := (bumpS s 0).continuous
  have h2 : Continuous fun p : ℝ × ℂ => circleMap w ρ p.1 - (x - p.2) :=
    ((continuous_circleMap w ρ).comp continuous_fst).sub (continuous_const.sub continuous_snd)
  exact (h1.comp continuous_snd).measurable.mul (Real.measurable_log.comp h2.measurable.norm).neg

lemma integrable_fubFS : Integrable (fubFS s w ρ x) (μθS.prod volume) := by
  obtain ⟨M, hM⟩ := (bumpS s 0).continuous.bounded_above_of_compact_support
    (bumpS s 0).hasCompactSupport
  set B := closedBall w (|ρ| + |s|)
  set b : ℂ → ℝ := fun y => M * (B.indicator (fun y => ‖x - y‖) y + logBallFun (x - y))
  have hb : Integrable b := by
    refine Integrable.const_mul (Integrable.add ?_ (integrable_logBallFun.comp_sub_left x)) M
    rw [integrable_indicator_iff measurableSet_closedBall]
    exact (continuous_const.sub continuous_id).norm.continuousOn.integrableOn_compact
      (isCompact_closedBall _ _)
  refine Integrable.mono' (hb.comp_snd μθS) (measurable_fubFS s w ρ x).aestronglyMeasurable
    (Eventually.of_forall fun p => ?_)
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM 0)
  simp only [fubFS, b, norm_mul, norm_neg]
  by_cases hp : ‖p.2 - circleMap w ρ p.1‖ < |s|
  · have hpB : p.2 ∈ B := by
      have h2 : dist (circleMap w ρ p.1) w = |ρ| := by
        simp [dist_eq_norm, circleMap_sub_center]
      have h3 : dist p.2 (circleMap w ρ p.1) < |s| := by rw [dist_eq_norm]; exact hp
      rw [mem_closedBall]
      linarith [dist_triangle p.2 (circleMap w ρ p.1) w]
    rw [indicator_of_mem hpB, mul_comm]
    refine mul_le_mul (hM _) ?_ (norm_nonneg _) hM0
    rw [Real.norm_eq_abs]
    exact abs_log_norm_le (x - p.2)
  · rw [bumpS_eq_zero s (by rw [dist_zero_right]; linarith), norm_zero, mul_zero]
    have : 0 ≤ B.indicator (fun y => ‖x - y‖) p.2 + logBallFun (x - p.2) :=
      add_nonneg (indicator_nonneg (fun _ _ => norm_nonneg _) _) (logBallFun_nonneg _)
    positivity

lemma integrable_fubGS : Integrable (fubGS s w ρ x) (μθS.prod volume) := by
  have hF := integrable_fubFS s w ρ x
  rw [integrable_prod_iff (measurable_fubGS s w ρ x).aestronglyMeasurable]
  constructor
  · filter_upwards [hF.prod_right_ae] with θ hθ
    have := hθ.comp_add_right (circleMap w ρ θ)
    refine this.congr (Eventually.of_forall fun t => ?_)
    simp only [fubGS_eq]
  · refine hF.integral_norm_prod_left.congr (Eventually.of_forall fun θ => ?_)
    simp only
    rw [← integral_add_right_eq_self (fun y => ‖fubFS s w ρ x (θ, y)‖) (circleMap w ρ θ)]
    simp only [fubGS_eq]

/-- **The log potential of `circBumpS`:** `logPot Φ x = −∫ ψ_s(t) g_{w,ρ}(x − t) dt`. -/
theorem logPot_circBumpS :
    logPot (circBumpS s w ρ) x = -∫ t, bumpS s 0 t * circLog w ρ (x - t) := by
  have e1 : logPot (circBumpS s w ρ) x =
      (2 * π)⁻¹ * ∫ y, ∫ θ, fubFS s w ρ x (θ, y) ∂μθS := by
    rw [logPot, ← integral_const_mul]
    congr 1
    funext y
    rw [circBumpS_eq_integral, mul_left_comm, ← integral_const_mul]
    rfl
  have e2 : ∫ y, ∫ θ, fubFS s w ρ x (θ, y) ∂μθS = ∫ θ, (∫ t, fubGS s w ρ x (θ, t)) ∂μθS := by
    rw [← integral_integral_swap (f := fun θ y => fubFS s w ρ x (θ, y))
      (integrable_fubFS s w ρ x)]
    refine integral_congr_ae (Eventually.of_forall fun θ => ?_)
    simp only
    rw [← integral_add_right_eq_self (fun y => fubFS s w ρ x (θ, y)) (circleMap w ρ θ)]
    simp only [fubGS_eq]
  have e3 : ∫ θ, (∫ t, fubGS s w ρ x (θ, t)) ∂μθS = ∫ t, ∫ θ, fubGS s w ρ x (θ, t) ∂μθS :=
    integral_integral_swap (f := fun θ t => fubGS s w ρ x (θ, t)) (integrable_fubGS s w ρ x)
  rw [e1, e2, e3, ← integral_const_mul, ← integral_neg]
  congr 1
  funext t
  simp only [fubGS, circLog, Real.circleAverage_def, smul_eq_mul,
    intervalIntegral.integral_of_le (by positivity : (0 : ℝ) ≤ 2 * π)]
  rw [integral_const_mul, integral_neg]
  ring

end Fubini

/-- **Scaled form:** `logPot (circBumpS s w ρ) x = −∫ ψ₀(v) g_{w,ρ}(x − s v) dv` for `s > 0`. -/
theorem logPot_circBumpS' {s : ℝ} (hs : 0 < s) (w : ℂ) (ρ : ℝ) (x : ℂ) :
    logPot (circBumpS s w ρ) x = -∫ v, psi0 v * circLog w ρ (x - (s : ℂ) * v) := by
  rw [logPot_circBumpS, integral_eq_affine _ hs 0]
  congr 1
  rw [← integral_const_mul]
  congr 1
  funext v
  rw [bumpS_apply hs.ne', add_zero, sub_zero, Complex.real_smul]
  have hs' : (s : ℂ) ≠ 0 := by exact_mod_cast hs.ne'
  rw [mul_div_cancel_left₀ _ hs']
  field_simp

lemma continuous_circLog' {ρ : ℝ} (hρ : 0 < ρ) (w : ℂ) : Continuous (circLog w ρ) := by
  have : circLog w ρ = fun u => Real.log ρ + Real.posLog (ρ⁻¹ * ‖w - u‖) :=
    funext fun u => circLog_eq hρ.ne' w u
  rw [this]
  fun_prop

/-- **Lipschitz bound for the log potentials.** -/
theorem abs_logPot_circBumpS_sub_le {s s' ρ ρ' : ℝ} (hs : 0 < s) (hs' : 0 < s') (hρ : 0 < ρ)
    (hρ' : 0 < ρ') (w w' x : ℂ) :
    |logPot (circBumpS s w ρ) x - logPot (circBumpS s' w' ρ') x| ≤
      (|s - s'| + |ρ - ρ'| + ‖w - w'‖) / min ρ ρ' := by
  rw [logPot_circBumpS' hs, logPot_circBumpS' hs']
  have hc1 : Continuous fun v : ℂ => circLog w ρ (x - (s : ℂ) * v) :=
    (continuous_circLog' hρ w).comp (continuous_const.sub (continuous_const.mul continuous_id))
  have hc2 : Continuous fun v : ℂ => circLog w' ρ' (x - (s' : ℂ) * v) :=
    (continuous_circLog' hρ' w').comp (continuous_const.sub (continuous_const.mul continuous_id))
  have hi1 : Integrable fun v => psi0 v * circLog w ρ (x - (s : ℂ) * v) :=
    (psi0.continuous.mul hc1).integrable_of_hasCompactSupport psi0.hasCompactSupport.mul_right
  have hi2 : Integrable fun v => psi0 v * circLog w' ρ' (x - (s' : ℂ) * v) :=
    (psi0.continuous.mul hc2).integrable_of_hasCompactSupport psi0.hasCompactSupport.mul_right
  have hm : 0 < min ρ ρ' := lt_min hρ hρ'
  set c := (|s - s'| + |ρ - ρ'| + ‖w - w'‖) / min ρ ρ'
  have e : -(∫ v, psi0 v * circLog w ρ (x - (s : ℂ) * v)) -
      -(∫ v, psi0 v * circLog w' ρ' (x - (s' : ℂ) * v)) =
      ∫ v, psi0 v * (circLog w' ρ' (x - (s' : ℂ) * v) - circLog w ρ (x - (s : ℂ) * v)) := by
    simp_rw [mul_sub]
    rw [integral_sub hi2 hi1]
    ring
  rw [e, ← Real.norm_eq_abs]
  have hb : ∀ v, ‖psi0 v * (circLog w' ρ' (x - (s' : ℂ) * v) - circLog w ρ (x - (s : ℂ) * v))‖ ≤
      psi0 v * c := by
    intro v
    rw [norm_mul, Real.norm_of_nonneg (psi0_nonneg v)]
    by_cases hv : ‖v‖ < 1
    · refine mul_le_mul_of_nonneg_left ?_ (psi0_nonneg v)
      rw [Real.norm_eq_abs]
      have h1 := abs_circLog_sub_circLog_le hρ hρ' w w' (x - (s' : ℂ) * v)
      have h2 := abs_circLog_sub_le hρ w (x - (s' : ℂ) * v) (x - (s : ℂ) * v)
      have h3 : ‖(x - (s' : ℂ) * v) - (x - (s : ℂ) * v)‖ ≤ |s - s'| := by
        rw [show (x - (s' : ℂ) * v) - (x - (s : ℂ) * v) = ((s - s' : ℝ) : ℂ) * v by
          push_cast; ring, norm_mul, Complex.norm_real, Real.norm_eq_abs]
        exact mul_le_of_le_one_right (abs_nonneg _) hv.le
      have h4 : ‖(x - (s' : ℂ) * v) - (x - (s : ℂ) * v)‖ / ρ ≤ |s - s'| / min ρ ρ' :=
        div_le_div₀ (abs_nonneg _) h3 hm (min_le_left _ _)
      have h5 : (|ρ - ρ'| + ‖w - w'‖) / min ρ ρ' + |s - s'| / min ρ ρ' = c := by
        simp only [c]; ring
      calc |circLog w' ρ' (x - (s' : ℂ) * v) - circLog w ρ (x - (s : ℂ) * v)|
          ≤ |circLog w' ρ' (x - (s' : ℂ) * v) - circLog w ρ (x - (s' : ℂ) * v)| +
            |circLog w ρ (x - (s' : ℂ) * v) - circLog w ρ (x - (s : ℂ) * v)| :=
            abs_sub_le _ _ _
        _ ≤ (|ρ - ρ'| + ‖w - w'‖) / min ρ ρ' + |s - s'| / min ρ ρ' := by
            exact add_le_add h1 (h2.trans h4)
        _ = c := h5
    · rw [psi0_eq_zero (not_lt.mp hv), zero_mul, zero_mul]
  refine (norm_integral_le_of_norm_le ((integrable_testC _).mul_const _)
    (Eventually.of_forall hb)).trans (le_of_eq ?_)
  rw [integral_mul_const, integral_psi0, one_mul]

/-- `circBumpS s w ρ − circBumpS s' w' ρ'`, a mean-zero test function (`s, s' > 0`). -/
def circDiffS (s : ℝ) (w : ℂ) (ρ : ℝ) (s' : ℝ) (w' : ℂ) (ρ' : ℝ) (hs : 0 < s) (hs' : 0 < s') :
    TestC0 :=
  ⟨circBumpS s w ρ - circBumpS s' w' ρ', by
    show ∫ x, (circBumpS s w ρ x - circBumpS s' w' ρ' x) = 0
    rw [integral_sub (integrable_testC _) (integrable_testC _), integral_circBumpS hs,
      integral_circBumpS hs', sub_self]⟩

/-- **Variance bound:** `logCov D D ≤ 2 (|s − s'| + |ρ − ρ'| + ‖w − w'‖)/min ρ ρ'`. -/
theorem logCov_circDiffS_le {s s' ρ ρ' : ℝ} (hs : 0 < s) (hs' : 0 < s') (hρ : 0 < ρ)
    (hρ' : 0 < ρ') (w w' : ℂ) :
    logCov (circDiffS s w ρ s' w' ρ' hs hs').1 (circDiffS s w ρ s' w' ρ' hs hs').1 ≤
      2 * ((|s - s'| + |ρ - ρ'| + ‖w - w'‖) / min ρ ρ') := by
  set D := circDiffS s w ρ s' w' ρ' hs hs'
  set c := (|s - s'| + |ρ - ρ'| + ‖w - w'‖) / min ρ ρ'
  rw [logCov_eq_integral_logPot]
  have hD : ∀ x, |D.1 x| ≤ circBumpS s w ρ x + circBumpS s' w' ρ' x := by
    intro x
    show |circBumpS s w ρ x - circBumpS s' w' ρ' x| ≤ _
    refine (abs_sub _ _).trans (le_of_eq ?_)
    rw [abs_of_nonneg (circBumpS_nonneg _ _ _ _), abs_of_nonneg (circBumpS_nonneg _ _ _ _)]
  have hP : ∀ x, |logPot D.1 x| ≤ c := by
    intro x
    show |logPot (⇑(circBumpS s w ρ - circBumpS s' w' ρ')) x| ≤ c
    rw [logPot_sub]
    exact abs_logPot_circBumpS_sub_le hs hs' hρ hρ' w w' x
  have hb : ∀ x, ‖D.1 x * logPot D.1 x‖ ≤ (circBumpS s w ρ x + circBumpS s' w' ρ' x) * c := by
    intro x
    rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs]
    exact mul_le_mul (hD x) (hP x) (abs_nonneg _)
      (add_nonneg (circBumpS_nonneg _ _ _ _) (circBumpS_nonneg _ _ _ _))
  have hint : Integrable fun x => (circBumpS s w ρ x + circBumpS s' w' ρ' x) * c :=
    ((integrable_testC _).add (integrable_testC _)).mul_const c
  have := (le_abs_self _).trans ((Real.norm_eq_abs _).symm.le.trans
    (norm_integral_le_of_norm_le hint (Eventually.of_forall hb)))
  refine this.trans (le_of_eq ?_)
  rw [integral_mul_const, integral_add (integrable_testC _) (integrable_testC _),
    integral_circBumpS hs, integral_circBumpS hs']
  ring

end MatedCRTHarmonic.LQGCoord
