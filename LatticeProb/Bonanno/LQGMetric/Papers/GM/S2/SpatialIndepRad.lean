/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.GM.S2.SpatialIndepRad at commit 31e7483; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Field.MeasurableAvg
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S2.SpatialIndepMV
import Mathlib.Analysis.SpecialFunctions.SmoothTransition

/-!
# Radial test functions and point values of harmonic distributions

`radBump δ x` is the smooth radial test function `y ↦ e(δ² − |y − x|²)` (`e` = mathlib
`expNegInvGlue`), supported in `B̄(x, δ)`. With the mean value lemma
`integral_mul_radial_of_harmonic`, a distribution `T` which equals a harmonic `g` on an open
`V ⊇ B̄(x, δ)` satisfies `T(radBump δ x) = g(x) · ∫ radBump δ 0` (`pair_radBump_of_harmonic`), and
`(T, x) ↦ T(radBump δ x)` is jointly measurable (`measurable_apply_radBump`). This expresses the
harmonic part `𝔥` of GM l. 976–979 (`literature/src/1905.00383/uniqueness-final.tex`) and
`𝔐_z = sup |𝔥 − 𝔥(z)|` through countably many pairings. Own elementary constructions (the
continuity proof follows `MeasurableAvg.continuous_bumpTest`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Filter Topology Set TopologicalSpace Metric InnerProductSpace
open scoped Distributions

namespace LQGMetric.GM

/-- the profile `y ↦ e(δ² − |y|²)` -/
def radProf (δ : ℝ) (y : ℂ) : ℝ := expNegInvGlue (δ ^ 2 - ‖y‖ ^ 2)

lemma contDiff_radProf (δ : ℝ) : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (radProf δ) :=
  (expNegInvGlue.contDiff (n := ⊤)).comp (contDiff_const.sub (contDiff_norm_sq ℝ))

lemma radProf_eq_zero {δ : ℝ} (hδ : 0 ≤ δ) {y : ℂ} (hy : δ ≤ ‖y‖) : radProf δ y = 0 :=
  expNegInvGlue.zero_of_nonpos (by nlinarith [norm_nonneg y])

lemma radProf_nonneg (δ : ℝ) (y : ℂ) : 0 ≤ radProf δ y := expNegInvGlue.nonneg _

lemma radProf_rot (δ : ℝ) (a : Circle) (y : ℂ) : radProf δ (a * y) = radProf δ y := by
  simp [radProf]

lemma integral_radProf_pos {δ : ℝ} (hδ : 0 < δ) : 0 < ∫ y, radProf δ y := by
  have hc : Continuous (radProf δ) := (contDiff_radProf δ).continuous
  have hcs : HasCompactSupport (radProf δ) :=
    HasCompactSupport.intro (isCompact_closedBall (0 : ℂ) δ) fun y hy => radProf_eq_zero hδ.le
      (by rw [mem_closedBall, dist_zero_right, not_le] at hy; exact hy.le)
  rw [integral_pos_iff_support_of_nonneg (radProf_nonneg δ) (hc.integrable_of_hasCompactSupport hcs)]
  refine (measure_ball_pos volume (0 : ℂ) hδ).trans_le (measure_mono fun y hy => ?_)
  rw [mem_ball, dist_zero_right] at hy
  exact (expNegInvGlue.pos_of_pos (by nlinarith [norm_nonneg y])).ne'

/-- the radial test function `y ↦ e(δ² − |y − x|²)` -/
def radBump (δ : ℝ) (hδ : 0 ≤ δ) (x : ℂ) : TestC where
  toFun := fun y => radProf δ (y - x)
  contDiff' := (contDiff_radProf δ).comp (contDiff_id.sub contDiff_const)
  hasCompactSupport' := HasCompactSupport.intro (isCompact_closedBall x δ) fun y hy =>
    radProf_eq_zero hδ (by
      rw [mem_closedBall, dist_eq_norm, not_le] at hy; exact hy.le)
  tsupport_subset' := subset_univ _

lemma radBump_apply (δ : ℝ) (hδ : 0 ≤ δ) (x y : ℂ) : radBump δ hδ x y = radProf δ (y - x) := rfl

theorem continuous_radBump (δ : ℝ) (hδ : 0 ≤ δ) : Continuous (radBump δ hδ) := by
  rw [continuous_iff_continuousAt]
  intro x₀
  let S := closedBall x₀ 1
  have : CompactSpace S := isCompact_iff_compactSpace.mp (isCompact_closedBall _ _)
  let K : Compacts ℂ := ⟨closedBall 0 (‖x₀‖ + 1 + δ), isCompact_closedBall _ _⟩
  have hs : ∀ x : S, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) fun y => radProf δ (y + -(x : ℂ)) :=
    fun x => (contDiff_radProf δ).comp (contDiff_id.add contDiff_const)
  have hK : ∀ x : S, ∀ y ∉ (K : Set ℂ), radProf δ (y + -(x : ℂ)) = 0 := by
    intro x y hy
    apply radProf_eq_zero hδ
    have hx : ‖(x : ℂ) - x₀‖ ≤ 1 := by rw [← dist_eq_norm]; exact mem_closedBall.1 x.2
    have hy' : ‖x₀‖ + 1 + δ < ‖y‖ := by simpa [K] using hy
    have h1 : ‖y‖ ≤ ‖y + -(x : ℂ)‖ + ‖(x : ℂ) - x₀‖ + ‖x₀‖ := by
      calc ‖y‖ = ‖(y + -(x : ℂ)) + ((x : ℂ) - x₀) + x₀‖ := by ring_nf
        _ ≤ _ := norm_add₃_le
    linarith
  have hD : ∀ i : ℕ, Continuous fun p : S × ℂ =>
      iteratedFDeriv ℝ i (fun y => radProf δ (y + -(p.1 : ℂ))) p.2 := by
    intro i
    simp_rw [iteratedFDeriv_comp_add_right]
    exact ((contDiff_radProf δ).continuous_iteratedFDeriv (by exact_mod_cast le_top)).comp
      (continuous_snd.add (continuous_subtype_val.comp continuous_fst).neg)
  have hc := continuous_testFamK K (fun (x : S) y => radProf δ (y + -(x : ℂ))) hs hK hD
  have e : (fun x : S => radBump δ hδ x) = ofSuppC K ∘ testFamK K _ hs hK := by
    funext x
    ext y
    show radProf δ (y - x) = radProf δ (y + -(x : ℂ))
    rw [sub_eq_add_neg]
  have h2 : Continuous fun x : S => radBump δ hδ x := by
    rw [e]; exact (ofSuppC K).continuous.comp hc
  exact (continuousOn_iff_continuous_domRestrict.2 h2).continuousAt
    (closedBall_mem_nhds _ one_pos)

/-- `(T, x) ↦ T(radBump δ x)` is jointly measurable -/
theorem measurable_apply_radBump (δ : ℝ) (hδ : 0 ≤ δ) :
    Measurable fun p : DistC × ℂ => p.1 (radBump δ hδ p.2) := by
  have := measurable_uncurry_of_continuous_of_measurable (u := fun (x : ℂ) (h : DistC) =>
      h (radBump δ hδ x)) (fun h => (map_continuous h).comp (continuous_radBump δ hδ))
    (fun x => measurable_distOn_apply _)
  exact this.comp measurable_swap

/-- **point values of a harmonic distribution**: if `T = g` on an open `V ⊇ B̄(x, δ)` with `g`
harmonic on `V`, then `T(radBump δ x) = g(x) ∫ radProf δ`. -/
theorem pair_radBump_of_harmonic {V : Opens ℂ} {g : ℂ → ℝ} (hg : HarmonicOnNhd g V)
    {T : DistC} (hT : ∀ φ : TestOn V, restrictTo V T φ = ∫ y, g y * φ y) {δ : ℝ} (hδ : 0 < δ)
    {x : ℂ} (hB : closedBall x δ ⊆ V) :
    T (radBump δ hδ.le x) = g x * ∫ y, radProf δ y := by
  -- `radBump δ x` as a test function on `V`
  have htsupp : tsupport (radBump δ hδ.le x : ℂ → ℝ) ⊆ (V : Set ℂ) := by
    refine (closure_minimal (fun y hy => ?_) isClosed_closedBall).trans hB
    by_contra hy'
    rw [mem_closedBall, dist_eq_norm, not_le] at hy'
    exact hy (radProf_eq_zero hδ.le hy'.le)
  let φ : TestOn V := ⟨radBump δ hδ.le x, (radBump δ hδ.le x).contDiff,
    (radBump δ hδ.le x).hasCompactSupport, htsupp⟩
  have h1 : T (radBump δ hδ.le x) = restrictTo V T φ := by
    show T _ = T (TestFunction.monoCLM ℝ φ)
    congr 1
    ext y
    simp [TestFunction.monoCLM_apply, φ]
  rw [h1, hT φ]
  have h2 : ∫ y, g y * φ y = ∫ y, g (x + y) * radProf δ y := by
    rw [← integral_add_left_eq_self (fun y => g y * φ y) x]
    congr 1; funext y
    show g (x + y) * radProf δ (x + y - x) = _
    rw [add_sub_cancel_left]
  rw [h2]
  exact integral_mul_radial_of_harmonic V.isOpen hg hB (contDiff_radProf δ).continuous
    (fun y hy => radProf_eq_zero hδ.le hy.le) (radProf_rot δ)

lemma radProf_le (δ : ℝ) (y : ℂ) : radProf δ y ≤ expNegInvGlue (δ ^ 2) :=
  expNegInvGlue.monotone (by nlinarith [norm_nonneg y])

/-- **sup bound for harmonic functions by a local `L¹` norm** (mean value property):
`|g(u) − b| ≤ C_δ ∫_{B̄(u,δ)} |g − b|` with `C_δ = e(δ²)/∫ radProf δ`. -/
theorem abs_sub_le_integral_of_harmonic {V : Set ℂ} (hV : IsOpen V) {g : ℂ → ℝ}
    (hg : HarmonicOnNhd g V) {u : ℂ} {δ : ℝ} (hδ : 0 < δ) (hB : closedBall u δ ⊆ V) (b : ℝ) :
    |g u - b| ≤ expNegInvGlue (δ ^ 2) / (∫ y, radProf δ y) *
      ∫ y in closedBall u δ, |g y - b| := by
  have hI := integral_radProf_pos hδ
  have hg' : HarmonicOnNhd (fun y => g y - b) V := hg.sub (harmonicOnNhd_const b)
  have hmv := integral_mul_radial_of_harmonic hV hg' hB (contDiff_radProf δ).continuous
    (fun y hy => radProf_eq_zero hδ.le hy.le) (radProf_rot δ)
  have hcont : ContinuousOn (fun y => |g y - b|) (closedBall u δ) := fun y hy =>
    (((hg y (hB hy)).1.continuousAt.sub continuousAt_const).abs).continuousWithinAt
  have hint : IntegrableOn (fun y => |g y - b|) (closedBall u δ) :=
    hcont.integrableOn_compact (isCompact_closedBall _ _)
  set C := expNegInvGlue (δ ^ 2)
  have key : |g u - b| * ∫ y, radProf δ y ≤ C * ∫ y in closedBall u δ, |g y - b| := by
    rw [← abs_of_pos hI, ← abs_mul, ← hmv]
    refine (abs_integral_le_integral_abs).trans ?_
    have hupper : Integrable (fun x => (closedBall u δ).indicator (fun y => C * |g y - b|) (u + x)) := by
      have : Integrable ((closedBall u δ).indicator fun y => C * |g y - b|) :=
        (integrable_indicator_iff measurableSet_closedBall).2
          (IntegrableOn.integrable (hint.const_mul C))
      exact this.comp_add_left u
    calc ∫ x, |(g (u + x) - b) * radProf δ x|
        ≤ ∫ x, (closedBall u δ).indicator (fun y => C * |g y - b|) (u + x) := by
          refine integral_mono_of_nonneg (Eventually.of_forall fun x => abs_nonneg _) hupper
            (Eventually.of_forall fun x => ?_)
          show |(g (u + x) - b) * radProf δ x| ≤
            (closedBall u δ).indicator (fun y => C * |g y - b|) (u + x)
          by_cases hx : u + x ∈ closedBall u δ
          · rw [Set.indicator_of_mem hx, abs_mul, abs_of_nonneg (radProf_nonneg δ x), mul_comm]
            exact mul_le_mul_of_nonneg_right (radProf_le δ x) (abs_nonneg _)
          · have : δ < ‖x‖ := by
              rw [mem_closedBall, dist_eq_norm, add_sub_cancel_left, not_le] at hx; exact hx
            simp [Set.indicator_of_notMem hx, radProf_eq_zero hδ.le this.le]
      _ = ∫ y, (closedBall u δ).indicator (fun y => C * |g y - b|) y :=
          integral_add_left_eq_self (fun y => (closedBall u δ).indicator (fun y => C * |g y - b|) y) u
      _ = C * ∫ y in closedBall u δ, |g y - b| := by
          rw [integral_indicator measurableSet_closedBall, integral_const_mul]
  rw [div_mul_eq_mul_div, le_div_iff₀ hI]
  exact key

end LQGMetric.GM
