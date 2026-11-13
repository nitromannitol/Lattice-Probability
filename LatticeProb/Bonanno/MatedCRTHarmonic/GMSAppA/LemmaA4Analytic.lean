/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module MatedCRTHarmonic.GMSAppA.LemmaA4Analytic at commit fdb5cad; only the module paths of local imports are changed.
   Declarations, examples and checks that the copied results do not use are omitted. -/
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S2.SpatialIndepMoment
import LatticeProb.Bonanno.LQGMetric.Field.MarkovGermVerPot
import LatticeProb.Bonanno.LQGMetric.Field.CircleAvgRate
import Mathlib.Analysis.Convex.Integral
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace

/-!
# Analytic inputs of [18] Lemma A.4

[18] = Gwynne–Miller–Sheffield, arXiv 1807.07511v3, Lemma A.4. The
paper's proof uses (i) the mean value property `sup_{B_δ}|𝔥 − 𝔥(0)| ≲ δ^{-2} ∫_{B_{2δ}} |𝔥 − 𝔥(0)|` and
(ii) "`𝔥(z) − 𝔥(0)` is centered Gaussian with variance `−log(1 − |z|²)` … bounded above by a universal constant times
`δ²` for `z ∈ B_δ(0)`" (citing [MS16d, Lemma 6.4]). We replace (ii) by a self-contained argument
(the cited lemma concerns a different field): the harmonic part paired with the mean-zero test
function `ψ_y − ψ_0` (`ψ` a fixed radial bump of radius `1/4`) is dominated in the convex order by the whole-plane
pairing `h(ψ_y − ψ_0)`, whose variance is `logCov(ψ_y − ψ_0, ψ_y − ψ_0) = O(|y|²)`.

* `GMSAppA.exists_lipschitz_closedBall` — a `C¹` function is Lipschitz on a closed ball.
* `GMSAppA.exists_logCov_radDiff_le_sq` — `logCov(ψ_y − ψ_0, ψ_y − ψ_0) ≤ C|y|²` for `|y| ≤ 1/2`.
* `GMSAppA.abs_sub_le_setIntegral_of_harmonic_scaled` — the mean value bound (i) with the correct `δ^{-2}`
  scaling (rescaled radial profile).
* `GMSAppA.lintegral_convex_le_add_of_indepFun` — convex domination `E f(X) ≤ E f(X + Z)` for `Z` independent of
  `X` and centred.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set Metric InnerProductSpace
open LQGMetric LQGMetric.GM

namespace MatedCRTHarmonic.GMSAppA

/-! ### Lipschitz bounds -/

/-- A `C¹` function `ℂ → ℝ` is Lipschitz on every closed ball `B̄_R(0)`. -/
lemma exists_lipschitz_closedBall {f : ℂ → ℝ} (hf : ContDiff ℝ 1 f) (R : ℝ) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ x ∈ closedBall (0 : ℂ) R, ∀ y ∈ closedBall (0 : ℂ) R,
      |f y - f x| ≤ B * ‖y - x‖ := by
  obtain ⟨B, hB⟩ := (isCompact_closedBall (0 : ℂ) R).exists_bound_of_continuousOn
    (hf.continuous_fderiv one_ne_zero).continuousOn
  refine ⟨max B 0, le_max_right _ _, fun x hx y hy => ?_⟩
  have := (convex_closedBall (0 : ℂ) R).norm_image_sub_le_of_norm_fderiv_le (C := max B 0)
    (fun z _ => (hf.differentiable one_ne_zero) z) (fun z hz => (hB z hz).trans (le_max_left B 0))
    hx hy
  rwa [Real.norm_eq_abs] at this

/-! ### The log-energy of `ψ_y − ψ_0` is `O(|y|²)` -/

lemma quarter_pos : (0 : ℝ) < 1 / 4 := by norm_num

/-- the logarithmic potential of the fixed bump `ψ = radBump (1/4) 0` -/
def lamPot : ℂ → ℝ := CircleAvg.logPot (radBump (1 / 4) quarter_pos.le 0)

lemma contDiff_lamPot : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) lamPot :=
  MarkovGermVer.contDiff_logPot (radBump (1 / 4) quarter_pos.le 0)

/-- translation: the potential of `ψ_y` is `Λ(· − y)` -/
lemma logPot_radBump (y x : ℂ) :
    CircleAvg.logPot (radBump (1 / 4) quarter_pos.le y) x = lamPot (x - y) := by
  unfold lamPot CircleAvg.logPot
  rw [← integral_add_right_eq_self (fun x' => -Real.log ‖x - x'‖ * radBump (1 / 4) quarter_pos.le y x') y]
  congr 1
  funext u
  simp only [radBump_apply, add_sub_cancel_right, sub_zero]
  congr 3
  ring

/-- **`logCov(ψ_y − ψ_0, ψ_y − ψ_0) ≤ C|y|²` for `|y| ≤ 1/2`**, `ψ = radBump (1/4)`: both factors of
`∫ (ψ_y − ψ_0)(x) (Λ(x − y) − Λ(x)) dx` are `O(|y|)` and supported in `B̄_{3/4}(0)`. -/
theorem exists_logCov_radDiff_le_sq :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ y : ℂ, ‖y‖ ≤ 1 / 2 →
      logCov (radDiff quarter_pos.le y 0).1 (radDiff quarter_pos.le y 0).1 ≤ C * ‖y‖ ^ 2 := by
  obtain ⟨Bψ, hBψ0, hBψ⟩ := exists_lipschitz_closedBall
    ((contDiff_radProf (1 / 4)).of_le (by exact_mod_cast le_top)) 2
  obtain ⟨BΛ, hBΛ0, hBΛ⟩ := exists_lipschitz_closedBall
    (contDiff_lamPot.of_le (by exact_mod_cast le_top)) 2
  set K : Set ℂ := closedBall (0 : ℂ) (3 / 4)
  refine ⟨Bψ * BΛ * volume.real K, by positivity, fun y hy => ?_⟩
  set D := (radDiff quarter_pos.le y 0).1
  have hpot : ∀ x, CircleAvg.logPot D x = lamPot (x - y) - lamPot x := by
    intro x
    have e : (D : ℂ → ℝ) = ⇑(radBump (1 / 4) quarter_pos.le y - radBump (1 / 4) quarter_pos.le 0) :=
      rfl
    rw [e, CircleAvg.logPot_sub, logPot_radBump, logPot_radBump, sub_zero]
  have hD : ∀ x, D x = radProf (1 / 4) (x - y) - radProf (1 / 4) x := by
    intro x; rw [radDiff_apply, sub_zero]
  -- pointwise bound
  have hpt : ∀ x, |D x * (lamPot (x - y) - lamPot x)| ≤
      K.indicator (fun _ => Bψ * BΛ * ‖y‖ ^ 2) x := by
    intro x
    by_cases hx : x ∈ K
    · rw [Set.indicator_of_mem hx, abs_mul]
      have hxK : x ∈ closedBall (0 : ℂ) 2 := by
        rw [mem_closedBall, dist_zero_right] at hx ⊢; linarith
      have hxyK : x - y ∈ closedBall (0 : ℂ) 2 := by
        rw [mem_closedBall, dist_zero_right] at hx ⊢
        calc ‖x - y‖ ≤ ‖x‖ + ‖y‖ := norm_sub_le _ _
          _ ≤ 2 := by linarith
      have h1 : |D x| ≤ Bψ * ‖y‖ := by
        rw [hD]
        have := hBψ x hxK (x - y) hxyK
        rwa [sub_sub_cancel_left, norm_neg] at this
      have h2 : |lamPot (x - y) - lamPot x| ≤ BΛ * ‖y‖ := by
        have := hBΛ x hxK (x - y) hxyK
        rwa [sub_sub_cancel_left, norm_neg] at this
      calc |D x| * |lamPot (x - y) - lamPot x| ≤ (Bψ * ‖y‖) * (BΛ * ‖y‖) :=
            mul_le_mul h1 h2 (abs_nonneg _) (by positivity)
        _ = Bψ * BΛ * ‖y‖ ^ 2 := by ring
    · rw [Set.indicator_of_notMem hx]
      have hx' : 3 / 4 < ‖x‖ := by
        rw [mem_closedBall, dist_zero_right, not_le] at hx; exact hx
      have h1 : radProf (1 / 4) (x - y) = 0 := radProf_eq_zero quarter_pos.le (by
        have := norm_sub_norm_le x y; linarith)
      have h2 : radProf (1 / 4) x = 0 := radProf_eq_zero quarter_pos.le (by linarith)
      rw [hD, h1, h2, sub_zero, zero_mul, abs_zero]
  have hint : Integrable (K.indicator fun _ => Bψ * BΛ * ‖y‖ ^ 2) :=
    (integrable_indicator_iff measurableSet_closedBall).2
      (integrableOn_const (measure_closedBall_lt_top (x := (0 : ℂ))).ne)
  rw [CircleAvg.logCov_eq_integral_logPot]
  simp_rw [hpot]
  calc ∫ x, D x * (lamPot (x - y) - lamPot x)
      ≤ |∫ x, D x * (lamPot (x - y) - lamPot x)| := le_abs_self _
    _ ≤ ∫ x, |D x * (lamPot (x - y) - lamPot x)| := abs_integral_le_integral_abs
    _ ≤ ∫ x, K.indicator (fun _ => Bψ * BΛ * ‖y‖ ^ 2) x :=
        integral_mono_of_nonneg (ae_of_all _ fun x => abs_nonneg _) hint (ae_of_all _ hpt)
    _ = Bψ * BΛ * volume.real K * ‖y‖ ^ 2 := by
        rw [integral_indicator measurableSet_closedBall, setIntegral_const, smul_eq_mul]
        ring

/-! ### The mean value bound at scale `δ` -/

/-- the rescaled radial profile `x ↦ e(1 − |x/δ|²)`, supported in `B̄_δ(0)` -/
def radProfS (δ : ℝ) (x : ℂ) : ℝ := radProf 1 (δ⁻¹ • x)

lemma integral_radProfS {δ : ℝ} (hδ : 0 < δ) : ∫ x, radProfS δ x = δ ^ 2 * ∫ x, radProf 1 x := by
  unfold radProfS
  rw [Measure.integral_comp_smul, Complex.finrank_real_complex, smul_eq_mul, inv_pow, inv_inv,
    abs_of_pos (by positivity : (0 : ℝ) < δ ^ 2)]

/-- **Mean value bound with the correct scaling**: for `g` harmonic near `B̄_δ(u)`,
`|g(u) − b| ≤ e(1) / (δ² ∫ radProf 1) · ∫_{B̄_δ(u)} |g − b|`. -/
theorem abs_sub_le_setIntegral_of_harmonic_scaled {V : Set ℂ} (hV : IsOpen V) {g : ℂ → ℝ}
    (hg : HarmonicOnNhd g V) {u : ℂ} {δ : ℝ} (hδ : 0 < δ) (hB : closedBall u δ ⊆ V) (b : ℝ) :
    |g u - b| ≤ expNegInvGlue 1 / (δ ^ 2 * ∫ y, radProf 1 y) *
      ∫ y in closedBall u δ, |g y - b| := by
  have hI1 := integral_radProf_pos (one_pos : (0 : ℝ) < 1)
  have hI : 0 < ∫ y, radProfS δ y := by rw [integral_radProfS hδ]; positivity
  have hg' : HarmonicOnNhd (fun y => g y - b) V := hg.sub (harmonicOnNhd_const b)
  have hψc : Continuous (radProfS δ) :=
    (contDiff_radProf 1).continuous.comp (continuous_const_smul _)
  have hψs : ∀ y, δ < ‖y‖ → radProfS δ y = 0 := by
    intro y hy
    refine radProf_eq_zero zero_le_one ?_
    rw [norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hδ, ← div_eq_inv_mul, le_div_iff₀ hδ,
      one_mul]
    exact hy.le
  have hmv := integral_mul_radial_of_harmonic hV hg' hB hψc hψs (fun a y => by
    unfold radProfS
    rw [← mul_smul_comm]
    exact radProf_rot 1 a _)
  have hcont : ContinuousOn (fun y => |g y - b|) (closedBall u δ) := fun y hy =>
    (((hg y (hB hy)).1.continuousAt.sub continuousAt_const).abs).continuousWithinAt
  have hint : IntegrableOn (fun y => |g y - b|) (closedBall u δ) :=
    hcont.integrableOn_compact (isCompact_closedBall _ _)
  set C := expNegInvGlue 1
  have hψle : ∀ x, radProfS δ x ≤ C := fun x => by
    have := radProf_le 1 (δ⁻¹ • x); rwa [one_pow] at this
  have hψ0 : ∀ x, 0 ≤ radProfS δ x := fun x => radProf_nonneg 1 _
  have key : |g u - b| * ∫ y, radProfS δ y ≤ C * ∫ y in closedBall u δ, |g y - b| := by
    rw [← abs_of_pos hI, ← abs_mul, ← hmv]
    refine (abs_integral_le_integral_abs).trans ?_
    have hupper : Integrable (fun x => (closedBall u δ).indicator (fun y => C * |g y - b|) (u + x)) := by
      have : Integrable ((closedBall u δ).indicator fun y => C * |g y - b|) :=
        (integrable_indicator_iff measurableSet_closedBall).2
          (IntegrableOn.integrable (hint.const_mul C))
      exact this.comp_add_left u
    calc ∫ x, |(g (u + x) - b) * radProfS δ x|
        ≤ ∫ x, (closedBall u δ).indicator (fun y => C * |g y - b|) (u + x) := by
          refine integral_mono_of_nonneg (Eventually.of_forall fun x => abs_nonneg _) hupper
            (Eventually.of_forall fun x => ?_)
          show |(g (u + x) - b) * radProfS δ x| ≤
            (closedBall u δ).indicator (fun y => C * |g y - b|) (u + x)
          by_cases hx : u + x ∈ closedBall u δ
          · rw [Set.indicator_of_mem hx, abs_mul, abs_of_nonneg (hψ0 x), mul_comm]
            exact mul_le_mul_of_nonneg_right (hψle x) (abs_nonneg _)
          · have : δ < ‖x‖ := by
              rw [mem_closedBall, dist_eq_norm, add_sub_cancel_left, not_le] at hx; exact hx
            simp [Set.indicator_of_notMem hx, hψs x this]
      _ = ∫ y, (closedBall u δ).indicator (fun y => C * |g y - b|) y :=
          integral_add_left_eq_self
            (fun y => (closedBall u δ).indicator (fun y => C * |g y - b|) y) u
      _ = C * ∫ y in closedBall u δ, |g y - b| := by
          rw [integral_indicator measurableSet_closedBall, integral_const_mul]
  rw [← integral_radProfS hδ, div_mul_eq_mul_div, le_div_iff₀ hI]
  exact key

/-! ### Convex domination -/
/-- **Convex domination**: if `Z` is independent of `X`, integrable and centred, and `f ≥ 0` is convex and
continuous, then `E f(X) ≤ E f(X + Z)`. -/
theorem lintegral_convex_le_add_of_indepFun {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {X Z : Ω → ℝ} (hX : Measurable X) (hZ : Measurable Z)
    (hind : IndepFun X Z P) (hZi : Integrable Z P) (hZ0 : ∫ ω, Z ω ∂P = 0) {f : ℝ → ℝ}
    (hf : ConvexOn ℝ univ f) (hfc : Continuous f) (hf0 : ∀ x, 0 ≤ f x) :
    ∫⁻ ω, ENNReal.ofReal (f (X ω)) ∂P ≤ ∫⁻ ω, ENNReal.ofReal (f (X ω + Z ω)) ∂P := by
  have hmap := (indepFun_iff_map_prod_eq_prod_map_map hX.aemeasurable hZ.aemeasurable).1 hind
  have hFm : Measurable fun p : ℝ × ℝ => ENNReal.ofReal (f (p.1 + p.2)) :=
    ENNReal.measurable_ofReal.comp (hfc.measurable.comp (measurable_fst.add measurable_snd))
  have hR : ∫⁻ ω, ENNReal.ofReal (f (X ω + Z ω)) ∂P =
      ∫⁻ x, ∫⁻ z, ENNReal.ofReal (f (x + z)) ∂(P.map Z) ∂(P.map X) := by
    rw [← lintegral_prod _ hFm.aemeasurable, ← hmap,
      lintegral_map hFm (hX.prodMk hZ)]
  have hL : ∫⁻ ω, ENNReal.ofReal (f (X ω)) ∂P = ∫⁻ x, ENNReal.ofReal (f x) ∂(P.map X) :=
    (lintegral_map (f := fun x => ENNReal.ofReal (f x))
      (ENNReal.measurable_ofReal.comp hfc.measurable) hX).symm
  rw [hR, hL]
  have : IsProbabilityMeasure (P.map Z) := (Measure.isProbabilityMeasure_map_iff hZ.aemeasurable).2 inferInstance
  refine lintegral_mono fun x => ?_
  by_cases htop : ∫⁻ z, ENNReal.ofReal (f (x + z)) ∂(P.map Z) = ⊤
  · rw [htop]; exact le_top
  have hgm : Measurable fun z => f (x + z) := hfc.measurable.comp (measurable_const.add measurable_id)
  have hgi : Integrable (fun z => f (x + z)) (P.map Z) := by
    refine ⟨hgm.aestronglyMeasurable, ?_⟩
    rw [hasFiniteIntegral_iff_ofReal (ae_of_all _ fun z => hf0 _)]
    exact lt_top_iff_ne_top.2 htop
  have hidi : Integrable (fun z : ℝ => x + z) (P.map Z) := by
    exact (integrable_const x).add
      ((integrable_map_measure aestronglyMeasurable_id hZ.aemeasurable).2 hZi)
  have hJ := hf.map_integral_le hfc.continuousOn isClosed_univ (ae_of_all _ fun _ => mem_univ _)
    hidi hgi
  have hZmap : ∫ z, z ∂(P.map Z) = ∫ ω, Z ω ∂P :=
    integral_map hZ.aemeasurable aestronglyMeasurable_id
  have hZint : Integrable (fun z : ℝ => z) (P.map Z) :=
    (integrable_map_measure aestronglyMeasurable_id hZ.aemeasurable).2 hZi
  have hmean : ∫ z, (x + z) ∂(P.map Z) = x := by
    rw [integral_add (integrable_const x) hZint, integral_const, hZmap, hZ0]
    simp
  rw [hmean] at hJ
  rw [← ofReal_integral_eq_lintegral_ofReal hgi (ae_of_all _ fun z => hf0 _)]
  exact ENNReal.ofReal_le_ofReal hJ

end MatedCRTHarmonic.GMSAppA
