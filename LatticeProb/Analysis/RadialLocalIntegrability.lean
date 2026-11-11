import Mathlib.MeasureTheory.Constructions.HaarToSphere
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.MeasureTheory.Measure.Lebesgue.Complex
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.LinearAlgebra.Complex.FiniteDimensional

/-!
# Local integrability of radial functions with logarithmic growth at zero

The logarithmic kernel `log ‖z‖` of the planar Gaussian free field is locally
integrable on `ℂ` (Duplantier–Sheffield, arXiv:0808.1560, Sec. 3.1; Armitage–Gardiner,
*Classical Potential Theory*, Sec. 3.1). The statements below are general: a
radial function `z ↦ g ‖z‖` (or `z ↦ h (-log ‖z‖)`) is locally integrable under
a logarithmic bound at the origin.

* `integrableOn_one_add_abs_log_norm_closedBall`: the majorant `1 + |log ‖z‖|` is
  integrable on every closed disc of `ℂ`, by the polar coordinate criterion
  `MeasureTheory.integrable_fun_norm_addHaar`.
* `locallyIntegrable_of_continuousOn_compl_zero`: a function continuous on `ℂ \ {0}`
  and dominated near `0` by a multiple of the majorant is locally integrable
  (domination on compact sets).
* `locallyIntegrable_radial`: the radial form `z ↦ g ‖z‖`.
* `exists_abs_le_mul_one_add_of_sublinear`: a continuous function with `h t / t → 0`
  satisfies a linear envelope `|h t| ≤ C (1 + t)` on `[0, ∞)`.
* `locallyIntegrable_radial_of_sublinear`: `z ↦ h (-log ‖z‖)` is locally integrable
  when `h` is continuous and `h t / t → 0` as `t → ∞`.
-/

open MeasureTheory Set Filter Topology Metric

namespace LatticeProb.RadialLocalIntegrability

/-- On `(0, R]` the radial majorant satisfies `y (1 + |log y|) ≤ 2 + R + R ^ 2`.
For `y ≤ 1` this uses `|log y * y| < 1` (`Real.abs_log_mul_self_lt`); for
`1 < y ≤ R` it uses `log y ≤ y - 1`. -/
lemma mul_one_add_abs_log_le_of_mem_Ioc {y R : ℝ} (hy : y ∈ Ioc 0 R) :
    y * (1 + |Real.log y|) ≤ 2 + R + R ^ 2 := by
  obtain ⟨hy0, hyR⟩ := hy
  have hR : 0 < R := lt_of_lt_of_le hy0 hyR
  rcases le_total y 1 with hy1 | hy1
  · have h1 : |Real.log y * y| < 1 := Real.abs_log_mul_self_lt y hy0 hy1
    rw [abs_mul, abs_of_pos hy0] at h1
    nlinarith [sq_nonneg R]
  · have hlog : |Real.log y| = Real.log y := abs_of_nonneg (Real.log_nonneg hy1)
    have h2 : Real.log y ≤ y - 1 := Real.log_le_sub_one_of_pos hy0
    rw [hlog]
    nlinarith [mul_le_mul_of_nonneg_left h2 hy0.le, mul_le_mul hyR hyR hy0.le hR.le]

/-- The radial majorant `y ↦ y (1 + |log y|)` is Lebesgue integrable on `(0, R]`,
since it is bounded there. -/
lemma integrableOn_mul_one_add_abs_log_Ioc (R : ℝ) :
    IntegrableOn (fun y : ℝ => y * (1 + |Real.log y|)) (Ioc 0 R) := by
  refine Measure.integrableOn_of_bounded (M := 2 + R + R ^ 2) measure_Ioc_lt_top.ne ?_ ?_
  · exact (by fun_prop : Measurable fun y : ℝ => y * (1 + |Real.log y|)).aestronglyMeasurable
  · filter_upwards [ae_restrict_mem measurableSet_Ioc] with y hy
    have hy0 : 0 < y := hy.1
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hy0.le (by positivity))]
    exact mul_one_add_abs_log_le_of_mem_Ioc hy

/-- The majorant `1 + |log ‖z‖|` is integrable on every closed disc of `ℂ`.
Polar coordinates (`MeasureTheory.integrable_fun_norm_addHaar`) reduce this to
the one-dimensional integrability of `y ↦ y (1 + |log y|)` on `(0, R]`, where
the radial Jacobian in the plane is `y ^ (2 - 1) = y`. -/
lemma integrableOn_one_add_abs_log_norm_closedBall (R : ℝ) :
    IntegrableOn (fun z : ℂ => 1 + |Real.log ‖z‖|) (closedBall 0 R) := by
  set G : ℝ → ℝ := (Iic R).indicator fun r : ℝ => 1 + |Real.log r| with hGdef
  have hcomp : (fun z : ℂ => G ‖z‖) =
      (closedBall (0 : ℂ) R).indicator fun z : ℂ => 1 + |Real.log ‖z‖| := by
    funext z
    by_cases hz : ‖z‖ ≤ R
    · simp [hGdef, Set.mem_Iic, hz]
    · simp [hGdef, Set.mem_Iic, hz]
  have hint : Integrable (fun z : ℂ => G ‖z‖) volume := by
    refine (integrable_fun_norm_addHaar (f := G) volume).2 ?_
    refine (((integrable_indicator_iff measurableSet_Ioc).2
      (integrableOn_mul_one_add_abs_log_Ioc R)).integrableOn).congr_fun ?_ measurableSet_Ioi
    intro y hy
    have hy0 : 0 < y := hy
    by_cases hyR : y ≤ R
    · simp [hGdef, Set.mem_Iic, Set.mem_Ioc, hy0, hyR,
        Complex.finrank_real_complex]
    · simp [hGdef, Set.mem_Iic, Set.mem_Ioc, hyR,
        Complex.finrank_real_complex]
  rw [hcomp] at hint
  exact (integrable_indicator_iff measurableSet_closedBall).1 hint

/-- Domination: a function continuous on `ℂ \ {0}` and bounded near the origin by
`C (1 + |log ‖z‖|)` is locally integrable on `ℂ`.  On a closed disc `|z| ≤ R` the
annulus `δ ≤ |z| ≤ R` is compact and avoids the origin, so `f` is bounded there;
on the punctured disc `0 < |z| ≤ δ` the logarithmic majorant dominates. -/
theorem locallyIntegrable_of_continuousOn_compl_zero {f : ℂ → ℝ}
    (hf : ContinuousOn f {z : ℂ | z ≠ 0}) {C δ : ℝ} (hδ : 0 < δ)
    (hbound : ∀ z : ℂ, 0 < ‖z‖ → ‖z‖ ≤ δ → |f z| ≤ C * (1 + |Real.log ‖z‖|)) :
    LocallyIntegrable f volume := by
  have hcl : ({z : ℂ | z ≠ 0} : Set ℂ) = ({0}ᶜ : Set ℂ) := by
    ext z
    simp
  rw [hcl] at hf
  have hdisc : ∀ R : ℝ, IntegrableOn f (closedBall 0 R) volume := by
    intro R
    have hK : IsCompact (closedBall (0 : ℂ) R \ ball 0 δ) :=
      (isCompact_closedBall 0 R).diff isOpen_ball
    have hKsub : closedBall (0 : ℂ) R \ ball 0 δ ⊆ {0}ᶜ := by
      intro z hz
      have hzδ : δ ≤ ‖z‖ := not_lt.1 (fun h => hz.2 (mem_ball_zero_iff.2 h))
      intro hz0
      rw [Set.mem_singleton_iff] at hz0
      rw [hz0, norm_zero] at hzδ
      exact absurd hzδ (not_le.2 hδ)
    obtain ⟨M, hM⟩ := hK.exists_bound_of_continuousOn (hf.mono hKsub)
    have hmaj : IntegrableOn (fun z : ℂ => (|C| + |M|) * (1 + |Real.log ‖z‖|))
        (closedBall 0 R) volume :=
      (integrableOn_one_add_abs_log_norm_closedBall R).const_mul _
    have hae : ∀ᵐ z ∂(volume : Measure ℂ), z ≠ 0 := by
      rw [ae_iff]
      simp
    refine Integrable.mono' hmaj ?_ ?_
    · have h1 : AEStronglyMeasurable f (volume.restrict ({0}ᶜ : Set ℂ)) :=
        hf.aestronglyMeasurable (measurableSet_singleton 0).compl
      rw [restrict_compl_singleton] at h1
      exact h1.restrict
    · filter_upwards [ae_restrict_mem measurableSet_closedBall, ae_restrict_of_ae hae]
        with z hzmem hz0
      rw [Real.norm_eq_abs]
      by_cases hzδ : ‖z‖ ≤ δ
      · have h2 := hbound z (norm_pos_iff.2 hz0) hzδ
        have hpos : 0 ≤ 1 + |Real.log ‖z‖| := by positivity
        calc |f z| ≤ C * (1 + |Real.log ‖z‖|) := h2
          _ ≤ |C| * (1 + |Real.log ‖z‖|) := mul_le_mul_of_nonneg_right (le_abs_self C) hpos
          _ ≤ (|C| + |M|) * (1 + |Real.log ‖z‖|) :=
            mul_le_mul_of_nonneg_right (by linarith [abs_nonneg M]) hpos
      · have hzδ' : δ < ‖z‖ := not_le.1 hzδ
        have hzK : z ∈ closedBall (0 : ℂ) R \ ball 0 δ :=
          ⟨hzmem, fun h => by have := mem_ball_zero_iff.1 h; linarith⟩
        have h3 : ‖f z‖ ≤ M := hM z hzK
        rw [Real.norm_eq_abs] at h3
        have hpos : 1 ≤ 1 + |Real.log ‖z‖| := by linarith [abs_nonneg (Real.log ‖z‖)]
        calc |f z| ≤ M := h3
          _ ≤ |M| := le_abs_self M
          _ ≤ (|C| + |M|) * 1 := by linarith [abs_nonneg C]
          _ ≤ (|C| + |M|) * (1 + |Real.log ‖z‖|) :=
            mul_le_mul_of_nonneg_left hpos (by positivity)
  refine locallyIntegrable_iff.2 fun k hk => ?_
  obtain ⟨R, hR⟩ := hk.isBounded.subset_closedBall 0
  exact (hdisc R).mono_set hR

/-- Radial form: for `g` continuous on `(0, ∞)` and bounded near zero by
`C (1 + |log r|)` on `(0, δ]`, the function `z ↦ g ‖z‖` is locally integrable on `ℂ`.
This is the statement for a radial function; radiality is
the form `g ∘ norm`. -/
theorem locallyIntegrable_radial {g : ℝ → ℝ} (hg : ContinuousOn g (Ioi 0)) {C δ : ℝ}
    (hδ : 0 < δ) (hbound : ∀ r : ℝ, 0 < r → r ≤ δ → |g r| ≤ C * (1 + |Real.log r|)) :
    LocallyIntegrable (fun z : ℂ => g ‖z‖) volume := by
  refine locallyIntegrable_of_continuousOn_compl_zero (C := C) (δ := δ) ?_ hδ ?_
  · have hnorm : ContinuousOn (fun z : ℂ => ‖z‖) {z : ℂ | z ≠ 0} :=
      continuous_norm.continuousOn
    refine hg.comp hnorm ?_
    intro z hz
    exact norm_pos_iff.2 hz
  · intro z hz0 hzδ
    exact hbound ‖z‖ hz0 hzδ

/-- Sublinear growth gives a linear envelope in the radial time variable.
If `h` is continuous and `h t / t → 0` as `t → ∞`, then `|h t| ≤ C (1 + t)` for
all `t ≥ 0`, with `C ≥ 0`.  This is the deterministic step from sublinear growth
at `+∞` to the logarithmic bound `O(1 + |log ‖z‖|)` near zero. -/
lemma exists_abs_le_mul_one_add_of_sublinear {h : ℝ → ℝ} (hcont : Continuous h)
    (hsub : Tendsto (fun t : ℝ => h t / t) atTop (𝓝 0)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t : ℝ, 0 ≤ t → |h t| ≤ C * (1 + t) := by
  have h1 : ∀ᶠ t : ℝ in atTop, |h t / t| < 1 := by
    have h2 := hsub.abs
    rw [abs_zero] at h2
    exact h2.eventually (gt_mem_nhds zero_lt_one)
  obtain ⟨T₀, hT₀⟩ := eventually_atTop.1 h1
  obtain ⟨T, hT1, hT⟩ : ∃ T : ℝ, 1 ≤ T ∧ ∀ t : ℝ, T ≤ t → |h t / t| < 1 :=
    ⟨max T₀ 1, le_max_right _ _, fun t ht => hT₀ t (le_trans (le_max_left _ _) ht)⟩
  obtain ⟨M, hM⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := T)).exists_bound_of_continuousOn
    hcont.continuousOn
  refine ⟨max M 1, le_trans zero_le_one (le_max_right _ _), fun t ht => ?_⟩
  have hC1 : (1 : ℝ) ≤ max M 1 := le_max_right _ _
  have hMC : M ≤ max M 1 := le_max_left _ _
  rcases le_total t T with htT | htT
  · have h3 : ‖h t‖ ≤ M := hM t ⟨ht, htT⟩
    rw [Real.norm_eq_abs] at h3
    nlinarith [mul_nonneg (le_trans zero_le_one hC1) ht]
  · have htpos : 0 < t := lt_of_lt_of_le zero_lt_one (le_trans hT1 htT)
    have htne : t ≠ 0 := htpos.ne'
    have hq : |h t / t| < 1 := hT t htT
    have hht : |h t| = |h t / t| * t := by
      rw [abs_div, abs_of_pos htpos]
      field_simp
    have hlt : |h t| < t := by
      have := mul_lt_mul_of_pos_right hq htpos
      linarith
    nlinarith [mul_le_mul_of_nonneg_right hC1 (by linarith : (0 : ℝ) ≤ 1 + t)]

/-- Radial path with sublinear growth.  If `h` is continuous on `ℝ` and
`h t / t → 0` as `t → ∞`, then `z ↦ h (-log ‖z‖)` is locally integrable on `ℂ`.
The branch `t = -log ‖z‖ → ∞` corresponds to `z → 0`; continuity of `h`
on bounded intervals corresponds to continuity on bounded annuli. -/
theorem locallyIntegrable_radial_of_sublinear {h : ℝ → ℝ} (hcont : Continuous h)
    (hsub : Tendsto (fun t : ℝ => h t / t) atTop (𝓝 0)) :
    LocallyIntegrable (fun z : ℂ => h (-Real.log ‖z‖)) volume := by
  obtain ⟨C, -, hC⟩ := exists_abs_le_mul_one_add_of_sublinear hcont hsub
  refine locallyIntegrable_radial (g := fun r : ℝ => h (-Real.log r)) (C := C) (δ := 1) ?_
    zero_lt_one ?_
  · have hlog : ContinuousOn (fun r : ℝ => -Real.log r) (Ioi 0) :=
      (Real.continuousOn_log.mono fun r (hr : 0 < r) => Set.mem_compl_singleton_iff.2 hr.ne').neg
    exact hcont.comp_continuousOn hlog
  · intro r hr0 hr1
    show |h (-Real.log r)| ≤ C * (1 + |Real.log r|)
    have hlogr : Real.log r ≤ 0 := Real.log_nonpos hr0.le hr1
    have ht : 0 ≤ -Real.log r := by linarith
    rw [abs_of_nonpos hlogr]
    exact hC (-Real.log r) ht

end LatticeProb.RadialLocalIntegrability
