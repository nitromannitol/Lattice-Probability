/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Field.KilledHeatLaw at commit fdb5cad; only the module paths of local imports are changed.
   Declarations, examples and checks that the copied results do not use are omitted. -/
import Mathlib.Probability.Distributions.Gaussian.IsGaussianProcess.Basic
import Mathlib.Probability.Distributions.Gaussian.CharFun
import Mathlib.Probability.Process.FiniteDimensionalLaws
import Mathlib.Probability.Moments.CovarianceBilin
import Mathlib.Topology.MetricSpace.Thickening

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# Killed heat kernel, part 1: laws of Gaussian processes and the "stay in `A`" event
(task P2-KILLED, decision D-KHK1, `decisions/DEC-KHK.md`)

* `KilledHeat.map_restrict_eq_of_gaussian`, `KilledHeat.map_eq_of_gaussian`: two real Gaussian
  processes (on possibly different probability spaces) with the same means and covariances have
  the same finite-dimensional laws, hence (countable index) the same law. This is the argument of
  mathlib's `IsGaussianProcess.isPreBrownianReal_of_covariance`
  (`Mathlib/Probability/BrownianMotion/Basic.lean`), generalized from the Brownian covariance to
  an arbitrary one and to two probability spaces; the passage to the full law is mathlib's
  `isProjectiveLimit_map` + `IsProjectiveLimit.unique`.
* `KilledHeat.forall_mem_iff_exists_clamp`: a continuous path stays in an open set `A` on
  `[0, t]` iff for some `n` its values at the countably many times `clampT t q` (`q ∈ ℚ`) stay in
  the closed set `innerSet A n = {x | ball x (1/(n+1)) ⊆ A}` (compactness of the path, mathlib
  `IsCompact.exists_thickening_subset_open`, and density of `ℚ`). Own elementary argument.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal

namespace LQGMetric
namespace KilledHeat

/-! ### Gaussian processes with equal means and covariances have equal laws -/

section GaussLaw

variable {T Ω Ω' : Type*} {mΩ : MeasurableSpace Ω} {mΩ' : MeasurableSpace Ω'}
  {P : Measure Ω} {P' : Measure Ω'} {X : T → Ω → ℝ} {Y : T → Ω' → ℝ}

theorem map_restrict_eq_of_gaussian (hX : IsGaussianProcess X P) (hY : IsGaussianProcess Y P')
    (hm : ∀ t, P[X t] = P'[Y t]) (hc : ∀ s t, cov[X s, X t; P] = cov[Y s, Y t; P'])
    (I : Finset T) :
    P.map (fun ω ↦ I.restrict (X · ω)) = P'.map (fun ω ↦ I.restrict (Y · ω)) := by
  have hXm : AEMeasurable (fun ω ↦ I.restrict (X · ω)) P :=
    .of_eval fun _ ↦ hX.aemeasurable _
  have hYm : AEMeasurable (fun ω ↦ I.restrict (Y · ω)) P' :=
    .of_eval fun _ ↦ hY.aemeasurable _
  apply (MeasurableEquiv.toLp 2 (_ → ℝ)).map_measurableEquiv_injective
  rw [MeasurableEquiv.coe_toLp, ← PiLp.coe_symm_continuousLinearEquiv 2 ℝ]
  have := (hX.hasGaussianLaw I).isGaussian_map
  have := (hY.hasGaussianLaw I).isGaussian_map
  apply IsGaussian.ext
  · have h1 : ∫ x, x ∂(P.map (fun ω ↦ I.restrict (X · ω)))
        = ∫ x, x ∂(P'.map (fun ω ↦ I.restrict (Y · ω))) := by
      ext i
      rw [eval_integral (f := fun x ↦ x)
          (fun _ ↦ (IsGaussian.hasGaussianLaw_id.eval _).integrable),
        eval_integral (f := fun x ↦ x)
          (fun _ ↦ (IsGaussian.hasGaussianLaw_id.eval _).integrable),
        integral_map hXm (measurable_pi_apply i).aestronglyMeasurable,
        integral_map hYm (measurable_pi_apply i).aestronglyMeasurable]
      exact hm i
    have h2 : ∀ μ : Measure (I → ℝ), ∫ x, x ∂(μ.map (PiLp.continuousLinearEquiv 2 ℝ
        (fun _ : I ↦ ℝ)).symm) = (PiLp.continuousLinearEquiv 2 ℝ (fun _ : I ↦ ℝ)).symm
          (∫ x, x ∂μ) := fun μ ↦ by
      rw [integral_map (by fun_prop) (by fun_prop)]
      exact ContinuousLinearEquiv.integral_comp_comm _ _
    simp only [id_eq]
    rw [h2, h2, h1]
  · rw [← ContinuousLinearMap.toBilinForm_inj]
    refine LinearMap.BilinForm.ext_of_isSymm isPosSemidef_covarianceBilin.isSymm
      isPosSemidef_covarianceBilin.isSymm fun x ↦ ?_
    simp only [ContinuousLinearMap.toBilinForm_apply]
    rw [PiLp.coe_symm_continuousLinearEquiv, covarianceBilin_apply_pi, covarianceBilin_apply_pi]
    · congrm ∑ i, ∑ j, _ * ?_
      rw [covariance_map, covariance_map]
      · exact hc i j
      any_goals exact Measurable.aestronglyMeasurable (by fun_prop)
      · exact hYm
      · exact hXm
    · exact fun i ↦ ((hY.hasGaussianLaw I).isGaussian_map.hasGaussianLaw_id.eval i).memLp_two
    · exact fun i ↦ ((hX.hasGaussianLaw I).isGaussian_map.hasGaussianLaw_id.eval i).memLp_two


/-- Equal means and covariances give equal laws (countable index). -/
theorem map_eq_of_gaussian [Countable T] (hX : IsGaussianProcess X P)
    (hY : IsGaussianProcess Y P')
    (hm : ∀ t, P[X t] = P'[Y t]) (hc : ∀ s t, cov[X s, X t; P] = cov[Y s, Y t; P']) :
    P.map (fun ω t ↦ X t ω) = P'.map (fun ω t ↦ Y t ω) := by
  have := hX.isProbabilityMeasure
  have := hY.isProbabilityMeasure
  have hXm : AEMeasurable (fun ω t ↦ X t ω) P := .of_eval fun t ↦ hX.aemeasurable t
  have hYm : AEMeasurable (fun ω t ↦ Y t ω) P' := .of_eval fun t ↦ hY.aemeasurable t
  have h1 := isProjectiveLimit_map hXm
  have h2 := isProjectiveLimit_map hYm
  simp_rw [map_restrict_eq_of_gaussian hX hY hm hc] at h1
  have : ∀ I : Finset T, IsFiniteMeasure (P'.map (fun ω ↦ I.restrict (Y · ω))) :=
    fun _ ↦ inferInstance
  exact h1.unique h2

end GaussLaw


/-! ### The event "the path stays in `A` on `[0, t]`" through countably many times -/

/-- The times `clampT t q = min (q⁺) t ∈ [0, t]`, `q ∈ ℚ`; their closure contains `[0, t]`. -/
def clampT (t : ℝ≥0) (q : ℚ) : ℝ≥0 := min (Real.toNNReal q) t

lemma clampT_le (t : ℝ≥0) (q : ℚ) : clampT t q ≤ t := min_le_right _ _

/-- `innerSet A n = {x | ball x (1/(n+1)) ⊆ A}`: closed and contained in `A`. -/
def innerSet (A : Set ℂ) (n : ℕ) : Set ℂ := {x | Metric.ball x (1 / ((n : ℝ) + 1)) ⊆ A}

lemma innerSet_subset (A : Set ℂ) (n : ℕ) : innerSet A n ⊆ A := fun x hx ↦
  hx (Metric.mem_ball_self (by positivity))

lemma isClosed_innerSet (A : Set ℂ) (n : ℕ) : IsClosed (innerSet A n) := by
  have : innerSet A n = ⋂ y ∈ Aᶜ, {x | 1 / ((n : ℝ) + 1) ≤ dist y x} := by
    ext x
    simp only [innerSet, Set.mem_ofPred_eq, Set.mem_iInter, Set.mem_compl_iff]
    constructor
    · intro h y hy
      by_contra hlt
      exact hy (h (by rw [Metric.mem_ball]; exact not_le.mp hlt))
    · intro h y hy
      by_contra hyA
      have := h y hyA
      rw [Metric.mem_ball] at hy
      linarith
  rw [this]
  exact isClosed_biInter fun y _ ↦ isClosed_le continuous_const (continuous_const.dist continuous_id)

/-- A continuous path stays in the open set `A` on `[0, t]` iff, for some `n`, its values at the
times `clampT t q` lie in `innerSet A n`. -/
theorem forall_mem_iff_exists_clamp {F : ℝ≥0 → ℂ} (hF : Continuous F) {A : Set ℂ}
    (hA : IsOpen A) (t : ℝ≥0) :
    (∀ s : ℝ≥0, s ≤ t → F s ∈ A) ↔ ∃ n : ℕ, ∀ q : ℚ, F (clampT t q) ∈ innerSet A n := by
  constructor
  · intro h
    have hK : IsCompact (F '' Set.Icc 0 t) := isCompact_Icc.image hF
    have hKA : F '' Set.Icc 0 t ⊆ A := by
      rintro _ ⟨s, hs, rfl⟩
      exact h s hs.2
    obtain ⟨δ, hδ, hδA⟩ := hK.exists_thickening_subset_open hA hKA
    obtain ⟨n, hn⟩ := exists_nat_one_div_lt hδ
    refine ⟨n, fun q ↦ ?_⟩
    intro y hy
    apply hδA
    refine Metric.mem_thickening_iff.mpr ⟨F (clampT t q), ⟨clampT t q, ⟨zero_le, clampT_le t q⟩,
      rfl⟩, ?_⟩
    rw [Metric.mem_ball] at hy
    linarith
  · rintro ⟨n, hn⟩ s hs
    let G : ℝ → ℂ := fun x ↦ F (min (Real.toNNReal x) t)
    have hG : Continuous G := hF.comp (continuous_real_toNNReal.min continuous_const)
    have hclosed : IsClosed (G ⁻¹' innerSet A n) := (isClosed_innerSet A n).preimage hG
    have hdense : Dense (G ⁻¹' innerSet A n) :=
      Rat.denseRange_cast.mono (by rintro _ ⟨q, rfl⟩; exact hn q)
    have hs' : (s : ℝ) ∈ G ⁻¹' innerSet A n := by
      rw [← hclosed.closure_eq, hdense.closure_eq]
      trivial
    apply innerSet_subset A n
    simpa [G, min_eq_left hs] using hs'

end KilledHeat
end LQGMetric
