import LatticeProb.Analysis.AlexandrovLocal
import LatticeProb.Analysis.AlexandrovTaylor
import Mathlib.Analysis.Calculus.Rademacher
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.MeasureTheory.Function.Jacobian
import Mathlib.MeasureTheory.Measure.Haar.Unique
import Mathlib.MeasureTheory.Measure.Hausdorff

/-!
# Alexandrov's theorem

A convex function `f : E → ℝ` on a finite-dimensional real inner product space `E` is twice
differentiable almost everywhere with respect to any Haar measure: for almost every `x` there are a
vector `p` and a self-adjoint map `B` with
`f y = f x + ⟪p, y - x⟫ + 1/2 ⟪B (y - x), y - x⟫ + o(‖y - x‖ ^ 2)`.

The proof follows Mignot and the appendix of Crandall–Ishii–Lions: the resolvent
`J = convexResolvent f` is `1`-Lipschitz and onto, hence differentiable almost everywhere
(Rademacher), and it maps the null set of non-differentiability points, and the set of points where its
derivative is singular, to a null set. Almost every `x` is therefore the image `J y` of a point `y`
where `J` has an invertible derivative and `f` is differentiable at `x`; at such a point the
subgradients of `f` near `x` expand to first order (`subgradient_expansion`), which gives the second
order expansion of `f` (`hasSecondOrderTaylor_of_subgradient_expansion`). The matrix is symmetrised
at the end, which does not change the quadratic form.

## Main results

* `LatticeProb.ConvexAnalysis.ae_differentiableAt_of_convexOn`: a convex function is differentiable
  almost everywhere.
* `LatticeProb.ConvexAnalysis.measure_image_eq_zero_of_lipschitzWith`: a Lipschitz map of `E` sends
  Haar null sets to Haar null sets.
* `LatticeProb.ConvexAnalysis.alexandrov_ae`: Alexandrov's theorem.
-/

open MeasureTheory Set Filter Topology Asymptotics Metric
open scoped InnerProductSpace NNReal

namespace LatticeProb.ConvexAnalysis

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

/-- A Lipschitz map of a finite-dimensional space to itself sends Haar null sets to Haar null sets. -/
theorem measure_image_eq_zero_of_lipschitzWith (μ : Measure E) [μ.IsAddHaarMeasure] {J : E → E}
    {K : ℝ≥0} (hJ : LipschitzWith K J) {N : Set E} (hN : μ N = 0) : μ (J '' N) = 0 := by
  have h1 : μH[(Module.finrank ℝ E : ℝ)] ≪ μ :=
    Measure.absolutelyContinuous_isAddHaarMeasure (μH[(Module.finrank ℝ E : ℝ)]) μ
  have h2 : μ ≪ μH[(Module.finrank ℝ E : ℝ)] :=
    Measure.absolutelyContinuous_isAddHaarMeasure μ (μH[(Module.finrank ℝ E : ℝ)])
  have hN' : μH[(Module.finrank ℝ E : ℝ)] N = 0 := h1 hN
  have h3 := hJ.hausdorffMeasure_image_le (d := (Module.finrank ℝ E : ℝ)) (Nat.cast_nonneg _) N
  rw [hN', mul_zero] at h3
  exact h2 (nonpos_iff_eq_zero.mp h3)

/-- A convex function on a finite-dimensional space is differentiable almost everywhere. -/
theorem ae_differentiableAt_of_convexOn (μ : Measure E) [μ.IsAddHaarMeasure] {f : E → ℝ}
    (hf : ConvexOn ℝ Set.univ f) : ∀ᵐ x ∂μ, DifferentiableAt ℝ f x := by
  have hcont := continuous_of_convexOn_univ hf
  have key : ∀ n : ℕ, ∀ᵐ x ∂μ, x ∈ ball (0 : E) n → DifferentiableAt ℝ f x := by
    intro n
    obtain ⟨M, hM⟩ :=
      (isCompact_closedBall (0 : E) ((n : ℝ) + 1)).exists_bound_of_continuousOn hcont.continuousOn
    have hconv : ConvexOn ℝ (ball (0 : E) ((n : ℝ) + 1)) f :=
      hf.subset (subset_univ _) (convex_ball _ _)
    have hlip := hconv.lipschitzOnWith_of_abs_le (ε := 1) one_pos (M := M) fun a ha => by
      have := hM a (mem_closedBall.mpr ha.le)
      rwa [Real.norm_eq_abs] at this
    rw [add_sub_cancel_right] at hlip
    filter_upwards [hlip.ae_differentiableWithinAt_of_mem (μ := μ)] with x hx hxb
    exact (hx hxb).differentiableAt (isOpen_ball.mem_nhds hxb)
  filter_upwards [ae_all_iff.mpr key] with x hx
  obtain ⟨n, hn⟩ := exists_nat_gt ‖x‖
  exact hx n (by simpa using hn)

/-- **Alexandrov's theorem.** A convex function on a finite-dimensional real inner product space is
twice differentiable (in the sense of a second-order Taylor expansion with a symmetric matrix and a
Peano remainder) at almost every point, for any Haar measure. -/
theorem alexandrov_ae (μ : Measure E) [μ.IsAddHaarMeasure] {f : E → ℝ}
    (hf : ConvexOn ℝ Set.univ f) :
    ∀ᵐ x ∂μ, ∃ (p : E) (B : E →L[ℝ] E), IsSelfAdjoint B ∧
      (fun y => f y - f x - ⟪p, y - x⟫_ℝ - 1 / 2 * ⟪B (y - x), y - x⟫_ℝ) =o[𝓝 x]
        fun y => ‖y - x‖ ^ 2 := by
  have hJL : LipschitzWith 1 (convexResolvent f) := lipschitzWith_one_convexResolvent hf
  have h1 : ∀ᵐ x ∂μ, DifferentiableAt ℝ f x := ae_differentiableAt_of_convexOn μ hf
  have h2 : ∀ᵐ y ∂μ, DifferentiableAt ℝ (convexResolvent f) y := hJL.ae_differentiableAt
  have hS : μ {y | ¬ DifferentiableAt ℝ (convexResolvent f) y} = 0 := ae_iff.mp h2
  have hS' : μ (convexResolvent f '' {y | ¬ DifferentiableAt ℝ (convexResolvent f) y}) = 0 :=
    measure_image_eq_zero_of_lipschitzWith μ hJL hS
  have hT : μ (convexResolvent f ''
      {y | DifferentiableAt ℝ (convexResolvent f) y ∧ (fderiv ℝ (convexResolvent f) y).det = 0}) =
        0 :=
    addHaar_image_eq_zero_of_det_fderivWithin_eq_zero μ (f' := fderiv ℝ (convexResolvent f))
      (fun y hy => hy.1.hasFDerivAt.hasFDerivWithinAt) fun y hy => hy.2
  have h3 : ∀ᵐ x ∂μ, x ∉ convexResolvent f '' {y | ¬ DifferentiableAt ℝ (convexResolvent f) y} ∪
      convexResolvent f ''
        {y | DifferentiableAt ℝ (convexResolvent f) y ∧ (fderiv ℝ (convexResolvent f) y).det = 0} :=
    measure_eq_zero_iff_ae_notMem.mp (measure_union_null hS' hT)
  filter_upwards [h1, h3] with x hx1 hx3
  obtain ⟨g, hg⟩ := exists_isSubgradientAt hf x
  have hJy : convexResolvent f (x + g) = x := convexResolvent_eq_of_isSubgradientAt hf hg
  have hy2 : DifferentiableAt ℝ (convexResolvent f) (x + g) := by
    by_contra h
    exact hx3 (Or.inl ⟨x + g, h, hJy⟩)
  have hdet : (fderiv ℝ (convexResolvent f) (x + g)).det ≠ 0 := fun h =>
    hx3 (Or.inr ⟨x + g, ⟨hy2, h⟩, hJy⟩)
  have hA : Function.Injective (fderiv ℝ (convexResolvent f) (x + g)) := by
    have hne : ((fderiv ℝ (convexResolvent f) (x + g) : E →L[ℝ] E) : E →ₗ[ℝ] E).det ≠ 0 := hdet
    have hker : LinearMap.ker ((fderiv ℝ (convexResolvent f) (x + g) : E →L[ℝ] E) : E →ₗ[ℝ] E) =
        ⊥ := by
      by_contra hker
      exact hne (LinearMap.det_eq_zero_iff_ker_ne_bot.mpr hker)
    exact LinearMap.ker_eq_bot.mp hker
  have hdf : DifferentiableAt ℝ f (convexResolvent f (x + g)) := by rwa [hJy]
  have h4 := hasSecondOrderTaylor_of_subgradient_expansion hf
    (injectiveInv _ hA - ContinuousLinearMap.id ℝ E) (x + g - convexResolvent f (x + g))
    (convexResolvent f (x + g)) (subgradient_expansion hf hy2.hasFDerivAt hA hdf)
  rw [hJy] at h4
  set B₀ : E →L[ℝ] E := injectiveInv _ hA - ContinuousLinearMap.id ℝ E with hB₀
  refine ⟨x + g - x, (1 / 2 : ℝ) • (B₀ + star B₀), ?_, ?_⟩
  · exact (IsSelfAdjoint.all (1 / 2 : ℝ)).smul (IsSelfAdjoint.add_star_self B₀)
  · have hquad : ∀ v : E, ⟪((1 / 2 : ℝ) • (B₀ + star B₀)) v, v⟫_ℝ = ⟪B₀ v, v⟫_ℝ := by
      intro v
      simp only [smul_apply, add_apply, real_inner_smul_left,
        inner_add_left, ContinuousLinearMap.star_eq_adjoint, ContinuousLinearMap.adjoint_inner_left,
        real_inner_comm v (B₀ v)]
      ring
    have hfun : (fun y => f y - f x - ⟪x + g - x, y - x⟫_ℝ -
        1 / 2 * ⟪((1 / 2 : ℝ) • (B₀ + star B₀)) (y - x), y - x⟫_ℝ) =
        fun y => f y - f x - ⟪x + g - x, y - x⟫_ℝ - 1 / 2 * ⟪B₀ (y - x), y - x⟫_ℝ := by
      funext y
      rw [hquad]
    rw [hfun]
    exact h4

end LatticeProb.ConvexAnalysis
