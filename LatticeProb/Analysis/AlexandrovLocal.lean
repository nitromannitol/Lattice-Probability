import LatticeProb.Analysis.ConvexResolvent

/-!
# The expansion of the subgradients of a convex function at a differentiability point of its resolvent

Let `f` be a convex function on a finite-dimensional real inner product space `E` and let
`J = convexResolvent f` be its resolvent, so that `y - J y ∈ ∂f (J y)` and `J (z + g) = z` whenever
`g ∈ ∂f z`. Suppose that

* `J` is differentiable at `y₀` with injective derivative `A`, and
* `f` is differentiable at `x₀ = J y₀`.

Then `∇f x₀ = y₀ - x₀` and every subgradient `g` of `f` at a point `x₀ + h` satisfies
`g = (y₀ - x₀) + (A⁻¹ - 1) h + o(‖h‖)`, uniformly in the choice of the subgradient.

The argument: for `g ∈ ∂f (x₀ + h)` the point `x' = x₀ + h + g` satisfies `J x' = x₀ + h`, and
`x' → y₀` as `h → 0` because the subgradients at points near `x₀` are close to `∇f x₀`. Since `J` is
differentiable at `y₀` with injective derivative, `h = J x' - J y₀ = A (x' - y₀) + o(‖x' - y₀‖)`, and
inverting `A` gives `x' - y₀ = A⁻¹ h + o(‖h‖)`.

## Main results

* `LatticeProb.ConvexAnalysis.injectiveInv`: the inverse of an injective endomorphism of a
  finite-dimensional space.
* `LatticeProb.ConvexAnalysis.subgradient_expansion`: the expansion of the subgradients.
-/

open Set Topology
open scoped InnerProductSpace

namespace LatticeProb.ConvexAnalysis

section Differentiability

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Quantitative form of differentiability of a map `F : E → E` at `y₀` with derivative `A`. -/
theorem exists_forall_norm_sub_le_of_hasFDerivAt {F : E → E} {A : E →L[ℝ] E} {y₀ : E}
    (hF : HasFDerivAt F A y₀) {η : ℝ} (hη : 0 < η) :
    ∃ ρ > 0, ∀ u : E, ‖u‖ < ρ → ‖F (y₀ + u) - F y₀ - A u‖ ≤ η * ‖u‖ := by
  have h := hF.isLittleO.def hη
  obtain ⟨ρ, hρ, hball⟩ := Metric.eventually_nhds_iff.mp h
  refine ⟨ρ, hρ, fun u hu => ?_⟩
  have := hball (y := y₀ + u) (by rwa [dist_eq_norm, add_sub_cancel_left])
  simpa using this

end Differentiability

section Inverse

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

/-- The inverse of an injective continuous linear endomorphism of a finite-dimensional space. -/
noncomputable def injectiveInv (A : E →L[ℝ] E) (hA : Function.Injective A) : E →L[ℝ] E :=
  LinearMap.toContinuousLinearMap
    (LinearEquiv.ofInjectiveEndo (A : E →ₗ[ℝ] E) hA).symm.toLinearMap

theorem injectiveInv_apply_apply (A : E →L[ℝ] E) (hA : Function.Injective A) (x : E) :
    injectiveInv A hA (A x) = x := by
  have h := (LinearEquiv.ofInjectiveEndo (A : E →ₗ[ℝ] E) hA).symm_apply_apply x
  simpa [injectiveInv] using h

theorem apply_injectiveInv (A : E →L[ℝ] E) (hA : Function.Injective A) (x : E) :
    A (injectiveInv A hA x) = x := by
  exact (LinearEquiv.ofInjectiveEndo (A : E →ₗ[ℝ] E) hA).apply_symm_apply x

end Inverse

section Expansion

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  {f : E → ℝ}

/-- If the resolvent `J` of a convex function `f` is differentiable at `y₀` with injective derivative
`A`, and `f` is differentiable at `J y₀`, then every subgradient `g` of `f` at `J y₀ + h` is
`(y₀ - J y₀) + (A⁻¹ - 1) h + o(‖h‖)`, with `A⁻¹` the inverse of `A`. -/
theorem subgradient_expansion (hf : ConvexOn ℝ Set.univ f) {y₀ : E} {A : E →L[ℝ] E}
    (hJ : HasFDerivAt (convexResolvent f) A y₀) (hA : Function.Injective A)
    (hd : DifferentiableAt ℝ f (convexResolvent f y₀)) :
    ∀ ε > 0, ∃ r > 0, ∀ h : E, ‖h‖ < r → ∀ g, IsSubgradientAt f (convexResolvent f y₀ + h) g →
      ‖g - (y₀ - convexResolvent f y₀) - (injectiveInv A hA - ContinuousLinearMap.id ℝ E) h‖ ≤
        ε * ‖h‖ := by
  intro ε hε
  have hp : HasGradientAt f (y₀ - convexResolvent f y₀) (convexResolvent f y₀) := by
    have h1 := (isSubgradientAt_convexResolvent hf y₀).eq_of_hasGradientAt hd.hasGradientAt
    rw [h1]
    exact hd.hasGradientAt
  set A' := injectiveInv A hA with hA'
  set C : ℝ := ‖A'‖ + 1 with hCdef
  have hC : 0 < C := by positivity
  set η : ℝ := min (1 / (2 * C)) (ε / (2 * C ^ 2)) with hη
  have hηpos : 0 < η := lt_min (by positivity) (by positivity)
  have hη1 : η * C ≤ 1 / 2 :=
    calc η * C ≤ 1 / (2 * C) * C := mul_le_mul_of_nonneg_right (min_le_left _ _) hC.le
      _ = 1 / 2 := by field_simp
  have hη2 : η * (2 * C ^ 2) ≤ ε :=
    calc η * (2 * C ^ 2) ≤ ε / (2 * C ^ 2) * (2 * C ^ 2) :=
          mul_le_mul_of_nonneg_right (min_le_right _ _) (by positivity)
      _ = ε := by field_simp
  obtain ⟨ρ, hρ, hJρ⟩ := exists_forall_norm_sub_le_of_hasFDerivAt hJ hηpos
  obtain ⟨r₁, hr₁, hr₁'⟩ := tendsto_isSubgradientAt hf hp (ρ / 2) (half_pos hρ)
  refine ⟨min r₁ (ρ / 2), lt_min hr₁ (half_pos hρ), fun h hh g hg => ?_⟩
  have hh1 : ‖h‖ < r₁ := lt_of_lt_of_le hh (min_le_left _ _)
  have hh2 : ‖h‖ < ρ / 2 := lt_of_lt_of_le hh (min_le_right _ _)
  have hgp : ‖g - (y₀ - convexResolvent f y₀)‖ < ρ / 2 :=
    hr₁' (convexResolvent f y₀ + h) (by rw [dist_eq_norm, add_sub_cancel_left]; exact hh1) g hg
  set u : E := h + (g - (y₀ - convexResolvent f y₀)) with hu
  have hu_lt : ‖u‖ < ρ :=
    calc ‖u‖ ≤ ‖h‖ + ‖g - (y₀ - convexResolvent f y₀)‖ := norm_add_le _ _
      _ < ρ / 2 + ρ / 2 := add_lt_add hh2 hgp
      _ = ρ := by ring
  have hJx : convexResolvent f (y₀ + u) = convexResolvent f y₀ + h := by
    have e : y₀ + u = convexResolvent f y₀ + h + g := by rw [hu]; abel
    rw [e]
    exact convexResolvent_eq_of_isSubgradientAt hf hg
  have hJ1 := hJρ u hu_lt
  rw [hJx, add_sub_cancel_left] at hJ1
  have hAu : A' (A u) = u := injectiveInv_apply_apply A hA u
  have h1 : ‖u‖ ≤ C * ‖A u‖ :=
    calc ‖u‖ = ‖A' (A u)‖ := by rw [hAu]
      _ ≤ ‖A'‖ * ‖A u‖ := A'.le_opNorm _
      _ ≤ C * ‖A u‖ := mul_le_mul_of_nonneg_right (by linarith) (norm_nonneg _)
  have h2 : ‖A u‖ ≤ ‖h‖ + η * ‖u‖ :=
    calc ‖A u‖ = ‖h - (h - A u)‖ := by congr 1; abel
      _ ≤ ‖h‖ + ‖h - A u‖ := norm_sub_le _ _
      _ ≤ ‖h‖ + η * ‖u‖ := by linarith
  have h3 : ‖u‖ ≤ 2 * C * ‖h‖ := by
    have h4 := mul_le_mul_of_nonneg_left h2 hC.le
    have h5 := mul_le_mul_of_nonneg_right hη1 (norm_nonneg u)
    nlinarith [h1, h4, h5]
  have e : g - (y₀ - convexResolvent f y₀) - (A' - ContinuousLinearMap.id ℝ E) h = u - A' h := by
    simp only [sub_apply, ContinuousLinearMap.id_apply, hu]
    abel
  rw [e]
  have h6 : u - A' h = A' (A u - h) := by rw [map_sub, hAu]
  have h7 : ‖A u - h‖ ≤ η * ‖u‖ := by rw [norm_sub_rev]; exact hJ1
  calc ‖u - A' h‖ = ‖A' (A u - h)‖ := by rw [h6]
    _ ≤ ‖A'‖ * ‖A u - h‖ := A'.le_opNorm _
    _ ≤ C * (η * ‖u‖) := mul_le_mul (by linarith) h7 (norm_nonneg _) hC.le
    _ ≤ C * (η * (2 * C * ‖h‖)) := by gcongr
    _ = (η * (2 * C ^ 2)) * ‖h‖ := by ring
    _ ≤ ε * ‖h‖ := mul_le_mul_of_nonneg_right hη2 (norm_nonneg _)

end Expansion

end LatticeProb.ConvexAnalysis
