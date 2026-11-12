import Mathlib

/-!
# Joint continuity of circle averages in the centre and the radius

Mathlib proves that `r ↦ Real.circleAverage f c r` is continuous for a fixed centre `c`
(`ContinuousOn.circleAverage`). Here the centre moves as well: if `f` is continuous on an open set `U`
containing the circle `∂B(z₀, r₀)` with `r₀ > 0`, then `(z, r) ↦ Real.circleAverage f z r` is continuous
at `(z₀, r₀)`.

Route: the compact circle has a thickening of some width `δ` inside `U`; for `|z - z₀| < δ/2` and
`|r - r₀| < δ/2` every point `z + r e^{iθ}` lies within `δ` of `z₀ + r₀ e^{iθ}`, so the integrand
`(z, r, θ) ↦ f (z + r e^{iθ})` is continuous on that neighbourhood times `ℝ`, and the parametric interval
integral is continuous there.

The case of a function continuous off one point `a` (a logarithmic singularity, say) is
`continuousAt_circleAverage_of_continuousOn_compl`: it applies whenever the circle avoids `a`, that is
`dist z₀ a ≠ r₀`.
-/

open Complex Filter Metric Real Set MeasureTheory Topology

noncomputable section

namespace LatticeProb.CircleAverageCentreContinuity

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Points of circles with nearby centres and radii, at the same angle, are close. -/
theorem dist_circleMap_circleMap_le (z w : ℂ) (r s θ : ℝ) :
    dist (circleMap z r θ) (circleMap w s θ) ≤ dist z w + |r - s| := by
  rw [dist_eq_norm, dist_eq_norm]
  have h : circleMap z r θ - circleMap w s θ = (z - w) + ((r - s : ℝ) : ℂ) * exp (θ * I) := by
    simp only [circleMap]
    push_cast
    ring
  rw [h]
  calc ‖(z - w) + ((r - s : ℝ) : ℂ) * exp (θ * I)‖
      ≤ ‖z - w‖ + ‖((r - s : ℝ) : ℂ) * exp (θ * I)‖ := norm_add_le _ _
    _ = ‖z - w‖ + |r - s| := by
      rw [norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one, Complex.norm_real, Real.norm_eq_abs]

/-- **Joint continuity of circle averages.** If `f` is continuous on an open set `U` containing the circle
`∂B(z₀, r₀)`, `r₀ > 0`, then `(z, r) ↦ Real.circleAverage f z r` is continuous at `(z₀, r₀)`. -/
theorem continuousAt_circleAverage_prod {f : ℂ → E} {U : Set ℂ} (hU : IsOpen U)
    (hf : ContinuousOn f U) {z₀ : ℂ} {r₀ : ℝ} (hr₀ : 0 < r₀) (hsub : sphere z₀ r₀ ⊆ U) :
    ContinuousAt (fun p : ℂ × ℝ => Real.circleAverage f p.1 p.2) (z₀, r₀) := by
  obtain ⟨δ, hδ, hδU⟩ := (isCompact_sphere z₀ r₀).exists_thickening_subset_open hU hsub
  set V : Set (ℂ × ℝ) := ball z₀ (δ / 2) ×ˢ ball r₀ (δ / 2) with hV
  have hVo : IsOpen V := isOpen_ball.prod isOpen_ball
  have hmem : (z₀, r₀) ∈ V := ⟨mem_ball_self (half_pos hδ), mem_ball_self (half_pos hδ)⟩
  have hin : ∀ p ∈ V, ∀ θ : ℝ, circleMap p.1 p.2 θ ∈ U := by
    intro p hp θ
    apply hδU
    rw [mem_thickening_iff]
    refine ⟨circleMap z₀ r₀ θ, circleMap_mem_sphere z₀ hr₀.le θ, ?_⟩
    have h1 : dist p.1 z₀ < δ / 2 := hp.1
    have h2 : dist p.2 r₀ < δ / 2 := hp.2
    rw [Real.dist_eq] at h2
    have := dist_circleMap_circleMap_le p.1 z₀ p.2 r₀ θ
    linarith
  have hcont : Continuous fun q : V × ℝ => f (circleMap q.1.1.1 q.1.1.2 q.2) := by
    refine hf.comp_continuous ?_ (fun q => hin q.1.1 q.1.2 q.2)
    have h : Continuous fun q : V × ℝ => (q.1.1.1, q.1.1.2, q.2) := by fun_prop
    exact (show Continuous fun x : ℂ × ℝ × ℝ => circleMap x.1 x.2.1 x.2.2 by
      unfold circleMap; fun_prop).comp h
  have hon : ContinuousOn (fun p : ℂ × ℝ => Real.circleAverage f p.1 p.2) V := by
    rw [continuousOn_iff_continuous_domRestrict]
    exact (intervalIntegral.continuous_parametric_intervalIntegral_of_continuous' (μ := volume)
      (f := fun (x : V) (θ : ℝ) => f (circleMap x.1.1 x.1.2 θ)) hcont 0 (2 * π)).const_smul
      (2 * π)⁻¹
  exact hon.continuousAt (hVo.mem_nhds hmem)

/-- Continuity of circle averages on the set of (centre, radius) pairs whose circle lies in `U`. -/
theorem continuousOn_circleAverage_prod {f : ℂ → E} {U : Set ℂ} (hU : IsOpen U)
    (hf : ContinuousOn f U) :
    ContinuousOn (fun p : ℂ × ℝ => Real.circleAverage f p.1 p.2)
      {p : ℂ × ℝ | 0 < p.2 ∧ sphere p.1 p.2 ⊆ U} := fun _ hp =>
  (continuousAt_circleAverage_prod hU hf hp.1 hp.2).continuousWithinAt

/-- **Continuity in the centre.** If `f` is continuous on an open set containing `∂B(z₀, r)`, `r > 0`,
then `z ↦ Real.circleAverage f z r` is continuous at `z₀`. -/
theorem continuousAt_circleAverage_centre {f : ℂ → E} {U : Set ℂ} (hU : IsOpen U)
    (hf : ContinuousOn f U) {z₀ : ℂ} {r : ℝ} (hr : 0 < r) (hsub : sphere z₀ r ⊆ U) :
    ContinuousAt (fun z : ℂ => Real.circleAverage f z r) z₀ :=
  (continuousAt_circleAverage_prod hU hf hr hsub).comp (f := fun z : ℂ => (z, r))
    (continuous_id.prodMk continuous_const).continuousAt

/-- Sequential form: circle averages along converging centres and radii converge. -/
theorem tendsto_circleAverage {ι : Type*} {l : Filter ι} {f : ℂ → E} {U : Set ℂ} (hU : IsOpen U)
    (hf : ContinuousOn f U) {z₀ : ℂ} {r₀ : ℝ} (hr₀ : 0 < r₀) (hsub : sphere z₀ r₀ ⊆ U)
    {z : ι → ℂ} {r : ι → ℝ} (hz : Tendsto z l (𝓝 z₀)) (hr : Tendsto r l (𝓝 r₀)) :
    Tendsto (fun i => Real.circleAverage f (z i) (r i)) l (𝓝 (Real.circleAverage f z₀ r₀)) :=
  (continuousAt_circleAverage_prod hU hf hr₀ hsub).tendsto.comp (hz.prodMk_nhds hr)

/-- A circle avoids the point `a` exactly when its radius differs from the distance of its centre
to `a`. -/
theorem sphere_subset_compl_singleton_iff {z a : ℂ} {r : ℝ} :
    sphere z r ⊆ {a}ᶜ ↔ dist a z ≠ r := by
  constructor
  · intro h hd
    exact h (mem_sphere.2 hd) rfl
  · intro hd x hx hxa
    rw [mem_singleton_iff] at hxa
    subst hxa
    exact hd (mem_sphere.1 hx)

/-- **Functions continuous off one point.** If `f` is continuous on `ℂ ∖ {a}` and the circle `∂B(z₀, r₀)`
avoids `a` (`dist a z₀ ≠ r₀`), then `(z, r) ↦ Real.circleAverage f z r` is continuous at `(z₀, r₀)`. -/
theorem continuousAt_circleAverage_of_continuousOn_compl {f : ℂ → E} {a z₀ : ℂ} {r₀ : ℝ}
    (hf : ContinuousOn f {a}ᶜ) (hr₀ : 0 < r₀) (ha : dist a z₀ ≠ r₀) :
    ContinuousAt (fun p : ℂ × ℝ => Real.circleAverage f p.1 p.2) (z₀, r₀) :=
  continuousAt_circleAverage_prod isOpen_compl_singleton hf hr₀
    (sphere_subset_compl_singleton_iff.2 ha)

end LatticeProb.CircleAverageCentreContinuity
