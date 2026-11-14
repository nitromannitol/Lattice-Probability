import Mathlib
import LatticeProb.Analysis.MorreyOscillation

/-!
# A sup bound for the gradient of a `C²` function on a ball

Let `E` be a finite-dimensional real inner product space of dimension `d` with an additive Haar
measure `μ`, and let `d < p < ∞`. If `w : E → ℝ` is `C²` on the ball `B(a, R)` with `|w| ≤ K`
there, then for `0 < ρ < R` and every `z ∈ B(a, R - ρ)`,
`‖D w(z)‖ ≤ 2 K / ρ + C R^{1 - d/p} ‖D² w‖_{L^p(B(a, R))}`,
with a constant `C` that depends only on `E`, `μ` and `p`.

For a unit vector `v`, the mean value theorem on `t ↦ w (z + t v)` over `[0, ρ]` gives a point
`ξ ∈ (0, ρ)` with `|D w(z + ξ v) v| ≤ 2 K / ρ`. Morrey's oscillation estimate for `D w`
(`morrey_oscillation`) bounds `‖D w(z) - D w(z + ξ v)‖`, and the supremum over unit vectors is the
operator norm of `D w(z)`.

## Main results

* `LatticeProb.PegdenSmart.gradient_sup_bound`: the sup bound.
-/

open MeasureTheory Metric Set
open scoped ENNReal NNReal

namespace LatticeProb.PegdenSmart

/-- Sup bound for the gradient of a `C²` function on a ball from its sup norm and the `L^p` norm of
its Hessian, for `d < p < ∞`: the constant depends on `E`, `μ` and `p` only. -/
theorem gradient_sup_bound (E : Type) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [Nontrivial E] (μ : Measure E)
    [μ.IsAddHaarMeasure] (p : ℝ≥0∞) :
    (Module.finrank ℝ E : ℝ≥0∞) < p → p ≠ ⊤ →
    ∃ C : ℝ≥0, ∀ (w : E → ℝ) (a : E) (R ρ K : ℝ), 0 < ρ → ρ < R → 0 ≤ K →
      ContDiffOn ℝ 2 w (ball a R) → (∀ y ∈ ball a R, |w y| ≤ K) →
      ∀ z ∈ ball a (R - ρ),
        ‖fderiv ℝ w z‖ₑ ≤ ENNReal.ofReal (2 * K / ρ) +
          (C : ℝ≥0∞) * ENNReal.ofReal R ^ (1 - (Module.finrank ℝ E : ℝ) / p.toReal) *
            eLpNorm (fderiv ℝ (fderiv ℝ w)) p (μ.restrict (ball a R)) := by
  intro hdp hp
  obtain ⟨C, hC⟩ := morrey_oscillation E μ p hdp hp
  refine ⟨C, ?_⟩
  intro w a R ρ K hρ hρR hK hw hwK z hz
  set T : ℝ≥0∞ := (C : ℝ≥0∞) * ENNReal.ofReal R ^ (1 - (Module.finrank ℝ E : ℝ) / p.toReal) *
    eLpNorm (fderiv ℝ (fderiv ℝ w)) p (μ.restrict (ball a R)) with hT_def
  rcases eq_or_ne T ⊤ with hT | hT
  · rw [hT, add_top]
    exact le_top
  have hR : 0 < R := hρ.trans hρR
  have hzR : z ∈ ball a R := ball_subset_ball (by linarith) hz
  have hKρ : 0 ≤ 2 * K / ρ := div_nonneg (by linarith) hρ.le
  have hw1 : ContDiffOn ℝ 1 (fderiv ℝ w) (ball a R) :=
    hw.fderiv_of_isOpen isOpen_ball (by norm_num)
  have hdiff : DifferentiableOn ℝ w (ball a R) := hw.differentiableOn (by norm_num)
  have hseg : ∀ v : E, ‖v‖ = 1 → ∀ t ∈ Icc 0 ρ, z + t • v ∈ ball a R := by
    intro v hv t ht
    rw [mem_ball] at hz ⊢
    have hdist : dist (z + t • v) z = t := by
      rw [dist_eq_norm, add_sub_cancel_left, norm_smul, hv, mul_one, Real.norm_of_nonneg ht.1]
    calc dist (z + t • v) a ≤ dist (z + t • v) z + dist z a := dist_triangle _ _ _
      _ < R := by linarith [ht.2]
  have hbound : ∀ v : E, ‖v‖ = 1 → ‖fderiv ℝ w z v‖ ≤ 2 * K / ρ + T.toReal := by
    intro v hv
    have hcont : ContinuousOn (fun t : ℝ => w (z + t • v)) (Icc 0 ρ) :=
      hw.continuousOn.comp (by fun_prop) fun t ht => hseg v hv t ht
    have hderiv : ∀ t ∈ Ioo 0 ρ,
        HasDerivAt (fun t : ℝ => w (z + t • v)) (fderiv ℝ w (z + t • v) v) t := by
      intro t ht
      have hmem := hseg v hv t (Ioo_subset_Icc_self ht)
      have h1 : HasDerivAt (fun t : ℝ => z + t • v) v t := by
        simpa using ((hasDerivAt_id' t).smul_const v).const_add z
      exact ((hdiff.differentiableAt (isOpen_ball.mem_nhds hmem)).hasFDerivAt).comp_hasDerivAt t h1
    obtain ⟨ξ, hξ, hslope⟩ := exists_hasDerivAt_eq_slope (fun t : ℝ => w (z + t • v))
      (fun t => fderiv ℝ w (z + t • v) v) hρ hcont hderiv
    have hslope' : fderiv ℝ w (z + ξ • v) v = (w (z + ρ • v) - w z) / ρ := by
      simpa using hslope
    have hξmem : z + ξ • v ∈ ball a R := hseg v hv ξ (Ioo_subset_Icc_self hξ)
    have h1 : ‖fderiv ℝ w (z + ξ • v) v‖ ≤ 2 * K / ρ := by
      rw [Real.norm_eq_abs, hslope', abs_div, abs_of_pos hρ, div_le_div_iff_of_pos_right hρ]
      have h₁ := hwK _ (hseg v hv ρ ⟨hρ.le, le_rfl⟩)
      have h₂ := hwK _ hzR
      calc |w (z + ρ • v) - w z| ≤ |w (z + ρ • v)| + |w z| := abs_sub _ _
        _ ≤ 2 * K := by linarith
    have h2 : ‖fderiv ℝ w z - fderiv ℝ w (z + ξ • v)‖ ≤ T.toReal := by
      have h := hC (E →L[ℝ] ℝ) (fderiv ℝ w) a R hR hw1 z hzR _ hξmem
      rw [← ofReal_norm] at h
      exact (ENNReal.ofReal_le_iff_le_toReal hT).mp h
    have e : fderiv ℝ w z v =
        fderiv ℝ w (z + ξ • v) v + (fderiv ℝ w z - fderiv ℝ w (z + ξ • v)) v := by
      rw [sub_apply]
      ring
    calc ‖fderiv ℝ w z v‖
        ≤ ‖fderiv ℝ w (z + ξ • v) v‖ + ‖(fderiv ℝ w z - fderiv ℝ w (z + ξ • v)) v‖ := by
          rw [e]
          exact norm_add_le _ _
      _ ≤ 2 * K / ρ + ‖fderiv ℝ w z - fderiv ℝ w (z + ξ • v)‖ * ‖v‖ :=
          add_le_add h1 (ContinuousLinearMap.le_opNorm _ _)
      _ ≤ 2 * K / ρ + T.toReal := by
          rw [hv, mul_one]
          linarith
  have hop : ‖fderiv ℝ w z‖ ≤ 2 * K / ρ + T.toReal :=
    ContinuousLinearMap.opNorm_le_of_unit_norm (add_nonneg hKρ ENNReal.toReal_nonneg) hbound
  calc ‖fderiv ℝ w z‖ₑ = ENNReal.ofReal ‖fderiv ℝ w z‖ := (ofReal_norm _).symm
    _ ≤ ENNReal.ofReal (2 * K / ρ + T.toReal) := ENNReal.ofReal_le_ofReal hop
    _ = ENNReal.ofReal (2 * K / ρ) + T := by
        rw [ENNReal.ofReal_add hKρ ENNReal.toReal_nonneg, ENNReal.ofReal_toReal hT]

end LatticeProb.PegdenSmart
