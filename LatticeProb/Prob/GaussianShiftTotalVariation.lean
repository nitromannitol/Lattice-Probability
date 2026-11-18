import LatticeProb.Bonanno.QuantumZipper.Proofs.Section5.TVLocal
import LatticeProb.Prob.Pinsker
import LatticeProb.Prob.KlDivGaussian

/-!
# Total variation between Gaussian laws with a common variance

For a common variance `v ≠ 0`, the total variation distance between `N(a, v)` and `N(b, v)` is
at most `|b - a| / (2 √v)`: Pinsker's inequality applied to the relative entropy `m² / (2v)` of a
mean shift `m`. Total variation is subadditive over the two factors of a product law, so the law
`N(z, v I₂)` on `ℂ` (the time-`v` transition law of planar Brownian motion from `z`) satisfies

  `tvDist (N(z, v I₂)) (N(w, v I₂)) ≤ ‖w - z‖ / √v`,

and is therefore continuous in total variation in its mean: the strong Feller property of the
planar heat semigroup.

## Main statements

* `LatticeProb.tvDist_le_ofReal_of_forall_abs_le`: a uniform bound on `|μ A - ν A|` over
  measurable events bounds `tvDist μ ν`.
* `LatticeProb.tvDist_gaussianReal_le`: the one-dimensional bound.
* `LatticeProb.tvDist_prod_le_add`: total variation of product laws.
* `LatticeProb.tvDist_complexGaussian_le` and `LatticeProb.tendsto_tvDist_complexGaussian`: the
  planar bound and the continuity in the mean.
-/

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology

namespace LatticeProb

open QuantumZipper.TV

/-- A uniform bound on `|μ A - ν A|` over measurable events `A` bounds the total variation
distance of two finite measures. -/
theorem tvDist_le_ofReal_of_forall_abs_le {α : Type*} [MeasurableSpace α] (μ ν : Measure α)
    [IsFiniteMeasure μ] [IsFiniteMeasure ν] {c : ℝ}
    (h : ∀ A, MeasurableSet A → |μ.real A - ν.real A| ≤ c) :
    tvDist μ ν ≤ ENNReal.ofReal c := by
  refine iSup_le fun s => iSup_le fun hs => sup_le ?_ ?_
  · rw [← ofReal_measureReal (μ := μ) (s := s) (measure_ne_top μ s),
      ← ofReal_measureReal (μ := ν) (s := s) (measure_ne_top ν s),
      ← ENNReal.ofReal_sub _ measureReal_nonneg]
    exact ENNReal.ofReal_le_ofReal ((le_abs_self _).trans (h s hs))
  · rw [← ofReal_measureReal (μ := μ) (s := s) (measure_ne_top μ s),
      ← ofReal_measureReal (μ := ν) (s := s) (measure_ne_top ν s),
      ← ENNReal.ofReal_sub _ measureReal_nonneg]
    exact ENNReal.ofReal_le_ofReal
      ((le_abs_self _).trans ((abs_sub_comm _ _).le.trans (h s hs)))

/-- **Total variation between Gaussians with a common variance.** For `v ≠ 0`,
`tvDist (N(a, v)) (N(b, v)) ≤ |b - a| / (2 √v)` (Pinsker's inequality). -/
theorem tvDist_gaussianReal_le (a b : ℝ) {v : ℝ≥0} (hv : v ≠ 0) :
    tvDist (gaussianReal a v) (gaussianReal b v) ≤
      ENNReal.ofReal (|b - a| / (2 * Real.sqrt v)) := by
  have hv0 : (0 : ℝ) < v := NNReal.coe_pos.mpr (pos_iff_ne_zero.mpr hv)
  have h0 : tvDist (gaussianReal 0 v) (gaussianReal (b - a) v) ≤
      ENNReal.ofReal (|b - a| / (2 * Real.sqrt v)) := by
    apply tvDist_le_ofReal_of_forall_abs_le
    intro A hA
    have hp := pinsker ℝ (gaussianReal 0 v) (gaussianReal (b - a) v) A hA
      ((b - a) ^ 2 / (2 * v)) (by positivity) (klDiv_gaussianReal_shift hv (b - a)).le
    refine hp.trans (le_of_eq ?_)
    rw [show (b - a) ^ 2 / (2 * (v : ℝ)) / 2 = (|b - a| / (2 * Real.sqrt v)) ^ 2 by
      rw [div_pow, mul_pow, Real.sq_sqrt hv0.le, sq_abs]; ring]
    exact Real.sqrt_sq (by positivity)
  calc tvDist (gaussianReal a v) (gaussianReal b v)
      = tvDist ((gaussianReal 0 v).map (· + a)) ((gaussianReal (b - a) v).map (· + a)) := by
        rw [gaussianReal_map_add_const (μ := 0) (v := v) a,
          gaussianReal_map_add_const (μ := b - a) (v := v) a, zero_add, sub_add_cancel]
    _ ≤ tvDist (gaussianReal 0 v) (gaussianReal (b - a) v) :=
        tvDist_map_le (measurable_add_const a)
    _ ≤ _ := h0

/-- Total variation between product probability laws is at most the sum of the total variation
distances of the factors. -/
theorem tvDist_prod_le_add {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (μ₁ ν₁ : Measure α) (μ₂ ν₂ : Measure β) [IsProbabilityMeasure μ₁] [IsProbabilityMeasure ν₁]
    [IsProbabilityMeasure μ₂] [IsProbabilityMeasure ν₂] :
    tvDist (μ₁.prod μ₂) (ν₁.prod ν₂) ≤ tvDist μ₁ ν₁ + tvDist μ₂ ν₂ := by
  have hswap : tvDist (ν₁.prod μ₂) (ν₁.prod ν₂) ≤ tvDist μ₂ ν₂ := by
    rw [← Measure.prod_swap (μ := μ₂) (ν := ν₁), ← Measure.prod_swap (μ := ν₂) (ν := ν₁)]
    exact (tvDist_map_le measurable_swap).trans tvDist_prod_right_le
  exact (tvDist_triangle (ν := ν₁.prod μ₂)).trans (add_le_add tvDist_prod_right_le hswap)

/-- **Strong Feller bound for the planar Gaussian.** The law `N(z, v I₂)` on `ℂ`, written as the
image of `N(Re z, v) ⊗ N(Im z, v)`, satisfies `tvDist (N(z, v I₂)) (N(w, v I₂)) ≤ ‖w - z‖ / √v`
for `v ≠ 0`. -/
theorem tvDist_complexGaussian_le (z w : ℂ) {v : ℝ≥0} (hv : v ≠ 0) :
    tvDist (((gaussianReal z.re v).prod (gaussianReal z.im v)).map
        Complex.measurableEquivRealProd.symm)
      (((gaussianReal w.re v).prod (gaussianReal w.im v)).map
        Complex.measurableEquivRealProd.symm) ≤
      ENNReal.ofReal (‖w - z‖ / Real.sqrt v) := by
  have hv0 : (0 : ℝ) < v := NNReal.coe_pos.mpr (pos_iff_ne_zero.mpr hv)
  have hs : 0 < Real.sqrt v := Real.sqrt_pos.mpr hv0
  refine (tvDist_map_le Complex.measurableEquivRealProd.symm.measurable).trans ?_
  refine (tvDist_prod_le_add _ _ _ _).trans ?_
  refine (add_le_add (tvDist_gaussianReal_le _ _ hv) (tvDist_gaussianReal_le _ _ hv)).trans ?_
  rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
  apply ENNReal.ofReal_le_ofReal
  have h1 : |w.re - z.re| ≤ ‖w - z‖ := by simpa using Complex.abs_re_le_norm (w - z)
  have h2 : |w.im - z.im| ≤ ‖w - z‖ := by simpa using Complex.abs_im_le_norm (w - z)
  have h2s : (0 : ℝ) < 2 * Real.sqrt v := by positivity
  calc |w.re - z.re| / (2 * Real.sqrt v) + |w.im - z.im| / (2 * Real.sqrt v)
      ≤ ‖w - z‖ / (2 * Real.sqrt v) + ‖w - z‖ / (2 * Real.sqrt v) :=
        add_le_add ((div_le_div_iff_of_pos_right h2s).mpr h1)
          ((div_le_div_iff_of_pos_right h2s).mpr h2)
    _ = ‖w - z‖ / Real.sqrt v := by ring

/-- **Strong Feller property of the planar heat semigroup.** For `v ≠ 0`, the law
`N(w, v I₂)` on `ℂ` converges in total variation to `N(z, v I₂)` as `w → z`. -/
theorem tendsto_tvDist_complexGaussian (z : ℂ) {v : ℝ≥0} (hv : v ≠ 0) :
    Tendsto (fun w : ℂ => tvDist
        (((gaussianReal w.re v).prod (gaussianReal w.im v)).map
          Complex.measurableEquivRealProd.symm)
        (((gaussianReal z.re v).prod (gaussianReal z.im v)).map
          Complex.measurableEquivRealProd.symm)) (𝓝 z) (𝓝 0) := by
  have hc : Continuous fun w : ℂ => ‖z - w‖ / Real.sqrt v := by fun_prop
  have hlim : Tendsto (fun w : ℂ => ENNReal.ofReal (‖z - w‖ / Real.sqrt v)) (𝓝 z) (𝓝 0) := by
    have h : Tendsto (fun w : ℂ => ENNReal.ofReal (‖z - w‖ / Real.sqrt v)) (𝓝 z)
        (𝓝 (ENNReal.ofReal (‖z - z‖ / Real.sqrt v))) := (ENNReal.continuous_ofReal.comp hc).tendsto z
    rwa [sub_self, norm_zero, zero_div, ENNReal.ofReal_zero] at h
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hlim
    (fun _ => zero_le) (fun w => tvDist_complexGaussian_le w z hv)

end LatticeProb
