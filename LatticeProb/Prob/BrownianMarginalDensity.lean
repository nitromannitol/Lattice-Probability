import LatticeProb.Prob.BrownianExit
import LatticeProb.Prob.GaussDensity

/-!
# The marginal density of Brownian motion on `ℝ ^ d`

For the motion of `LatticeProb.IsBrownianSpace` started at `x`, whose generator is `Δ / (2 d)`,
the position at a time `t > 0` has the density
`brownianHeatKernel d t x y = (2 π t / d) ^ (- d / 2) * exp (- d ‖x - y‖ ^ 2 / (2 t))`
with respect to Lebesgue measure.

Each coordinate of `B t - x`, scaled by `√d`, is a standard real Brownian motion at time `t`, so
the `i`-th coordinate of `B t` is Gaussian with mean `x i` and variance `t / d`. The coordinates
are independent, so the law of `B t` is the product of these Gaussians, whose density is the
product of the one-dimensional Gaussian densities; that product is the heat kernel.
-/

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

noncomputable section

namespace LatticeProb

/-- The transition density of Brownian motion on `ℝ ^ d` with generator `Δ / (2 d)`. -/
noncomputable def brownianHeatKernel (d : ℕ) (t : ℝ) (x y : EuclideanSpace ℝ (Fin d)) : ℝ :=
  (2 * Real.pi * t / d) ^ (-(d : ℝ) / 2) * Real.exp (-(d : ℝ) * ‖x - y‖ ^ 2 / (2 * t))

/-- The product of the one-dimensional Gaussian densities of variance `t / d` centred at the
coordinates of `x` is the heat kernel. -/
theorem prod_gaussianPDFReal_eq_brownianHeatKernel {d : ℕ} (hd : 1 ≤ d) {t : ℝ}
    {v : ℝ≥0} (hv : (v : ℝ) = t / d) (x y : EuclideanSpace ℝ (Fin d)) :
    ∏ i, gaussianPDFReal (x i) v (y i) = brownianHeatKernel d t x y := by
  have hdpos : (0 : ℝ) < d := by exact_mod_cast hd
  have hnorm : ‖x - y‖ ^ 2 = ∑ i, (y i - x i) ^ 2 := by
    rw [EuclideanSpace.norm_eq, Real.sq_sqrt (Finset.sum_nonneg fun i _ => sq_nonneg _)]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Real.norm_eq_abs, sq_abs, PiLp.sub_apply]
    ring
  have hpos : (0 : ℝ) ≤ 2 * Real.pi * v := by positivity
  simp only [gaussianPDFReal]
  rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin,
    ← Real.exp_sum, brownianHeatKernel, hnorm]
  congr 1
  · rw [Real.sqrt_eq_rpow, ← Real.rpow_neg hpos, ← Real.rpow_natCast, ← Real.rpow_mul hpos, hv]
    congr 1
    · ring
    · ring
  · rw [← Finset.sum_div, Finset.sum_neg_distrib, hv]
    field_simp

/-- **The marginal density of Brownian motion.** For the motion of `IsBrownianSpace` on `ℝ ^ d`,
`1 ≤ d`, started at `x`, the law of `B t` at a time `t > 0` has the density
`brownianHeatKernel d t x` with respect to Lebesgue measure. -/
theorem IsBrownianSpace.map_eq_withDensity {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    {d : ℕ} (hd : 1 ≤ d) (x : EuclideanSpace ℝ (Fin d)) (B : ℝ≥0 → Ω → EuclideanSpace ℝ (Fin d))
    (hB : IsBrownianSpace d x B P) (hm : ∀ t, Measurable (B t)) (t : ℝ≥0) (ht : 0 < t) :
    P.map (B t) = volume.withDensity fun y => ENNReal.ofReal (brownianHeatKernel d t x y) := by
  have hP : IsProbabilityMeasure P := hB.isProbabilityMeasure
  have hdpos : (0 : ℝ) < d := by exact_mod_cast hd
  have hsd : Real.sqrt d ≠ 0 := (Real.sqrt_pos.2 hdpos).ne'
  have htR : (0 : ℝ) < t := by exact_mod_cast ht
  obtain ⟨v, hv_def⟩ : ∃ v : ℝ≥0, v = NNReal.mk ((Real.sqrt d)⁻¹ ^ 2) (sq_nonneg _) * t :=
    ⟨_, rfl⟩
  have hvR : (v : ℝ) = t / d := by
    have h1 : (v : ℝ) = (Real.sqrt d)⁻¹ ^ 2 * t := by rw [hv_def]; rfl
    rw [h1, inv_pow, Real.sq_sqrt hdpos.le]
    field_simp
  have hv0 : v ≠ 0 := by
    intro h
    have h' : (v : ℝ) = 0 := by rw [h, NNReal.coe_zero]
    rw [hvR] at h'
    exact (div_pos htR hdpos).ne' h'
  have hcoordm : ∀ i : Fin d, Measurable fun ω => B t ω i := fun i =>
    (EuclideanSpace.proj i).continuous.measurable.comp (hm t)
  have hlaw : ∀ i : Fin d, P.map (fun ω => B t ω i) = gaussianReal (x i) v := by
    intro i
    have hW := (hB.coord i).hasLaw_eval t
    have hWm : Measurable fun ω => Real.sqrt d * (B t ω i - x i) :=
      measurable_const.mul ((hcoordm i).sub measurable_const)
    have hcomp : (fun ω => B t ω i) = (fun u => u + x i) ∘ (fun u => (Real.sqrt d)⁻¹ * u) ∘
        (fun ω => Real.sqrt d * (B t ω i - x i)) := by
      funext ω
      simp only [Function.comp]
      rw [← mul_assoc, inv_mul_cancel₀ hsd, one_mul, sub_add_cancel]
    rw [hcomp, ← Measure.map_map (by fun_prop) ((measurable_const_mul _).comp hWm),
      ← Measure.map_map (by fun_prop) hWm, hW.map_eq, gaussianReal_map_const_mul,
      gaussianReal_map_add_const, ← hv_def, mul_zero, zero_add]
  have hind : iIndepFun (fun (i : Fin d) (ω : Ω) => B t ω i) P :=
    hB.indep.comp (fun _ f => f t) (fun _ => measurable_pi_apply t)
  have hpi : P.map (fun ω i => B t ω i) = Measure.pi fun i => gaussianReal (x i) v := by
    rw [(iIndepFun_iff_map_fun_eq_pi_map (fun i => (hcoordm i).aemeasurable)).1 hind]
    congr 1
    funext i
    exact hlaw i
  have hprob : ∀ i : Fin d,
      IsProbabilityMeasure ((volume : Measure ℝ).withDensity (gaussianPDF (x i) v)) := fun i => by
    rw [← gaussianReal_of_var_ne_zero (x i) hv0]
    infer_instance
  have hdens : Measure.pi (fun i => gaussianReal (x i) v)
      = (volume : Measure (Fin d → ℝ)).withDensity fun z => ∏ i, gaussianPDF (x i) v (z i) := by
    have h1 : Measure.pi (fun i => gaussianReal (x i) v)
        = Measure.pi fun i => (volume : Measure ℝ).withDensity (gaussianPDF (x i) v) := by
      congr 1
      funext i
      exact gaussianReal_of_var_ne_zero (x i) hv0
    rw [h1, pi_withDensity_prod (fun _ : Fin d => (volume : Measure ℝ))
      (fun i => gaussianPDF (x i) v) (fun i => measurable_gaussianPDF (x i) v), ← volume_pi]
  have hmeas : Measurable fun z : Fin d → ℝ => ∏ i, gaussianPDF (x i) v (z i) :=
    Finset.measurable_prod _ fun i _ => (measurable_gaussianPDF (x i) v).comp (measurable_pi_apply i)
  have hBt : B t = (MeasurableEquiv.toLp 2 (Fin d → ℝ)) ∘ fun ω i => B t ω i := by
    funext ω
    rfl
  rw [hBt, ← Measure.map_map (MeasurableEquiv.toLp 2 (Fin d → ℝ)).measurable
      (Measurable.of_eval hcoordm), hpi, hdens,
    map_withDensity_measurePreserving (MeasurableEquiv.toLp 2 (Fin d → ℝ))
      (PiLp.volume_preserving_toLp (Fin d)) hmeas]
  congr 1
  funext y
  simp only [gaussianPDF]
  rw [← ENNReal.ofReal_prod_of_nonneg fun i _ => gaussianPDFReal_nonneg _ _ _]
  congr 1
  exact prod_gaussianPDFReal_eq_brownianHeatKernel hd hvR x y

end LatticeProb
