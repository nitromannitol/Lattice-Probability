/-
The density of the standard Gaussian on a Euclidean space.

Mathlib defines the standard Gaussian on a finite-dimensional inner product
space as the pushforward of a product of one-dimensional Gaussians along an
orthonormal basis, and proves no density for it.  The density is the product of
the one-dimensional densities, because the pushforward is along a volume
preserving map.
-/
import Mathlib
import LatticeProb.Prob.PiDensity

noncomputable section

namespace LatticeProb

open MeasureTheory ProbabilityTheory

open scoped ENNReal NNReal

/-- Pushing a density forward along a measure preserving equivalence. -/
theorem map_withDensity_measurePreserving {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    {μ : Measure α} {ν : Measure β} (e : α ≃ᵐ β) (he : MeasurePreserving e μ ν)
    {g : α → ℝ≥0∞} (hg : Measurable g) :
    (μ.withDensity g).map e = ν.withDensity fun y => g (e.symm y) := by
  ext T hT
  rw [Measure.map_apply e.measurable hT, withDensity_apply _ (e.measurable hT),
    withDensity_apply _ hT, ← lintegral_indicator (e.measurable hT), ← lintegral_indicator hT]
  have key : ∫⁻ a, T.indicator (fun y => g (e.symm y)) (e a) ∂μ
      = ∫⁻ b, T.indicator (fun y => g (e.symm y)) b ∂ν :=
    he.lintegral_comp ((hg.comp e.symm.measurable).indicator hT)
  rw [← key]
  refine lintegral_congr fun x => ?_
  by_cases hx : e x ∈ T
  · rw [Set.indicator_of_mem hx, Set.indicator_of_mem (show x ∈ e ⁻¹' T from hx)]
    simp
  · rw [Set.indicator_of_notMem hx, Set.indicator_of_notMem (show x ∉ e ⁻¹' T from hx)]

/-- **The standard Gaussian on a Euclidean space has the product density.** -/
theorem stdGaussian_euclidean_eq_withDensity (ι : Type*) [Fintype ι] :
    stdGaussian (EuclideanSpace ℝ ι)
      = (volume : Measure (EuclideanSpace ℝ ι)).withDensity
          fun y => ∏ i, gaussianPDF 0 1 (y i) := by
  classical
  have hmeas : Measurable fun x : ι → ℝ => ∏ i, gaussianPDF 0 1 (x i) :=
    Finset.measurable_prod _ fun i _ =>
      (measurable_gaussianPDF 0 1).comp (measurable_pi_apply i)
  have hfun : (fun x : ι → ℝ => ∑ i, x i • (EuclideanSpace.basisFun ι ℝ) i)
      = ⇑(MeasurableEquiv.toLp 2 (ι → ℝ)) := by
    funext x
    ext j
    simp [Pi.single_apply, mul_ite]
  have hmp : MeasurePreserving ⇑(MeasurableEquiv.toLp 2 (ι → ℝ))
      (volume : Measure (ι → ℝ)) (volume : Measure (EuclideanSpace ℝ ι)) :=
    PiLp.volume_preserving_toLp ι
  rw [stdGaussian_eq_map_pi_orthonormalBasis (EuclideanSpace.basisFun ι ℝ), hfun,
    pi_gaussianReal_eq_withDensity,
    map_withDensity_measurePreserving (MeasurableEquiv.toLp 2 (ι → ℝ)) hmp hmeas]
  rfl

/-! ### The orthant probability of a product Gaussian -/

theorem pi_gaussianReal_eq_withDensity' {ι : Type*} [Fintype ι] (v : ℝ≥0) (hv : v ≠ 0) :
    Measure.pi (fun _ : ι => gaussianReal 0 v)
      = (volume : Measure (ι → ℝ)).withDensity fun x => ∏ i, gaussianPDF 0 v (x i) := by
  haveI hprob : IsProbabilityMeasure ((volume : Measure ℝ).withDensity (gaussianPDF 0 v)) := by
    rw [← gaussianReal_of_var_ne_zero 0 hv]
    infer_instance
  have hpi : Measure.pi (fun _ : ι => gaussianReal 0 v)
      = Measure.pi fun _ : ι => (volume : Measure ℝ).withDensity (gaussianPDF 0 v) := by
    congr 1
    funext i
    exact gaussianReal_of_var_ne_zero 0 hv
  rw [hpi, pi_withDensity_prod (fun _ : ι => (volume : Measure ℝ))
    (fun _ : ι => gaussianPDF 0 v) (fun _ => measurable_gaussianPDF 0 v), ← volume_pi]

/-- The product Gaussian density on a Euclidean space is the pushforward of the
product of one-dimensional Gaussians. -/
theorem euclidean_gaussDensity_eq_map (ι : Type*) [Fintype ι] (v : ℝ≥0) (hv : v ≠ 0) :
    (volume : Measure (EuclideanSpace ℝ ι)).withDensity (fun y => ∏ i, gaussianPDF 0 v (y i))
      = (Measure.pi fun _ : ι => gaussianReal 0 v).map (MeasurableEquiv.toLp 2 (ι → ℝ)) := by
  have hmeas : Measurable fun x : ι → ℝ => ∏ i, gaussianPDF 0 v (x i) :=
    Finset.measurable_prod _ fun i _ =>
      (measurable_gaussianPDF 0 v).comp (measurable_pi_apply i)
  have hmp : MeasurePreserving ⇑(MeasurableEquiv.toLp 2 (ι → ℝ))
      (volume : Measure (ι → ℝ)) (volume : Measure (EuclideanSpace ℝ ι)) :=
    PiLp.volume_preserving_toLp ι
  rw [pi_gaussianReal_eq_withDensity' v hv,
    map_withDensity_measurePreserving (MeasurableEquiv.toLp 2 (ι → ℝ)) hmp hmeas]
  rfl

/-- **The orthant probability of a product Gaussian on a Euclidean space.** -/
theorem euclidean_gaussDensity_orthant (ι : Type*) [Fintype ι] (v : ℝ≥0) (hv : v ≠ 0) (η : ℝ) :
    ((volume : Measure (EuclideanSpace ℝ ι)).withDensity
        (fun y => ∏ i, gaussianPDF 0 v (y i))) {y : EuclideanSpace ℝ ι | ∀ i, y i ≤ η}
      = (gaussianReal 0 v (Set.Iic η)) ^ (Fintype.card ι) := by
  classical
  have hset : MeasurableSet {y : EuclideanSpace ℝ ι | ∀ i, y i ≤ η} := by
    have : {y : EuclideanSpace ℝ ι | ∀ i, y i ≤ η}
        = ⋂ i : ι, {y : EuclideanSpace ℝ ι | y i ≤ η} := by
      ext y; simp
    rw [this]
    exact MeasurableSet.iInter fun i => measurableSet_le (by fun_prop) measurable_const
  rw [euclidean_gaussDensity_eq_map ι v hv,
    Measure.map_apply (MeasurableEquiv.toLp 2 (ι → ℝ)).measurable hset]
  have hpre : (⇑(MeasurableEquiv.toLp 2 (ι → ℝ)) ⁻¹' {y : EuclideanSpace ℝ ι | ∀ i, y i ≤ η})
      = Set.univ.pi fun _ : ι => Set.Iic η := by
    ext x
    simp [Pi.le_def]
  rw [hpre, Measure.pi_pi]
  simp

/-- **A Gaussian dominated by a product density has a product orthant bound.** -/
theorem orthant_le_of_le_smul {ι : Type*} [Fintype ι] {μ : Measure (EuclideanSpace ℝ ι)}
    (c : ℝ≥0∞) (v : ℝ≥0) (hv : v ≠ 0)
    (h : μ ≤ c • (volume : Measure (EuclideanSpace ℝ ι)).withDensity
      (fun y => ∏ i, gaussianPDF 0 v (y i))) (η : ℝ) :
    μ {y : EuclideanSpace ℝ ι | ∀ i, y i ≤ η}
      ≤ c * (gaussianReal 0 v (Set.Iic η)) ^ (Fintype.card ι) := by
  refine le_trans (h _) ?_
  rw [Measure.smul_apply, smul_eq_mul, euclidean_gaussDensity_orthant ι v hv η]

/-- The one-dimensional Gaussian tail at variance `v` is the standard one
rescaled. -/
theorem gaussianReal_Iic_eq (v : ℝ≥0) (hv : v ≠ 0) (η : ℝ) :
    gaussianReal 0 v (Set.Iic η)
      = gaussianReal 0 1 (Set.Iic (η / Real.sqrt (v : ℝ))) := by
  have hvpos : (0 : ℝ) < (v : ℝ) := lt_of_le_of_ne (NNReal.coe_nonneg v)
    (fun hcon => hv (NNReal.coe_eq_zero.mp hcon.symm))
  have hs : (0 : ℝ) < Real.sqrt (v : ℝ) := Real.sqrt_pos.mpr hvpos
  have hmap : (gaussianReal 0 1).map (fun x => Real.sqrt (v : ℝ) * x) = gaussianReal 0 v := by
    rw [gaussianReal_map_const_mul]
    congr 1
    · ring
    · rw [mul_one]
      ext
      simp [Real.sq_sqrt hvpos.le]
  rw [← hmap, Measure.map_apply (by fun_prop) measurableSet_Iic]
  congr 1
  ext x
  simp only [Set.mem_preimage, Set.mem_Iic]
  rw [le_div_iff₀ hs, mul_comm]

end LatticeProb

end
