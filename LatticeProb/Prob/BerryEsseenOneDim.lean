/- # Berry-Esseen in one dimension for independent non-identical summands

For a finite family of centred probability laws `ν i` on `ℝ` with finite third absolute moments
and positive total variance `V = ∑ Var ν_i`, the Kolmogorov distance between the law of the sum of
independent summands and the centred Gaussian law of variance `V` is at most
`100 ∑ ∫ |z|³ dν_i / V ^ (3/2)`.  The proof rescales the summands by `V^(-1/2)` and applies the
normalised theorem `berryEsseen_normalized`.

* `LatticeProb.sumLaw_map_const_mul` — the law of the sum of rescaled summands is the rescaled
  law of the sum.
* `LatticeProb.berryEsseen_oneDim` — the Berry-Esseen inequality in one dimension.
-/
import Mathlib
import LatticeProb.Prob.BerryEsseenNormalizedProved

open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace LatticeProb

/-- The law of the sum of independent summands rescaled by `c` is the image under `c * ·` of the
law of the sum. -/
theorem sumLaw_map_const_mul {ι : Type*} [Fintype ι] (ν : ι → Measure ℝ)
    [∀ i, IsProbabilityMeasure (ν i)] (c : ℝ) :
    sumLaw (fun i => (ν i).map (fun z : ℝ => c * z)) = (sumLaw ν).map (fun z : ℝ => c * z) := by
  have hm : Measurable (fun z : ℝ => c * z) := measurable_const_mul c
  haveI : ∀ i, IsProbabilityMeasure ((ν i).map (fun z : ℝ => c * z)) := fun i =>
    Measure.isProbabilityMeasure_map hm.aemeasurable
  have hsum : Measurable (fun y : ι → ℝ => ∑ i, y i) :=
    Finset.measurable_sum _ fun i _ => measurable_pi_apply i
  have hscale : Measurable (fun (x : ι → ℝ) (i : ι) => c * x i) :=
    measurable_pi_lambda _ fun i => hm.comp (measurable_pi_apply i)
  unfold sumLaw
  rw [← Measure.pi_map_pi (f := fun (_ : ι) (z : ℝ) => c * z) (fun i => hm.aemeasurable),
    Measure.map_map hsum hscale, Measure.map_map hm hsum]
  congr 1
  funext y
  simp [Finset.mul_sum]

/-- The centred Gaussian law of variance `V > 0` assigns to `Iic x` the mass that the standard
Gaussian law assigns to `Iic (x / √V)`. -/
theorem gaussianReal_Iic_eq_sqrt {V : ℝ} (hV : 0 < V) (x : ℝ) :
    gaussianReal 0 V.toNNReal (Set.Iic x)
      = gaussianReal 0 1 (Set.Iic ((Real.sqrt V)⁻¹ * x)) := by
  have hs : 0 < Real.sqrt V := Real.sqrt_pos.2 hV
  have hm : Measurable (fun z : ℝ => Real.sqrt V * z) := measurable_const_mul _
  have h1 := gaussianReal_map_const_mul (μ := 0) (v := 1) (Real.sqrt V)
  have h2 : (NNReal.mk (Real.sqrt V ^ 2) (sq_nonneg _) * 1 : ℝ≥0) = V.toNNReal := by
    apply NNReal.eq
    simp [Real.sq_sqrt hV.le, Real.coe_toNNReal V hV.le]
  rw [h2, mul_zero] at h1
  rw [← h1, Measure.map_apply hm measurableSet_Iic]
  congr 1
  ext z
  simp only [Set.mem_preimage, Set.mem_Iic]
  rw [← mul_le_mul_iff_of_pos_left (inv_pos.2 hs), ← mul_assoc, inv_mul_cancel₀ hs.ne', one_mul]

/-- The rescaled sum law, evaluated on `Iic (c * x)`, is the original sum law evaluated on
`Iic x`, for `c > 0`. -/
theorem sumLaw_map_const_mul_Iic {ι : Type*} [Fintype ι] (ν : ι → Measure ℝ)
    [∀ i, IsProbabilityMeasure (ν i)] {c : ℝ} (hc : 0 < c) (x : ℝ) :
    sumLaw (fun i => (ν i).map (fun z : ℝ => c * z)) (Set.Iic (c * x))
      = sumLaw ν (Set.Iic x) := by
  have hm : Measurable (fun z : ℝ => c * z) := measurable_const_mul c
  rw [sumLaw_map_const_mul, Measure.map_apply hm measurableSet_Iic]
  congr 1
  ext z
  simp only [Set.mem_preimage, Set.mem_Iic]
  exact mul_le_mul_iff_of_pos_left hc

/-- The variance of the identity under the rescaled law `c * ·` is `c ^ 2` times the variance
under the original law. -/
theorem variance_id_map_const_mul (ν : Measure ℝ) (c : ℝ) :
    variance id (ν.map (fun z : ℝ => c * z)) = c ^ 2 * variance id ν := by
  rw [variance_id_map (measurable_const_mul c).aemeasurable]
  exact variance_const_mul c id ν

/-- The mean of the rescaled law `c * ·` is `c` times the mean of the original law. -/
theorem integral_id_map_const_mul (ν : Measure ℝ) (c : ℝ) :
    ∫ z, z ∂(ν.map (fun z : ℝ => c * z)) = c * ∫ z, z ∂ν := by
  rw [integral_map (f := fun z : ℝ => z) (measurable_const_mul c).aemeasurable
    measurable_id.aestronglyMeasurable, integral_const_mul]

/-- The third absolute moment of the rescaled law `c * ·` is `|c| ^ 3` times the third absolute
moment of the original law. -/
theorem integral_abs_pow_map_const_mul (ν : Measure ℝ) (c : ℝ) :
    ∫ z, |z| ^ 3 ∂(ν.map (fun z : ℝ => c * z)) = |c| ^ 3 * ∫ z, |z| ^ 3 ∂ν := by
  rw [integral_map (measurable_const_mul c).aemeasurable
    (by fun_prop : Continuous fun z : ℝ => |z| ^ 3).aestronglyMeasurable,
    ← integral_const_mul]
  refine integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
  simp [abs_mul, mul_pow]

/-- The rescaled law `c * ·` has an integrable third absolute moment if the original one does. -/
theorem integrable_abs_pow_map_const_mul (ν : Measure ℝ) (c : ℝ)
    (h3 : Integrable (fun z : ℝ => |z| ^ 3) ν) :
    Integrable (fun z : ℝ => |z| ^ 3) (ν.map (fun z : ℝ => c * z)) := by
  rw [integrable_map_measure (by fun_prop : Continuous fun z : ℝ => |z| ^ 3).aestronglyMeasurable
    (measurable_const_mul c).aemeasurable]
  have : ((fun z : ℝ => |z| ^ 3) ∘ fun z : ℝ => c * z) = fun z : ℝ => |c| ^ 3 * |z| ^ 3 := by
    funext z
    simp [abs_mul, mul_pow]
  rw [this]
  exact h3.const_mul _

/-- For `V > 0`, `V ^ (3/2)` is the cube of `√V`. -/
theorem rpow_three_halves_eq_sqrt_pow {V : ℝ} (hV : 0 < V) :
    V ^ ((3 : ℝ) / 2) = Real.sqrt V ^ 3 := by
  rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_mul hV.le]
  norm_num

/-- **Berry-Esseen, one dimension, independent non-identical summands** (for an index type in any
universe, with the explicit constant `100`): the distribution function of the sum of independent
centred summands with finite third absolute moments and total variance `V > 0` differs from that
of the centred Gaussian of variance `V` by at most `100 ∑ ∫ |z|³ dν_i / V ^ (3/2)`. -/
theorem berryEsseen_oneDim_of_pos {ι : Type*} [Fintype ι] (ν : ι → Measure ℝ)
    [∀ i, IsProbabilityMeasure (ν i)] (hmean : ∀ i, ∫ z, z ∂(ν i) = 0)
    (h3 : ∀ i, Integrable (fun z : ℝ => |z| ^ 3) (ν i))
    (hV : 0 < ∑ i, variance id (ν i)) (x : ℝ) :
    |(sumLaw ν (Set.Iic x)).toReal -
        (gaussianReal 0 (∑ i, variance id (ν i)).toNNReal (Set.Iic x)).toReal|
      ≤ 100 * (∑ i, ∫ z, |z| ^ 3 ∂(ν i)) / (∑ i, variance id (ν i)) ^ ((3 : ℝ) / 2) := by
  set V : ℝ := ∑ i, variance id (ν i) with hVdef
  set s : ℝ := Real.sqrt V with hsdef
  have hs : 0 < s := Real.sqrt_pos.2 hV
  have hsi : 0 < s⁻¹ := inv_pos.2 hs
  haveI : ∀ i, IsProbabilityMeasure ((ν i).map (fun z : ℝ => s⁻¹ * z)) := fun i =>
    Measure.isProbabilityMeasure_map (measurable_const_mul s⁻¹).aemeasurable
  have hmean' : ∀ i, ∫ z, z ∂((ν i).map (fun z : ℝ => s⁻¹ * z)) = 0 := fun i => by
    rw [integral_id_map_const_mul, hmean i, mul_zero]
  have h3' : ∀ i, Integrable (fun z : ℝ => |z| ^ 3) ((ν i).map (fun z : ℝ => s⁻¹ * z)) :=
    fun i => integrable_abs_pow_map_const_mul _ _ (h3 i)
  have hvar' : ∑ i, variance id ((ν i).map (fun z : ℝ => s⁻¹ * z)) = 1 := by
    simp_rw [variance_id_map_const_mul]
    rw [← Finset.mul_sum, ← hVdef, inv_pow, hsdef, Real.sq_sqrt hV.le]
    exact inv_mul_cancel₀ hV.ne'
  have key := berryEsseen_normalized (fun i => (ν i).map (fun z : ℝ => s⁻¹ * z)) hmean' h3'
    hvar' (s⁻¹ * x)
  rw [sumLaw_map_const_mul_Iic ν hsi x, ← gaussianReal_Iic_eq_sqrt hV x] at key
  simp_rw [integral_abs_pow_map_const_mul] at key
  rw [← Finset.mul_sum] at key
  refine key.trans (le_of_eq ?_)
  rw [rpow_three_halves_eq_sqrt_pow hV, ← hsdef, abs_of_pos hsi]
  field_simp

/-- **Berry-Esseen, one dimension, independent non-identical summands.**  There is a constant
`C > 0` such that for every finite family of independent centred real summands with laws `ν i`,
finite third absolute moments and positive total variance `V = ∑ Var ν_i`, the distribution
function of their sum differs from that of the centred Gaussian of variance `V` by at most
`C ∑ ∫ |z|³ dν_i / V ^ (3/2)`.  One may take `C = 100`. -/
theorem berryEsseen_oneDim :
    ∃ C : ℝ, 0 < C ∧
      ∀ {ι : Type} [Fintype ι] (ν : ι → Measure ℝ) [∀ i, IsProbabilityMeasure (ν i)],
        (∀ i, ∫ z, z ∂(ν i) = 0) →
        (∀ i, Integrable (fun z : ℝ => |z| ^ 3) (ν i)) →
        0 < ∑ i, variance id (ν i) →
        ∀ x : ℝ,
          |(sumLaw ν (Set.Iic x)).toReal -
              (gaussianReal 0 (∑ i, variance id (ν i)).toNNReal (Set.Iic x)).toReal|
            ≤ C * (∑ i, ∫ z, |z| ^ 3 ∂(ν i)) / (∑ i, variance id (ν i)) ^ ((3 : ℝ) / 2) :=
  ⟨100, by norm_num, fun ν _ hmean h3 hV x => berryEsseen_oneDim_of_pos ν hmean h3 hV x⟩

end LatticeProb
