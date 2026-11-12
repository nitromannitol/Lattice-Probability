/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Field.KilledHeatGauss at commit fdb5cad; only the module paths of local imports are changed.
   Declarations, examples and checks that the copied results do not use are omitted. -/
import LatticeProb.Bonanno.LQGMetric.Field.KilledHeatBasic
import LatticeProb.Bonanno.LQGMetric.Field.HeatKernelSquare
import Mathlib.MeasureTheory.Measure.Lebesgue.Complex

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# Killed heat kernel, part 5: Gaussian toolkit on `ℂ` (task P2-KILLED)

* `map_eq_withDensity_heatKernel`: a complex random variable whose real and imaginary parts are
  independent `N(0, v)` has law `p_v(0, y) dy` (`heatKernel v 0 y`). Product of the two
  one-dimensional densities (mathlib `prod_withDensity`), transported by the volume-preserving
  identification `ℂ ≃ ℝ × ℝ` (`Complex.volume_preserving_equiv_real_prod`).
* `measure_pair_mem_eq_lintegral`: for independent `X, Y`, `P((X, Y) ∈ G) = ∫ P(Y ∈ G_x) dP_X(x)`
  (mathlib `IndepFun.map_prod_eq_prod_map_map` and `Measure.prod_apply`).
-/

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace LQGMetric
namespace KilledHeat

variable {Ω : Type*} {mΩ : MeasurableSpace Ω}

lemma gaussianPDFReal_zero_eq_gauss1 (v : ℝ≥0) (x : ℝ) :
    gaussianPDFReal 0 v x = HeatSq.gauss1 v x := by
  simp [gaussianPDFReal, HeatSq.gauss1]

/-- Law of a complex random variable with independent `N(0, v)` coordinates. -/
theorem map_eq_withDensity_heatKernel {P : Measure Ω} [IsProbabilityMeasure P] {Y : Ω → ℂ}
    {v : ℝ≥0} (hv : v ≠ 0)
    (hre : HasLaw (fun ω ↦ (Y ω).re) (gaussianReal 0 v) P)
    (him : HasLaw (fun ω ↦ (Y ω).im) (gaussianReal 0 v) P)
    (hind : IndepFun (fun ω ↦ (Y ω).re) (fun ω ↦ (Y ω).im) P) :
    P.map Y = volume.withDensity (fun y ↦ ENNReal.ofReal (heatKernel v 0 y)) := by
  have hpair : P.map (fun ω ↦ ((Y ω).re, (Y ω).im)) = (gaussianReal 0 v).prod (gaussianReal 0 v) := by
    rw [hind.map_prod_eq_prod_map_map hre.aemeasurable him.aemeasurable, hre.map_eq, him.map_eq]
  have hY : Y = Complex.measurableEquivRealProd.symm ∘ (fun ω ↦ ((Y ω).re, (Y ω).im)) := by
    funext ω
    simp [Complex.measurableEquivRealProd_symm_apply]
  have hpm : AEMeasurable (fun ω ↦ ((Y ω).re, (Y ω).im)) P :=
    hre.aemeasurable.prodMk him.aemeasurable
  rw [hY, ← AEMeasurable.map_map_of_aemeasurable
    Complex.measurableEquivRealProd.symm.measurable.aemeasurable hpm, hpair,
    gaussianReal_of_var_ne_zero _ hv, prod_withDensity (measurable_gaussianPDF 0 v)
      (measurable_gaussianPDF 0 v)]
  ext S hS
  rw [Measure.map_apply Complex.measurableEquivRealProd.symm.measurable hS,
    withDensity_apply _ (Complex.measurableEquivRealProd.symm.measurable hS),
    withDensity_apply _ hS, ← Measure.volume_eq_prod,
    ← (Complex.volume_preserving_equiv_real_prod.symm).setLIntegral_comp_preimage_emb
      Complex.measurableEquivRealProd.symm.measurableEmbedding]
  refine setLIntegral_congr_fun (Complex.measurableEquivRealProd.symm.measurable hS) fun x _ ↦ ?_
  have hv' : (0 : ℝ) < v := by positivity
  rw [gaussianPDF, gaussianPDF, ← ENNReal.ofReal_mul (gaussianPDFReal_nonneg _ _ _),
    gaussianPDFReal_zero_eq_gauss1, gaussianPDFReal_zero_eq_gauss1, heatKernel_comm,
    ← HeatSq.gauss1_mul_gauss1 v hv']
  simp [Complex.measurableEquivRealProd_symm_apply]

/-- For independent `X, Y`: `P((X, Y) ∈ G) = ∫ P(Y ∈ G_x) dP_X(x)`. -/
theorem measure_pair_mem_eq_lintegral {α β : Type*} {mα : MeasurableSpace α}
    {mβ : MeasurableSpace β} {P : Measure Ω} [IsProbabilityMeasure P] {X : Ω → α} {Y : Ω → β}
    (hX : AEMeasurable X P) (hY : AEMeasurable Y P) (hXY : IndepFun X Y P) {G : Set (α × β)}
    (hG : MeasurableSet G) :
    P {ω | (X ω, Y ω) ∈ G} = ∫⁻ x, P.map Y (Prod.mk x ⁻¹' G) ∂(P.map X) := by
  have h1 : P {ω | (X ω, Y ω) ∈ G} = P.map (fun ω ↦ (X ω, Y ω)) G := by
    rw [Measure.map_apply_of_aemeasurable (hX.prodMk hY) hG]
    rfl
  rw [h1, hXY.map_prod_eq_prod_map_map hX hY, Measure.prod_apply hG]

end KilledHeat
end LQGMetric
