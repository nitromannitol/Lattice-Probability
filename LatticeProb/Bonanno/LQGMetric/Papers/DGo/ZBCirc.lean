/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DGo.ZBCirc at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DGo.ZBDist
import LatticeProb.Bonanno.LQGMetric.Field.CircleAvgPairing

/-!
# The kernel of a mollified circle is the mollified circle kernel (task P2-DGZB)

For `f_n = σ_{x,δ} * ψ_n = circBump n x δ` (the test function whose pairing is the circle average
of the mollified field, `CircleAvg.circleAverage_pairing`) supported in `D = (a, a+L)²`:

* `integral_circBump_mul_sqDirKernel`: `∫ f_n(y') p^D_r(y', y) dy' =
  ∫ ψ_n(z) (2π)⁻¹ ∫_0^{2π} p^D_r(x + z + δe^{iθ}, y) dθ dz` (Fubini and translation);
* `inner_zbKerL2_circBump`: `⟪zbKer f_n, G⟫ = ∫ ψ_n(z) ⟪K_{δ, x+z}, G⟫ dz` for every `G ∈ L²`;
* `norm_zbKerL2_circBump_sub_le`: `‖zbKer f_n − K_{δ,x}‖ ≤ sup_{|z| < 2^{-n}} ‖K_{δ,x+z} − K_{δ,x}‖`.

Together with DGo's increment bound (3.9) (`dgo_incr_bound_compact`) this gives the rate
`π‖zbKer f_n − K_{δ,x}‖² = O(2^{-n})` used to identify the circle averages of the random
distribution. Own elementary proof (Fubini; the mollified circle is a mixture of circles).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Metric Real
open scoped RealInnerProductSpace

namespace LQGMetric
namespace DGo
namespace ZB

open WhiteNoise HeatSq DDDF.P29WN GFFExist HeatDir CircleAvg

variable {a L : ℝ}

lemma bumpTest_zero_eq_zero (n : ℕ) {z : ℂ} (hz : (2 : ℝ)⁻¹ ^ n ≤ ‖z‖) : bumpTest n 0 z = 0 := by
  rw [bumpTest_apply, ContDiffBump.normed_def, (bumpAt n 0).zero_of_le_dist, zero_div]
  show (2 : ℝ)⁻¹ ^ n ≤ dist z 0
  rwa [dist_zero_right]

lemma bumpTest_nonneg (n : ℕ) (z : ℂ) : 0 ≤ bumpTest n 0 z := by
  rw [bumpTest_apply]; exact ContDiffBump.nonneg_normed _ _

lemma circBump_eq (n : ℕ) (x : ℂ) (δ : ℝ) (y : ℂ) :
    circBump n x δ y = (2 * π)⁻¹ * ∫ θ in Ioc 0 (2 * π), bumpTest n 0 (y - circleMap x δ θ) := by
  rw [circBump_apply, Real.circleAverage_def, smul_eq_mul,
    intervalIntegral.integral_of_le (by positivity : (0 : ℝ) ≤ 2 * π)]
  simp_rw [bumpTest_eq_sub n _ y]

lemma measurable_sqDirKernel_left (hL : 0 < L) {r : ℝ} (hr : 0 < r) (y : ℂ) :
    Measurable fun w => sqDirKernel a L r w y := by
  have e : (fun w => sqDirKernel a L r w y) = fun w => sqDirKernel a L r y w := by
    funext w; exact sqDirKernel_symm hr hL w y
  rw [e]; exact measurable_sqDirKernel_right' hr hL y

/-- a mixture of circles against a bounded kernel (generic form) -/
theorem integral_mix_mul (ψ : ℂ → ℝ) (hψc : Continuous ψ) (hψi : Integrable ψ)
    (hψ0 : ∀ z, 0 ≤ ψ z) (pk : ℂ → ℝ) (hpkm : Measurable pk) {B : ℝ} (hpkb : ∀ w, |pk w| ≤ B)
    (x : ℂ) (δ : ℝ) :
    ∫ y', ((2 * π)⁻¹ * ∫ θ in Ioc 0 (2 * π), ψ (y' - circleMap x δ θ)) * pk y' =
      ∫ z, ψ z * ((2 * π)⁻¹ * ∫ θ in Ioc 0 (2 * π), pk (circleMap (x + z) δ θ)) := by
  set ν : Measure ℝ := volume.restrict (Ioc 0 (2 * π))
  have : IsFiniteMeasure ν := ⟨by
    rw [Measure.restrict_apply_univ]; exact measure_Ioc_lt_top⟩
  have hcm : Continuous fun θ : ℝ => circleMap x δ θ := continuous_circleMap x δ
  have hI1 : Integrable (fun p : ℂ × ℝ => ψ (p.1 - circleMap x δ p.2)) (volume.prod ν) := by
    have hm : Measurable fun p : ℂ × ℝ => ψ (p.1 - circleMap x δ p.2) :=
      hψc.measurable.comp (measurable_fst.sub (hcm.measurable.comp measurable_snd))
    rw [integrable_prod_iff' hm.aestronglyMeasurable]
    refine ⟨Eventually.of_forall fun θ =>
      (hψi.comp_sub_right (circleMap x δ θ) : Integrable fun y' => ψ (y' - circleMap x δ θ)), ?_⟩
    have e : (fun θ => ∫ y', ‖ψ (y' - circleMap x δ θ)‖) = fun _ => ∫ y', ψ y' := by
      funext θ
      rw [integral_sub_right_eq_self (fun w => ‖ψ w‖) (circleMap x δ θ)]
      congr 1; funext w; rw [Real.norm_of_nonneg (hψ0 w)]
    simp only [e]; exact integrable_const _
  have hF1 : Integrable (fun p : ℂ × ℝ => ψ (p.1 - circleMap x δ p.2) * pk p.1)
      (volume.prod ν) := by
    refine (hI1.mul_const B).mono' ((hI1.1.mul (hpkm.comp measurable_fst).aestronglyMeasurable))
      (Eventually.of_forall fun p => ?_)
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hψ0 _)]
    exact mul_le_mul_of_nonneg_left (hpkb _) (hψ0 _)
  have hF2 : Integrable (fun p : ℝ × ℂ => ψ p.2 * pk (p.2 + circleMap x δ p.1))
      (ν.prod volume) := by
    have hm : Measurable fun p : ℝ × ℂ => ψ p.2 * pk (p.2 + circleMap x δ p.1) :=
      (hψc.measurable.comp measurable_snd).mul
        (hpkm.comp (measurable_snd.add (hcm.measurable.comp measurable_fst)))
    refine (((integrable_const (1 : ℝ)).mul_prod hψi).mul_const B).mono' hm.aestronglyMeasurable
      (Eventually.of_forall fun p => ?_)
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hψ0 _), one_mul]
    exact mul_le_mul_of_nonneg_left (hpkb _) (hψ0 _)
  calc ∫ y', ((2 * π)⁻¹ * ∫ θ in Ioc 0 (2 * π), ψ (y' - circleMap x δ θ)) * pk y'
      = (2 * π)⁻¹ * ∫ y' : ℂ, (∫ θ : ℝ, ψ (y' - circleMap x δ θ) * pk y' ∂ν) := by
        rw [← integral_const_mul]; congr 1; funext y'
        rw [mul_assoc, ← integral_mul_const]
    _ = (2 * π)⁻¹ * ∫ θ : ℝ, (∫ y' : ℂ, ψ (y' - circleMap x δ θ) * pk y') ∂ν := by
        rw [integral_integral_swap hF1]
    _ = (2 * π)⁻¹ * ∫ θ : ℝ, (∫ z : ℂ, ψ z * pk (z + circleMap x δ θ)) ∂ν := by
        congr 1; refine integral_congr_ae (Eventually.of_forall fun θ => ?_)
        simp only
        rw [← integral_sub_right_eq_self (fun z => ψ z * pk (z + circleMap x δ θ))
          (circleMap x δ θ)]
        simp only [sub_add_cancel]
    _ = (2 * π)⁻¹ * ∫ z : ℂ, (∫ θ : ℝ, ψ z * pk (z + circleMap x δ θ) ∂ν) := by
        rw [integral_integral_swap hF2]
    _ = _ := by
        rw [← integral_const_mul]; congr 1; funext z
        rw [integral_const_mul, ← mul_assoc, mul_comm (2 * π)⁻¹ (ψ z), mul_assoc]
        congr 2
        refine integral_congr_ae (Eventually.of_forall fun θ => ?_)
        simp only [circleMap]
        congr 1; ring

/-- the mollified circle against the Dirichlet heat kernel -/
theorem integral_circBump_mul_sqDirKernel (hL : 0 < L) {r : ℝ} (hr : 0 < r) (n : ℕ) (x : ℂ)
    (δ : ℝ) (y : ℂ) :
    ∫ y', circBump n x δ y' * sqDirKernel a L r y' y =
      ∫ z, bumpTest n 0 z *
        ((2 * π)⁻¹ * ∫ θ in Ioc 0 (2 * π), sqDirKernel a L r (circleMap (x + z) δ θ) y) := by
  simp_rw [circBump_eq]
  exact integral_mix_mul (fun z => bumpTest n 0 z) (bumpTest n 0).continuous
    (GFFInv.integrable_test (bumpTest n 0)) (bumpTest_nonneg n) (fun w => sqDirKernel a L r w y)
    (measurable_sqDirKernel_left hL hr y) (fun w => abs_sqDirKernel_le_const hL hr w y) x δ

end ZB
end DGo
end LQGMetric
