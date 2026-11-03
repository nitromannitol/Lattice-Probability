/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Field.ExistCov at commit 31e7483; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Field.ExistKernelL2
import LatticeProb.Bonanno.LQGMetric.Field.ExistHeatCov

/-!
# The white-noise kernels reproduce `logCov` on mean-zero functions (task P2-EXIST, part 3)

`integral_kerFun_mul_eq_logCov`: for bounded measurable `φ, ψ` vanishing outside a ball, with
`∫ φ = ∫ ψ = 0`, `⟪kerFun φ, kerFun ψ⟫_{L²(ℝ × ℂ)} = logCov φ ψ`. This is the covariance
computation of the white-noise representation `h = √π ∫∫ p_{t/2}(·, y) W(dy, dt)` (DDDF,
arXiv:1904.08021, `tightness.tex` l. 143–145, 287: "`p_{t/2} * p_{t/2} = p_t`"): Fubini, the
semigroup identity (`WhiteNoise.integral_heatKernel_mul_heatKernel`), and the heat-kernel
representation of `−log` (`logCov_eq_integral_heat`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Filter Set Metric

namespace LQGMetric
namespace GFFExist

open WhiteNoise

variable {φ ψ : ℂ → ℝ} {M N R : ℝ}

lemma BddSupp.integrable_mul_heatKernel (hφ : BddSupp φ M R) {s : ℝ} (hs : 0 < s) (y : ℂ) :
    Integrable fun u => φ u * heatKernel s u y := by
  have := hφ.integrable_mul_bdd (f := fun u => heatKernel s u y) (by unfold heatKernel; fun_prop)
    (K := (2 * Real.pi * s)⁻¹) (fun u _ => by
      rw [abs_of_nonneg (heatKernel_nonneg _ hs.le _ _)]; exact heatKernel_le s hs u y)
  exact this.congr (Eventually.of_forall fun u => mul_comm _ _)

lemma kerInner_of_mean_zero (hφ : BddSupp φ M R) (hφ0 : ∫ u, φ u = 0) {t : ℝ} (ht : 0 < t)
    (y : ℂ) : kerInner φ t y = ∫ u, φ u * heatKernel (t / 2) u y := by
  unfold kerInner
  set c := (Ioi (1 : ℝ)).indicator (fun _ => heatKernel (t / 2) 0 y) t
  have e : ∀ u, φ u * (heatKernel (t / 2) u y - c) = φ u * heatKernel (t / 2) u y - c * φ u :=
    fun u => by ring
  simp_rw [e]
  rw [integral_sub (hφ.integrable_mul_heatKernel (by linarith) y) (hφ.integrable.const_mul c),
    integral_const_mul, hφ0, mul_zero, sub_zero]

/-- `∫ (∫ φ p_{t/2}(·, y)) (∫ ψ p_{t/2}(·, y)) dy = ∫∫ φ(u) ψ(v) p_t(u, v)` -/
lemma integral_heat_pair (hφ : BddSupp φ M R) (hψ : BddSupp ψ N R) {t : ℝ} (ht : 0 < t) :
    ∫ y, (∫ u, φ u * heatKernel (t / 2) u y) * (∫ v, ψ v * heatKernel (t / 2) v y) =
      ∫ q : ℂ × ℂ, φ q.1 * ψ q.2 * heatKernel t q.1 q.2 := by
  have hs : 0 < t / 2 := by linarith
  have h2s : 2 * (t / 2) = t := by ring
  set H : (ℂ × ℂ) × ℂ → ℝ := fun z => φ z.1.1 * ψ z.1.2 *
    (heatKernel (t / 2) z.1.1 z.2 * heatKernel (t / 2) z.1.2 z.2) with hHdef
  have hφm := hφ.meas
  have hψm := hψ.meas
  have hHm : Measurable H := by simp only [hHdef]; unfold heatKernel; fun_prop
  have hslice : ∀ x : ℂ × ℂ, ∫ y, H (x, y) = φ x.1 * ψ x.2 * heatKernel t x.1 x.2 := by
    intro x
    simp only [hHdef]
    rw [integral_const_mul, integral_heatKernel_mul_heatKernel _ hs, h2s]
  have hφi := hφ.integrable
  have hψi := hψ.integrable
  have hprod : Integrable (fun x : ℂ × ℂ => |φ x.1| * |ψ x.2|) (volume.prod volume) :=
    hφi.abs.mul_prod hψi.abs
  have hH : Integrable H ((volume.prod volume).prod volume) := by
    rw [integrable_prod_iff hHm.aestronglyMeasurable]
    refine ⟨Eventually.of_forall fun x => ?_, ?_⟩
    · simp only [hHdef]
      exact (integrable_heatKernel_mul_heatKernel _ hs x.1 x.2).const_mul _
    · have e : (fun x : ℂ × ℂ => ∫ y, ‖H (x, y)‖) =
          fun x => |φ x.1| * |ψ x.2| * heatKernel t x.1 x.2 := by
        funext x
        have : ∀ y, ‖H (x, y)‖ = |φ x.1| * |ψ x.2| *
            (heatKernel (t / 2) x.1 y * heatKernel (t / 2) x.2 y) := fun y => by
          simp only [hHdef, Real.norm_eq_abs, abs_mul]
          rw [abs_of_nonneg (heatKernel_nonneg _ hs.le _ _),
            abs_of_nonneg (heatKernel_nonneg _ hs.le _ _)]
        simp_rw [this]
        rw [integral_const_mul, integral_heatKernel_mul_heatKernel _ hs, h2s]
      rw [e]
      refine hprod.mul_of_top_left (memLp_top_of_bound (by unfold heatKernel; fun_prop)
        (2 * Real.pi * t)⁻¹ (Eventually.of_forall fun x => ?_))
      rw [Real.norm_eq_abs, abs_of_nonneg (heatKernel_nonneg _ ht.le _ _)]
      exact heatKernel_le t ht _ _
  rw [show (volume : Measure (ℂ × ℂ)) = volume.prod volume from rfl]
  simp_rw [← hslice]
  rw [← integral_prod H hH, integral_prod_symm H hH]
  congr 1; funext y
  rw [← integral_prod_mul]
  congr 1; funext x
  simp only [hHdef]; ring

/-- **Covariance of the kernels.** For mean-zero bounded `φ, ψ` vanishing outside `B̄_R(0)`,
`∫ kerFun φ · kerFun ψ = logCov φ ψ`. -/
theorem integral_kerFun_mul_eq_logCov (hR : 0 ≤ R) (hφ : BddSupp φ M R) (hψ : BddSupp ψ N R)
    (hφ0 : ∫ u, φ u = 0) (hψ0 : ∫ u, ψ u = 0) :
    ∫ q, kerFun φ q * kerFun ψ q = logCov φ ψ := by
  have hint : Integrable (fun q => kerFun φ q * kerFun ψ q) (volume.prod volume) :=
    hφ.memLp_kerFun.1.integrable_mul hψ.memLp_kerFun.1
  rw [show (volume : Measure (ℝ × ℂ)) = volume.prod volume from rfl, integral_prod _ hint,
    ← setIntegral_eq_integral_of_forall_compl_eq_zero (s := Ioi (0 : ℝ)) (fun t ht => by
      simp [kerFun, indicator_of_notMem ht])]
  rw [← logCov_eq_integral_heat hR hφ.meas hψ.meas hφ.bdd hψ.bdd hφ.supp hψ.supp hψ0]
  refine setIntegral_congr_fun measurableSet_Ioi fun t ht => ?_
  have ht0 : 0 < t := ht
  have hpi : Real.sqrt Real.pi * Real.sqrt Real.pi = Real.pi :=
    Real.mul_self_sqrt Real.pi_pos.le
  have e : ∀ y, kerFun φ (t, y) * kerFun ψ (t, y) = Real.pi *
      ((∫ u, φ u * heatKernel (t / 2) u y) * (∫ v, ψ v * heatKernel (t / 2) v y)) := fun y => by
    simp only [kerFun, indicator_of_mem ht]
    rw [kerInner_of_mean_zero hφ hφ0 ht0, kerInner_of_mean_zero hψ hψ0 ht0]
    linear_combination ((∫ u, φ u * heatKernel (t / 2) u y) *
      (∫ v, ψ v * heatKernel (t / 2) v y)) * hpi
  simp_rw [e]
  rw [integral_const_mul, integral_heat_pair hφ hψ ht0]

end GFFExist
end LQGMetric
