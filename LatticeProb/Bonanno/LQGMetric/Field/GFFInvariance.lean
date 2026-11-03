/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Field.GFFInvariance at commit 31e7483; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Statement.GFF
import Mathlib.Probability.Distributions.Gaussian.IsGaussianProcess.Basic
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Mathlib.MeasureTheory.Measure.Lebesgue.Complex
import Mathlib.LinearAlgebra.Complex.FiniteDimensional

/-!
# Invariances of the whole-plane GFF (task P2-FINV)

For `IsWholePlaneGFF` (FOUNDATIONS §2: pairings with mean-zero test functions form a centered
Gaussian process with covariance `logCov`):

* `logCov_affine`: for `r > 0`, `z ∈ ℂ` and `∫ ψ = 0`,
  `logCov φ((·-z)/r) ψ((·-z)/r) = r⁴ logCov φ ψ` (change of variables; the `log r` term dies
  because `ψ` has mean zero);
* `IsWholePlaneGFF.affineComp`: `h(r·+z)` is again a whole-plane GFF (scale and translation
  invariance of the law of the whole-plane GFF modulo additive constant, used throughout GM,
  arXiv:1905.00383v3, e.g. `uniqueness-final.tex` l. 458, 516, 988, 1070);
* `IsWholePlaneGFF.addConst`: adding a random constant preserves the property;
  `integral_mul_eq_zero_of_addFun`: a deterministic continuous `f` with `h + f` again a
  whole-plane GFF satisfies `∫ f φ = 0` for every mean-zero test function `φ` (so only constants
  are allowed).

Sources: the covariance computation is the standard one (Duplantier–Sheffield, *Liouville
quantum gravity and KPZ*, §2; Miller–Sheffield IG4, arXiv:1302.4738, §2.2, l. 1082: the
whole-plane GFF modulo constants has covariance `−log|x−y|` on mean-zero test functions, and its
law is invariant under `z ↦ rz + z₀`). Own elementary write-up of the change of variables.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped Distributions ENNReal

namespace LQGMetric
namespace GFFInv

/-! ## Measurability on `DistC` -/

lemma measurable_pair (φ : TestC) : Measurable (fun h : DistC => h φ) := by
  have : Measurable (fun (h : DistC) (φ : TestC) => h φ) := fun s hs => ⟨s, hs, rfl⟩
  exact (measurable_pi_apply φ).comp this

lemma measurable_distC_iff {α : Type*} {mα : MeasurableSpace α} {g : α → DistC} :
    Measurable g ↔ ∀ φ : TestC, Measurable fun a => g a φ := by
  refine ⟨fun hg φ => (measurable_pair φ).comp hg, fun h => ?_⟩
  rw [measurable_iff_comap_le]
  show MeasurableSpace.comap g
    (MeasurableSpace.comap (fun (h : DistC) (φ : TestC) => h φ) MeasurableSpace.pi) ≤ mα
  rw [MeasurableSpace.comap_comp]
  exact measurable_iff_comap_le.1 (measurable_pi_iff.2 h)

/-! ## Change of variables -/

lemma integral_smul_add (F : ℂ → ℝ) {r : ℝ} (hr : 0 < r) (z : ℂ) :
    ∫ v, F (r • v + z) = (r ^ 2)⁻¹ * ∫ x, F x := by
  have h1 := Measure.integral_comp_smul_of_nonneg volume (fun w => F (w + z)) r (hR := hr.le)
  rw [h1, integral_add_right_eq_self F z, Complex.finrank_real_complex, smul_eq_mul]

lemma integral_eq_smul_add (F : ℂ → ℝ) {r : ℝ} (hr : 0 < r) (z : ℂ) :
    ∫ x, F x = r ^ 2 * ∫ v, F (r • v + z) := by
  rw [integral_smul_add F hr z, ← mul_assoc, mul_inv_cancel₀ (by positivity), one_mul]

lemma integral_comp_aff (F : ℂ → ℝ) {r : ℝ} (hr : 0 < r) (z : ℂ) :
    ∫ x, F ((x - z) / r) = r ^ 2 * ∫ x, F x := by
  rw [integral_eq_smul_add _ hr z]
  congr 2
  funext v
  congr 1
  rw [Complex.real_smul, add_sub_cancel_right, mul_div_cancel_left₀]
  exact_mod_cast hr.ne'

/-- `∫ (a + b) = ∫ b` when `a` is integrable with `∫ a = 0` (both sides vanish if `b` is not
integrable). -/
lemma integral_add_of_left {a b : ℂ → ℝ} (ha : Integrable a) (ha0 : ∫ x, a x = 0) :
    ∫ x, (a x + b x) = ∫ x, b x := by
  by_cases hb : Integrable b
  · rw [integral_add ha hb, ha0, zero_add]
  · have hab : ¬ Integrable (fun x => a x + b x) := fun h => hb
      ((h.sub ha).congr (ae_of_all _ fun x => by simp))
    rw [integral_undef hab, integral_undef hb]

lemma integrable_test (φ : TestC) : Integrable (fun x => φ x) :=
  φ.continuous.integrable_of_hasCompactSupport φ.hasCompactSupport

/-! ## The covariance is invariant under `x ↦ r x + z` on mean-zero functions -/

/-- `logCov φ((·-z)/r) ψ((·-z)/r) = r⁴ logCov φ ψ` for `r > 0` and `∫ ψ = 0`. -/
theorem logCov_affine (φ ψ : ℂ → ℝ) (hψ : Integrable ψ) (hψ0 : ∫ y, ψ y = 0) {r : ℝ}
    (hr : 0 < r) (z : ℂ) :
    logCov (fun x => φ ((x - z) / r)) (fun y => ψ ((y - z) / r)) = r ^ 4 * logCov φ ψ := by
  have hr0 : (r : ℂ) ≠ 0 := by exact_mod_cast hr.ne'
  have hc : ∀ u : ℂ, (r • u + z - z) / r = u := fun u => by
    rw [Complex.real_smul, add_sub_cancel_right, mul_div_cancel_left₀ _ hr0]
  have hinner : ∀ u : ℂ, ∫ y, φ ((r • u + z - z) / r) * (-Real.log ‖r • u + z - y‖) *
      ψ ((y - z) / r) = r ^ 2 * ∫ v, φ u * (-Real.log ‖u - v‖) * ψ v := by
    intro u
    rw [integral_eq_smul_add _ hr z]
    congr 1
    simp only [hc]
    have hae : (fun v => φ u * (-Real.log ‖r • u + z - (r • v + z)‖) * ψ v) =ᵐ[volume]
        fun v => φ u * (-Real.log r) * ψ v + φ u * (-Real.log ‖u - v‖) * ψ v := by
      filter_upwards [(Set.countable_singleton u).measure_zero volume |> measure_eq_zero_iff_ae_notMem.1]
        with v hv
      have huv : ‖u - v‖ ≠ 0 := by
        rw [norm_ne_zero_iff, sub_ne_zero]; exact fun h => hv (h ▸ rfl)
      rw [show r • u + z - (r • v + z) = r • (u - v) by rw [smul_sub]; abel, norm_smul,
        Real.norm_eq_abs, abs_of_pos hr, Real.log_mul hr.ne' huv]
      ring
    rw [integral_congr_ae hae, integral_add_of_left ((hψ.const_mul (φ u * -Real.log r)).congr
      (ae_of_all _ fun v => by simp only [mul_assoc]))]
    rw [integral_const_mul, hψ0, mul_zero]
  unfold logCov
  rw [integral_eq_smul_add _ hr z]
  simp only [hinner, integral_const_mul]
  ring

/-! ## Mean-zero test functions are preserved by the affine pullback -/

lemma integral_testAffinePull (φ : TestC) {r : ℝ} (hr : 0 < r) (z : ℂ) :
    ∫ x, testAffinePull r z φ x = r ^ 2 * ∫ x, φ x := by
  simp only [testAffinePull_apply r z hr.ne' φ]
  exact integral_comp_aff (fun x => φ x) hr z

/-- the affine pullback on mean-zero test functions -/
def pull0 (r : ℝ) (z : ℂ) (hr : 0 < r) (φ : TestC0) : TestC0 :=
  ⟨testAffinePull r z φ.1, by rw [integral_testAffinePull φ.1 hr z, φ.2, mul_zero]⟩

lemma logCov_pull0 {r : ℝ} (hr : 0 < r) (z : ℂ) (φ ψ : TestC0) :
    logCov (pull0 r z hr φ).1 (pull0 r z hr ψ).1 = r ^ 4 * logCov φ.1 ψ.1 := by
  have e : ∀ χ : TestC0, ((pull0 r z hr χ).1 : ℂ → ℝ) = fun x => χ.1 ((x - z) / r) :=
    fun χ => funext fun x => testAffinePull_apply r z hr.ne' χ.1 x
  rw [e, e]
  exact logCov_affine _ _ (integrable_test ψ.1) ψ.2 hr z

lemma affineComp_apply (r : ℝ) (z : ℂ) (h : DistC) (φ : TestC) :
    affineComp r z h φ = (r ^ 2)⁻¹ * h (testAffinePull r z φ) := rfl

lemma addConst_apply (h : DistC) (c : ℝ) (φ : TestC) :
    addConst h c φ = h φ + (∫ x, φ x) * c := by
  show h φ + ofCont _ φ = _
  rw [ofCont, Distribution.ofFun_apply (f := ⇑(ContinuousMap.const ℂ c))
    (by exact (locallyIntegrable_const c).locallyIntegrableOn _)]
  simp [integral_mul_const]

end GFFInv

open GFFInv

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}

/-- Scale and translation invariance: if `h` is a whole-plane GFF then so is `h(r · + z)`. -/
theorem IsWholePlaneGFF.affineComp {h : Ω → DistC} (hh : IsWholePlaneGFF h P) {r : ℝ}
    (hr : 0 < r) (z : ℂ) : IsWholePlaneGFF (fun ω => affineComp r z (h ω)) P where
  measurable := by
    refine measurable_distC_iff.2 fun φ => ?_
    simp only [affineComp_apply]
    exact ((measurable_pair _).comp hh.measurable).const_mul _
  gaussian := by
    have := (hh.gaussian.comp_right (pull0 r z hr)).smul (fun _ => (r ^ 2)⁻¹)
    have e : (fun (φ : TestC0) ω => LQGMetric.affineComp r z (h ω) φ.1) =
        fun t ω => (r ^ 2)⁻¹ • ((fun (φ : TestC0) ω => h ω φ.1) ∘ pull0 r z hr) t ω := rfl
    rw [e]; exact this
  centered := fun φ => by
    simp only [affineComp_apply]
    rw [integral_const_mul]
    exact mul_eq_zero_of_right _ (hh.centered (pull0 r z hr φ))
  covariance_eq := fun φ ψ => by
    simp only [affineComp_apply]
    rw [covariance_const_mul_left, covariance_const_mul_right]
    have := hh.covariance_eq (pull0 r z hr φ) (pull0 r z hr ψ)
    simp only [pull0] at this
    rw [this]
    have h4 := logCov_pull0 hr z φ ψ
    simp only [pull0] at h4
    rw [h4]
    field_simp

/-- Adding a (random, measurable) constant preserves `IsWholePlaneGFF`. -/
theorem IsWholePlaneGFF.addConst {h : Ω → DistC} (hh : IsWholePlaneGFF h P) {c : Ω → ℝ}
    (hc : Measurable c) : IsWholePlaneGFF (fun ω => LQGMetric.addConst (h ω) (c ω)) P := by
  have e : (fun (φ : TestC0) (ω : Ω) => LQGMetric.addConst (h ω) (c ω) φ.1) =
      fun (φ : TestC0) (ω : Ω) => h ω φ.1 := by
    funext φ ω; rw [addConst_apply, φ.2, zero_mul, add_zero]
  refine ⟨?_, ?_, ?_, ?_⟩
  · refine measurable_distC_iff.2 fun φ => ?_
    simp only [addConst_apply]
    exact ((measurable_pair _).comp hh.measurable).add (hc.const_mul _)
  · rw [e]; exact hh.gaussian
  · intro φ
    have h1 : (fun ω => LQGMetric.addConst (h ω) (c ω) φ.1) = fun ω => h ω φ.1 := congrFun e φ
    rw [h1]; exact hh.centered φ
  · intro φ ψ
    have h1 : (fun ω => LQGMetric.addConst (h ω) (c ω) φ.1) = fun ω => h ω φ.1 := congrFun e φ
    have h2 : (fun ω => LQGMetric.addConst (h ω) (c ω) ψ.1) = fun ω => h ω ψ.1 := congrFun e ψ
    rw [h1, h2]; exact hh.covariance_eq φ ψ

end LQGMetric
