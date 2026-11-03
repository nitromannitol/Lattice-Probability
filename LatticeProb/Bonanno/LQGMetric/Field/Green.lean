/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Field.Green at commit 31e7483; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Statement.GFF
import LatticeProb.Bonanno.QuantumZipper.Proofs.GFF.K3.HarmonicPart

/-!
# Whole-plane Green identity for the log kernel (task P2-FCM, part 1)

For a test function `φ ∈ 𝓓(ℂ)` put `ρ_φ := −Δφ/(2π)` (`cmTest φ`, again a test function, of mean
zero: `cmTest0 φ : TestC0`). Then

* `logCov_cmTest_right` : `∫∫ ψ(x) (−log|x−y|) ρ_φ(y) dx dy = ∫ ψ φ` for **every** `ψ`
  (the fundamental-solution identity `φ(x) = (2π)⁻¹∫ (−log|x−y|)(−Δφ)(y) dy`);
* `logCov_cmTest_cmTest` : `∫∫ ρ_φ(x) (−log|x−y|) ρ_φ(y) = (φ, φ)_∇ := (2π)⁻¹∫|∇φ|²`
  (`gradEnergy φ`, GM's normalization of the Dirichlet inner product).

So `−Δ/(2π)` inverts the covariance kernel `logCov` of `IsWholePlaneGFF`, which is what makes
the Cameron–Martin shift of `h` by `φ` the Gaussian-process shift in the direction `ρ_φ`
(`LQGMetric/Field/CameronMartin.lean`).

Sources: Berestycki–Powell, *Gaussian free field and Liouville quantum gravity*, arXiv:2404.16642,
`BookNathanael/definitionGFF.tex` l. 1390 (Prop. `lem:CMGFF`, `(h, F)_∇ = (h, −ΔF)/(2π)`); the
whole-plane fundamental solution `−(2π)⁻¹ log|·|` of `−Δ` is standard. The analytic inputs are reused verbatim from
QuantumZipper: `QuantumZipper.K3.integral_log_norm_sub_mul_laplacian` (`∫ log|z−w| Δφ(z) dz =
2π φ(w)`), `K3.integral_norm_fderiv_sq_eq_neg_integral_mul_laplacian` (Green's first identity),
`K3.integral_laplacian_eq_zero`, `K3.laplacian_eq_fderiv_fderiv` (QZ/Proofs/GFF/K3/Polar.lean,
HarmonicPart.lean).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Laplacian
open scoped Real

namespace LQGMetric

/-- `(φ, φ)_∇ = (2π)⁻¹ ∫ |∇φ|²` (GM's Dirichlet energy). -/
def gradEnergy (φ : ℂ → ℝ) : ℝ := (2 * π)⁻¹ * ∫ z, ‖fderiv ℝ φ z‖ ^ 2

lemma contDiff_two_testC (φ : TestC) : ContDiff ℝ 2 φ :=
  φ.contDiff.of_le (by simp)

lemma contDiff_laplacian_testC (φ : TestC) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (Δ (⇑φ)) := by
  have hφ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) φ := φ.contDiff
  have h1 : ∀ v : ℂ, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun y => fderiv ℝ φ y v) := fun v =>
    (hφ.fderiv_right (m := ((⊤ : ℕ∞) : WithTop ℕ∞)) (by simp)).clm_apply contDiff_const
  have h2 : ∀ v w : ℂ, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun z => fderiv ℝ (fun y => fderiv ℝ φ y v) z w) := fun v w =>
    ((h1 v).fderiv_right (m := ((⊤ : ℕ∞) : WithTop ℕ∞)) (by simp)).clm_apply contDiff_const
  rw [show Δ (⇑φ) = fun z => fderiv ℝ (fun y => fderiv ℝ φ y 1) z 1 +
      fderiv ℝ (fun y => fderiv ℝ φ y Complex.I) z Complex.I from
    funext (QuantumZipper.K3.laplacian_eq_fderiv_fderiv (contDiff_two_testC φ))]
  exact (h2 1 1).add (h2 Complex.I Complex.I)

/-- `ρ_φ = −Δφ/(2π)` as a test function. -/
def cmTest (φ : TestC) : TestC where
  toFun := fun z => -(2 * π)⁻¹ * Δ (⇑φ) z
  contDiff' := contDiff_const.mul (contDiff_laplacian_testC φ)
  hasCompactSupport' :=
    (QuantumZipper.K3.hasCompactSupport_laplacian_K3 φ.hasCompactSupport).mul_left
  tsupport_subset' := subset_univ _

lemma cmTest_apply (φ : TestC) (z : ℂ) : cmTest φ z = -(2 * π)⁻¹ * Δ (⇑φ) z := rfl

lemma integral_cmTest (φ : TestC) : ∫ z, cmTest φ z = 0 := by
  simp only [cmTest_apply]
  rw [integral_const_mul,
    QuantumZipper.K3.integral_laplacian_eq_zero (contDiff_two_testC φ) φ.hasCompactSupport,
    mul_zero]

/-- `ρ_φ = −Δφ/(2π)` as a mean-zero test function. -/
def cmTest0 (φ : TestC) : TestC0 := ⟨cmTest φ, integral_cmTest φ⟩

/-- Fundamental solution: `(2π)⁻¹ ∫ (−log|x−y|)(−Δφ)(y) dy = φ(x)`. -/
lemma integral_negLog_mul_cmTest (φ : TestC) (x : ℂ) :
    ∫ y, -Real.log ‖x - y‖ * cmTest φ y = φ x := by
  have e : ∀ y, -Real.log ‖x - y‖ * cmTest φ y =
      (2 * π)⁻¹ * (Real.log ‖y - x‖ * Δ (⇑φ) y) := fun y => by
    rw [cmTest_apply, norm_sub_rev]; ring
  simp_rw [e]
  rw [integral_const_mul, QuantumZipper.K3.integral_log_norm_sub_mul_laplacian
    (contDiff_two_testC φ) φ.hasCompactSupport x, ← mul_assoc,
    inv_mul_cancel₀ (by positivity), one_mul]

/-- **Green identity.** `logCov ψ ρ_φ = ∫ ψ φ` for every `ψ : ℂ → ℝ`. -/
theorem logCov_cmTest_right (φ : TestC) (ψ : ℂ → ℝ) :
    logCov ψ (cmTest φ) = ∫ x, ψ x * φ x := by
  unfold logCov
  congr 1
  funext x
  simp_rw [mul_assoc]
  rw [integral_const_mul, integral_negLog_mul_cmTest]

/-- **Energy identity.** `logCov ρ_φ ρ_φ = (φ, φ)_∇`. -/
theorem logCov_cmTest_cmTest (φ : TestC) :
    logCov (cmTest φ) (cmTest φ) = gradEnergy φ := by
  rw [logCov_cmTest_right, gradEnergy,
    QuantumZipper.K3.integral_norm_fderiv_sq_eq_neg_integral_mul_laplacian
      (contDiff_two_testC φ) φ.hasCompactSupport]
  simp only [cmTest_apply]
  rw [show (fun x => -(2 * π)⁻¹ * Δ (⇑φ) x * φ x) =
      fun x => -(2 * π)⁻¹ * (φ x * Δ (⇑φ) x) from funext fun x => by ring, integral_const_mul]
  ring

end LQGMetric
