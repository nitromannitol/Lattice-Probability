/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Field.MarkovWeyl2Pot at commit 31e7483; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.QuantumZipper.Proofs.GFF.K3.Polar
import LatticeProb.Bonanno.QuantumZipper.Proofs.GFF.K3.GreenLower3
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S2.SpatialIndepMV
import Mathlib.Analysis.InnerProductSpace.Harmonic.Constructions
import Mathlib.Analysis.Calculus.ContDiff.Convolution

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# Radial test functions with equal mass differ by a Laplacian (task P2-MKH, leaf (H))

The crux of the mollification proof of Weyl's lemma (Hörmander, *ALPDO I*, proof of
Thm 4.4.1; the "radial" step, e.g. Hörmander Thm 4.4.1 / Evans–Gariepy-style mean value
argument): for `σ` smooth, rotation invariant, vanishing off `B̄(0, r)` with `∫ σ = 0`, the
logarithmic potential `u = log|·| * σ` is smooth, satisfies `Δu = 2π σ` and vanishes off
`B̄(0, r)` (Newton's theorem). Hence `σ = −Δf/(2π)` with `f = log|·| * (−σ) ∈ C_c^∞(B̄(0,r))`.

* `logConv σ = log‖·‖ ⋆ σ`, `contDiff_logConv`, `fderiv_logConv_apply` (mathlib
  `HasCompactSupport.hasFDerivAt_convolution_right`);
* `laplacian_logConv`: `Δ(log‖·‖ ⋆ σ) = 2πσ` (QuantumZipper Green formula F4
  `K3.integral_log_norm_sub_mul_laplacian`);
* `logConv_eq_zero_of_radial` (Newton's theorem): the mean value property against radial
  weights `GM.integral_mul_radial_of_harmonic` applied to the harmonic `z ↦ log‖w − z‖`;
* `exists_poisson_radial`.
-/

noncomputable section

open MeasureTheory Filter Topology Set Metric Laplacian InnerProductSpace
open scoped Real

namespace LQGMetric
namespace MarkovWeyl2

/-- the logarithmic potential `(log‖·‖ ⋆ σ)(w) = ∫ log‖t‖ σ(w − t) dt` -/
def logConv (σ : ℂ → ℝ) : ℂ → ℝ :=
  convolution (fun t : ℂ => Real.log ‖t‖) σ (ContinuousLinearMap.lsmul ℝ ℝ) volume

lemma logConv_apply (σ : ℂ → ℝ) (w : ℂ) : logConv σ w = ∫ t, Real.log ‖t‖ * σ (w - t) := by
  simp [logConv, convolution_def]

lemma logConv_apply' (σ : ℂ → ℝ) (w : ℂ) : logConv σ w = ∫ y, Real.log ‖w - y‖ * σ y := by
  rw [logConv_apply, ← integral_sub_left_eq_self (fun y => Real.log ‖w - y‖ * σ y) volume w]
  simp

lemma contDiff_logConv {σ : ℂ → ℝ} (hσ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) σ)
    (hc : HasCompactSupport σ) : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (logConv σ) :=
  hc.contDiff_convolution_right (ContinuousLinearMap.lsmul ℝ ℝ) (n := ⊤)
    QuantumZipper.K3.locallyIntegrable_log_norm hσ

lemma integrable_logConv {σ : ℂ → ℝ} (hσ : Continuous σ) (hc : HasCompactSupport σ) (w : ℂ) :
    Integrable (fun t => Real.log ‖t‖ * σ (w - t)) := by
  have := hc.convolutionExists_right (ContinuousLinearMap.lsmul ℝ ℝ) (μ := volume)
    QuantumZipper.K3.locallyIntegrable_log_norm hσ w
  simpa [ConvolutionExistsAt] using this

lemma fderiv_logConv_apply {σ : ℂ → ℝ} (hσ : ContDiff ℝ 1 σ) (hc : HasCompactSupport σ)
    (w v : ℂ) : fderiv ℝ (logConv σ) w v = logConv (fun x => fderiv ℝ σ x v) w := by
  rw [logConv, (hc.hasFDerivAt_convolution_right (ContinuousLinearMap.lsmul ℝ ℝ)
    QuantumZipper.K3.locallyIntegrable_log_norm hσ w).fderiv]
  have hex := (hc.fderiv (𝕜 := ℝ)).convolutionExists_right
    ((ContinuousLinearMap.lsmul ℝ ℝ).precompR ℂ) (μ := volume)
    QuantumZipper.K3.locallyIntegrable_log_norm (hσ.continuous_fderiv one_ne_zero) w
  rw [convolution_def, ContinuousLinearMap.integral_apply hex, logConv_apply]
  simp

lemma contDiff_fderiv_apply {σ : ℂ → ℝ} (hσ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) σ) (v : ℂ) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun x => fderiv ℝ σ x v) :=
  (hσ.fderiv_right (m := ((⊤ : ℕ∞) : WithTop ℕ∞)) (by simp)).clm_apply contDiff_const

lemma hasCompactSupport_fderiv_apply {σ : ℂ → ℝ} (hc : HasCompactSupport σ) (v : ℂ) :
    HasCompactSupport (fun x => fderiv ℝ σ x v) :=
  (hc.fderiv (𝕜 := ℝ)).comp_left (g := fun L : ℂ →L[ℝ] ℝ => L v) rfl

/-- `∂_v ∂_v (log‖·‖ ⋆ σ) = log‖·‖ ⋆ ∂_v ∂_v σ` -/
lemma fderiv_fderiv_logConv {σ : ℂ → ℝ} (hσ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) σ)
    (hc : HasCompactSupport σ) (w v : ℂ) :
    fderiv ℝ (fun y => fderiv ℝ (logConv σ) y v) w v =
      logConv (fun x => fderiv ℝ (fun y => fderiv ℝ σ y v) x v) w := by
  have e : (fun y => fderiv ℝ (logConv σ) y v) = logConv (fun x => fderiv ℝ σ x v) :=
    funext fun y => fderiv_logConv_apply (hσ.of_le (by simp)) hc y v
  rw [e]
  exact fderiv_logConv_apply ((contDiff_fderiv_apply hσ v).of_le (by simp))
    (hasCompactSupport_fderiv_apply hc v) w v

/-- **`Δ(log‖·‖ ⋆ σ) = 2πσ`** for `σ ∈ C_c^∞`. -/
theorem laplacian_logConv {σ : ℂ → ℝ} (hσ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) σ)
    (hc : HasCompactSupport σ) (w : ℂ) : Δ (logConv σ) w = 2 * π * σ w := by
  have h2 : ContDiff ℝ 2 (logConv σ) := (contDiff_logConv hσ hc).of_le (by simp)
  rw [QuantumZipper.K3.laplacian_eq_fderiv_fderiv h2, fderiv_fderiv_logConv hσ hc,
    fderiv_fderiv_logConv hσ hc, logConv_apply, logConv_apply, ← integral_add]
  · have hΔ : ∀ x, fderiv ℝ (fun y => fderiv ℝ σ y 1) x 1 +
        fderiv ℝ (fun y => fderiv ℝ σ y Complex.I) x Complex.I = Δ σ x := fun x =>
      (QuantumZipper.K3.laplacian_eq_fderiv_fderiv (hσ.of_le (by simp)) x).symm
    simp_rw [← mul_add, hΔ]
    rw [← QuantumZipper.K3.integral_log_norm_sub_mul_laplacian (hσ.of_le (by simp)) hc w,
      ← integral_sub_left_eq_self (fun z => Real.log ‖z - w‖ * Δ σ z) volume w]
    simp
  all_goals
    refine integrable_logConv (σ := fun x => fderiv ℝ (fun y => fderiv ℝ σ y _) x _) ?_ ?_ w
    · exact (contDiff_fderiv_apply (contDiff_fderiv_apply hσ _) _).continuous
    · exact hasCompactSupport_fderiv_apply (hasCompactSupport_fderiv_apply hc _) _

/-- **Newton's theorem.** The logarithmic potential of a rotation invariant `σ` with `∫ σ = 0`
vanishes outside `B̄(0, r) ⊇ supp σ`. -/
theorem logConv_eq_zero_of_radial {σ : ℂ → ℝ} (hσc : Continuous σ)
    (hrad : ∀ (a : Circle) (y : ℂ), σ (a * y) = σ y) {r : ℝ}
    (hs : ∀ y, r < ‖y‖ → σ y = 0) (h0 : ∫ y, σ y = 0) {w : ℂ} (hw : r < ‖w‖) :
    logConv σ w = 0 := by
  have hV : IsOpen {z : ℂ | z ≠ w} := isOpen_ne
  have hg : HarmonicOnNhd (fun z : ℂ => Real.log ‖w - z‖) {z : ℂ | z ≠ w} := by
    intro z hz
    exact AnalyticAt.harmonicAt_log_norm (f := fun z : ℂ => w - z)
      (analyticAt_const.sub analyticAt_id) (sub_ne_zero.2 (Ne.symm hz))
  have hB : closedBall (0 : ℂ) r ⊆ {z : ℂ | z ≠ w} := by
    intro z hz hzw
    rw [mem_closedBall, dist_zero_right, hzw] at hz
    linarith
  have := GM.integral_mul_radial_of_harmonic hV hg hB hσc hs hrad
  rw [logConv_apply']
  simpa [h0] using this

/-- **Radial test functions of mass zero are Laplacians of test functions.** For `σ` smooth,
rotation invariant, vanishing off `B̄(0, r)` with `∫ σ = 0`, `f = log‖·‖ ⋆ (−σ)` is smooth,
vanishes off `B̄(0, r)` and `−Δf/(2π) = σ`. -/
theorem exists_poisson_radial {σ : ℂ → ℝ} (hσ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) σ)
    (hrad : ∀ (a : Circle) (y : ℂ), σ (a * y) = σ y) {r : ℝ}
    (hs : ∀ y, r < ‖y‖ → σ y = 0) (h0 : ∫ y, σ y = 0) :
    ∃ f : ℂ → ℝ, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) f ∧ (∀ x, r < ‖x‖ → f x = 0) ∧
      ∀ x, -(2 * π)⁻¹ * Δ f x = σ x := by
  have hc : HasCompactSupport (fun x => -σ x) := HasCompactSupport.intro
    (isCompact_closedBall (0 : ℂ) r) fun x hx => by
      rw [hs x (by simpa [mem_closedBall, dist_zero_right] using hx), neg_zero]
  refine ⟨logConv (fun x => -σ x), contDiff_logConv hσ.neg hc, fun x hx => ?_, fun x => ?_⟩
  · refine logConv_eq_zero_of_radial (σ := fun x => -σ x) hσ.continuous.neg
      (fun a y => by simp only [hrad]) (fun y hy => by simp only [hs y hy, neg_zero])
      (by rw [integral_neg, h0, neg_zero]) hx
  · rw [laplacian_logConv hσ.neg hc]
    field_simp

end MarkovWeyl2
end LQGMetric
