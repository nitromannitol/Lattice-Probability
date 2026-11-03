/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Field.MarkovWeylConv at commit 31e7483; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Field.MarkovWeylInt
import Mathlib.Topology.UniformSpace.HeineCantor

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# Distributions commute with convolution integrals (task P2-MKA, toward leaf (H))

For a test function `ρ` and a continuous compactly supported `φ`, the family
`y ↦ φ(y) ρ(· − y)` is a bounded continuous family in `𝓓_K`, `K = closedBall 0 (R_φ + R_ρ)`
(`convFam`, `continuous_convFam`), so (`exists_testIntegral_measure`) the convolution
`φ * ρ = ∫ φ(y) ρ(· − y) dy` is in `𝓓_K` and `T(φ * ρ) = ∫ T(φ(y) ρ(· − y)) dy` for every
continuous linear `T` on `𝓓_K` (`exists_conv_pairing`). This is the regularization identity
`⟨T, φ * ρ⟩ = ∫ φ(y) ⟨T, ρ(· − y)⟩ dy` of Hörmander, *ALPDO I*, Thm 4.1.1 / (4.1.2), used in the
mollification proof of Weyl's lemma. Template: `CircleAvg.continuous_bumpCurve`.
-/

noncomputable section

open MeasureTheory Filter Topology Set TopologicalSpace Metric
open scoped Distributions BoundedContinuousFunction

namespace LQGMetric
namespace MarkovWeyl

open TestIntegral

/-- the compact `closedBall 0 R` -/
def ballK0 (R : ℝ) : Compacts ℂ := ⟨closedBall 0 R, isCompact_closedBall _ _⟩

variable {ρ : ℂ → ℝ} (hρ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ρ) {φ : ℂ → ℝ} {R S : ℝ}
  (hρS : ∀ x, S < ‖x‖ → ρ x = 0) (hφR : ∀ y, R < ‖y‖ → φ y = 0)

include hρS hφR in
lemma support_convFam (y : ℂ) :
    Function.support (fun x => φ y * ρ (x - y)) ⊆ (ballK0 (R + S) : Set ℂ) := by
  intro x hx
  have h1 : φ y ≠ 0 := left_ne_zero_of_mul hx
  have h2 : ρ (x - y) ≠ 0 := right_ne_zero_of_mul hx
  have a1 : ‖y‖ ≤ R := not_lt.1 fun h => h1 (hφR y h)
  have a2 : ‖x - y‖ ≤ S := not_lt.1 fun h => h2 (hρS _ h)
  show x ∈ closedBall 0 (R + S)
  rw [mem_closedBall, dist_zero_right]
  calc ‖x‖ = ‖(x - y) + y‖ := by rw [sub_add_cancel]
    _ ≤ ‖x - y‖ + ‖y‖ := norm_add_le _ _
    _ ≤ R + S := by linarith

/-- the family `y ↦ φ(y) ρ(· − y)` in `𝓓_K` -/
def convFam (y : ℂ) : 𝓓^{⊤}_{ballK0 (R + S)}(ℂ, ℝ) :=
  ContDiffMapSupportedIn.of_support_subset
    (contDiff_const.mul (hρ.comp (contDiff_id.sub contDiff_const)))
    (support_convFam hρS hφR y)

lemma convFam_apply (y x : ℂ) : convFam hρ hρS hφR y x = φ y * ρ (x - y) := rfl

lemma iteratedFDeriv_convFam (i : ℕ) (y x : ℂ) :
    iteratedFDeriv ℝ i (convFam hρ hρS hφR y) x = φ y • iteratedFDeriv ℝ i ρ (x - y) := by
  have e : (convFam hρ hρS hφR y : ℂ → ℝ) = φ y • fun x => ρ (x + -y) := by
    funext x; simp [convFam_apply, sub_eq_add_neg]
  have hf : ContDiffAt ℝ i (fun x => ρ (x + -y)) x :=
    ((hρ.comp (contDiff_id.add contDiff_const)).contDiffAt.of_le (by exact_mod_cast le_top))
  rw [e, iteratedFDeriv_const_smul_apply hf, iteratedFDeriv_comp_add_right, sub_eq_add_neg]

lemma structureMap_convFam (i : ℕ) (y x : ℂ) :
    (ContDiffMapSupportedIn.structureMapCLM ℝ ⊤ i (convFam hρ hρS hφR y)) x =
      φ y • iteratedFDeriv ℝ i ρ (x - y) := by
  rw [ContDiffMapSupportedIn.structureMapCLM_top_apply]
  exact iteratedFDeriv_convFam hρ hρS hφR i y x

include hρ hρS in
lemma exists_bound_iteratedFDeriv (i : ℕ) : ∃ M, 0 ≤ M ∧ ∀ x, ‖iteratedFDeriv ℝ i ρ x‖ ≤ M := by
  have hc : HasCompactSupport ρ := HasCompactSupport.intro (isCompact_closedBall (0 : ℂ) S)
    fun x hx => hρS x (by simpa [mem_closedBall, dist_zero_right] using hx)
  obtain ⟨M, hM⟩ := (hc.iteratedFDeriv i).exists_bound_of_continuous
    (hρ.continuous_iteratedFDeriv (by exact_mod_cast le_top))
  exact ⟨max M 0, le_max_right _ _, fun x => (hM x).trans (le_max_left _ _)⟩

lemma continuous_convFam (hφ : Continuous φ) : Continuous (convFam hρ hρS hφR) := by
  rw [ContDiffMapSupportedIn.continuous_iff_comp]
  intro i
  set G := iteratedFDeriv ℝ i ρ
  have hc : HasCompactSupport ρ := HasCompactSupport.intro (isCompact_closedBall (0 : ℂ) S)
    fun x hx => hρS x (by simpa [mem_closedBall, dist_zero_right] using hx)
  have hGc : Continuous G := hρ.continuous_iteratedFDeriv (by exact_mod_cast le_top)
  have hGu : UniformContinuous G := (hc.iteratedFDeriv i).uniformContinuous_of_continuous hGc
  obtain ⟨M, hM0, hM⟩ := exists_bound_iteratedFDeriv hρ hρS i
  rw [Metric.continuous_iff]
  intro y₀ ε hε
  set A := |φ y₀| + 1
  have hA : 0 < A := by positivity
  obtain ⟨δ, hδ, hG⟩ := Metric.uniformContinuous_iff.mp hGu (ε / (4 * A)) (by positivity)
  obtain ⟨η₁, hη₁, hφc⟩ := Metric.continuous_iff.mp hφ y₀ (ε / (4 * (M + 1))) (by positivity)
  refine ⟨min δ η₁, lt_min hδ hη₁, fun y hy => ?_⟩
  have hyδ : dist y y₀ < δ := hy.trans_le (min_le_left _ _)
  have hyη : dist (φ y) (φ y₀) < ε / (4 * (M + 1)) := hφc y (hy.trans_le (min_le_right _ _))
  refine lt_of_le_of_lt ((BoundedContinuousFunction.dist_le (by positivity)).mpr fun x => ?_)
    (half_lt_self hε)
  simp only [Function.comp_apply, structureMap_convFam]
  rw [dist_eq_norm]
  have hd : dist (G (x - y)) (G (x - y₀)) < ε / (4 * A) := hG (by
    rw [dist_eq_norm, sub_sub_sub_cancel_left, ← dist_eq_norm']; exact hyδ)
  have e : φ y • G (x - y) - φ y₀ • G (x - y₀) =
      (φ y - φ y₀) • G (x - y) + φ y₀ • (G (x - y) - G (x - y₀)) := by
    rw [sub_smul, smul_sub]; abel
  rw [e]
  refine (norm_add_le _ _).trans ?_
  rw [norm_smul, norm_smul, ← dist_eq_norm, ← dist_eq_norm]
  have t1 : dist (φ y) (φ y₀) * ‖G (x - y)‖ ≤ ε / (4 * (M + 1)) * (M + 1) :=
    mul_le_mul hyη.le ((hM _).trans (le_add_of_nonneg_right zero_le_one)) (norm_nonneg _)
      (by positivity)
  have t2 : |φ y₀| * dist (G (x - y)) (G (x - y₀)) ≤ A * (ε / (4 * A)) := by
    exact mul_le_mul (by linarith) hd.le dist_nonneg hA.le
  have e1 : ε / (4 * (M + 1)) * (M + 1) = ε / 4 := by field_simp
  have e2 : A * (ε / (4 * A)) = ε / 4 := by field_simp
  rw [Real.norm_eq_abs]
  linarith

lemma bound_convFam {C : ℝ} (hC : ∀ y, |φ y| ≤ C) (i : ℕ) :
    ∃ B, ∀ y, ‖ContDiffMapSupportedIn.structureMapCLM ℝ ⊤ i (convFam hρ hρS hφR y)‖ ≤ B := by
  obtain ⟨M, hM0, hM⟩ := exists_bound_iteratedFDeriv hρ hρS i
  have hC0 : 0 ≤ C := (abs_nonneg _).trans (hC 0)
  refine ⟨C * M, fun y => (BoundedContinuousFunction.norm_le (by positivity)).2 fun x => ?_⟩
  rw [structureMap_convFam, norm_smul, Real.norm_eq_abs]
  exact mul_le_mul (hC y) (hM _) (norm_nonneg _) hC0

end MarkovWeyl
end LQGMetric
