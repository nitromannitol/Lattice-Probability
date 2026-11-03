/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Field.CircleAvgPairing at commit 31e7483; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Field.CircleAvgIntegral
import LatticeProb.Bonanno.LQGMetric.Field.Measurable
import LatticeProb.Bonanno.LQGMetric.Field.GFFInvariance
import Mathlib.Topology.UniformSpace.HeineCantor

/-!
# Circle averages of mollified fields are pairings with one test function

For a distribution `h` on `ℂ`, `x ↦ h (bumpTest n x)` is the mollification `h * ψ_n`. Its
circle average over `∂B(z, r)` is the pairing of `h` with the single test function
`circBump n z r = σ_{z,r} * ψ_n`, `y ↦ (1/2π) ∫₀^{2π} ψ_n(y − z − r e^{iθ}) dθ`
(`circleAverage_pairing`). This is the bridge between our definition `circleAvg` (a limit of
circle averages of mollified fields, FOUNDATIONS §3, deviation F4) and Duplantier–Sheffield's
circle average `(h, ρ_ε^z)` (DS, arXiv:0808.1560, §3.1), where `circBump n z r → σ_{z,r}`.
Proof: `TestIntegral.exists_testIntegral` applied to the continuous curve
`θ ↦ ψ_{n, z + r e^{iθ}}` in `𝓓_K`, `K = closedBall z (|r| + 1)`.

Consequences proved here: `∫ circBump n z r = 1`, and the effect of adding a constant.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Filter Topology Set TopologicalSpace Metric
open scoped Distributions BoundedContinuousFunction

namespace LQGMetric
namespace CircleAvg

open TestIntegral

/-- the bump underlying `bumpTest n x` -/
def bumpAt (n : ℕ) (x : ℂ) : ContDiffBump x :=
  ⟨(2 : ℝ)⁻¹ ^ (n + 1), (2 : ℝ)⁻¹ ^ n, by positivity,
    pow_lt_pow_right_of_lt_one₀ (by norm_num) (by norm_num) (Nat.lt_succ_self n)⟩

lemma bumpTest_apply (n : ℕ) (x y : ℂ) : bumpTest n x y = (bumpAt n x).normed volume y := rfl

lemma bumpAt_apply (n : ℕ) (x y : ℂ) : bumpAt n x y = bumpAt n 0 (y - x) := by
  rw [ContDiffBump.apply, ContDiffBump.apply, sub_zero]
  rfl

/-- translation structure of the mollifiers -/
lemma bumpTest_eq_sub (n : ℕ) (x y : ℂ) : bumpTest n x y = bumpTest n 0 (y - x) := by
  rw [bumpTest_apply, bumpTest_apply, ContDiffBump.normed_def, ContDiffBump.normed_def,
    bumpAt_apply]
  congr 1
  simp_rw [bumpAt_apply n x]
  exact integral_sub_right_eq_self (fun w => bumpAt n 0 w) x

lemma bumpTest_eq_zero (n : ℕ) {x y : ℂ} (hy : 1 ≤ dist y x) : bumpTest n x y = 0 := by
  rw [bumpTest_apply, ContDiffBump.normed_def, (bumpAt n x).zero_of_le_dist, zero_div]
  show (2 : ℝ)⁻¹ ^ n ≤ dist y x
  exact le_trans (pow_le_one₀ (by norm_num) (by norm_num)) hy

/-- the compact `closedBall z (|r| + 1)` -/
def ballK (z : ℂ) (r : ℝ) : Compacts ℂ := ⟨closedBall z (|r| + 1), isCompact_closedBall _ _⟩

lemma support_bumpTest_circle (n : ℕ) (z : ℂ) (r θ : ℝ) :
    Function.support (bumpTest n (circleMap z r θ)) ⊆ (ballK z r : Set ℂ) := by
  intro y hy
  by_contra hK
  apply hy
  apply bumpTest_eq_zero
  have h1 : |r| + 1 < dist y z := by simpa [ballK] using hK
  have h2 : dist (circleMap z r θ) z = |r| := by simp [dist_eq_norm, circleMap_sub_center]
  linarith [dist_triangle y (circleMap z r θ) z]

/-- the curve `θ ↦ ψ_{n, z + r e^{iθ}}` in `𝓓_K` -/
def bumpCurve (n : ℕ) (z : ℂ) (r : ℝ) (θ : ℝ) : 𝓓^{⊤}_{ballK z r}(ℂ, ℝ) :=
  ContDiffMapSupportedIn.of_support_subset (bumpTest n (circleMap z r θ)).contDiff
    (support_bumpTest_circle n z r θ)

lemma iteratedFDeriv_bumpTest (n : ℕ) (x : ℂ) (i : ℕ) (y : ℂ) :
    iteratedFDeriv ℝ i (bumpTest n x) y = iteratedFDeriv ℝ i (bumpTest n 0) (y - x) := by
  have : (bumpTest n x : ℂ → ℝ) = fun y => bumpTest n 0 (y + -x) := by
    funext y; rw [bumpTest_eq_sub, sub_eq_add_neg]
  rw [this, iteratedFDeriv_comp_add_right, sub_eq_add_neg]

lemma continuous_bumpCurve (n : ℕ) (z : ℂ) (r : ℝ) : Continuous (bumpCurve n z r) := by
  rw [ContDiffMapSupportedIn.continuous_iff_comp]
  intro i
  set G := iteratedFDeriv ℝ i (bumpTest n 0 : ℂ → ℝ)
  have hGc : Continuous G := (bumpTest n 0).contDiff.continuous_iteratedFDeriv
    (by exact_mod_cast le_top)
  have hGu : UniformContinuous G :=
    ((bumpTest n 0).hasCompactSupport.iteratedFDeriv i).uniformContinuous_of_continuous hGc
  have hval : ∀ θ y, (ContDiffMapSupportedIn.structureMapCLM ℝ ⊤ i (bumpCurve n z r θ)) y =
      G (y - circleMap z r θ) := by
    intro θ y
    rw [ContDiffMapSupportedIn.structureMapCLM_top_apply]
    exact iteratedFDeriv_bumpTest n _ i y
  rw [Metric.continuous_iff]
  intro θ₀ ε hε
  obtain ⟨δ, hδ, hG⟩ := Metric.uniformContinuous_iff.mp hGu (ε / 2) (by positivity)
  obtain ⟨η, hη, hc⟩ := Metric.continuous_iff.mp (continuous_circleMap z r) θ₀ δ hδ
  refine ⟨η, hη, fun θ hθ => ?_⟩
  refine lt_of_le_of_lt ((BoundedContinuousFunction.dist_le (by positivity)).mpr fun y => ?_)
    (half_lt_self hε)
  simp only [Function.comp_apply, hval]
  refine (hG ?_).le
  rw [dist_eq_norm, sub_sub_sub_cancel_left, ← dist_eq_norm']
  exact hc θ hθ

lemma bumpCurve_eq (n : ℕ) (z : ℂ) (r θ : ℝ) :
    TestFunction.ofSupportedIn (subset_univ _) (bumpCurve n z r θ) =
      bumpTest n (circleMap z r θ) := by
  ext y; rfl

lemma exists_circBump (n : ℕ) (z : ℂ) (r : ℝ) :
    ∃ I : 𝓓^{⊤}_{ballK z r}(ℂ, ℝ), (∀ y, I y = ∫ θ in (0 : ℝ)..2 * Real.pi, bumpCurve n z r θ y) ∧
      ∀ T : 𝓓^{⊤}_{ballK z r}(ℂ, ℝ) →L[ℝ] ℝ,
        T I = ∫ θ in (0 : ℝ)..2 * Real.pi, T (bumpCurve n z r θ) :=
  exists_testIntegral 0 (2 * Real.pi) (continuous_bumpCurve n z r)

/-- `σ_{z,r} * ψ_n` as a test function -/
def circBump (n : ℕ) (z : ℂ) (r : ℝ) : TestC :=
  (2 * Real.pi)⁻¹ • TestFunction.ofSupportedIn (subset_univ _) (exists_circBump n z r).choose

lemma circBump_apply (n : ℕ) (z : ℂ) (r : ℝ) (y : ℂ) :
    circBump n z r y = Real.circleAverage (fun x => bumpTest n x y) z r := by
  rw [Real.circleAverage_def]
  show (2 * Real.pi)⁻¹ * (exists_circBump n z r).choose y = _
  rw [(exists_circBump n z r).choose_spec.1 y, smul_eq_mul]
  rfl

lemma comp_bumpCurve (T : DistC) (n : ℕ) (z : ℂ) (r θ : ℝ) :
    (T.comp (TestFunction.ofSupportedInCLM ℝ (subset_univ _))) (bumpCurve n z r θ) =
      T (bumpTest n (circleMap z r θ)) := by
  show T (TestFunction.ofSupportedIn (subset_univ _) (bumpCurve n z r θ)) = _
  rw [bumpCurve_eq]

/-- **Circle averages of the mollified field are pairings.** -/
theorem circleAverage_pairing (T : DistC) (n : ℕ) (z : ℂ) (r : ℝ) :
    Real.circleAverage (fun x => T (bumpTest n x)) z r = T (circBump n z r) := by
  rw [circBump, map_smul, Real.circleAverage_def]
  have := (exists_circBump n z r).choose_spec.2
    (T.comp (TestFunction.ofSupportedInCLM ℝ (subset_univ _)))
  simp_rw [comp_bumpCurve] at this
  rw [← this]
  rfl

/-- the circle average of `x ↦ T(ψ_{n,x})` is circle integrable -/
lemma circleIntegrable_pairing (T : DistC) (n : ℕ) (z : ℂ) (r : ℝ) :
    CircleIntegrable (fun x => T (bumpTest n x)) z r := by
  have hc : Continuous fun θ => T (bumpTest n (circleMap z r θ)) := by
    have := (T.comp (TestFunction.ofSupportedInCLM ℝ (subset_univ _))).continuous.comp
      (continuous_bumpCurve n z r)
    exact this.congr fun θ => comp_bumpCurve T n z r θ
  exact hc.intervalIntegrable _ _

lemma integral_bumpTest' (n : ℕ) (x : ℂ) : ∫ y, bumpTest n x y = 1 :=
  ContDiffBump.integral_normed _

lemma integral_circBump (n : ℕ) (z : ℂ) (r : ℝ) : ∫ y, circBump n z r y = 1 := by
  have h := circleAverage_pairing (ofCont (ContinuousMap.const ℂ 1)) n z r
  simp only [ofCont_apply, ContinuousMap.const_apply, mul_one] at h
  simp_rw [integral_bumpTest'] at h
  rw [← h, Real.circleAverage_const]

/-- adding a constant shifts every mollified circle average by that constant -/
lemma circleAverage_addConst (h : DistC) (c : ℝ) (n : ℕ) (z : ℂ) (r : ℝ) :
    Real.circleAverage (fun x => addConst h c (bumpTest n x)) z r =
      Real.circleAverage (fun x => h (bumpTest n x)) z r + c := by
  rw [circleAverage_pairing, circleAverage_pairing, GFFInv.addConst_apply, integral_circBump, one_mul]

end CircleAvg
end LQGMetric
