/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Field.MarkovWeyl2Fam at commit 31e7483; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Field.MarkovWeyl2Rad
import LatticeProb.Bonanno.LQGMetric.Field.CircleAvgIntegral

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# Translates of a test function as a continuous family in `𝓓_K` (task P2-MKH)

`transFam`: `x ↦ ρ(· − q x)` for continuous `q : X → ℂ` with `B̄(q x, s) ⊆ K`, continuous into
`𝓓_K` (the argument of `CircleAvg.continuous_bumpCurve`, for a general translation curve).
Also: circle averages of the radial mollifiers are rotation invariant
(`integral_rbump_circle_rot`).
-/

noncomputable section

open MeasureTheory Filter Topology Set Metric TopologicalSpace
open scoped Real Distributions BoundedContinuousFunction

namespace LQGMetric
namespace MarkovWeyl2

section Fam

variable {K : Compacts ℂ} {ρ : ℂ → ℝ} (hρ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ρ) {s : ℝ}
  (hρs : ∀ y, s < ‖y‖ → ρ y = 0) {X : Type*} [PseudoMetricSpace X] {q : X → ℂ}
  (hqK : ∀ x, closedBall (q x) s ⊆ K)

include hρs hqK in
lemma support_trans_subset (x : X) : Function.support (fun y => ρ (y - q x)) ⊆ K := by
  intro y hy
  refine hqK x ?_
  by_contra h
  exact hy (hρs _ (by simpa [mem_closedBall, dist_eq_norm] using h))

/-- the family `x ↦ ρ(· − q x)` in `𝓓_K` -/
def transFam (x : X) : 𝓓^{⊤}_{K}(ℂ, ℝ) :=
  ContDiffMapSupportedIn.of_support_subset (hρ.comp (contDiff_id.sub contDiff_const))
    (support_trans_subset hρs hqK x)

lemma transFam_apply (x : X) (y : ℂ) : transFam hρ hρs hqK x y = ρ (y - q x) := rfl

include hρs in
lemma continuous_transFam (hq : Continuous q) : Continuous (transFam hρ hρs hqK) := by
  rw [ContDiffMapSupportedIn.continuous_iff_comp]
  intro i
  set G := iteratedFDeriv ℝ i ρ
  have hc : HasCompactSupport ρ := HasCompactSupport.intro (isCompact_closedBall (0 : ℂ) s)
    fun x hx => hρs x (by simpa [mem_closedBall, dist_zero_right] using hx)
  have hGc : Continuous G := hρ.continuous_iteratedFDeriv (by exact_mod_cast le_top)
  have hGu : UniformContinuous G := (hc.iteratedFDeriv i).uniformContinuous_of_continuous hGc
  have hval : ∀ x y, (ContDiffMapSupportedIn.structureMapCLM ℝ ⊤ i (transFam hρ hρs hqK x)) y =
      G (y - q x) := by
    intro x y
    rw [ContDiffMapSupportedIn.structureMapCLM_top_apply]
    have e : (transFam hρ hρs hqK x : ℂ → ℝ) = fun y => ρ (y + -q x) := by
      funext y; rw [transFam_apply, sub_eq_add_neg]
    rw [e, iteratedFDeriv_comp_add_right, sub_eq_add_neg]
  rw [Metric.continuous_iff]
  intro x₀ ε hε
  obtain ⟨δ, hδ, hG⟩ := Metric.uniformContinuous_iff.mp hGu (ε / 2) (by positivity)
  obtain ⟨η, hη, hcq⟩ := Metric.continuous_iff.mp hq x₀ δ hδ
  refine ⟨η, hη, fun x hx => ?_⟩
  refine lt_of_le_of_lt ((BoundedContinuousFunction.dist_le (by positivity)).mpr fun y => ?_)
    (half_lt_self hε)
  simp only [Function.comp_apply, hval]
  refine (hG ?_).le
  rw [dist_eq_norm, sub_sub_sub_cancel_left, ← dist_eq_norm']
  exact hcq x hx

end Fam

lemma rbump_congr_norm (r : ℝ) {w w' : ℂ} (h : ‖w‖ = ‖w'‖) : rbump r w = rbump r w' := by
  simp [rbump, rbump0, h]

lemma continuous_rbump (r : ℝ) : Continuous (rbump r) := (contDiff_rbump r).continuous

/-- rotation invariance of circle averages of the radial mollifiers -/
lemma integral_rbump_circle_rot (r s : ℝ) (a : Circle) (y : ℂ) :
    ∫ θ in (0 : ℝ)..2 * π, rbump r (a * y - circleMap 0 s θ) =
      ∫ θ in (0 : ℝ)..2 * π, rbump r (y - circleMap 0 s θ) := by
  obtain ⟨α, rfl⟩ := Circle.exp_surjective a
  have hn : ∀ θ : ℝ, ‖(Circle.exp α : ℂ) * y - circleMap 0 s θ‖ =
      ‖y - circleMap 0 s (θ - α)‖ := by
    intro θ
    have e : Complex.exp (θ * Complex.I) =
        Complex.exp (α * Complex.I) * Complex.exp ((θ - α : ℝ) * Complex.I) := by
      rw [← Complex.exp_add]; congr 1; push_cast; ring
    simp only [circleMap, Circle.coe_exp, zero_add]
    rw [e, show Complex.exp (α * Complex.I) * y - s * (Complex.exp (α * Complex.I) *
        Complex.exp ((θ - α : ℝ) * Complex.I)) = Complex.exp (α * Complex.I) *
        (y - s * Complex.exp ((θ - α : ℝ) * Complex.I)) by ring, norm_mul,
      Complex.norm_exp_ofReal_mul_I, one_mul]
  simp_rw [rbump_congr_norm r (hn _)]
  set f : ℝ → ℝ := fun θ => rbump r (y - circleMap 0 s θ)
  have hper : Function.Periodic f (2 * π) := fun θ => by
    simp only [f, periodic_circleMap 0 s θ]
  show ∫ θ in (0 : ℝ)..2 * π, f (θ - α) = ∫ θ in (0 : ℝ)..2 * π, f θ
  rw [intervalIntegral.integral_comp_sub_right f α]
  have := hper.intervalIntegral_add_eq (-α) 0
  simp only [zero_add] at this
  rw [← this, zero_sub, show 2 * π - α = -α + 2 * π by ring]

end MarkovWeyl2
end LQGMetric
