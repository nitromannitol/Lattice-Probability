/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DFGPS.P4_3Cross at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S4.Setup

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# DFGPS Proposition 4.3: a geodesic crossing an annulus (task P2-DFA10)

DFGPS (arXiv:1905.00380, `lqg-metric-estimates-final.tex`, "T"), proof of Proposition 4.3,
Step 3, (`eqn-C-good-cross`, T:2716–2719): "Since `P` is a `D_h`-geodesic and `P` crosses the
annulus `(2B_k) ∖ B_k` between times `τ_k` and `σ_k`, `σ_k − τ_k ≥ D_h(∂B_k, ∂(2B_k))`", and
(T:2722) the existence of `t ∈ [τ_k, σ_k]` with `P(t) ∈ ∂B_k`. Proof: the intermediate value
theorem for `t ↦ |P(t) − y|` (the geodesic is Euclidean-continuous, `GM.gm_geodL_continuousOn`).
-/

noncomputable section

open Set Metric

namespace LQGMetric.DFGPS
namespace P43

open Blueprint

variable {D : ContMetric} {z x : ℂ} {P : ℝ → ℂ} {L : ℝ}

/-- a geodesic segment from inside `B̄_ρ(y)` to outside `B_{2ρ}(y)` hits `∂B_ρ(y)` and then
`∂B_{2ρ}(y)` -/
theorem exists_cross_times (hP : IsGeodesicL D P L z x) {τ σ : ℝ} (hτ : 0 ≤ τ) (hτσ : τ ≤ σ)
    (hσ : σ ≤ L) {y : ℂ} {ρ : ℝ} (hρ : 0 ≤ ρ) (hin : ‖P τ - y‖ ≤ ρ) (hout : 2 * ρ ≤ ‖P σ - y‖) :
    ∃ t₁ t₂ : ℝ, τ ≤ t₁ ∧ t₁ ≤ t₂ ∧ t₂ ≤ σ ∧ P t₁ ∈ sphere y ρ ∧ P t₂ ∈ sphere y (2 * ρ) := by
  have hc : ContinuousOn (fun t => ‖P t - y‖) (Icc τ σ) :=
    ((GM.gm_geodL_continuousOn hP).mono (Icc_subset_Icc hτ hσ)).sub continuousOn_const |>.norm
  obtain ⟨t₁, ht₁, h₁⟩ := intermediate_value_Icc hτσ hc ⟨hin, by linarith⟩
  have hc' : ContinuousOn (fun t => ‖P t - y‖) (Icc t₁ σ) := hc.mono (Icc_subset_Icc ht₁.1 le_rfl)
  obtain ⟨t₂, ht₂, h₂⟩ := intermediate_value_Icc ht₁.2 hc'
    ⟨by simp only at h₁; rw [h₁]; linarith, hout⟩
  refine ⟨t₁, t₂, ht₁.1, ht₂.1, ht₂.2, ?_, ?_⟩
  · rw [mem_sphere, dist_eq_norm]; exact h₁
  · rw [mem_sphere, dist_eq_norm]; exact h₂

end P43
end LQGMetric.DFGPS
