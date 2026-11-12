/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.CONF.S3T39I2 at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.CONF.S3T39G5
import LatticeProb.Bonanno.LQGMetric.Papers.CONF.S3T39G6
import LatticeProb.Bonanno.LQGMetric.Papers.CONF.S3T39I1

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# CONF Theorem 3.9 from almost sure iteration inputs (D119 S5)

Gwynne–Miller, *Confluence of geodesics in LQG* (arXiv:1905.00381), `confluence-final.tex`
C:1506–1744. Copy-and-adapt of S3T39G7 (D119 S5):

* `T39IterData'`: `T39IterData` with the recursion `s_{k+1} = σ^{ε_k}_{s_k,𝕣}` (C:1545), the
  count (3.21′) (C:1590) and the kill step (C:1600–1617) required almost surely (the recursion is
  impossible surely where `σ^{ε}_{s,𝕣} = ∞`, a null event);
* `CONFThm3_9Iter'`: `CONFThm3_9Iter` with `T39IterData'`;
* **`confThm3_9At_of_iterAE`** / `confThm3_9At_of_iterAE'`: `CONFThm3_9Iter' → CONFThm3_9At`
  (via `t39i_arcs`, S3T39I1, and `t39g_points_of_arcs`);
* `t39i_iterData_of_sure`, `t39i_iter_of_sure`: the old sure inputs imply the new ones.
-/

noncomputable section

open MeasureTheory Set Metric Filter
open LQGMetric.Blueprint LQGMetric.GM
open scoped ENNReal

namespace LQGMetric
namespace CONF

open Classical in
/-- the inputs of `t39i_arcs` for one arc family `I₀`: `T39IterData` with the recursion, (3.21′)
and the kill step almost sure (D119 S5) -/
def T39IterData' (γ : ℝ) (D : DistC → ContMetric) (c : ℝ → ℝ) (p : CONFParams)
    (χ α C₀ a : ℝ) (N₀ : ℕ) {Ω : Type} [m0 : MeasurableSpace Ω] (P : Measure Ω) (h : Ω → DistC)
    (z₀ : ℂ) (R : ℝ) {ι : Type} [Fintype ι] (I₀ : ι → Ω → Set ℂ) (τ : Ω → ℝ) : Prop :=
  ∃ (s : ℕ → Ω → ℝ) (n : ℕ → Ω → ℕ) (𝓕 : ℕ → MeasurableSpace Ω) (Act G : ℕ → ι → Set Ω),
    (∀ i ω, I₀ i ω ⊆ frontier (filledBall (D (h ω)) z₀ (τ ω))) ∧
    (∀ ω, s 0 ω = τ ω) ∧
    (∀ k, ∀ᵐ ω ∂P, ENNReal.ofReal (s (k + 1) ω) = confSigma (xiGamma γ) c D P h p z₀ R
        ((2 : ℝ)⁻¹ ^ t39gExp (n k ω)) (s k ω) ω) ∧
    (∀ k ω, n k ω = (Finset.univ.filter fun i =>
        (t39gArc (D (h ω)) z₀ (s k ω) (I₀ i ω)).Nonempty).card) ∧
    Monotone 𝓕 ∧ (∀ k, 𝓕 k ≤ m0) ∧ (∀ k, Measurable[𝓕 k] (n k)) ∧
    (∀ k i, MeasurableSet[𝓕 k] (Act k i)) ∧ (∀ k i, MeasurableSet[𝓕 (k + 1)] (G k i)) ∧
    (∀ k i, ∀ᵐ ω ∂P, ω ∈ Act k i → 1 - C₀ * ((2 : ℝ)⁻¹ ^ t39gExp (n k ω)) ^ α ≤
        P[(G k i).indicator (fun _ => (1 : ℝ)) | 𝓕 k] ω) ∧
    (∀ k i ω, ω ∈ Act k i → (t39gArc (D (h ω)) z₀ (s k ω) (I₀ i ω)).Nonempty) ∧
    (∀ᵐ ω ∂P, ω ∈ confReg (xiGamma γ) c D P h p χ z₀ R a → ∀ k, s k ω < tauR D h z₀ (3 * R) ω →
      N₀ ≤ n k ω → 4 * (Finset.univ.filter fun i =>
        (t39gArc (D (h ω)) z₀ (s k ω) (I₀ i ω)).Nonempty ∧ ω ∉ Act k i).card ≤ n k ω) ∧
    (∀ᵐ ω ∂P, ω ∈ confReg (xiGamma γ) c D P h p χ z₀ R a → ∀ k, s k ω < tauR D h z₀ (3 * R) ω →
      N₀ ≤ n k ω → ∀ i, ω ∈ Act k i → ω ∈ G k i →
        t39gArc (D (h ω)) z₀ (s (k + 1) ω) (I₀ i ω) = ∅)

end CONF
end LQGMetric
