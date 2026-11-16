import LatticeProb.Analysis.Schauder.ApproxIdentity
import LatticeProb.Analysis.Schauder.GaussTail
import LatticeProb.Analysis.Schauder.KernelIntegral

/-!
# The heat kernel is an approximate identity

The heat kernel `p_t` is nonnegative, integrable and of total mass one at every positive time, and
its mass outside every ball tends to zero as `t → 0⁺`. By the abstract approximate-identity
theorem, `∫ p_t(y) g(x - y) dy → g(x)` as `t → 0⁺` for every bounded continuous `g`.
-/

namespace LatticeProb.Analysis.Schauder

open MeasureTheory Filter Topology

noncomputable section

variable {d : ℕ}

/-- The heat kernel is an approximate identity for bounded continuous functions:
`∫ p_t(y) g(x − y) dy → g(x)` as `t → 0⁺`. -/
theorem tendsto_integral_heatKernel_mul {g : Euc d → ℝ} (hgc : Continuous g) {A : ℝ}
    (hgA : ∀ y, |g y| ≤ A) (x : Euc d) :
    Tendsto (fun t => ∫ y, heatKernel d t y * g (x - y)) (𝓝[>] (0 : ℝ)) (𝓝 (g x)) :=
  tendsto_integral_mul_comp_sub_of_tails (K := heatKernel d)
    (fun _ ht y => heatKernel_nonneg ht y) (fun _ ht => integrable_heatKernel ht)
    (fun _ ht => integral_heatKernel ht) (fun _ hδ => tendsto_setIntegral_heatKernel_tail hδ)
    hgc hgA x

end

end LatticeProb.Analysis.Schauder
