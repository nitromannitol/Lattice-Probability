import LatticeProb.Prob.KingmanLinear.FromInducedToAllTimes
import LatticeProb.Prob.KingmanLinear.LimitInvariant

/-!
# Main theorem (statement byte-identical to the Exploding design files)

Assembles the a.e. convergence of `g n x / n` (stage 4), the a.e. subinvariance of its limsup
(stage 5), and the ergodic-invariance principle restated in
`LatticeProb.Prob.KingmanLinear.Restated` into `ae_tendsto_div_of_linear`, Kingman's subadditive
ergodic theorem under a linear bound and a Lipschitz-in-time control, without assuming `g 1`
integrable.
-/

open MeasureTheory Filter Topology Set

namespace LatticeProb

/-- **Kingman's subadditive ergodic theorem under a linear bound.** For `g` nonnegative, measurable
and subadditive along a measure-preserving, ergodic `T`, with an a.e. linear bound and a
Lipschitz-in-time control on dyadic windows, the ratios `g n x / n` converge a.e. to a single
constant `L`, without assuming `g 1` integrable. -/
theorem ae_tendsto_div_of_linear {Ω} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (T : Ω → Ω) (hT : MeasurePreserving T μ μ) (herg : Ergodic T μ)
    (g : ℕ → Ω → ℝ) (hsub : ∀ m n x, g (m+n) x ≤ g m x + g n (T^[m] x))
    (hg : ∀ n x, 0 ≤ g n x) (hgm : ∀ n, Measurable (g n))
    (hlin : ∃ C, ∀ᵐ x ∂μ, ∃ K, ∀ n, g n x ≤ C*n + K)
    (hlip : ∃ C, ∀ᵐ x ∂μ, ∀ ε > 0, ∀ᶠ n in atTop, ∀ m, n ≤ m → m ≤ 2*n →
              |g m x - g n x| ≤ C*((m:ℝ)-n) + ε*n) :
    ∃ L : ℝ, ∀ᵐ x ∂μ, Tendsto (fun n => g n x / n) atTop (𝓝 L) := by
  obtain ⟨C, hC⟩ := hlin
  obtain ⟨C', hC'⟩ := hlip
  have hconv := ae_exists_tendsto_div hT hsub hg hgm hC hC'
  obtain ⟨L, hL⟩ := exists_eq_const_ae_of_ergodic_le_comp μ T herg _ (measurable_limsup_div hgm)
    (limsup_div_le_comp_ae hT hsub hconv)
  refine ⟨L, ?_⟩
  filter_upwards [hconv, hL] with x ⟨l, hl⟩ hLx
  have h1 : limsup (fun n : ℕ => g n x / (n : ℝ)) atTop = l := hl.limsup_eq
  have h2 : l = L := by rw [← h1]; exact hLx
  exact h2 ▸ hl

end LatticeProb
