import Mathlib
import LatticeProb.LQG.InternalMetricStripTailPoly
import LatticeProb.LQG.InternalMetricStripTailUniversal
import LatticeProb.LQG.ExpShellInternalDiamSummable

/-!
# The uniform tail of the unit-square crossing distance of a γ-LQG metric

For a γ-LQG metric `𝔇` with `0 < γ < 2` and Weyl exponent `ξ > 0`, the four strip distances around the halves of the unit
square have exponential tails in one realization of the whole-plane GFF
(`IsLQGMetric.exists_measure_horizontalCrossingDist_ge_exp_le`, `..verticalCrossingDist..`), and the probability that
`[0, 1]²` has no hard half-crossings of `D_h`-length at most `e^{δ n}` is at most four times the strip tails in every
realization (`IsLQGMetric.uniform_tail_of_realization`). Choosing `δ = ξ (Q - 2) log 2 / 2 > 0` and the decay rate `m`
with `m δ = log 4 + 1`, the bound `p n = 4 K e^{-m δ n}` satisfies `4^n p n ≤ 4 K e^{-n}`, hence `∑ 4^n p n < ∞`.

## Main statement

* `IsLQGMetric.exists_uniform_crossing_tail`: there are `δ < ξ (Q - 2) log 2` and `p : ℕ → ℝ≥0∞` with
  `∑ 4^n p n ≠ ∞` such that, for every realization of the whole-plane GFF, `P[[0,1]² has no hard half-crossings of
  D_h-length ≤ e^{δ n}] ≤ p n` for all `n`. The hypothesis is the existence of one realization of the whole-plane GFF
  whose pairings and circle averages are almost surely those of a distribution-valued whole-plane GFF.
-/

namespace LatticeProb.LQG

open MeasureTheory Set Metric LatticeProb.Gauss LQGMetric LQGMetric.Blueprint LQGMetric.DFGPS LQGMetric.DFGPS.P31
open scoped ENNReal

/-- **The uniform crossing tail of a γ-LQG metric.** Let `𝔇` be a γ-LQG metric with `0 < γ < 2` and `ξ > 0`, and assume
that some realization `(Ω, P, hC, hcirc)` of the whole-plane GFF is almost surely given by a distribution-valued
whole-plane GFF `H` (`hC ω ψ = H ω ψ` and `hcirc ω r z = circleAvg (H ω) r z` almost surely). Then there are
`δ < ξ (Q - 2) log 2` and `p : ℕ → ℝ≥0∞` with `∑ 4^n p n ≠ ∞` such that, in every realization of the whole-plane GFF on
a probability space in `Type`, the probability that `[0, 1]²` has no hard half-crossings of `D_h`-length at most
`e^{δ n}` is at most `p n`. -/
theorem IsLQGMetric.exists_uniform_crossing_tail {γ ξ : ℝ} {𝔇 : ((ℂ → ℝ) → ℝ) → ℂ → ℂ → ℝ}
    (h𝔇 : IsLQGMetric γ ξ 𝔇) (hξ : 0 < ξ) (hγ : 0 < γ) (hγ2 : γ < 2)
    (hex : ∃ (Ω : Type) (_ : MeasurableSpace Ω) (P : Measure Ω) (_ : IsProbabilityMeasure P)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), LatticeProb.Gauss.IsWholePlaneGFF P hC hcirc ∧
        ∃ H : Ω → DistC, LQGMetric.IsWholePlaneGFF H P ∧
          (∀ ψ : TestC, (fun ω => H ω ψ) =ᵐ[P] fun ω => hC ω ψ) ∧
          ∀ r : ℝ, 0 < r → ∀ z : ℂ, ∀ᵐ ω ∂P, hcirc ω r z = circleAvg (H ω) r z) :
    ∃ δ : ℝ, δ < ξ * (lqgQ γ - 2) * Real.log 2 ∧ ∃ p : ℕ → ℝ≥0∞, ∑' n, 4 ^ n * p n ≠ ⊤ ∧
      ∀ (Ω₁ : Type) [MeasurableSpace Ω₁] (P₁ : Measure Ω₁) (hC₁ : Ω₁ → (ℂ → ℝ) → ℝ)
        (hcirc₁ : Ω₁ → ℝ → ℂ → ℝ), LatticeProb.Gauss.IsWholePlaneGFF P₁ hC₁ hcirc₁ → ∀ n : ℕ,
          P₁ {ω | ¬ HasShortHalfCrossings (𝔇 (hC₁ ω)) 0 1 0 1 (ENNReal.ofReal (Real.exp (δ * n)))} ≤ p n := by
  obtain ⟨Ω, _, P, hPprob, hC, hcirc, hG, H, hH, hHC, hHcirc⟩ := hex
  have hδ₀ : 0 < ξ * (lqgQ γ - 2) * Real.log 2 :=
    mul_pos (mul_pos hξ (sub_pos.2 (two_lt_lqgQ hγ hγ2))) (Real.log_pos one_lt_two)
  set δ : ℝ := ξ * (lqgQ γ - 2) * Real.log 2 / 2 with hδ
  have hδpos : 0 < δ := by positivity
  have hlog4 : 0 < Real.log 4 := Real.log_pos (by norm_num)
  set m : ℝ := (Real.log 4 + 1) / δ with hm_def
  have hm : 0 < m := by positivity
  have hmδ : m * δ = Real.log 4 + 1 := by rw [hm_def]; field_simp
  obtain ⟨K₁, hK₁⟩ := h𝔇.exists_measure_horizontalCrossingDist_ge_exp_le hξ hγ 0 δ m hm hG hH hHC hHcirc
  obtain ⟨K₂, hK₂⟩ := h𝔇.exists_measure_horizontalCrossingDist_ge_exp_le hξ hγ (1 / 2) δ m hm hG hH hHC hHcirc
  obtain ⟨K₃, hK₃⟩ := h𝔇.exists_measure_verticalCrossingDist_ge_exp_le hξ hγ 0 δ m hm hG hH hHC hHcirc
  obtain ⟨K₄, hK₄⟩ := h𝔇.exists_measure_verticalCrossingDist_ge_exp_le hξ hγ (1 / 2) δ m hm hG hH hHC hHcirc
  set K : ℝ := |K₁| + |K₂| + |K₃| + |K₄| with hK_def
  have hK0 : 0 ≤ K := by positivity
  have hKa := abs_nonneg K₁
  have hKb := abs_nonneg K₂
  have hKc := abs_nonneg K₃
  have hKd := abs_nonneg K₄
  have hK1 : K₁ ≤ K := (le_abs_self K₁).trans (by rw [hK_def]; linarith)
  have hK2 : K₂ ≤ K := (le_abs_self K₂).trans (by rw [hK_def]; linarith)
  have hK3 : K₃ ≤ K := (le_abs_self K₃).trans (by rw [hK_def]; linarith)
  have hK4 : K₄ ≤ K := (le_abs_self K₄).trans (by rw [hK_def]; linarith)
  have hKle : ∀ K' : ℝ, K' ≤ K → ∀ n : ℕ, ENNReal.ofReal (K' * Real.exp (-(m * δ * n))) ≤
      ENNReal.ofReal (K * Real.exp (-(m * δ * n))) := fun K' h n =>
    ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right h (Real.exp_pos _).le)
  set q : ℕ → ℝ≥0∞ := fun n => ENNReal.ofReal (K * Real.exp (-(m * δ * n))) with hq_def
  have hh : ∀ n : ℕ, ∀ y₀ ∈ ({0, 1 / 2} : Set ℝ),
      P {ω | ENNReal.ofReal (Real.exp (δ * n)) ≤ horizontalCrossingDist (𝔇 (hC ω)) y₀} ≤ q n := by
    intro n y₀ hy
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
    rcases hy with rfl | rfl
    · exact (hK₁ n).trans (hKle K₁ hK1 n)
    · exact (hK₂ n).trans (hKle K₂ hK2 n)
  have hv : ∀ n : ℕ, ∀ x₀ ∈ ({0, 1 / 2} : Set ℝ),
      P {ω | ENNReal.ofReal (Real.exp (δ * n)) ≤ verticalCrossingDist (𝔇 (hC ω)) x₀} ≤ q n := by
    intro n x₀ hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl
    · exact (hK₃ n).trans (hKle K₃ hK3 n)
    · exact (hK₄ n).trans (hKle K₄ hK4 n)
  refine ⟨δ, by rw [hδ]; linarith, fun n => 4 * q n, ?_, ?_⟩
  · -- `4 ^ n * (4 * q n) = ofReal (4 * K * exp (-1) ^ n)`
    have key : ∀ n : ℕ, (4 : ℝ) ^ n * Real.exp (-(m * δ * n)) = Real.exp (-1) ^ n := by
      intro n
      have h4 : (4 : ℝ) ^ n = Real.exp (n * Real.log 4) := by
        rw [Real.exp_nat_mul, Real.exp_log (by norm_num)]
      rw [h4, ← Real.exp_nat_mul, ← Real.exp_add]
      congr 1
      rw [hmδ]
      ring
    have hterm : ∀ n : ℕ, (4 : ℝ≥0∞) ^ n * (4 * q n) = ENNReal.ofReal (4 * K * Real.exp (-1) ^ n) := by
      intro n
      have h : (4 : ℝ) * K * Real.exp (-1) ^ n = 4 ^ n * (4 * (K * Real.exp (-(m * δ * n)))) := by
        rw [← key n]; ring
      rw [h, ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_pow (by norm_num)]
      simp [hq_def]
    have hexp1 : Real.exp (-1) < 1 := by
      have := Real.exp_lt_exp.2 (show (-1 : ℝ) < 0 by norm_num)
      rwa [Real.exp_zero] at this
    have hsum : Summable fun n : ℕ => 4 * K * Real.exp (-1) ^ n :=
      (summable_geometric_of_lt_one (Real.exp_pos _).le hexp1).mul_left (4 * K)
    simp only [hterm]
    rw [← ENNReal.ofReal_tsum_of_nonneg (fun n => by positivity) hsum]
    exact ENNReal.ofReal_ne_top
  · intro Ω₁ _ P₁ hC₁ hcirc₁ hG₁ n
    exact h𝔇.uniform_tail_of_realization hG δ q hh hv Ω₁ P₁ hC₁ hcirc₁ hG₁ n

end LatticeProb.LQG
