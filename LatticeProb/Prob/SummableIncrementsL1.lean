import LatticeProb.Prob.SummableIncrements

/-!
# `L¹` convergence from summable mean increments

If the consecutive increments of a sequence of real random variables `Y k` have summable `L¹` norms and `Y k → L`
almost everywhere, then `Y k → L` in `L¹`. Indeed `|Y k - L| ≤ ∑_{j ≥ 0} |Y (j + k + 1) - Y (j + k)|` pointwise
(triangle inequality and passage to the limit), so by Tonelli `E|Y k - L|` is at most the tail `∑_{j ≥ k} b j` of a
convergent series.

## Main statements

* `LatticeProb.SummableIncrements.ofReal_abs_sub_le_tsum`: the deterministic tail bound.
* `LatticeProb.SummableIncrements.integral_abs_sub_le_tsum`: `E|Y k - L| ≤ ∑' j, b (j + k)`.
* `LatticeProb.SummableIncrements.tendsto_integral_abs_sub_of_integral_abs_sub_le`: `E|Y k - L| → 0`.
-/

open MeasureTheory Filter Topology
open scoped ENNReal

namespace LatticeProb.SummableIncrements

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}

/-- Deterministic tail bound: if `y k → l`, then `|y k - l| ≤ ∑_{j ≥ 0} |y (j + k + 1) - y (j + k)|` in `ℝ≥0∞`. -/
theorem ofReal_abs_sub_le_tsum {y : ℕ → ℝ} {l : ℝ} (hy : Tendsto y atTop (𝓝 l)) (k : ℕ) :
    ENNReal.ofReal |y k - l| ≤ ∑' j, ENNReal.ofReal |y (j + k + 1) - y (j + k)| := by
  have hfin : ∀ n, ENNReal.ofReal |y k - y (n + k)| ≤
      ∑ j ∈ Finset.range n, ENNReal.ofReal |y (j + k + 1) - y (j + k)| := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      rw [Finset.sum_range_succ]
      have hnk : n + 1 + k = n + k + 1 := by omega
      calc ENNReal.ofReal |y k - y (n + 1 + k)|
          ≤ ENNReal.ofReal (|y k - y (n + k)| + |y (n + k + 1) - y (n + k)|) := by
            apply ENNReal.ofReal_le_ofReal
            rw [hnk]
            have h : y k - y (n + k + 1) = (y k - y (n + k)) - (y (n + k + 1) - y (n + k)) := by ring
            rw [h]
            exact abs_sub _ _
        _ = ENNReal.ofReal |y k - y (n + k)| + ENNReal.ofReal |y (n + k + 1) - y (n + k)| :=
            ENNReal.ofReal_add (abs_nonneg _) (abs_nonneg _)
        _ ≤ _ := add_le_add_left ih _
  have hlim : Tendsto (fun n => ENNReal.ofReal |y k - y (n + k)|) atTop (𝓝 (ENNReal.ofReal |y k - l|)) :=
    (ENNReal.continuous_ofReal.tendsto _).comp
      ((continuous_abs.tendsto _).comp (tendsto_const_nhds.sub ((tendsto_add_atTop_iff_nat k).2 hy)))
  exact le_of_tendsto' hlim fun n => (hfin n).trans (ENNReal.sum_le_tsum _)

/-- `L¹` tail bound: if the increments of real random variables `Y k` are integrable with
`E|Y (k + 1) - Y k| ≤ b k`, `b` summable, and `Y k → L` almost everywhere, then `E|Y k - L| ≤ ∑_{j ≥ 0} b (j + k)`. -/
theorem integral_abs_sub_le_tsum {Y : ℕ → Ω → ℝ} {L : Ω → ℝ} (hY : ∀ k, AEStronglyMeasurable (Y k) μ)
    (hint : ∀ k, Integrable (fun ω => Y (k + 1) ω - Y k ω) μ) {b : ℕ → ℝ}
    (hb : ∀ k, ∫ ω, |Y (k + 1) ω - Y k ω| ∂μ ≤ b k) (hsum : Summable b)
    (hL : ∀ᵐ ω ∂μ, Tendsto (fun k => Y k ω) atTop (𝓝 (L ω))) (k : ℕ) :
    ∫ ω, |Y k ω - L ω| ∂μ ≤ ∑' j, b (j + k) := by
  have hLm : AEStronglyMeasurable L μ := aestronglyMeasurable_of_tendsto_ae atTop hY hL
  have hb0 : ∀ j, 0 ≤ b j := fun j => (integral_nonneg fun _ => abs_nonneg _).trans (hb j)
  have hlin : ∫⁻ ω, ENNReal.ofReal |Y k ω - L ω| ∂μ ≤ ENNReal.ofReal (∑' j, b (j + k)) := by
    calc ∫⁻ ω, ENNReal.ofReal |Y k ω - L ω| ∂μ
        ≤ ∫⁻ ω, ∑' j, ENNReal.ofReal |Y (j + k + 1) ω - Y (j + k) ω| ∂μ := by
          refine lintegral_mono_ae ?_
          filter_upwards [hL] with ω hω
          exact ofReal_abs_sub_le_tsum hω k
      _ = ∑' j, ∫⁻ ω, ENNReal.ofReal |Y (j + k + 1) ω - Y (j + k) ω| ∂μ :=
          lintegral_tsum fun j => (hint (j + k)).aestronglyMeasurable.aemeasurable.abs.ennreal_ofReal
      _ = ∑' j, ENNReal.ofReal (∫ ω, |Y (j + k + 1) ω - Y (j + k) ω| ∂μ) := by
          congr 1
          funext j
          exact (ofReal_integral_eq_lintegral_ofReal (hint (j + k)).abs
            (ae_of_all _ fun ω => abs_nonneg _)).symm
      _ ≤ ∑' j, ENNReal.ofReal (b (j + k)) :=
          ENNReal.tsum_le_tsum fun j => ENNReal.ofReal_le_ofReal (hb (j + k))
      _ = ENNReal.ofReal (∑' j, b (j + k)) :=
          (ENNReal.ofReal_tsum_of_nonneg (fun j => hb0 (j + k)) ((summable_nat_add_iff k).2 hsum)).symm
  have hm : AEStronglyMeasurable (fun ω => |Y k ω - L ω|) μ := ((hY k).sub hLm).norm
  rw [integral_eq_lintegral_of_nonneg_ae (ae_of_all _ fun ω => abs_nonneg (Y k ω - L ω)) hm]
  exact ENNReal.toReal_le_of_le_ofReal (tsum_nonneg fun j => hb0 (j + k)) hlin

/-- **`L¹` convergence from summable mean increments.** If the increments of real random variables `Y k` are
integrable with `E|Y (k + 1) - Y k| ≤ b k`, `b` summable, and `Y k → L` almost everywhere, then `E|Y k - L| → 0`. -/
theorem tendsto_integral_abs_sub_of_integral_abs_sub_le {Y : ℕ → Ω → ℝ} {L : Ω → ℝ}
    (hY : ∀ k, AEStronglyMeasurable (Y k) μ)
    (hint : ∀ k, Integrable (fun ω => Y (k + 1) ω - Y k ω) μ) {b : ℕ → ℝ}
    (hb : ∀ k, ∫ ω, |Y (k + 1) ω - Y k ω| ∂μ ≤ b k) (hsum : Summable b)
    (hL : ∀ᵐ ω ∂μ, Tendsto (fun k => Y k ω) atTop (𝓝 (L ω))) :
    Tendsto (fun k => ∫ ω, |Y k ω - L ω| ∂μ) atTop (𝓝 0) :=
  tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds (tendsto_sum_nat_add b)
    (fun _ => integral_nonneg fun _ => abs_nonneg _)
    (integral_abs_sub_le_tsum hY hint hb hsum hL)

end LatticeProb.SummableIncrements
