import LatticeProb.LQG.InternalMetricSquareTail
import LatticeProb.Gauss.CircleAverageDyadicScaleFactor

/-!
# Finite internal diameter of a closed square for the γ-LQG metric from the unit-square crossing tail

The probabilistic assembly of Dubédat-Falconet-Gwynne-Pfeffer-Sun (arXiv:1905.00380, Proposition 3.10) with the
crossing lengths `l n = e^{-(θ - δ) n}` at level `n` and the unit-square thresholds `A n = e^{δ n}`. For a γ-LQG metric
`𝔇` and a whole-plane GFF `h`, let `S = [a, a + s] × [b, b + s]`, `r_n = s / 2ⁿ` and `z_{n,i,j} = (a + i r_n, b + j r_n)`.
The probability that the scaling factor `e^{ξ (h_{r_n}(z_{n,i,j}) + Q log r_n)}` exceeds `e^{-θ n}` is summable over the
`4ⁿ` subsquares of all levels when `ξ > 0` and `θ < ξ (Q - 2) log 2`
(`IsWholePlaneGFF.tsum_dyadic_measure_scaleFactor_ne_top`). Hence the internal diameter of `S` is almost surely finite as
soon as every dyadic subsquare almost surely has half crossings of finite length and the probabilities that the unit
square has no half crossings of length at most `e^{δ n}` for the recentred fields `h(r_n · + z_{n,i,j}) - h_{r_n}(z_{n,i,j})`
are summable over the subsquares of all levels, for some `δ < θ`.

## Main statements

* `LatticeProb.LQG.IsLQGMetric.ae_exists_internalMetric_closedSquare_le_of_unitTail`
-/

open MeasureTheory Filter Set LatticeProb.Gauss
open scoped ENNReal

namespace LatticeProb.LQG

variable {γ ξ : ℝ} {𝔇 : ((ℂ → ℝ) → ℝ) → ℂ → ℂ → ℝ} {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
  {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}

/-- `∑ₙ e^{-c n} < ∞` in `ℝ≥0∞` for `c > 0`. -/
theorem tsum_ofReal_exp_neg_mul_ne_top {c : ℝ} (hc : 0 < c) :
    ∑' n : ℕ, ENNReal.ofReal (Real.exp (-(c * n))) ≠ ⊤ := by
  have h : ∀ n : ℕ, ENNReal.ofReal (Real.exp (-(c * n))) = ENNReal.ofReal (Real.exp (-c)) ^ n := by
    intro n
    rw [← ENNReal.ofReal_pow (Real.exp_pos _).le, ← Real.exp_nat_mul,
      show -(c * (n : ℝ)) = n * -c by ring]
  simp_rw [h]
  exact (tsum_geometric_lt_top.2
    (ENNReal.ofReal_lt_one.2 (by rw [← Real.exp_zero]; exact Real.exp_lt_exp.2 (by linarith)))).ne

/-- **Almost sure finiteness of the internal diameter of a closed square for the γ-LQG metric, from the tail of the
unit-square half crossings** (Dubédat-Falconet-Gwynne-Pfeffer-Sun, Proposition 3.10, assembly). Let `𝔇` be a γ-LQG
metric, `h` a whole-plane GFF, `S = [a, a + s] × [b, b + s]`, `r_n = s / 2ⁿ`, `z_{n,i,j} = (a + i r_n, b + j r_n)`, `ξ > 0`
and `δ < θ < ξ (Q - 2) log 2`. Suppose that almost surely every closed dyadic subsquare of `S` has half crossings of
finite `D_h`-length, and that
`∑ₙ ∑_{i,j < 2ⁿ} P[the unit square has no half crossings of length at most e^{δ n} for the metric of
h(r_n · + z_{n,i,j}) - h_{r_n}(z_{n,i,j})] < ∞`.
Then almost surely there is a real `A` with `D_h(z, w; S) ≤ A` for all `z, w ∈ S`. -/
theorem IsLQGMetric.ae_exists_internalMetric_closedSquare_le_of_unitTail (h𝔇 : IsLQGMetric γ ξ 𝔇)
    (hG : IsWholePlaneGFF P hC hcirc) {a b s : ℝ} (hs : 0 < s) (hξ : 0 < ξ) {θ δ : ℝ}
    (hθ : θ < ξ * (lqgQ γ - 2) * Real.log 2) (hδ : δ < θ)
    (hfin : ∀ n i j : ℕ, i < 2 ^ n → j < 2 ^ n → ∀ᵐ ω ∂P, ∃ L : ℝ≥0∞, L ≠ ⊤ ∧
      HasShortHalfCrossings (𝔇 (hC ω)) (a + i * (s / 2 ^ n)) (a + (i + 1) * (s / 2 ^ n)) (b + j * (s / 2 ^ n))
        (b + (j + 1) * (s / 2 ^ n)) L)
    (hunit : ∑' n : ℕ, ∑ i ∈ Finset.range (2 ^ n), ∑ j ∈ Finset.range (2 ^ n),
      P {ω | ¬ HasShortHalfCrossings
        (𝔇 (recentredPairing hC hcirc (s / 2 ^ n) ⟨a + i * (s / 2 ^ n), b + j * (s / 2 ^ n)⟩ ω)) 0 1 0 1
          (ENNReal.ofReal (Real.exp (δ * n)))} ≠ ⊤) :
    ∀ᵐ ω ∂P, ∃ A : ℝ, ∀ z ∈ Icc a (a + s) ×ℂ Icc b (b + s), ∀ w ∈ Icc a (a + s) ×ℂ Icc b (b + s),
      internalMetric (𝔇 (hC ω)) (Icc a (a + s) ×ℂ Icc b (b + s)) z w ≤ ENNReal.ofReal A := by
  refine h𝔇.ae_exists_internalMetric_closedSquare_le hG hs hfin
    (fun n => ENNReal.ofReal (Real.exp (δ * n))) (fun n => ENNReal.ofReal (Real.exp (-((θ - δ) * n))))
    (tsum_ofReal_exp_neg_mul_ne_top (by linarith)) hunit ?_
  refine ne_top_of_le_ne_top
    (hG.tsum_dyadic_measure_scaleFactor_ne_top (a := a) (b := b) (Q := lqgQ γ) hs hξ hθ)
    (ENNReal.tsum_le_tsum fun n => Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => measure_mono ?_)
  intro ω hω
  simp only [Set.mem_ofPred_eq] at hω ⊢
  rw [← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add,
    ENNReal.ofReal_lt_ofReal_iff (Real.exp_pos _), Real.exp_lt_exp] at hω
  rw [Real.exp_lt_exp]
  linarith

end LatticeProb.LQG
