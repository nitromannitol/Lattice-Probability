import LatticeProb.Gauss.CircleAverageDyadicSum

/-!
# Finite sums of one-point tails over dyadic grids

For a whole-plane Gaussian free field `h`, `s > 0`, `ξ > 0` and `θ < ξ (Q - 2) log 2`, the sum over
`n` of the sums over the `4ⁿ` lower-left corners `z = (a + i s/2ⁿ) + (b + j s/2ⁿ) i`,
`i, j < 2ⁿ`, of the probabilities of the events `e^{-θ n} < e^{ξ (h_{s/2ⁿ}(z) + Q log (s/2ⁿ))}` is
finite.  This is a reformulation of the summable tail bound
`IsWholePlaneGFF.exists_tsum_dyadic_circle_exp_le`.

* `LatticeProb.Gauss.IsWholePlaneGFF.tsum_dyadic_measure_scaleFactor_ne_top`: the finiteness.
-/

open MeasureTheory Set
open scoped ENNReal

noncomputable section

namespace LatticeProb.Gauss

namespace IsWholePlaneGFF

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {hC : Ω → (ℂ → ℝ) → ℝ}
  {hcirc : Ω → ℝ → ℂ → ℝ}

/-- **Finite total tail over dyadic grids.** For `s > 0`, `ξ > 0` and `θ < ξ (Q - 2) log 2`,
`∑ₙ ∑_{i,j < 2ⁿ} P{e^{-θ n} < e^{ξ (h_{s/2ⁿ}(z_{ij}) + Q log (s/2ⁿ))}} < ∞`, where
`z_{ij} = (a + i s/2ⁿ) + (b + j s/2ⁿ) i`. -/
theorem tsum_dyadic_measure_scaleFactor_ne_top (hG : IsWholePlaneGFF P hC hcirc) {a b s ξ Q θ : ℝ}
    (hs : 0 < s) (hξ : 0 < ξ) (hθ : θ < ξ * (Q - 2) * Real.log 2) :
    ∑' n : ℕ, ∑ i ∈ Finset.range (2 ^ n), ∑ j ∈ Finset.range (2 ^ n),
      P {ω | Real.exp (-(θ * n)) <
        Real.exp (ξ * (hcirc ω (s / 2 ^ n) ⟨a + i * (s / 2 ^ n), b + j * (s / 2 ^ n)⟩ +
          Q * Real.log (s / 2 ^ n)))} ≠ ⊤ := by
  obtain ⟨p, hp, hsum⟩ := hG.exists_tsum_dyadic_circle_exp_le (a := a) (b := b) hs hξ hθ
  refine ne_top_of_le_ne_top hsum (ENNReal.tsum_le_tsum fun n => ?_)
  calc ∑ i ∈ Finset.range (2 ^ n), ∑ j ∈ Finset.range (2 ^ n),
        P {ω | Real.exp (-(θ * n)) <
          Real.exp (ξ * (hcirc ω (s / 2 ^ n) ⟨a + i * (s / 2 ^ n), b + j * (s / 2 ^ n)⟩ +
            Q * Real.log (s / 2 ^ n)))}
      ≤ ∑ _i ∈ Finset.range (2 ^ n), ∑ _j ∈ Finset.range (2 ^ n), p n := by
        refine Finset.sum_le_sum fun i hi => Finset.sum_le_sum fun j hj => ?_
        have := hp n i j (Finset.mem_range.1 hi) (Finset.mem_range.1 hj)
        simpa only [Real.exp_lt_exp, neg_mul, neg_mul] using this
    _ = 4 ^ n * p n := by
        simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
        rw [← mul_assoc, ← Nat.cast_mul, ← pow_two, ← pow_mul, mul_comm n 2, pow_mul]
        norm_num

end IsWholePlaneGFF

end LatticeProb.Gauss
