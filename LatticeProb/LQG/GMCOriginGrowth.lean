import LatticeProb.LQG.GMCMaximalMoment
import LatticeProb.LQG.GMCDilationField

/-!
# Subexponential growth of the rescaled unit-ball masses at the origin

Let `h` be a whole-plane Gaussian free field, `0 < γ < 2`, and for `j ∈ ℕ` let
`Z_j = sup_n μ^{(j)}_n(B(0,1))` be the maximal mass of the unit ball for the circle-average approximations
`μ^{(j)}_n = ε_n^{γ²/2} e^{γ h^{(j)}_{ε_n}} dz` of the dilated recentred field `h^{(j)} = h(2^{-j}·)(2^{-j}·) - h_{2^{-j}}(0)`,
which is again a whole-plane Gaussian free field.

## Main results

* `IsWholePlaneGFF.ae_eventually_maximal_dilated_le`: for every `ε > 0`, almost surely `Z_j ≤ e^{ε j}` for all large
  `j` (Borel-Cantelli, the tail bound being summable and uniform over the fields `h^{(j)}`).
* `IsWholePlaneGFF.ae_eventually_exp_circle_mul_maximal_dilated_le`: almost surely, for every `η > 0`,
  `e^{γ h_{2^{-j}}(0)} Z_j ≤ e^{η j}` for all large `j`.
-/

open MeasureTheory ProbabilityTheory Real Function Filter Topology Metric
open scoped ENNReal NNReal

namespace LatticeProb.Gauss.IsWholePlaneGFF

open LatticeProb.LQG

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}

/-- **Borel-Cantelli for the maximal masses of the dilated recentred fields.** For every `ε > 0`, almost surely
the maximal unit-ball mass `Z_j` of the dilated recentred field at scale `2^{-j}` is at most `e^{ε j}` for all
large `j`. -/
theorem ae_eventually_maximal_dilated_le (hh : IsWholePlaneGFF P hC hcirc) {γ : ℝ} (hγ0 : 0 < γ) (hγ2 : γ < 2)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᵐ ω ∂P, ∀ᶠ j : ℕ in atTop,
      (⨆ n : ℕ, lqgApprox γ (dilateRecentre (dyadicScale j) (hcirc ω)) (dyadicScale n) (ball 0 1)) ≤
        ENNReal.ofReal (rexp (ε * j)) := by
  obtain ⟨B, hB⟩ := exists_maximal_ball_mass_tail hγ0 hγ2
  choose hC' hG' using fun j : ℕ => isWholePlaneGFF_dilateRecentre hh (c := dyadicScale j)
    (pow_pos (by norm_num) j)
  set s : ℕ → Set Ω := fun j => {ω | ENNReal.ofReal (rexp (ε * j)) <
    ⨆ n : ℕ, lqgApprox γ (dilateRecentre (dyadicScale j) (hcirc ω)) (dyadicScale n) (ball 0 1)} with hs
  set q : ℝ := rexp (-(ε / 2)) with hq
  have hq1 : q < 1 := (Real.exp_lt_exp.mpr (by linarith : -(ε / 2) < 0)).trans_eq Real.exp_zero
  have hq0 : 0 ≤ q := (Real.exp_pos _).le
  have hbound : ∀ j : ℕ, P (s j) ≤ ENNReal.ofReal (|B| * q ^ j) := fun j => by
    refine (hB (hG' j) (Real.exp_pos (ε * j))).trans (ENNReal.ofReal_le_ofReal ?_)
    have hsq : Real.sqrt (rexp (ε * j)) = rexp (ε * j / 2) := by
      rw [Real.sqrt_eq_iff_mul_self_eq (Real.exp_pos _).le (Real.exp_pos _).le, ← Real.exp_add]
      congr 1
      ring
    rw [hsq, hq, ← Real.exp_nat_mul, div_eq_mul_inv, ← Real.exp_neg]
    have : rexp (-(ε * j / 2)) = rexp (j * -(ε / 2)) := by
      congr 1
      ring
    rw [this]
    exact mul_le_mul_of_nonneg_right (le_abs_self B) (Real.exp_pos _).le
  have hsum : Summable fun j : ℕ => |B| * q ^ j := (summable_geometric_of_lt_one hq0 hq1).mul_left _
  have hfin : ∑' j, P (s j) ≠ ∞ := by
    refine ne_top_of_le_ne_top ?_ (ENNReal.tsum_le_tsum hbound)
    rw [← ENNReal.ofReal_tsum_of_nonneg (fun j => by positivity) hsum]
    exact ENNReal.ofReal_ne_top
  filter_upwards [ae_eventually_notMem hfin] with ω hω
  filter_upwards [hω] with j hj
  exact not_lt.mp hj

/-- **Subexponential growth of the product `e^{γ h_{2^{-j}}(0)} Z_j`.** Almost surely, for every `η > 0` and all
large `j`, `e^{γ h_{2^{-j}}(0)} Z_j ≤ e^{η j}`, where `Z_j` is the maximal unit-ball mass of the dilated recentred
field at scale `2^{-j}`. -/
theorem ae_eventually_exp_circle_mul_maximal_dilated_le (hh : IsWholePlaneGFF P hC hcirc) {γ : ℝ}
    (hγ0 : 0 < γ) (hγ2 : γ < 2) :
    ∀ᵐ ω ∂P, ∀ η : ℝ, 0 < η → ∀ᶠ j : ℕ in atTop,
      ENNReal.ofReal (rexp (γ * hcirc ω (dyadicScale j) 0)) *
          (⨆ n : ℕ, lqgApprox γ (dilateRecentre (dyadicScale j) (hcirc ω)) (dyadicScale n) (ball 0 1)) ≤
        ENNReal.ofReal (rexp (η * j)) := by
  have hall : ∀ᵐ ω ∂P, ∀ m : ℕ, ∀ᶠ j : ℕ in atTop,
      (⨆ n : ℕ, lqgApprox γ (dilateRecentre (dyadicScale j) (hcirc ω)) (dyadicScale n) (ball 0 1)) ≤
        ENNReal.ofReal (rexp (1 / ((m : ℝ) + 1) * j)) :=
    ae_all_iff.mpr fun m => hh.ae_eventually_maximal_dilated_le hγ0 hγ2 (by positivity)
  filter_upwards [hall, hh.ae_forall_eventually_exp_circle_dyadic_le γ] with ω h1 h2 η hη
  obtain ⟨m, hm⟩ := exists_nat_one_div_lt (half_pos hη)
  filter_upwards [h1 m, h2 (η / 2) (half_pos hη)] with j hj1 hj2
  have hj3 : rexp (1 / ((m : ℝ) + 1) * j) ≤ rexp (η / 2 * j) :=
    Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right hm.le (Nat.cast_nonneg j))
  calc ENNReal.ofReal (rexp (γ * hcirc ω (dyadicScale j) 0)) *
        (⨆ n : ℕ, lqgApprox γ (dilateRecentre (dyadicScale j) (hcirc ω)) (dyadicScale n) (ball 0 1))
      ≤ ENNReal.ofReal (rexp (η / 2 * j)) * ENNReal.ofReal (rexp (η / 2 * j)) :=
        mul_le_mul' (ENNReal.ofReal_le_ofReal hj2) (hj1.trans (ENNReal.ofReal_le_ofReal hj3))
    _ = ENNReal.ofReal (rexp (η * j)) := by
        rw [← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add]
        congr 2
        ring

end LatticeProb.Gauss.IsWholePlaneGFF
