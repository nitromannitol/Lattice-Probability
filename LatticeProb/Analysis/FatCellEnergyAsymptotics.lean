import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Analysis.SpecialFunctions.Log.Base

/-!
# Exponent bookkeeping for the energy of a flow through fat cells

As `ε → 0⁺`, a power `ε^{-a}` times a logarithmic factor `A log(1/ε) + B` is eventually at
most `ε^{-b}` for every `b > a`. Applied to the bound
`D · (1/2) · Δ · ((log₂ (M/m) + 1) · 16/κ² + 8 log (R/m) / κ²)` on the energy of a flow through
fat planar cells (`LatticeProb.le_of_poisson_of_fatCells`), with degrees `D, Δ ≤ ε^{-δ}`, inball
ratio `κ = ε^{δ/4}` and diameters in `[ε^p, ε^q]`, it shows that the bound is eventually at
most `ε^{-ζ}` whenever `5δ/2 < ζ`.

## Main results

* `LatticeProb.eventually_rpow_neg_mul_log_add_le`
* `LatticeProb.eventually_fatCell_energy_rpow_le`
-/

open Filter Topology

namespace LatticeProb

/-- For `a < b`, eventually as `ε → 0⁺`, `ε^{-a} (A log(1/ε) + B) ≤ ε^{-b}`. -/
theorem eventually_rpow_neg_mul_log_add_le {a b : ℝ} (A B : ℝ) (hab : a < b) :
    ∀ᶠ ε in 𝓝[>] (0 : ℝ), ε ^ (-a) * (A * Real.log ε⁻¹ + B) ≤ ε ^ (-b) := by
  have hc : 0 < b - a := sub_pos.2 hab
  have h1 : Tendsto (fun ε : ℝ => ε ^ (b - a)) (𝓝[>] 0) (𝓝 0) := by
    have := ((Real.continuous_rpow_const hc.le).tendsto 0).mono_left
      (nhdsWithin_le_nhds (s := Set.Ioi (0 : ℝ)))
    simpa [Real.zero_rpow hc.ne'] using this
  have h2 := tendsto_log_mul_rpow_nhdsGT_zero hc
  have h3 : Tendsto (fun ε : ℝ => ε ^ (b - a) * (A * Real.log ε⁻¹ + B)) (𝓝[>] 0) (𝓝 0) := by
    have := (h2.const_mul (-A)).add (h1.const_mul B)
    simp only [mul_zero, add_zero] at this
    refine this.congr' (Eventually.of_forall fun ε => ?_)
    simp only [Real.log_inv]
    ring
  filter_upwards [h3.eventually (gt_mem_nhds zero_lt_one), self_mem_nhdsWithin] with ε hε hpos
  have hε0 : (0 : ℝ) < ε := hpos
  have hsplit : ε ^ (-a) = ε ^ (-b) * ε ^ (b - a) := by
    rw [← Real.rpow_add hε0]; congr 1; ring
  rw [hsplit, mul_assoc]
  calc ε ^ (-b) * (ε ^ (b - a) * (A * Real.log ε⁻¹ + B)) ≤ ε ^ (-b) * 1 :=
        mul_le_mul_of_nonneg_left hε.le (Real.rpow_nonneg hε0.le _)
    _ = ε ^ (-b) := mul_one _

/-- **Exponent bookkeeping for the fat-cell energy bound.** With degrees `ε^{-δ}`, inball ratio
`κ = ε^{δ/4}` and cell diameters in `[ε^p, ε^q]` inside a disc of radius `R > 0`, the energy
bound `D · (1/2) · Δ · ((log₂ (M/m) + 1) · 16/κ² + 8 log (R/m) / κ²)` is eventually at most
`ε^{-ζ}` as `ε → 0⁺`, provided `5δ/2 < ζ`. -/
theorem eventually_fatCell_energy_rpow_le {p q δ ζ R : ℝ} (hR : 0 < R)
    (hζ : 5 * δ / 2 < ζ) :
    ∀ᶠ ε in 𝓝[>] (0 : ℝ), ε ^ (-δ) * ((1 / 2) * (ε ^ (-δ) *
      ((Real.logb 2 (ε ^ q / ε ^ p) + 1) * (16 / (ε ^ (δ / 4)) ^ 2) +
        8 * Real.log (R / ε ^ p) / (ε ^ (δ / 4)) ^ 2))) ≤ ε ^ (-ζ) := by
  filter_upwards [eventually_rpow_neg_mul_log_add_le (8 * (p - q) / Real.log 2 + 4 * p)
    (8 + 4 * Real.log R) hζ, self_mem_nhdsWithin] with ε hε hpos
  have hε0 : (0 : ℝ) < ε := hpos
  have hL1 : Real.logb 2 (ε ^ q / ε ^ p) = (p - q) / Real.log 2 * Real.log ε⁻¹ := by
    rw [Real.logb, Real.log_div (Real.rpow_pos_of_pos hε0 q).ne'
      (Real.rpow_pos_of_pos hε0 p).ne', Real.log_rpow hε0, Real.log_rpow hε0, Real.log_inv]
    ring
  have hL2 : Real.log (R / ε ^ p) = Real.log R + p * Real.log ε⁻¹ := by
    rw [Real.log_div hR.ne' (Real.rpow_pos_of_pos hε0 p).ne', Real.log_rpow hε0, Real.log_inv]
    ring
  have hk : (ε ^ (δ / 4)) ^ 2 = ε ^ (δ / 2) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hε0.le]; congr 1; push_cast; ring
  have h5 : ε ^ (-(5 * δ / 2)) = ε ^ (-δ) * ε ^ (-δ) * (ε ^ (δ / 2))⁻¹ := by
    rw [← Real.rpow_neg hε0.le, ← Real.rpow_add hε0, ← Real.rpow_add hε0]
    congr 1; ring
  refine le_trans (le_of_eq ?_) hε
  rw [hL1, hL2, hk, h5]
  ring

end LatticeProb
