/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DZZ.S3L12Main at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.S3L12Asym

/-!
# DZZ Lemma 3.12 from Lemma 3.16 and the path surgery (P2-DZZ312)

Ding–Zeitouni–Zhang, arXiv:1807.00422, `LBM_LGDarXiv.tex`, proof of Lemma 3.12, l. 1428–1446:

* work on `𝓔_{δ,α}` (Lemma 3.4, `dzz_lemma34_fine`) and on `𝓔_{δ,α*}` (`dzz_lemma34_of_pos`);
* (eq-B-good) for the `O(log δ⁻¹)` boxes `B` with `u ∈ B_large` or `v ∈ B_large` makes `u`, `v` good
  (`measureReal_window_levels_le`, `isGoodPoint_of_boxColl`);
* (eq-B-percolation) and a union bound give `𝓔_{δ,𝖢}` for every cell `𝖢` (`measureReal_levels_le`);
* on these events the path surgery (Eq.sequence-good-cells), l. 1436–1499, gives the good sequence.

The path surgery is the deterministic statement `L312Surgery` (verbatim the claim (Eq.sequence-good-cells)
of DZZ, l. 1440–1446, with the hypotheses DZZ use there: cell sizes in `[δ^{C_mc}, δ^{C_Mc}]` and every
point in a cell (`𝓔_{δ,α}`), `𝓔_{δ,𝖢}` for every cell, `u`, `v` good). It is a hypothesis here.

* **`dzz_lemma312_of`**: `DZZLemma316 P γ W → L312Surgery γ → DZZLemma312 P γ W`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology
open scoped ENNReal

namespace LQGMetric
namespace DZZ

open WhiteNoise DyBox

lemma one_le_epsStarN {αs δ : ℝ} (hαs : 0 < αs) (hL : 1 < Real.log δ⁻¹) : 1 ≤ epsStarN αs δ := by
  classical
  rw [Nat.one_le_iff_ne_zero]
  intro h0
  have h := Nat.find_spec (exists_two_pow_le_epsStarThr αs δ)
  have e : Nat.find (exists_two_pow_le_epsStarThr αs δ) = epsStarN αs δ := rfl
  rw [e, h0, pow_zero] at h
  have hpos : 0 < αs * Real.sqrt (Real.log δ⁻¹) * Real.log (Real.log δ⁻¹) :=
    mul_pos (mul_pos hαs (Real.sqrt_pos.mpr (by linarith))) (Real.log_pos hL)
  have : epsStarThr αs δ < 1 := Real.exp_lt_one_iff.mpr (by linarith)
  linarith

/-- Levels of cells on `𝓔_{δ,α}`: `δ^{C_mc} ≤ s ⇒ n ≤ C_mc log₂ δ⁻¹`. -/
lemma n_le_of_rpow_le_side {δ C : ℝ} (hδ0 : 0 < δ) {b : DyBox} (h : δ ^ C ≤ b.side) :
    (b.n : ℝ) ≤ C * Real.logb 2 δ⁻¹ := by
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hs : 0 < b.side := by unfold DyBox.side; positivity
  have := Real.log_le_log (by positivity) h
  rw [Real.log_rpow hδ0, DyBox.log_side] at this
  rw [Real.logb, Real.log_inv, ← mul_div_assoc, le_div_iff₀ hl2]
  nlinarith

lemma one_le_n_of_side_le {δ C : ℝ} (hδ0 : 0 < δ) (hδ1 : δ < 1) (hC : 0 < C) {b : DyBox}
    (h : b.side ≤ δ ^ C) : 1 ≤ b.n := by
  rw [Nat.one_le_iff_ne_zero]
  intro h0
  have : b.side = 1 := by simp [DyBox.side, h0]
  have : δ ^ C < 1 := Real.rpow_lt_one hδ0.le hδ1 hC
  linarith

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {W : WNSpace → Ω → ℝ}

end DZZ
end LQGMetric
