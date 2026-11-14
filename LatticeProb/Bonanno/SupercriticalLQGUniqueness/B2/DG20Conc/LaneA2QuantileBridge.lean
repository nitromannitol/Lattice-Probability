/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.B2.DG20Conc.LaneA2QuantileBridge at commit fdb5cad; only the module paths of local imports are changed.
   Declarations, examples and checks that the copied results do not use are omitted.
   Imports of copied modules that this file does not need are replaced by their own imports. -/
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Conc.LaneATails
import LatticeProb.Bonanno.LQGMetric.Papers.DDDF.T20BRect
import LatticeProb.Bonanno.LQGMetric.LFPP.ContMetric
import LatticeProb.Bonanno.LQGMetric.Topo.Disconnect
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Conc.LaneBSiteExitMeet
import LatticeProb.Bonanno.LQGMetric.LFPP.Length
import LatticeProb.Bonanno.LQGMetric.Papers.DDDF.T20DGeom
import LatticeProb.Bonanno.LQGMetric.Papers.DDDF.P18Geom
import Mathlib.Data.Fintype.EquivFin
import LatticeProb.Bonanno.LQGMetric.Papers.DDDF.P18Step3
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Conc.LaneA2ReverseBridge

 






set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

open MeasureTheory
open scoped ENNReal

namespace SupercriticalLQGUniqueness.B2.DG20Conc

open LQGMetric.DDDF LQGMetric.WhiteNoise

theorem laneA2_LambdaN_mono {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (W : WNSpace → Ω → ℝ) (ξ : ℝ) (p : ℝ≥0∞)
    {j m : ℕ} (hjm : j ≤ m) :
    LambdaN ξ W P j p ≤ LambdaN ξ W P m p := by
  unfold LambdaN
  apply Finset.sup'_le
  intro i hi
  exact Finset.le_sup'
    (fun k => ellBarN ξ W P k p / ellN ξ W P k p)
    (Finset.mem_range.mpr (Nat.lt_succ_of_le
      ((Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)).trans hjm)))

 
theorem laneA2_lambdaN_le_B_ellN
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    {W : WNSpace → Ω → ℝ} (hW : IsWhiteNoise P W)
    (ξ : ℝ) {p B : ℝ} (hp : 0 < p) (hpHalf : p ≤ 1 / 2)
    {m : ℕ} (hB : LambdaN ξ W P m (ENNReal.ofReal p) ≤ B) :
    lambdaN ξ W P m ≤ B * ellN ξ W P m (ENNReal.ofReal p) := by
  have : IsProbabilityMeasure P := hW.isProbabilityMeasure
  have hpq0 : 0 < ENNReal.ofReal p := ENNReal.ofReal_pos.mpr hp
  have hpq : ENNReal.ofReal p ≤ (2⁻¹ : ℝ≥0∞) := by
    have he : ENNReal.ofReal (1 / 2 : ℝ) = (2⁻¹ : ℝ≥0∞) := by
      rw [show (1 / 2 : ℝ) = (2 : ℝ)⁻¹ by norm_num,
        ENNReal.ofReal_inv_of_pos (by norm_num)]
      norm_num
    rw [← he]
    exact ENNReal.ofReal_le_ofReal hpHalf
  have hℓ0 : 0 < ellN ξ W P m (ENNReal.ofReal p) :=
    T20B.ellN_pos hW hpq0 (lt_of_le_of_lt hpq (by norm_num)) m
  have hmed : lambdaN ξ W P m ≤ ellBarN ξ W P m (ENNReal.ofReal p) :=
    T20B.lambdaN_le_ellBarN hpq0 hpq m
  have hratio : ellBarN ξ W P m (ENNReal.ofReal p) /
      ellN ξ W P m (ENNReal.ofReal p) ≤
      LambdaN ξ W P m (ENNReal.ofReal p) := by
    unfold LambdaN
    exact Finset.le_sup'
      (fun k => ellBarN ξ W P k (ENNReal.ofReal p) /
        ellN ξ W P k (ENNReal.ofReal p))
      (Finset.self_mem_range_succ m)
  have hbar : ellBarN ξ W P m (ENNReal.ofReal p) ≤
      B * ellN ξ W P m (ENNReal.ofReal p) := by
    have := (div_le_iff₀ hℓ0).1 (hratio.trans hB)
    simpa only [mul_comm] using this
  exact hmed.trans hbar

 


theorem laneA2_three_octave_of_local_eq698
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    {W : WNSpace → Ω → ℝ} (hW : IsWhiteNoise P W)
    (ξ : ℝ) {p B D : ℝ} (hp : 0 < p) (hpHalf : p ≤ 1 / 2)
    (hB1 : 1 ≤ B) (hD1 : 1 ≤ D) {m : ℕ} (hm : 3 ≤ m)
    (hΛ : LambdaN ξ W P m (ENNReal.ofReal p) ≤ B)
    (hstep : ∀ j : ℕ, j < m →
      LambdaN ξ W P j (ENNReal.ofReal p) ≤ B →
      lambdaN ξ W P (j + 1) ≤ D * B * lambdaN ξ W P j) :
    ellN ξ W P m (ENNReal.ofReal p) ≤
      D^3 * B^4 * ellN ξ W P (m - 3) (ENNReal.ofReal p) := by
  have : IsProbabilityMeasure P := hW.isProbabilityMeasure
  have hpq0 : 0 < ENNReal.ofReal p := ENNReal.ofReal_pos.mpr hp
  have hpq : ENNReal.ofReal p ≤ (2⁻¹ : ℝ≥0∞) := by
    have he : ENNReal.ofReal (1 / 2 : ℝ) = (2⁻¹ : ℝ≥0∞) := by
      rw [show (1 / 2 : ℝ) = (2 : ℝ)⁻¹ by norm_num,
        ENNReal.ofReal_inv_of_pos (by norm_num)]
      norm_num
    rw [← he]
    exact ENNReal.ofReal_le_ofReal hpHalf
  have hmed : ellN ξ W P m (ENNReal.ofReal p) ≤ lambdaN ξ W P m :=
    T20B.ellN_le_lambdaN hpq0 hpq m
  have hprev : lambdaN ξ W P (m - 3) ≤
      B * ellN ξ W P (m - 3) (ENNReal.ofReal p) :=
    laneA2_lambdaN_le_B_ellN P hW ξ hp hpHalf
      ((laneA2_LambdaN_mono P W ξ (ENNReal.ofReal p)
        (Nat.sub_le m 3)).trans hΛ)
  have h₁ : m - 3 + 1 < m := by omega
  have h₂ : m - 3 + 2 < m := by omega
  have h₃ : m - 3 + 3 = m := by omega
  have hs₁ := hstep (m - 3) (by omega)
    ((laneA2_LambdaN_mono P W ξ (ENNReal.ofReal p)
      (by omega : m - 3 ≤ m)).trans hΛ)
  have hs₂ := hstep (m - 3 + 1) h₁
    ((laneA2_LambdaN_mono P W ξ (ENNReal.ofReal p)
      (by omega : m - 3 + 1 ≤ m)).trans hΛ)
  have hs₃ := hstep (m - 3 + 2) h₂
    ((laneA2_LambdaN_mono P W ξ (ENNReal.ofReal p)
      (by omega : m - 3 + 2 ≤ m)).trans hΛ)
  have hDB : 0 ≤ D * B := by positivity
  have hchain : lambdaN ξ W P m ≤
      (D * B)^3 * lambdaN ξ W P (m - 3) := by
    rw [← h₃]
    calc
      lambdaN ξ W P (m - 3 + 3) ≤
          D * B * lambdaN ξ W P (m - 3 + 2) := by
            simpa only [Nat.add_assoc] using hs₃
      _ ≤ D * B * (D * B * lambdaN ξ W P (m - 3 + 1)) :=
        mul_le_mul_of_nonneg_left hs₂ hDB
      _ ≤ D * B * (D * B * (D * B * lambdaN ξ W P (m - 3))) := by
        gcongr
      _ = (D * B)^3 * lambdaN ξ W P (m - 3) := by ring
  calc
    ellN ξ W P m (ENNReal.ofReal p) ≤ lambdaN ξ W P m := hmed
    _ ≤ (D * B)^3 * lambdaN ξ W P (m - 3) := hchain
    _ ≤ (D * B)^3 * (B * ellN ξ W P (m - 3) (ENNReal.ofReal p)) :=
      mul_le_mul_of_nonneg_left hprev (by positivity)
    _ = D^3 * B^4 * ellN ξ W P (m - 3) (ENNReal.ofReal p) := by ring

end SupercriticalLQGUniqueness.B2.DG20Conc
