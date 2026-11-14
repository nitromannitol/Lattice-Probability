/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.B2.DG20Conc.J1RoundCrossPoint at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Conc.J1SourceCrossLaw
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Conc.J1ShiftRate
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Conc.LaneA2LargeSameP

 

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

open MeasureTheory Metric
open scoped ENNReal

namespace SupercriticalLQGUniqueness.B2.DG20Conc

open LQGMetric.DDDF LQGMetric.WhiteNoise

universe u

theorem j1_source_round_cross_pointwise
    {ξ p : ℝ} (hunit : LaneA2HasUnitTails.{u} ξ p)
    (hp : 0 < p) (hpHalf : p < 2⁻¹)
    (C : ℝ) (hC : 0 ≤ C) :
    ∃ R₀ CN cN : ℝ, 24 ≤ R₀ ∧ 0 < CN ∧ 0 < cN ∧
      ∀ {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω)
        (W : WNSpace → Ω → ℝ) (hW : IsWhiteNoise P W)
        (K n m : ℕ) (hKn : K ≤ n) (hmK : m ≤ K)
        (hR : R₀ ≤ (2 : ℝ)^m)
        (hH : LambdaN ξ W P (n - K) (ENNReal.ofReal p) ≤
          Real.exp (C * Real.sqrt (K : ℝ)))
        (b : ℤ × ℤ) (T : ℝ)
        (hT : Real.exp (6 * (C + 1) *
          Real.sqrt ((K : ℝ) + 1)) ≤ T),
        P {ω | crossLenIn ξ (fun z => phiMN W P K n z ω)
          (j1SourceCross K m b)
          (LaneCInputs.sourceInner K m b)
          (LaneCInputs.sourceOuter K m b) <
          ENNReal.ofReal ((2 : ℝ)⁻¹ ^ K) *
            ENNReal.ofReal (T⁻¹ * lambdaN ξ W P (n - K))} ≤
          ENNReal.ofReal (CN * (2 : ℝ)^m *
            Real.exp (-cN * (Real.log T)^2)) := by
  obtain ⟨R₀, G, Cneg, cNeg, Cpos, cPos,
    hR₀, hG, hCn, hcn, hCp, hcp, hlarge⟩ :=
      laneA2_large_same_p hunit
  refine ⟨R₀, G * Cneg, cNeg / 4, hR₀,
    by positivity, by positivity, ?_⟩
  intro Ω _ P W hW K n m hKn hmK hR hH b T hT
  let B : ℝ := Real.exp (C * Real.sqrt (K : ℝ))
  have hB : 0 < B := Real.exp_pos _
  obtain ⟨hs, _⟩ := j1_induction_parameter_shift
    (A₀ := 1) (by norm_num) hC K (by convert hT using 1 <;> norm_num)
  have hT0 : 0 < T := (Real.exp_pos _).trans_le hT
  obtain ⟨hmed, _⟩ := j1_quantile_sandwich_of_induction
    P hW ξ hp (by linarith) hH
  have hth : T⁻¹ * lambdaN ξ W P (n - K) ≤
      (T / B)⁻¹ * ellN ξ W P (n - K) (ENNReal.ofReal p) :=
    j1_lower_threshold_of_quantile hB hT0 hmed
  have hsubset :
      {ω | crossLenIn ξ (fun z => phiMN W P K n z ω)
        (j1SourceCross K m b)
        (LaneCInputs.sourceInner K m b)
        (LaneCInputs.sourceOuter K m b) <
        ENNReal.ofReal ((2 : ℝ)⁻¹ ^ K) *
          ENNReal.ofReal (T⁻¹ * lambdaN ξ W P (n - K))} ⊆
      {ω | crossLenIn ξ (fun z => phiMN W P K n z ω)
        (j1SourceCross K m b)
        (LaneCInputs.sourceInner K m b)
        (LaneCInputs.sourceOuter K m b) <
        ENNReal.ofReal ((2 : ℝ)⁻¹ ^ K) *
          ENNReal.ofReal ((T / B)⁻¹ *
            ellN ξ W P (n - K) (ENNReal.ofReal p))} := by
    intro ω hω
    change crossLenIn ξ (fun z => phiMN W P K n z ω)
      (j1SourceCross K m b) (LaneCInputs.sourceInner K m b)
      (LaneCInputs.sourceOuter K m b) <
      ENNReal.ofReal ((2 : ℝ)⁻¹ ^ K) *
        ENNReal.ofReal (T⁻¹ * lambdaN ξ W P (n - K)) at hω
    exact hω.trans_le (mul_le_mul_of_nonneg_left
      (ENNReal.ofReal_le_ofReal hth) (zero_le : (0 : ℝ≥0∞) ≤ _))
  have hsource := (hlarge ((2 : ℝ)^m) hR P W hW (n - K)
    (T / B) hs).1
  have hscaled :
      P {ω | crossLenIn ξ (fun z => phiMN W P K n z ω)
        (j1SourceCross K m b)
        (LaneCInputs.sourceInner K m b)
        (LaneCInputs.sourceOuter K m b) <
        ENNReal.ofReal ((2 : ℝ)⁻¹ ^ K) *
          ENNReal.ofReal ((T / B)⁻¹ *
            ellN ξ W P (n - K) (ENNReal.ofReal p))} ≤
        ENNReal.ofReal ((G * Cneg) * (2 : ℝ)^m *
          Real.exp (-cNeg * (Real.log (T / B))^2)) := by
    rw [j1_source_round_cross_scale_law P W hW hKn hmK ξ b]
    simpa only [j1RoundCross] using hsource
  have hrates := (j1_induction_shifted_rates
    (A₀ := 1) (by norm_num) hC hcn (by norm_num : 0 < (1 : ℝ))
    (by positivity : 0 ≤ G * Cneg) (by norm_num : 0 ≤ (1 : ℝ)) K
    (by convert hT using 1 <;> norm_num)).1
  have hrate : (G * Cneg) * (2 : ℝ)^m *
      Real.exp (-cNeg * (Real.log (T / B))^2) ≤
      (G * Cneg) * (2 : ℝ)^m *
        Real.exp (-(cNeg / 4) * (Real.log T)^2) := by
    calc
      _ = (2 : ℝ)^m *
          ((G * Cneg) * Real.exp (-cNeg * (Real.log (T / B))^2)) := by ring
      _ ≤ (2 : ℝ)^m *
          ((G * Cneg) * Real.exp (-(cNeg / 4) * (Real.log T)^2)) :=
            mul_le_mul_of_nonneg_left hrates (by positivity)
      _ = _ := by ring
  exact ((measure_mono hsubset).trans hscaled).trans
    (ENNReal.ofReal_le_ofReal hrate)

end SupercriticalLQGUniqueness.B2.DG20Conc
