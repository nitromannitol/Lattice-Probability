/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.B2.DG20Conc.J1RoundUpperPoint at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Conc.J1RoundUpperShift
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Conc.J1QuantileStep

 

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

open MeasureTheory Metric
open scoped ENNReal

namespace SupercriticalLQGUniqueness.B2.DG20Conc

open LQGMetric.DDDF LQGMetric.WhiteNoise LQGMetric.LFPP

universe u

theorem j1_round_upper_pointwise
    {ξ p : ℝ} (hunit : LaneA2HasUnitTails.{u} ξ p)
    (hp : 0 < p) (hpHalf : p < 2⁻¹)
    (C : ℝ) (hC : 0 ≤ C) :
    ∃ R₀ A CP cP : ℝ,
      24 ≤ R₀ ∧ 0 < A ∧ 0 < CP ∧ 0 < cP ∧
      ∀ {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω)
        (W : WNSpace → Ω → ℝ) (hW : IsWhiteNoise P W)
        (K n : ℕ) (hKn : K ≤ n) (R : ℝ)
        (hR : R₀ ≤ R) (hRK : R ≤ 2 * (K : ℝ))
        (hH : LambdaN ξ W P (n - K) (ENNReal.ofReal p) ≤
          Real.exp (C * Real.sqrt (K : ℝ)))
        (c : ℂ) (T : ℝ)
        (hT : Real.exp (A * Real.sqrt ((K : ℝ) + 1)) ≤ T),
        P {ω | ENNReal.ofReal (T * lambdaN ξ W P (n - K)) <
          (lfppContMetric ξ (fun z => phiMN W P K n
            (((2 : ℝ)⁻¹ ^ K : ℝ) * z + c) ω)
            ((isPhiVersion_phiMN hW hKn).cont ω |>.comp
              (show Continuous (fun z : ℂ =>
                (((2 : ℝ)⁻¹ ^ K : ℝ) * z + c)) by fun_prop))).aroundDist
            {z : ℂ | R < dist z 0 ∧ dist z 0 < 2 * R}
            (sphere (0 : ℂ) R) (sphere (0 : ℂ) (2 * R))} ≤
          ENNReal.ofReal (CP * R * Real.exp
            (-cP * (Real.log T)^2 / Real.log (Real.log T))) := by
  obtain ⟨R₀, G, Cp, cp, hR₀, hG, hCp, hcp, hcover⟩ :=
    j1_round_upper_cover hunit
  let A : ℝ := 2 * (G + C + 4) + 2
  have hA : 0 < A := by dsimp [A]; linarith
  refine ⟨R₀, A, G * Cp, cp / 4,
    hR₀, hA, by positivity, by positivity, ?_⟩
  intro Ω _ P W hW K n hKn R hR hRK hH c T hT
  let B : ℝ := Real.exp (C * Real.sqrt (K : ℝ))
  let D : ℝ := G * R * B
  let s : ℝ := T / D
  have hR1 : 1 ≤ R := by linarith
  obtain ⟨hD1, hstart⟩ :=
    j1_round_upper_parameter_shift G C hG hC K R hR1 hRK T hT
  have hD0 : 0 < D := by linarith
  have hB0 : 0 < B := Real.exp_pos _
  have hs : 3 < s := (laneA2_shifted_sq_rate hD1 hstart).1
  have hT0 : 0 < T := (Real.exp_pos _).trans_le hT
  obtain ⟨_, hupper⟩ := j1_quantile_sandwich_of_induction
    P hW ξ hp (by linarith) hH
  have hth : (G * R) * (s * LambdaN ξ W P (n - K)
      (ENNReal.ofReal p) * ellN ξ W P (n - K) (ENNReal.ofReal p)) ≤
      T * lambdaN ξ W P (n - K) := by
    have hh := j1_upper_threshold_of_quantile hB0 hT0 hupper
    calc
      _ = (T / B) * (LambdaN ξ W P (n - K)
        (ENNReal.ofReal p) * ellN ξ W P (n - K)
          (ENNReal.ofReal p)) := by
          dsimp [s, D]
          field_simp [hB0.ne', (by linarith : G ≠ 0),
            (by linarith : R ≠ 0)]
      _ ≤ _ := hh
  have hsub :
      {ω | ENNReal.ofReal (T * lambdaN ξ W P (n - K)) <
        (lfppContMetric ξ (fun z => phiMN W P K n
          (((2 : ℝ)⁻¹ ^ K : ℝ) * z + c) ω)
          ((isPhiVersion_phiMN hW hKn).cont ω |>.comp
            (show Continuous (fun z : ℂ =>
              (((2 : ℝ)⁻¹ ^ K : ℝ) * z + c)) by fun_prop))).aroundDist
          {z : ℂ | R < dist z 0 ∧ dist z 0 < 2 * R}
          (sphere (0 : ℂ) R) (sphere (0 : ℂ) (2 * R))} ⊆
      {ω | ENNReal.ofReal ((G * R) *
          (s * LambdaN ξ W P (n - K) (ENNReal.ofReal p) *
            ellN ξ W P (n - K) (ENNReal.ofReal p))) <
        (lfppContMetric ξ (fun z => phiMN W P K n
          (((2 : ℝ)⁻¹ ^ K : ℝ) * z + c) ω)
          ((isPhiVersion_phiMN hW hKn).cont ω |>.comp
            (show Continuous (fun z : ℂ =>
              (((2 : ℝ)⁻¹ ^ K : ℝ) * z + c)) by fun_prop))).aroundDist
          {z : ℂ | R < dist z 0 ∧ dist z 0 < 2 * R}
          (sphere (0 : ℂ) R) (sphere (0 : ℂ) (2 * R))} := by
    intro ω hω
    exact (ENNReal.ofReal_le_ofReal hth).trans_lt hω
  have hraw := hcover P W hW K n hKn R hR c s hs
  have hrate := laneA_shifted_log_rate hD1 hstart
  have hreal : (G * R) * (Cp * Real.exp
      (-cp * (Real.log s)^2 / Real.log (Real.log s))) ≤
      (G * Cp) * R * Real.exp
        (-(cp / 4) * (Real.log T)^2 / Real.log (Real.log T)) := by
    have hlog : -cp * (Real.log s)^2 / Real.log (Real.log s) ≤
        -(cp / 4) * (Real.log T)^2 / Real.log (Real.log T) := by
      have hh := mul_le_mul_of_nonneg_left hrate hcp.le
      calc
        _ = -(cp * ((Real.log s)^2 /
            Real.log (Real.log s))) := by ring
        _ ≤ -(cp * ((Real.log T)^2 /
            (4 * Real.log (Real.log T)))) := neg_le_neg hh
        _ = _ := by ring
    have he := Real.exp_le_exp.mpr hlog
    nlinarith [mul_le_mul_of_nonneg_left he
      (by positivity : 0 ≤ G * R * Cp)]
  calc
    _ ≤ P {ω | ENNReal.ofReal ((G * R) *
          (s * LambdaN ξ W P (n - K) (ENNReal.ofReal p) *
            ellN ξ W P (n - K) (ENNReal.ofReal p))) <
        (lfppContMetric ξ (fun z => phiMN W P K n
          (((2 : ℝ)⁻¹ ^ K : ℝ) * z + c) ω)
          ((isPhiVersion_phiMN hW hKn).cont ω |>.comp
            (show Continuous (fun z : ℂ =>
              (((2 : ℝ)⁻¹ ^ K : ℝ) * z + c)) by fun_prop))).aroundDist
          {z : ℂ | R < dist z 0 ∧ dist z 0 < 2 * R}
          (sphere (0 : ℂ) R) (sphere (0 : ℂ) (2 * R))} :=
        measure_mono hsub
    _ ≤ ENNReal.ofReal (G * R) * ENNReal.ofReal
          (Cp * Real.exp
            (-cp * (Real.log s)^2 / Real.log (Real.log s))) := hraw
    _ = ENNReal.ofReal ((G * R) * (Cp * Real.exp
          (-cp * (Real.log s)^2 / Real.log (Real.log s)))) :=
      (ENNReal.ofReal_mul (by positivity : 0 ≤ G * R)).symm
    _ ≤ _ := ENNReal.ofReal_le_ofReal hreal

end SupercriticalLQGUniqueness.B2.DG20Conc
