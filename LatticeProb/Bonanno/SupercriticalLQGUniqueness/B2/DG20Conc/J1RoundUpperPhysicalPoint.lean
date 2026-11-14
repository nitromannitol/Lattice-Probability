/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.B2.DG20Conc.J1RoundUpperPhysicalPoint at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Conc.J1RoundAroundScale
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Conc.J1RoundUpperPoint

 

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

open MeasureTheory Metric
open scoped ENNReal

namespace SupercriticalLQGUniqueness.B2.DG20Conc

open LQGMetric.DDDF LQGMetric.WhiteNoise LQGMetric.LFPP

universe u

theorem j1_source_round_upper_pointwise
    {ξ p : ℝ} (hunit : LaneA2HasUnitTails.{u} ξ p)
    (hp : 0 < p) (hpHalf : p < 2⁻¹)
    (C : ℝ) (hC : 0 ≤ C) :
    ∃ R₀ A CP cP : ℝ,
      24 ≤ R₀ ∧ 0 < A ∧ 0 < CP ∧ 0 < cP ∧
      ∀ {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω)
        (W : WNSpace → Ω → ℝ) (hW : IsWhiteNoise P W)
        (K n m : ℕ) (hKn : K ≤ n) (hmK : m ≤ K)
        (hR : R₀ ≤ (2 : ℝ)^m)
        (hRK : (2 : ℝ)^m ≤ 2 * (K : ℝ))
        (hH : LambdaN ξ W P (n - K) (ENNReal.ofReal p) ≤
          Real.exp (C * Real.sqrt (K : ℝ)))
        (b : ℤ × ℤ) (T : ℝ)
        (hT : Real.exp (A * Real.sqrt ((K : ℝ) + 1)) ≤ T),
        P {ω | ENNReal.ofReal ((2 : ℝ)⁻¹ ^ K) *
          ENNReal.ofReal (T * lambdaN ξ W P (n - K)) <
          (lfppContMetric ξ (fun z => phiMN W P K n z ω)
            ((isPhiVersion_phiMN hW hKn).cont ω)).aroundDist
            (LaneCInputs.sourceAround K m b)
            (LaneCInputs.sourceInner K m b)
            (LaneCInputs.sourceOuter K m b)} ≤
          ENNReal.ofReal (CP * (2 : ℝ)^m * Real.exp
            (-cP * (Real.log T)^2 / Real.log (Real.log T))) := by
  obtain ⟨R₀, A, CP, cP, hR₀, hA, hCP, hcP, ht⟩ :=
    j1_round_upper_pointwise hunit hp hpHalf C hC
  refine ⟨R₀, A, CP, cP, hR₀, hA, hCP, hcP, ?_⟩
  intro Ω _ P W hW K n m hKn hmK hR hRK hH b T hT
  have hr : 0 < (2 : ℝ)⁻¹ ^ K := by positivity
  have hr0 : ENNReal.ofReal ((2 : ℝ)⁻¹ ^ K) ≠ 0 :=
    (ENNReal.ofReal_pos.mpr hr).ne'
  have hrt : ENNReal.ofReal ((2 : ℝ)⁻¹ ^ K) ≠ ∞ :=
    ENNReal.ofReal_ne_top
  apply (measure_mono ?_).trans
    (ht P W hW K n hKn ((2 : ℝ)^m) hR hRK hH
      (T20.dyCenter K b) T hT)
  intro ω hω
  have hle := j1_source_round_around_le P W hW hKn hmK ξ b ω
  exact (ENNReal.mul_lt_mul_iff_right hr0 hrt).mp
    (hω.trans_le hle)

end SupercriticalLQGUniqueness.B2.DG20Conc
