/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.B2.DG20Conc.LaneA2CanonicalUpper at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Conc.LaneA2CanonicalLower

 

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

open MeasureTheory
open scoped ENNReal

namespace SupercriticalLQGUniqueness.B2.DG20Conc

open LQGMetric.DDDF LQGMetric.WhiteNoise

universe u

 

theorem laneA2_canonical_upper_of_unit_tail {ξ p Cpos cPos : ℝ}
    (hp : 0 < p) (hpHalf : p ≤ 1 / 2)
    (htail : ∀ {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω)
      (W : WNSpace → Ω → ℝ) (hW : IsWhiteNoise P W)
      (m : ℕ) (T : ℝ), 3 < T →
        P {ω | T * LambdaN ξ W P m (ENNReal.ofReal p) *
          ellN ξ W P m (ENNReal.ofReal p) <
          lenObs ξ (phiMN W P 0 m) (rectAB 3 1) ω} ≤
          ENNReal.ofReal (Cpos * Real.exp
            (-cPos * (Real.log T)^2 / Real.log (Real.log T)))) :
    ∃ C A : ℝ, 0 < C ∧ 0 < A ∧
      ∀ {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω)
        (W : WNSpace → Ω → ℝ) (_hW : IsWhiteNoise P W)
        (m : ℕ) (_hm : 3 ≤ m) (M : ℝ) (_hM : 0 < M)
        (T : ℝ) (_hT : 6 < T),
        P {ω | Real.exp (|ξ| * M) *
            ((1 / 8) * T * LambdaN ξ W P (m - 3) (ENNReal.ofReal p) *
              ellN ξ W P (m - 3) (ENNReal.ofReal p)) ≤
            lenObs ξ (phiMN W P 0 m) (rectAB (3 / 8) (1 / 8)) ω} ≤
          ENNReal.ofReal (C * Real.exp (-((M / A)^2 * 3 / Real.log 4))) +
          ENNReal.ofReal (Cpos * Real.exp
            (-cPos * (Real.log (T / 2))^2 / Real.log (Real.log (T / 2)))) := by
  obtain ⟨C, A, hC, hA, hcoarse⟩ := laneA2_coarse_sup_three
  refine ⟨C, A, hC, hA, ?_⟩
  intro Ω _ P W hW m hm M hM T hT
  have hsplit := dddf_p18_step2_split (ξ := ξ) hW hm
    (a := 3 / 8) (b := 1 / 8) (by norm_num) (by norm_num) M
    ((1 / 8) * T * LambdaN ξ W P (m - 3) (ENNReal.ofReal p) *
      ellN ξ W P (m - 3) (ENNReal.ofReal p))
  have hc := hcoarse P W hW (3 / 8) (1 / 8)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) M hM
  have hpq0 : 0 < ENNReal.ofReal p := ENNReal.ofReal_pos.mpr hp
  have hpq : ENNReal.ofReal p ≤ (2⁻¹ : ℝ≥0∞) := by
    have he : ENNReal.ofReal (1 / 2 : ℝ) = (2⁻¹ : ℝ≥0∞) := by
      rw [show (1 / 2 : ℝ) = (2 : ℝ)⁻¹ by norm_num,
        ENNReal.ofReal_inv_of_pos (by norm_num)]
      norm_num
    rw [← he]
    exact ENNReal.ofReal_le_ofReal hpHalf
  have : IsProbabilityMeasure P := hW.isProbabilityMeasure
  have hprod : 0 < LambdaN ξ W P (m - 3) (ENNReal.ofReal p) *
      ellN ξ W P (m - 3) (ENNReal.ofReal p) := by
    have hΛ := T20B.LambdaN_pos (ξ := ξ) hW hpq0 hpq (m - 3)
    have hℓ := T20B.ellN_pos (ξ := ξ) hW hpq0
      (lt_of_le_of_lt hpq (by norm_num)) (m - 3)
    positivity
  have hfine : P {ω | (1 / 8) * T * LambdaN ξ W P (m - 3) (ENNReal.ofReal p) *
      ellN ξ W P (m - 3) (ENNReal.ofReal p) ≤
      (2 : ℝ)⁻¹ ^ 3 * lenMN ξ W P ((2 : ℝ)^3 * (3 / 8))
        ((2 : ℝ)^3 * (1 / 8)) 0 (m - 3) ω} ≤
      ENNReal.ofReal (Cpos * Real.exp
        (-cPos * (Real.log (T / 2))^2 / Real.log (Real.log (T / 2)))) := by
    norm_num only [lenMN, inv_pow] at *
    have hsets : {ω | (1 / 8 : ℝ) * T * LambdaN ξ W P (m - 3) (ENNReal.ofReal p) *
        ellN ξ W P (m - 3) (ENNReal.ofReal p) ≤
        (1 / 8) * lenObs ξ (phiMN W P 0 (m - 3)) (rectAB 3 1) ω} ⊆
        {ω | (T / 2) * LambdaN ξ W P (m - 3) (ENNReal.ofReal p) *
          ellN ξ W P (m - 3) (ENNReal.ofReal p) <
          lenObs ξ (phiMN W P 0 (m - 3)) (rectAB 3 1) ω} := by
      intro ω hω
      have hω' : T * LambdaN ξ W P (m - 3) (ENNReal.ofReal p) *
          ellN ξ W P (m - 3) (ENNReal.ofReal p) ≤
          lenObs ξ (phiMN W P 0 (m - 3)) (rectAB 3 1) ω := by
        change (1 / 8 : ℝ) * T * LambdaN ξ W P (m - 3) (ENNReal.ofReal p) *
          ellN ξ W P (m - 3) (ENNReal.ofReal p) ≤
          (1 / 8) * lenObs ξ (phiMN W P 0 (m - 3)) (rectAB 3 1) ω at hω
        nlinarith [hω]
      have hT0 : 0 < T := by linarith
      change (T / 2) * _ * _ < _
      nlinarith [hω', hprod]
    exact (measure_mono hsets).trans
      (htail (Ω := Ω) P W hW (m - 3) (T / 2) (by linarith))
  exact hsplit.trans (add_le_add hc hfine)

end SupercriticalLQGUniqueness.B2.DG20Conc
