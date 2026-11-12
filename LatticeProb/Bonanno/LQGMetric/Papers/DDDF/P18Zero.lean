/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DDDF.P18Zero at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DDDF.P18Step2
import LatticeProb.Bonanno.LQGMetric.Papers.DDDF.P18Step4

/-!
# DDDF Proposition 18, the trivial case `n = 0` (task P2-DDDF16c)

DDDF (arXiv:1904.08021, `tightness.tex` l. 868–945) state Prop 18 "for all `n ≥ 0`"; Steps 2–4
are written for `n ≥ 1`. For `n = 0` the field `φ_{0,0} = φ_{1,1}` vanishes (a.s., for all `x`,
from `φ_{0,0} = φ_{0,0} + φ_{0,0}`, `ae_phiMN_add`), so `L^{(0)}_{3,1} = 3`, `L^{(0)}_{1,1} = 1`,
`ℓ_0(φ,p) ≥ 1`, `Λ_0 ℓ_0 ≥ 1` and the event `{L^{(0)}_{3,1} ≥ e^s Λ_0 ℓ_0}` is null for
`s > 2` (`e^s > 3`). Own elementary argument (the paper does not spell out `n = 0`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

namespace LQGMetric
namespace DDDF

open WhiteNoise

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {ξ : ℝ}

/-- `φ_{0,0} = 0` almost surely, for all `x` -/
lemma ae_phiMN_zero_zero {W : WNSpace → Ω → ℝ} (hW : IsWhiteNoise P W) :
    ∀ᵐ ω ∂P, ∀ x : ℂ, phiMN W P 0 0 x ω = 0 := by
  filter_upwards [ae_phiMN_add hW (le_refl 0)] with ω hω x
  have := hω x
  linarith

/-- **DDDF Prop 18 for `n = 0`**: the event is null. -/
theorem dddf_p18_zero {W : WNSpace → Ω → ℝ} (hW : IsWhiteNoise P W) {p : ℝ} (hp0 : 0 < p)
    (hp : p ≤ 1 / 2) {s : ℝ} (hs : 2 < s) :
    P {ω | Real.exp s * LambdaN ξ W P 0 (ENNReal.ofReal p) * ellN ξ W P 0 (ENNReal.ofReal p) ≤
        lenObs ξ (phiMN W P 0 0) (rectAB 3 1) ω} = 0 := by
  have := hW.isProbabilityMeasure
  have hφ := isPhiVersion_phiMN hW (le_refl 0)
  have hz := ae_phiMN_zero_zero hW
  have hb : ∀ ω, (∀ x, phiMN W P 0 0 x ω = 0) → ∀ R : MarkedRect,
      ∀ x ∈ R.toSet, |phiMN W P 0 0 x ω| ≤ 0 := by
    intro ω hω R x _; rw [hω x, abs_zero]
  -- `L^{(0)}_{1,1} ≥ 1` and `L^{(0)}_{3,1} ≤ 3`, a.s.
  have hL11 : ∀ᵐ ω ∂P, 1 ≤ lenObs ξ (phiMN W P 0 0) (rectAB 1 1) ω := by
    filter_upwards [hz] with ω hω
    have h := exp_neg_le_lenObs (ξ := ξ) hφ.cont (rectAB 1 1) (by norm_num [rectAB])
      (by norm_num [rectAB]) (hb ω hω _)
    simpa [rectAB, MarkedRect.crossWidth] using h
  have hL31 : ∀ᵐ ω ∂P, lenObs ξ (phiMN W P 0 0) (rectAB 3 1) ω ≤ 3 := by
    filter_upwards [hz] with ω hω
    have h := rectLen_le (ξ := ξ) (rectAB 3 1) (by norm_num [rectAB]) (by norm_num [rectAB])
      (hb ω hω _)
    have h' : rectLen ξ (fun x => phiMN W P 0 0 x ω) (rectAB 3 1) ≤ ENNReal.ofReal 3 := by
      simpa [rectAB, MarkedRect.crossWidth] using h
    exact ENNReal.toReal_le_of_le_ofReal (by norm_num) h'
  -- `ℓ_0(φ,p) ≥ 1`
  have hℓ : 1 ≤ ellN ξ W P 0 (ENNReal.ofReal p) := by
    by_contra hcon
    push Not at hcon
    have hq := prob_le_ellQ (ξ := ξ) (P := P) hφ.cont hφ.meas (rectAB 1 1)
      (ENNReal.ofReal_pos.2 hp0) (by rw [ENNReal.ofReal_lt_one]; linarith)
    have hnull : P {ω | lenObs ξ (phiMN W P 0 0) (rectAB 1 1) ω ≤
        ellQ ξ P (phiMN W P 0 0) (rectAB 1 1) (ENNReal.ofReal p)} = 0 := by
      rw [measure_eq_zero_iff_ae_notMem]
      filter_upwards [hL11] with ω hω hmem
      exact absurd (lt_of_le_of_lt hmem hcon) (not_lt.2 hω)
    rw [hnull, nonpos_iff_eq_zero, ENNReal.ofReal_eq_zero] at hq
    linarith
  have hℓ0 : 0 < ellN ξ W P 0 (ENNReal.ofReal p) := by linarith
  have hΛ := ellN_le_LambdaN_mul (ξ := ξ) (P := P) (W := W) hp0 hp hℓ0
  have he : 3 < Real.exp s := by linarith [Real.add_one_le_exp s]
  rw [measure_eq_zero_iff_ae_notMem]
  filter_upwards [hL31] with ω hω hmem
  have hmem' : Real.exp s * LambdaN ξ W P 0 (ENNReal.ofReal p) *
      ellN ξ W P 0 (ENNReal.ofReal p) ≤ lenObs ξ (phiMN W P 0 0) (rectAB 3 1) ω := hmem
  have h1 : Real.exp s ≤ Real.exp s * LambdaN ξ W P 0 (ENNReal.ofReal p) *
      ellN ξ W P 0 (ENNReal.ofReal p) := by
    rw [mul_assoc]
    exact le_mul_of_one_le_right (Real.exp_pos _).le (by linarith)
  linarith

end DDDF
end LQGMetric
