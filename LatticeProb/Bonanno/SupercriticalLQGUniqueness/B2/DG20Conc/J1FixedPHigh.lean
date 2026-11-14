/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.B2.DG20Conc.J1FixedPHigh at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Conc.J1SamePRawSmall
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Conc.LaneA2ThresholdExp
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Conc.LaneAShift

 

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

open MeasureTheory
open scoped ENNReal

namespace SupercriticalLQGUniqueness.B2.DG20Conc

open LQGMetric.DDDF LQGMetric.WhiteNoise LQGMetric.LFPP

universe u

theorem j1_fixed_p_small_high_of_C1
    (hC1 : LaneBInputs.C1UnitBlockGeometry)
    {ξ : ℝ} (hξ : 0 < ξ) :
    ∃ p : ℝ, 0 < p ∧ p < 2⁻¹ ∧ LaneA2HasUnitTails.{u} ξ p ∧
      ∀ (C : ℝ) (hC : 0 ≤ C), ∃ A₀ CN cN CP cP : ℝ,
      0 < A₀ ∧
      0 < CN ∧ 0 < cN ∧ 0 < CP ∧ 0 < cP ∧
      ∀ {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω)
        (W : WNSpace → Ω → ℝ) (hW : IsWhiteNoise P W)
        (K m : ℕ)
        (hH : LambdaN ξ W P m (ENNReal.ofReal p) ≤
          Real.exp (C * Real.sqrt (K : ℝ)))
        (i : Bool) (c : ℂ) (T : ℝ) (hT : 3 < T),
        (Real.exp (A₀ * (C + 1) * Real.sqrt ((K : ℝ) + 1)) ≤ T →
          P {ω | crossLenIn ξ (fun z => phiMN W P 0 m z ω)
            (laneCUnitUcross i) (laneCUnitInner i) (laneCUnitOuter i) <
            ENNReal.ofReal (T⁻¹ * ellN ξ W P m (ENNReal.ofReal p))} ≤
            ENNReal.ofReal (CN * Real.exp (-cN * (Real.log T)^2))) ∧
        P {ω | ENNReal.ofReal (T *
          LambdaN ξ W P m (ENNReal.ofReal p) *
          ellN ξ W P m (ENNReal.ofReal p)) <
          (lfppContMetric ξ (fun z => phiMN W P K (K + m)
            (((2 : ℝ)⁻¹ ^ K : ℝ) * z + c) ω)
            ((isPhiVersion_phiMN hW (by omega : K ≤ K + m)).cont ω |>.comp
              (show Continuous (fun z : ℂ =>
                (((2 : ℝ)⁻¹ ^ K : ℝ) * z + c)) by fun_prop))).aroundDist
            (laneCUnitUaround i) (laneCUnitInner i)
            (laneCUnitOuter i)} ≤
          ENNReal.ofReal (CP * Real.exp
            (-cP * (Real.log T)^2 / Real.log (Real.log T))) := by
  obtain ⟨p, Aneg, Apos, G, Cneg, cNeg, Cpos, cPos, CU, cU,
    hp, hpHalf, hAn, hAp, hG, hCn, hcn, hCp, hcp, hCU, hcU,
    hunit, hparam⟩ := j1_same_p_raw_small_of_C1 hC1 hξ
  refine ⟨p, hp, hpHalf, hunit, ?_⟩
  intro C hC
  obtain ⟨A₀, hA₀, hshift⟩ :=
    laneA2_induction_shift_threshold hAn hAp hG hC
  let D : ℝ := G * Apos
  let U : ℝ := max (3 * D) (D^2)
  let M : ℝ := (Real.log U)^2 / Real.log (Real.log 3)
  let CN : ℝ := G * Cneg
  let cN : ℝ := cNeg / 4
  let cP : ℝ := min cPos cU / 4
  let CP : ℝ := G * (Cpos + CU) + Real.exp (cP * M)
  have hD : 1 ≤ D := by dsimp [D]; nlinarith
  have hG0 : 0 ≤ G := by linarith
  have hCN : 0 < CN := by dsimp [CN]; positivity
  have hcN : 0 < cN := by dsimp [cN]; positivity
  have hcP : 0 < cP := by dsimp [cP]; positivity
  have hCP : 0 < CP := by dsimp [CP]; positivity
  refine ⟨A₀, CN, cN, CP, cP,
    hA₀, hCN, hcN, hCP, hcP, ?_⟩
  intro Ω _ P W hW K m hH i c T hT
  haveI : IsProbabilityMeasure P := hW.isProbabilityMeasure
  let B := Real.exp (C * Real.sqrt (K : ℝ))
  have hB : 1 ≤ B := Real.one_le_exp (mul_nonneg hC (Real.sqrt_nonneg _))
  have hL := (hshift K T)
  constructor
  · intro hStart
    obtain ⟨hTL, _⟩ := hL hStart
    have hDL : 1 ≤ Aneg * B^4 := by
      have hB4 : 1 ≤ B^4 := one_le_pow₀ hB
      nlinarith
    let sL : ℝ := T / (Aneg * B^4)
    have hsL : 3 < sL := (laneA2_shifted_sq_rate hDL hTL).1
    obtain ⟨hlow, _, _⟩ := hparam P W hW m B hB hH sL 4 hsL (by norm_num) i K c
    have hcancel : Aneg * B^4 * sL = T := by
      dsimp [sL]
      field_simp
    rw [hcancel] at hlow
    have hrate := laneA2_shifted_lower_tail_rate hDL hTL hCn.le hcn
    calc
      _ ≤ ENNReal.ofReal G * ENNReal.ofReal
            (Cneg * Real.exp (-cNeg * (Real.log sL)^2)) := hlow
      _ ≤ ENNReal.ofReal G * ENNReal.ofReal
            (Cneg * Real.exp (-(cNeg / 4) * (Real.log T)^2)) :=
          mul_le_mul_of_nonneg_left (ENNReal.ofReal_le_ofReal hrate) (zero_le)
      _ = ENNReal.ofReal (CN * Real.exp (-cN * (Real.log T)^2)) := by
          dsimp [CN, cN]
          rw [mul_assoc, ENNReal.ofReal_mul hG0]
  · by_cases hbig : U < T
    · have hTU : max (3 * D) (D^2) < T := hbig
      have hTUG : max (3 * G) (G^2) < T := by
        have hGD : G ≤ D := by dsimp [D]; nlinarith
        have h3 : 3 * G ≤ 3 * D := by nlinarith
        have hsq : G^2 ≤ D^2 := by nlinarith [sq_nonneg (D - G)]
        exact max_lt (h3.trans_lt ((le_max_left _ _).trans_lt hbig))
          (hsq.trans_lt ((le_max_right _ _).trans_lt hbig))
      let sU : ℝ := T / D
      have hsU : 3 < sU := (laneA2_shifted_sq_rate hD hTU).1
      obtain ⟨_, _, hupp⟩ := hparam P W hW m B hB hH 4 sU (by norm_num) hsU i K c
      have hcancel : G * (Apos * sU *
          LambdaN ξ W P m (ENNReal.ofReal p) *
          ellN ξ W P m (ENNReal.ofReal p)) =
          T * LambdaN ξ W P m (ENNReal.ofReal p) *
          ellN ξ W P m (ENNReal.ofReal p) := by
        dsimp [sU, D]
        field_simp
      rw [hcancel] at hupp
      have harg : Apos * sU = T / G := by
        dsimp [sU, D]
        field_simp
      have hrate : Cpos * Real.exp
            (-cPos * (Real.log sU)^2 / Real.log (Real.log sU)) +
          CU * Real.exp
            (-cU * (Real.log (Apos * sU))^2 /
              Real.log (Real.log (Apos * sU))) ≤
          (Cpos + CU) * Real.exp
            (-cP * (Real.log T)^2 / Real.log (Real.log T)) := by
        rw [harg]
        exact laneA2_shifted_upper_tail_rate hD hG hTU hTUG
          hCp.le hCU.le hcp hcU
      have hcoef : G * ((Cpos + CU) * Real.exp
            (-cP * (Real.log T)^2 / Real.log (Real.log T))) ≤
          CP * Real.exp (-cP * (Real.log T)^2 /
            Real.log (Real.log T)) := by
        have hle : G * (Cpos + CU) ≤ CP := by
          dsimp [CP]; linarith [Real.exp_pos (cP * M)]
        have h := mul_le_mul_of_nonneg_right hle
          (Real.exp_pos (-cP * (Real.log T)^2 /
            Real.log (Real.log T))).le
        nlinarith
      calc
        _ ≤ ENNReal.ofReal G * ENNReal.ofReal
              (Cpos * Real.exp
                (-cPos * (Real.log sU)^2 / Real.log (Real.log sU)) +
                CU * Real.exp
                (-cU * (Real.log (Apos * sU))^2 /
                  Real.log (Real.log (Apos * sU)))) := hupp
        _ ≤ ENNReal.ofReal G * ENNReal.ofReal
              ((Cpos + CU) * Real.exp
                (-cP * (Real.log T)^2 / Real.log (Real.log T))) :=
            mul_le_mul_of_nonneg_left (ENNReal.ofReal_le_ofReal hrate) (zero_le)
        _ = ENNReal.ofReal (G * ((Cpos + CU) * Real.exp
              (-cP * (Real.log T)^2 / Real.log (Real.log T)))) := by
            exact (ENNReal.ofReal_mul hG0).symm
        _ ≤ ENNReal.ofReal (CP * Real.exp
              (-cP * (Real.log T)^2 / Real.log (Real.log T))) :=
            ENNReal.ofReal_le_ofReal hcoef
    · have hTle : T ≤ U := le_of_not_gt hbig
      have hq : (Real.log T)^2 / Real.log (Real.log T) ≤ M :=
        laneA_bounded_log_rate hT hTle
      have hexp : 1 ≤ Real.exp (cP * M) * Real.exp
          (-cP * (Real.log T)^2 / Real.log (Real.log T)) := by
        rw [← Real.exp_add, ← Real.exp_zero]
        apply Real.exp_le_exp.mpr
        have := mul_nonneg hcP.le (sub_nonneg.mpr hq)
        calc
          0 ≤ cP * (M - (Real.log T)^2 /
              Real.log (Real.log T)) := this
          _ = cP * M + -cP * (Real.log T)^2 /
              Real.log (Real.log T) := by ring
      have hcoef : 1 ≤ CP * Real.exp
          (-cP * (Real.log T)^2 / Real.log (Real.log T)) := by
        have hle : Real.exp (cP * M) ≤ CP := by
          dsimp [CP]; nlinarith [mul_pos (by linarith : 0 < G) (by linarith : 0 < Cpos + CU)]
        exact hexp.trans (mul_le_mul_of_nonneg_right hle (Real.exp_pos _).le)
      calc
        _ ≤ 1 := prob_le_one
        _ = ENNReal.ofReal (1 : ℝ) := by norm_num
        _ ≤ ENNReal.ofReal (CP * Real.exp
              (-cP * (Real.log T)^2 / Real.log (Real.log T))) :=
            ENNReal.ofReal_le_ofReal hcoef

end SupercriticalLQGUniqueness.B2.DG20Conc
