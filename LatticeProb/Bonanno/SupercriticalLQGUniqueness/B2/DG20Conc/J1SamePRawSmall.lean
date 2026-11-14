/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.B2.DG20Conc.J1SamePRawSmall at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Conc.LaneA2UnitLong
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Conc.J1CoverUpper
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Conc.J1RectLaw

 

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

open MeasureTheory
open scoped ENNReal

namespace SupercriticalLQGUniqueness.B2.DG20Conc

open LQGMetric.DDDF LQGMetric.WhiteNoise LQGMetric.LFPP

universe u

theorem j1_same_p_raw_small_of_C1
    (hC1 : LaneBInputs.C1UnitBlockGeometry)
    {ξ : ℝ} (hξ : 0 < ξ) :
    ∃ p Aneg Apos G Cneg cNeg Cpos cPos CU cU : ℝ,
      0 < p ∧ p < 2⁻¹ ∧ 1 ≤ Aneg ∧ 1 ≤ Apos ∧ 1 ≤ G ∧
      0 < Cneg ∧ 0 < cNeg ∧ 0 < Cpos ∧ 0 < cPos ∧
      0 < CU ∧ 0 < cU ∧ LaneA2HasUnitTails.{u} ξ p ∧
      ∀ {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω)
        (W : WNSpace → Ω → ℝ) (hW : IsWhiteNoise P W)
        (m : ℕ) (B : ℝ) (hB : 1 ≤ B)
        (hΛ : LambdaN ξ W P m (ENNReal.ofReal p) ≤ B)
        (sL sU : ℝ) (hsL : 3 < sL) (hsU : 3 < sU) (i : Bool)
        (K : ℕ) (c : ℂ),
        P {ω | crossLenIn ξ (fun z => phiMN W P 0 m z ω)
          (laneCUnitUcross i) (laneCUnitInner i) (laneCUnitOuter i) <
          ENNReal.ofReal ((Aneg * B^4 * sL)⁻¹ *
            ellN ξ W P m (ENNReal.ofReal p))} ≤
          ENNReal.ofReal G * ENNReal.ofReal
            (Cneg * Real.exp (-cNeg * (Real.log sL)^2)) ∧
        P {ω | ENNReal.ofReal (G *
            (Apos * sU * LambdaN ξ W P m (ENNReal.ofReal p) *
              ellN ξ W P m (ENNReal.ofReal p))) <
          (lfppContMetric ξ (fun z => phiMN W P 0 m z ω)
            ((isPhiVersion_phiMN hW (Nat.zero_le m)).cont ω)).aroundDist
            (laneCUnitUaround i) (laneCUnitInner i)
            (laneCUnitOuter i)} ≤
          ENNReal.ofReal G * ENNReal.ofReal
            (Cpos * Real.exp
              (-cPos * (Real.log sU)^2 / Real.log (Real.log sU)) +
              CU * Real.exp
              (-cU * (Real.log (Apos * sU))^2 /
                Real.log (Real.log (Apos * sU)))) ∧
        P {ω | ENNReal.ofReal (G *
            (Apos * sU * LambdaN ξ W P m (ENNReal.ofReal p) *
              ellN ξ W P m (ENNReal.ofReal p))) <
          (lfppContMetric ξ (fun z => phiMN W P K (K + m)
            (((2 : ℝ)⁻¹ ^ K : ℝ) * z + c) ω)
            ((isPhiVersion_phiMN hW (by omega : K ≤ K + m)).cont ω |>.comp
              (show Continuous (fun z : ℂ =>
                (((2 : ℝ)⁻¹ ^ K : ℝ) * z + c)) by fun_prop))).aroundDist
            (laneCUnitUaround i) (laneCUnitInner i)
            (laneCUnitOuter i)} ≤
          ENNReal.ofReal G * ENNReal.ofReal
            (Cpos * Real.exp
              (-cPos * (Real.log sU)^2 / Real.log (Real.log sU)) +
            CU * Real.exp
              (-cU * (Real.log (Apos * sU))^2 /
                Real.log (Real.log (Apos * sU)))) := by
  obtain ⟨G, hG, hgeom⟩ := hC1
  obtain ⟨p, Aneg, Apos, Cneg, cNeg, Cpos, cPos,
    hp, hpHalf, hAn, hAp, hCn, hcn, hCp, hcp, hunitEx, hrect⟩ :=
      laneA2_repaired_rectangle_tails hξ
  obtain ⟨UN, un, CU, cU, hUN, hun, hCU, hcU, hunit⟩ := hunitEx
  refine ⟨p, Aneg, Apos, G, Cneg, cNeg, Cpos, cPos, CU, cU,
    hp, hpHalf, hAn, hAp, hG, hCn, hcn, hCp, hcp, hCU, hcU,
    ⟨UN, un, CU, cU, hUN, hun, hCU, hcU, hunit⟩, ?_⟩
  intro Ω _ P W hW m B hB hΛ sL sU hsL hsU i K c
  let a : ℝ := (Aneg * B^4 * sL)⁻¹ * ellN ξ W P m (ENNReal.ofReal p)
  let b : ℝ := Apos * sU * LambdaN ξ W P m (ENNReal.ofReal p) *
    ellN ξ W P m (ENNReal.ofReal p)
  let qlo : ℝ := Cneg * Real.exp (-cNeg * (Real.log sL)^2)
  let qhi : ℝ := Cpos * Real.exp
      (-cPos * (Real.log sU)^2 / Real.log (Real.log sU)) +
    CU * Real.exp
      (-cU * (Real.log (Apos * sU))^2 /
        Real.log (Real.log (Apos * sU)))
  have hlow (j : Bool) (v : Circle) (z : ℂ) :
      P {ω | T20B.mrectLen ξ (fun x => phiMN W P 0 m x ω)
        3 v z 1 3 < a} ≤ ENNReal.ofReal qlo :=
    (hrect P W hW m B hB hΛ sL hsL v z).1
  have hupp (j : Bool) (v : Circle) (z : ℂ) :
      P {ω | b < T20B.mrectLen ξ (fun x => phiMN W P 0 m x ω)
        (if j then 0 else 3) v z 3 1} ≤ ENNReal.ofReal qhi := by
    cases j
    · have h := (hrect P W hW m B hB hΛ sU hsU v z).2
      exact h.trans (ENNReal.ofReal_le_ofReal (by
        dsimp [qhi]
        have hh : 0 ≤ CU * Real.exp
            (-cU * (Real.log (Apos * sU))^2 /
              Real.log (Real.log (Apos * sU))) := by positivity
        linarith))
    · have hSU : 3 < Apos * sU := by
        have hs : 0 < sU := by linarith
        nlinarith
      have h := laneA2_unit_long_tail P hW hunit m (Apos * sU) hSU v z
      have h' : P {ω | b < T20B.mrectLen ξ
          (fun x => phiMN W P 0 m x ω) 0 v z 3 1} ≤
          ENNReal.ofReal (CU * Real.exp
            (-cU * (Real.log (Apos * sU))^2 /
              Real.log (Real.log (Apos * sU)))) := by
        simpa only [b, mul_assoc] using h
      exact h'.trans (ENNReal.ofReal_le_ofReal (by
        dsimp [qhi]
        have hh : 0 ≤ Cpos * Real.exp
            (-cPos * (Real.log sU)^2 / Real.log (Real.log sU)) := by positivity
        linarith))
  have hh := laneA2_cover_tail_of_rect_tails P hW (hgeom i)
    (fun v z => hlow i v z) (fun v z => hupp i v z)
  refine ⟨hh.1, hh.2, ?_⟩
  let Y : ℂ → Ω → ℝ := fun z ω => phiMN W P K (K + m)
    (((2 : ℝ)⁻¹ ^ K : ℝ) * z + c) ω
  have hKn : K ≤ K + m := by omega
  have hc : Continuous (fun z : ℂ =>
      (((2 : ℝ)⁻¹ ^ K : ℝ) * z + c)) := by fun_prop
  have hYc : ∀ ω, Continuous (fun z => Y z ω) :=
    fun ω => ((isPhiVersion_phiMN hW hKn).cont ω).comp hc
  change P {ω | ENNReal.ofReal (G * b) <
    (lfppContMetric ξ (fun z => Y z ω) (hYc ω)).aroundDist
      (laneCUnitUaround i) (laneCUnitInner i)
      (laneCUnitOuter i)} ≤ ENNReal.ofReal G * ENNReal.ofReal qhi
  apply j1_cover_upper_of_rect_tails P Y hYc (hgeom i)
  intro v z
  change P {ω | T20B.mrectLen ξ (fun x => Y x ω)
    (if i then 0 else 3) v z 3 1 ∈ Set.Ioi b} ≤ ENNReal.ofReal qhi
  dsimp only [Y]
  rw [j1_mrectLen_field_law P W hW hKn ξ
    (if i then 0 else 3) v z c 3 1 measurableSet_Ioi]
  simpa only [Nat.add_sub_cancel_left, Set.mem_Ioi] using hupp i v z

end SupercriticalLQGUniqueness.B2.DG20Conc
