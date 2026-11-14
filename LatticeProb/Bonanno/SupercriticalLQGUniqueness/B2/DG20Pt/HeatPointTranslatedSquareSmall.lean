/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.B2.DG20Pt.HeatPointTranslatedSquareSmall at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Pt.HeatPointSquareSmallTight
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Pt.HeatTranslateVersion
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Pt.TranslatedCostBadEvent
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Pt.SameSpaceCostTails

 

set_option autoImplicit false
noncomputable section

open MeasureTheory ProbabilityTheory Set Topology
open scoped ENNReal
open LQGMetric LQGMetric.DDDF LQGMetric.Blueprint

namespace SupercriticalLQGUniqueness.B2.DG20Pt

theorem dg20_heat_point_translated_square_small_tails_of_inputs
    (hPerc : SupercriticalLQGUniqueness.B2.Iface.DG20PercEstimate')
    (hExp : SupercriticalLQGUniqueness.B2.Iface.DG20ExponentRelation)
    (hPos : SupercriticalLQGUniqueness.B2.Iface.DG20ExponentPositive)
    (ξ : Ioi (0 : ℝ)) (Qexp : ℝ) (hQ : IsLFPPExponent ξ Qexp)
    (m : Ioi (0 : ℝ) → Ioi (0 : ℝ))
    (hm : ∀ ε, IsLFPPNormalizer ξ ε (m ε))
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (h : Ω → DistC)
    (hh : IsNormalizedWholePlaneGFF h P)
    (X : Ioi (0 : ℝ) → Ω → C(ℂ, ℝ))
    (hX : ∀ ε, IsHeatSmoothing P h ε (X ε))
    (a : ℂ) (U : Set ℂ) (hU : IsOpen U) (hUc : IsConnected U)
    (hUsq : U ⊆ closedUnitSquare)
    (z w : ℂ) (hz : z ∈ U) (hw : w ∈ U) (hzw : z ≠ w)
    (η : ℝ) (hη : 0 < η) :
    ∃ T ε₀ : ℝ, 0 < T ∧ 0 < ε₀ ∧
      ∀ ε : Ioo (0 : ℝ) 1, (ε : ℝ) < ε₀ →
        P {ω | ENNReal.ofReal T <
          ENNReal.ofReal (m ⟨ε, ε.property.1⟩ : ℝ)⁻¹ *
            crossLenIn ξ (X ⟨ε, ε.property.1⟩ ω)
              ((· + a) '' U) {z + a} {w + a}} ≤ ENNReal.ofReal η ∧
        P {ω | ENNReal.ofReal (m ⟨ε, ε.property.1⟩ : ℝ)⁻¹ *
            crossLenIn ξ (X ⟨ε, ε.property.1⟩ ω)
              ((· + a) '' U) {z + a} {w + a} <
              ENNReal.ofReal T⁻¹} ≤ ENNReal.ofReal η := by
  let g : Ω → DistC := fun ω =>
    addConst (affineComp 1 a (h ω)) (-circleAvg (h ω) 1 a)
  have hg : IsNormalizedWholePlaneGFF g P :=
    (dg20_heat_translate_normalized P h hh a 1 one_pos).1
  obtain ⟨Y, hY, hYeq⟩ := dg20_exists_translated_heat_family P h hh X hX a
  let c : Ω → ℝ := fun ω => circleAvg (h ω) 1 a
  have hcm : Measurable c :=
    (measurable_circleAvg_left 1 a).comp hh.1.measurable
  have hthird : 0 < η / 3 := by linarith
  obtain ⟨M, hM, hctail⟩ := dg20_real_random_tail P c hcm (η / 3) hthird
  obtain ⟨N, ε₀, hN, hε₀, hYtail⟩ :=
    dg20_heat_point_square_small_tails_of_inputs hPerc hExp hPos
      ξ Qexp hQ m hm P g hg Y hY U hU hUc hUsq
      z w hz hw hzw (η / 3) hthird
  let C : ℝ := Real.exp (|(ξ : ℝ)| * M)
  have hC : 0 < C := Real.exp_pos _
  let T : ℝ := 4 * (C + 1) * (N + 1)
  have hT : 0 < T := by dsimp [T]; positivity
  have hTN : 2 * C * N ≤ T := by
    dsimp [T]
    nlinarith [mul_nonneg hC.le hN.le]
  have hInv : C * T⁻¹ ≤ (2 * N)⁻¹ := by
    have h2N : 0 < 2 * N := by positivity
    have h := (div_le_div_iff₀ hT h2N).2 (by nlinarith [hTN] :
      C * (2 * N) ≤ 1 * T)
    simpa only [div_eq_mul_inv, one_div, one_mul] using h
  have hsmall : (2 * N)⁻¹ < N⁻¹ := by
    have h := one_div_lt_one_div_of_lt hN (by nlinarith : N < 2 * N)
    simpa only [one_div] using h
  have hsmallE : ENNReal.ofReal ((2 * N)⁻¹) < ENNReal.ofReal N⁻¹ :=
    (ENNReal.ofReal_lt_ofReal_iff (inv_pos.mpr hN)).2 hsmall
  have hCL : ENNReal.ofReal C * ENNReal.ofReal T⁻¹ ≤
      ENNReal.ofReal ((2 * N)⁻¹) := by
    rw [← ENNReal.ofReal_mul hC.le]
    exact ENNReal.ofReal_le_ofReal hInv
  have hCH : ENNReal.ofReal C * ENNReal.ofReal N ≤ ENNReal.ofReal T := by
    rw [← ENNReal.ofReal_mul hC.le]
    exact ENNReal.ofReal_le_ofReal (by linarith [hTN, mul_nonneg hC.le hN.le])
  have htwothirds : ENNReal.ofReal (η / 3) + ENNReal.ofReal (η / 3) ≤
      ENNReal.ofReal η := by
    rw [← ENNReal.ofReal_add hthird.le]
    exact ENNReal.ofReal_le_ofReal (by linarith)
    all_goals positivity
  refine ⟨T, ε₀, hT, hε₀, ?_⟩
  intro ε hε
  let e : Ioi (0 : ℝ) := ⟨ε, ε.property.1⟩
  let b : ℝ≥0∞ := ENNReal.ofReal (m e : ℝ)⁻¹
  let A : Ω → ℝ≥0∞ := fun ω => b *
    crossLenIn ξ (X e ω) ((· + a) '' U) {z + a} {w + a}
  let B : Ω → ℝ≥0∞ := fun ω => b * crossLenIn ξ (Y e ω) U {z} {w}
  have hbad : P {ω | ¬ (A ω ≤ ENNReal.ofReal C * B ω ∧
      B ω ≤ ENNReal.ofReal C * A ω)} ≤ ENNReal.ofReal (η / 3) := by
    simpa only [A, B, b, C, e] using
      dg20_translated_cost_bad_event P ξ (X e) (Y e) c U z w a b M (η / 3)
        hM.le (hYeq e) hctail
  obtain ⟨hhiY, hloY⟩ := hYtail ε hε
  have hloY' : P {ω | B ω ≤ ENNReal.ofReal ((2 * N)⁻¹)} ≤
      ENNReal.ofReal (η / 3) := by
    calc
      _ ≤ P {ω | B ω < ENNReal.ofReal N⁻¹} :=
        measure_mono (by intro ω hω; exact lt_of_le_of_lt hω hsmallE)
      _ ≤ ENNReal.ofReal (η / 3) := by simpa only [B, b, e] using hloY
  have hhiY' : P {ω | ENNReal.ofReal N < B ω} ≤
      ENNReal.ofReal (η / 3) := by simpa only [B, b, e] using hhiY
  obtain ⟨hloX, hhiX⟩ := dg20_same_space_cost_tails P A B
    (ENNReal.ofReal C) (ENNReal.ofReal ((2 * N)⁻¹))
    (ENNReal.ofReal N) (ENNReal.ofReal T⁻¹) (ENNReal.ofReal T)
    (ENNReal.ofReal (η / 3)) hCL hCH hbad hloY' hhiY'
  constructor
  · simpa only [A, b, e] using hhiX.trans htwothirds
  · simpa only [A, b, e] using hloX.trans htwothirds

end SupercriticalLQGUniqueness.B2.DG20Pt
