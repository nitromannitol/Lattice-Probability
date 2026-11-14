/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.B2.DG20Pt.HeatPointSquareSmallTight at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Pt.PhiPointTailLaw
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Pt.CouplingCostTails
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.PfeAxioms.HeatVersionMeasurable

 

set_option autoImplicit false
noncomputable section

open MeasureTheory ProbabilityTheory Set Topology
open scoped ENNReal
open LQGMetric LQGMetric.LFPP LQGMetric.DDDF LQGMetric.WhiteNoise

namespace SupercriticalLQGUniqueness.B2.DG20Pt

theorem dg20_heat_point_square_small_tails_of_inputs
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
    (U : Set ℂ) (hU : IsOpen U) (hUc : IsConnected U)
    (hUsq : U ⊆ LQGMetric.Blueprint.closedUnitSquare)
    (z w : ℂ) (hz : z ∈ U) (hw : w ∈ U) (hzw : z ≠ w)
    (η : ℝ) (hη : 0 < η) :
    ∃ T ε₀ : ℝ, 0 < T ∧ 0 < ε₀ ∧
      ∀ ε : Ioo (0 : ℝ) 1, (ε : ℝ) < ε₀ →
        P {ω | ENNReal.ofReal T <
          ENNReal.ofReal (m ⟨ε, ε.property.1⟩ : ℝ)⁻¹ *
            crossLenIn ξ (X ⟨ε, ε.property.1⟩ ω) U {z} {w}} ≤
          ENNReal.ofReal η ∧
        P {ω | ENNReal.ofReal (m ⟨ε, ε.property.1⟩ : ℝ)⁻¹ *
            crossLenIn ξ (X ⟨ε, ε.property.1⟩ ω) U {z} {w} <
              ENNReal.ofReal T⁻¹} ≤ ENNReal.ofReal η := by
  obtain ⟨N, hN, hwhite⟩ :=
    dg20_white_noise_point_tails_uniform_of_inputs hPerc hExp hPos
      ξ Qexp hQ U hU hUc z w hz hw hzw (η / 2) (half_pos hη)
  obtain ⟨F, ε₀, hF, hε₀, hcouple⟩ :=
    dg20_heat_phi_point_square_normalized_coupling hPerc ξ m hm
      P h hh X hX U hUsq z w (η / 2) (half_pos hη)
  let T : ℝ := 4 * (F + 1) * (N + 1)
  have hT : 0 < T := by dsimp [T]; positivity
  have hTN : F * N ≤ T := by
    dsimp [T]
    nlinarith [mul_nonneg hF.le hN.le]
  have hTN2 : 2 * F * N ≤ T := by
    dsimp [T]
    nlinarith [mul_nonneg hF.le hN.le]
  have hInv : F * T⁻¹ ≤ (2 * N)⁻¹ := by
    have h2N : 0 < 2 * N := by positivity
    have h := (div_le_div_iff₀ hT h2N).2 (by nlinarith [hTN2] :
      F * (2 * N) ≤ 1 * T)
    simpa only [div_eq_mul_inv, one_div, one_mul] using h
  have hsmall : (2 * N)⁻¹ < N⁻¹ := by
    have h := one_div_lt_one_div_of_lt hN (by nlinarith : N < 2 * N)
    simpa only [one_div] using h
  have hsmallE : ENNReal.ofReal ((2 * N)⁻¹) < ENNReal.ofReal N⁻¹ :=
    (ENNReal.ofReal_lt_ofReal_iff (inv_pos.mpr hN)).2 hsmall
  have hCL : ENNReal.ofReal F * ENNReal.ofReal T⁻¹ ≤
      ENNReal.ofReal ((2 * N)⁻¹) := by
    rw [← ENNReal.ofReal_mul hF.le]
    exact ENNReal.ofReal_le_ofReal hInv
  have hCH : ENNReal.ofReal F * ENNReal.ofReal N ≤ ENNReal.ofReal T := by
    rw [← ENNReal.ofReal_mul hF.le]
    exact ENNReal.ofReal_le_ofReal hTN
  refine ⟨T, ε₀, hT, hε₀, ?_⟩
  intro ε hε
  obtain ⟨Ω', iΩ', Q, W, φ, R, hQ', hW, hφ, hR, hfst, hsnd, hbad⟩ :=
    hcouple ε hε
  letI : MeasurableSpace Ω' := iΩ'
  letI : IsProbabilityMeasure Q := hQ'
  obtain ⟨hhiW, hloW⟩ := hwhite Q W hW ε
  obtain ⟨hhiQ, hloQ⟩ := dg20_phi_normalized_point_tail_law Q W hW
    ξ ε φ hφ U hU z w N (η / 2) ⟨hhiW, hloW⟩
  let A : Ω → ℝ≥0∞ := fun ω =>
    ENNReal.ofReal (m ⟨ε, ε.property.1⟩ : ℝ)⁻¹ *
      crossLenIn ξ (X ⟨ε, ε.property.1⟩ ω) U {z} {w}
  let B : C(ℂ, ℝ) → ℝ≥0∞ := fun ψ =>
    ENNReal.ofReal (lambdaDelta ξ W Q ε)⁻¹ *
      crossLenIn ξ ψ U {z} {w}
  have hBm : Measurable B :=
    measurable_const.mul (pt_dist_measurable_crossLenIn_open ξ
      U {z} {w} hU (fun ψ => ψ.continuous)
      (fun y => (continuous_eval_const y).measurable))
  have hAm : AEMeasurable A P :=
    (measurable_const.mul (pt_dist_measurable_crossLenIn_open ξ
      U {z} {w} hU (fun ψ : C(ℂ, ℝ) => ψ.continuous)
      (fun y => (continuous_eval_const y).measurable))).comp_aemeasurable
      (B2.PfeAxioms.aemeasurable_heat_smoothing_version P h hh
        ⟨ε, ε.property.1⟩ (X ⟨ε, ε.property.1⟩) (hX ⟨ε, ε.property.1⟩))
  have hloQ' : (Q.map φ) {ψ | B ψ ≤ ENNReal.ofReal ((2 * N)⁻¹)} ≤
      ENNReal.ofReal (η / 2) := by
    calc
      (Q.map φ) {ψ | B ψ ≤ ENNReal.ofReal ((2 * N)⁻¹)} ≤
        (Q.map φ) {ψ | B ψ < ENNReal.ofReal N⁻¹} :=
          measure_mono (by intro ψ hψ; exact lt_of_le_of_lt hψ hsmallE)
      _ ≤ ENNReal.ofReal (η / 2) := hloQ
  have hmain := dg20_coupling_cost_tails P (Q.map φ) R hfst hsnd
    A B hAm hBm (ENNReal.ofReal F)
    (ENNReal.ofReal ((2 * N)⁻¹)) (ENNReal.ofReal N)
    (ENNReal.ofReal T⁻¹) (ENNReal.ofReal T)
    (ENNReal.ofReal (η / 2)) hCL hCH
    (by simpa only [A, B] using hbad)
    hloQ' hhiQ
  have hsum : ENNReal.ofReal (η / 2) + ENNReal.ofReal (η / 2) =
      ENNReal.ofReal η := by
    rw [← ENNReal.ofReal_add (half_pos hη).le (half_pos hη).le]
    congr 1
    ring
  have hmain' := hmain
  rw [hsum] at hmain'
  simpa only [A] using ⟨hmain'.2, hmain'.1⟩

end SupercriticalLQGUniqueness.B2.DG20Pt
