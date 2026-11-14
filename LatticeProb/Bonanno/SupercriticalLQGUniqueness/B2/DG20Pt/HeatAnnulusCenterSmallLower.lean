/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.B2.DG20Pt.HeatAnnulusCenterSmallLower at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Pt.HeatPhiCompactCrossingNormalized
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Pt.HeatPhiAnnulusTailLaw
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Pt.HeatClosedBallSquare
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Pt.CouplingCostTails
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.PfeAxioms.HeatVersionMeasurable

 

set_option autoImplicit false
noncomputable section

open MeasureTheory ProbabilityTheory Set Metric
open scoped ENNReal
open LQGMetric LQGMetric.DDDF LQGMetric.WhiteNoise LQGMetric.Blueprint

namespace SupercriticalLQGUniqueness.B2.DG20Pt

theorem dg20_heat_center_annulus_small_lower_of_perc
    (hPerc : SupercriticalLQGUniqueness.B2.Iface.DG20PercEstimate')
    (ξ : Ioi (0 : ℝ))
    (m : Ioi (0 : ℝ) → Ioi (0 : ℝ))
    (hm : ∀ ε, IsLFPPNormalizer ξ ε (m ε))
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (h : Ω → DistC)
    (hh : IsNormalizedWholePlaneGFF h P)
    (X : Ioi (0 : ℝ) → Ω → C(ℂ, ℝ))
    (hX : ∀ ε, IsHeatSmoothing P h ε (X ε))
    (d : ℝ) (hd : 0 < d) (hd2 : d ≤ 1 / 2)
    (η : ℝ) (hη : 0 < η) :
    let c : ℂ := Complex.mk (1 / 2) (1 / 2)
    ∃ T ε₀ : ℝ, 0 < T ∧ 0 < ε₀ ∧
      ∀ ε : Ioo (0 : ℝ) 1, (ε : ℝ) < ε₀ →
        P {ω | ENNReal.ofReal (m ⟨ε, ε.property.1⟩ : ℝ)⁻¹ *
          crossLenIn ξ (X ⟨ε, ε.property.1⟩ ω)
            (closedBall c d) (sphere c (d / 16))
            (sphere c (3 * d / 4)) < ENNReal.ofReal T⁻¹} ≤
          ENNReal.ofReal η := by
  dsimp only
  let c : ℂ := Complex.mk (1 / 2) (1 / 2)
  let K : Set ℂ := closedUnitSquare
  let U : Set ℂ := closedBall c d
  let A : Set ℂ := sphere c (d / 16)
  let B : Set ℂ := sphere c (3 * d / 4)
  have hUK : U ⊆ K := dg20_closedBall_squareCenter_subset_square hd2
  have hη2 : 0 < η / 2 := half_pos hη
  obtain ⟨N, hN, hwhite⟩ :=
    dg20_white_noise_annulus_lower_uniform_of_perc hPerc ξ c d hd (η / 2) hη2
  obtain ⟨F, ε₀, hF, hε₀, hcouple⟩ :=
    dg20_heat_phi_compact_crossing_normalized_coupling hPerc ξ m hm
      P h hh X hX K U A B LQGMetric.DFGPS.isCompact_closedUnitSquare Subset.rfl hUK
      (η / 2) hη2
  let T : ℝ := 4 * (F + 1) * (N + 1)
  have hT : 0 < T := by dsimp [T]; positivity
  have hTN : 2 * F * N ≤ T := by
    dsimp [T]
    nlinarith [mul_nonneg hF.le (by linarith : 0 ≤ N)]
  have hInv : F * T⁻¹ ≤ (2 * N)⁻¹ := by
    have h2N : 0 < 2 * N := by linarith
    have h := (div_le_div_iff₀ hT h2N).2 (by nlinarith [hTN] :
      F * (2 * N) ≤ 1 * T)
    simpa only [div_eq_mul_inv, one_div, one_mul] using h
  have hCL : ENNReal.ofReal F * ENNReal.ofReal T⁻¹ ≤
      ENNReal.ofReal ((2 * N)⁻¹) := by
    rw [← ENNReal.ofReal_mul hF.le]
    exact ENNReal.ofReal_le_ofReal hInv
  have hsum : ENNReal.ofReal (η / 2) + ENNReal.ofReal (η / 2) =
      ENNReal.ofReal η := by
    rw [← ENNReal.ofReal_add hη2.le hη2.le]
    congr 1
    ring
  refine ⟨T, ε₀, hT, hε₀, ?_⟩
  intro ε hε
  obtain ⟨Ω', iΩ', Q, W, φ, R, hQ, hW, hφ, hR, hfst, hsnd, hbad⟩ :=
    hcouple ε hε
  letI : MeasurableSpace Ω' := iΩ'
  letI : IsProbabilityMeasure Q := hQ
  have htail := hwhite Q W hW ε
  let Aheat : Ω → ℝ≥0∞ := fun ω =>
    ENNReal.ofReal (m ⟨ε, ε.property.1⟩ : ℝ)⁻¹ *
      crossLenIn ξ (X ⟨ε, ε.property.1⟩ ω) U A B
  let Bphi : C(ℂ, ℝ) → ℝ≥0∞ := fun ψ =>
    ENNReal.ofReal (lambdaDelta ξ W Q ε)⁻¹ * crossLenIn ξ ψ U A B
  have hBm : Measurable Bphi :=
    measurable_const.mul (measurable_crossLenIn
      (Y := fun y (ψ : C(ℂ, ℝ)) => ψ y)
      (isCompact_closedBall c d) (fun ψ => ψ.continuous)
      (fun y => ContinuousMap.measurable_eval y))
  have hAm : AEMeasurable Aheat P :=
    (measurable_const.mul (measurable_crossLenIn
      (Y := fun y (ψ : C(ℂ, ℝ)) => ψ y)
      (isCompact_closedBall c d) (fun ψ => ψ.continuous)
      (fun y => ContinuousMap.measurable_eval y))).comp_aemeasurable
        (B2.PfeAxioms.aemeasurable_heat_smoothing_version P h hh
          ⟨ε, ε.property.1⟩ (X ⟨ε, ε.property.1⟩) (hX ⟨ε, ε.property.1⟩))
  have hloQ : (Q.map φ) {ψ | Bphi ψ ≤ ENNReal.ofReal ((2 * N)⁻¹)} ≤
      ENNReal.ofReal (η / 2) := by
    simpa only [Bphi, U, A, B] using
      dg20_phi_annulus_normalized_lower_tail_law hPerc Q W hW ξ ε φ hφ
        c d hd N (η / 2) hN htail
  have hhiQ : (Q.map φ) {ψ | (⊤ : ℝ≥0∞) < Bphi ψ} ≤
      ENNReal.ofReal (η / 2) := by
    have he : {ψ | (⊤ : ℝ≥0∞) < Bphi ψ} = ∅ := by simp
    rw [he, measure_empty]
    exact zero_le
  obtain ⟨hlo, _⟩ := dg20_coupling_cost_tails P (Q.map φ) R hfst hsnd
    Aheat Bphi hAm hBm (ENNReal.ofReal F)
    (ENNReal.ofReal ((2 * N)⁻¹)) (⊤ : ℝ≥0∞)
    (ENNReal.ofReal T⁻¹) (⊤ : ℝ≥0∞)
    (ENNReal.ofReal (η / 2)) hCL le_top
    (by simpa only [Aheat, Bphi] using hbad) hloQ hhiQ
  simpa only [Aheat, U, A, B, hsum] using hlo

end SupercriticalLQGUniqueness.B2.DG20Pt
