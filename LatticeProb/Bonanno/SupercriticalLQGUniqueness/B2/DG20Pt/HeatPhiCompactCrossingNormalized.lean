/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.B2.DG20Pt.HeatPhiCompactCrossingNormalized at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Pt.HeatPhiCompactCrossingCoupling
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Pt.HeatMedianCompare
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Pt.NormalizedCostArithmetic

 

set_option autoImplicit false
noncomputable section

open MeasureTheory ProbabilityTheory Set Topology
open scoped ENNReal
open LQGMetric LQGMetric.DDDF LQGMetric.WhiteNoise LQGMetric.Blueprint

namespace SupercriticalLQGUniqueness.B2.DG20Pt

theorem dg20_heat_phi_compact_crossing_normalized_coupling
    (hPerc : SupercriticalLQGUniqueness.B2.Iface.DG20PercEstimate')
    (ξ : Ioi (0 : ℝ))
    (m : Ioi (0 : ℝ) → Ioi (0 : ℝ))
    (hm : ∀ ε, IsLFPPNormalizer ξ ε (m ε))
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (h : Ω → DistC)
    (hh : IsNormalizedWholePlaneGFF h P)
    (X : Ioi (0 : ℝ) → Ω → C(ℂ, ℝ))
    (hX : ∀ ε, IsHeatSmoothing P h ε (X ε))
    (K U A B : Set ℂ) (hK : IsCompact K)
    (hKsq : K ⊆ closedUnitSquare) (hUK : U ⊆ K)
    (ζ : ℝ) (hζ : 0 < ζ) :
    ∃ F ε₀ : ℝ, 0 < F ∧ 0 < ε₀ ∧
      ∀ ε : Ioo (0 : ℝ) 1, (ε : ℝ) < ε₀ →
        ∃ (Ω' : Type) (_ : MeasurableSpace Ω') (Q : Measure Ω')
          (W : WNSpace → Ω' → ℝ) (φ : Ω' → C(ℂ, ℝ))
          (R : Measure (Ω × C(ℂ, ℝ))),
          IsProbabilityMeasure Q ∧ IsWhiteNoise Q W ∧
          (∀ ω z, φ ω z = phiVer W Q ε 1 z ω) ∧
          IsProbabilityMeasure R ∧ R.map Prod.fst = P ∧ R.map Prod.snd = Q.map φ ∧
          R {p | ¬ (
            ENNReal.ofReal (m ⟨ε, ε.property.1⟩ : ℝ)⁻¹ *
              crossLenIn ξ (X ⟨ε, ε.property.1⟩ p.1) U A B ≤
              ENNReal.ofReal F *
                (ENNReal.ofReal (lambdaDelta ξ W Q ε)⁻¹ *
                  crossLenIn ξ p.2 U A B) ∧
            ENNReal.ofReal (lambdaDelta ξ W Q ε)⁻¹ *
              crossLenIn ξ p.2 U A B ≤
              ENNReal.ofReal F *
                (ENNReal.ofReal (m ⟨ε, ε.property.1⟩ : ℝ)⁻¹ *
                  crossLenIn ξ (X ⟨ε, ε.property.1⟩ p.1) U A B))} ≤
            ENNReal.ofReal ζ := by
  obtain ⟨Am, ε₁, hAm, hε₁, hmed⟩ :=
    dg20_heat_median_white_noise_compare_of_perc hPerc ξ m hm P h hh X hX
  obtain ⟨M, ε₂, hε₂, hcouple⟩ :=
    dg20_heat_phi_compact_crossing_coupling P h hh X hX
      ξ K U A B hK hKsq hUK ζ hζ
  let F : ℝ := Am * Real.exp (|(ξ : ℝ)| * M)
  have hF : 0 < F := mul_pos hAm (Real.exp_pos _)
  refine ⟨F, min ε₁ ε₂, hF, lt_min hε₁ hε₂, ?_⟩
  intro ε hε
  obtain ⟨Ω', iΩ', Q, W, φ, R, hQ, hW, hφ, hR, hfst, hsnd, hbad⟩ :=
    hcouple ⟨ε, ε.property.1⟩ (lt_of_lt_of_le hε (min_le_right _ _))
  letI : MeasurableSpace Ω' := iΩ'
  letI : IsProbabilityMeasure Q := hQ
  have hmedian := hmed ε (lt_of_lt_of_le hε (min_le_left _ _)) Q W hW
  have hLam : 0 < lambdaDelta ξ W Q ε :=
    S6Thm.lambdaDelta_pos_of_698 hW
      (dg20_non_dyadic_median_compare_of_perc hPerc ξ Q W hW) ε.property
  have hC0 : ENNReal.ofReal Am ≠ 0 := (ENNReal.ofReal_pos.mpr hAm).ne'
  have hCtop : ENNReal.ofReal Am ≠ ∞ := ENNReal.ofReal_ne_top
  have hmedE : (ENNReal.ofReal Am)⁻¹ * ENNReal.ofReal (lambdaDelta ξ W Q ε) ≤
        ENNReal.ofReal (m ⟨ε, ε.property.1⟩ : ℝ) ∧
      ENNReal.ofReal (m ⟨ε, ε.property.1⟩ : ℝ) ≤
        ENNReal.ofReal Am * ENNReal.ofReal (lambdaDelta ξ W Q ε) := by
    constructor
    · rw [← ENNReal.ofReal_inv_of_pos hAm, ← ENNReal.ofReal_mul (inv_nonneg.mpr hAm.le)]
      exact ENNReal.ofReal_le_ofReal hmedian.1
    · rw [← ENNReal.ofReal_mul hAm.le]
      exact ENNReal.ofReal_le_ofReal hmedian.2
  have hfactor : ENNReal.ofReal Am *
      ENNReal.ofReal (Real.exp (|(ξ : ℝ)| * M)) = ENNReal.ofReal F := by
    rw [← ENNReal.ofReal_mul hAm.le]
  have hsub :
      {p : Ω × C(ℂ, ℝ) | ¬ (
        ENNReal.ofReal (m ⟨ε, ε.property.1⟩ : ℝ)⁻¹ *
          crossLenIn ξ (X ⟨ε, ε.property.1⟩ p.1) U A B ≤
          ENNReal.ofReal F *
            (ENNReal.ofReal (lambdaDelta ξ W Q ε)⁻¹ * crossLenIn ξ p.2 U A B) ∧
        ENNReal.ofReal (lambdaDelta ξ W Q ε)⁻¹ * crossLenIn ξ p.2 U A B ≤
          ENNReal.ofReal F *
            (ENNReal.ofReal (m ⟨ε, ε.property.1⟩ : ℝ)⁻¹ *
              crossLenIn ξ (X ⟨ε, ε.property.1⟩ p.1) U A B))} ⊆
      {p | ¬ (
        crossLenIn ξ (X ⟨ε, ε.property.1⟩ p.1) U A B ≤
          ENNReal.ofReal (Real.exp (|(ξ : ℝ)| * M)) * crossLenIn ξ p.2 U A B ∧
        crossLenIn ξ p.2 U A B ≤
          ENNReal.ofReal (Real.exp (|(ξ : ℝ)| * M)) *
            crossLenIn ξ (X ⟨ε, ε.property.1⟩ p.1) U A B)} := by
    intro p hno hraw
    have hnorm := dg20_normalized_cost_compare
      (ENNReal.ofReal Am) (ENNReal.ofReal (Real.exp (|(ξ : ℝ)| * M)))
      (ENNReal.ofReal (m ⟨ε, ε.property.1⟩ : ℝ))
      (ENNReal.ofReal (lambdaDelta ξ W Q ε))
      (crossLenIn ξ (X ⟨ε, ε.property.1⟩ p.1) U A B)
      (crossLenIn ξ p.2 U A B) hC0 hCtop hmedE hraw
    rw [hfactor] at hnorm
    change ¬ (_ ∧ _) at hno
    rw [ENNReal.ofReal_inv_of_pos (m ⟨ε, ε.property.1⟩).property,
      ENNReal.ofReal_inv_of_pos hLam] at hno
    exact hno hnorm
  refine ⟨Ω', iΩ', Q, W, φ, R, hQ, hW, hφ, hR, hfst, hsnd, ?_⟩
  exact (measure_mono hsub).trans hbad

end SupercriticalLQGUniqueness.B2.DG20Pt
