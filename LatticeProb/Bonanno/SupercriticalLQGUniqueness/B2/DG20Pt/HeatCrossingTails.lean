/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.B2.DG20Pt.HeatCrossingTails at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Pt.CouplingCostTails
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Pt.HeatCrossingAE
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Pt.PhiCrossingTailLaw

 

set_option autoImplicit false
noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal
open LQGMetric LQGMetric.DDDF LQGMetric.WhiteNoise

namespace SupercriticalLQGUniqueness.B2.DG20Pt

theorem dg20_heat_square_crossing_tails_of_perc
    (hPerc : SupercriticalLQGUniqueness.B2.Iface.DG20PercEstimate')
    (ξ : Ioi (0 : ℝ))
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (h : Ω → DistC)
    (hh : IsNormalizedWholePlaneGFF h P)
    (X : Ioi (0 : ℝ) → Ω → C(ℂ, ℝ))
    (hX : ∀ ε, IsHeatSmoothing P h ε (X ε)) :
    ∃ M s ε₀ : ℝ, 0 < ε₀ ∧
      ∀ ε : Ioo (0 : ℝ) 1, (ε : ℝ) < ε₀ →
        ∀ {Ω' : Type} [MeasurableSpace Ω'] (Q : Measure Ω')
          [IsProbabilityMeasure Q] (W : WNSpace → Ω' → ℝ),
          IsWhiteNoise Q W →
          let C : ℝ≥0∞ := ENNReal.ofReal (Real.exp (|(ξ : ℝ)| * M))
          let bLo : ℝ≥0∞ := ENNReal.ofReal
            (Real.exp (-s) * lambdaDelta ξ W Q ε)
          let bHi : ℝ≥0∞ := ENNReal.ofReal
            (Real.exp s * lambdaDelta ξ W Q ε)
          P {ω | lfppCrossingLength ξ (X ⟨ε, ε.property.1⟩ ω) < C⁻¹ * bLo} ≤
            ENNReal.ofReal (1 / 4 : ℝ) ∧
          P {ω | C * bHi < lfppCrossingLength ξ (X ⟨ε, ε.property.1⟩ ω)} ≤
            ENNReal.ofReal (1 / 4 : ℝ) := by
  obtain ⟨s, hs, htail⟩ :=
    dg20_real_square_cross_tails_small_uniform hPerc ξ (1 / 8) (by norm_num)
  obtain ⟨M, ε₁, hε₁, hcouple⟩ :=
    dg20_heat_phi_square_crossing_coupling P h hh X hX ξ (1 / 8) (by norm_num)
  refine ⟨M, s, min ε₁ 1, lt_min hε₁ one_pos, ?_⟩
  intro ε hε Ω' _ Q _ W hW
  let C : ℝ≥0∞ := ENNReal.ofReal (Real.exp (|(ξ : ℝ)| * M))
  let bLo : ℝ≥0∞ := ENNReal.ofReal
    (Real.exp (-s) * lambdaDelta ξ W Q ε)
  let bHi : ℝ≥0∞ := ENNReal.ofReal
    (Real.exp s * lambdaDelta ξ W Q ε)
  have hC0 : C ≠ 0 := (ENNReal.ofReal_pos.mpr (Real.exp_pos _)).ne'
  have hCtop : C ≠ ∞ := ENNReal.ofReal_ne_top
  have hε₁ : (ε : ℝ) < ε₁ := lt_of_lt_of_le hε (min_le_left _ _)
  obtain ⟨Ω₂, iΩ₂, Q₂, W₂, φ, R, hQ₂, hW₂, hφ, hR, hfst, hsnd, hbad⟩ :=
    hcouple ⟨ε, ε.property.1⟩ hε₁
  letI : MeasurableSpace Ω₂ := iΩ₂
  letI : IsProbabilityMeasure Q₂ := hQ₂
  have htail₂ := htail Q₂ W₂ hW₂ ε
  have hmaptail := dg20_phi_square_crossing_tail_law Q₂ W₂ hW₂ ξ ε φ hφ
    s (1 / 8) htail₂
  have hLam : lambdaDelta ξ W Q ε = lambdaDelta ξ W₂ Q₂ ε :=
    lambdaDelta_eq_of_whiteNoise hW hW₂ ξ ε ε.property.1 ε.property.2.le
  have hAe := dg20_aemeasurable_heat_crossing P h hh ⟨ε, ε.property.1⟩
    (X ⟨ε, ε.property.1⟩) (hX ⟨ε, ε.property.1⟩) ξ
  have hmain := dg20_coupling_cost_tails P (Q₂.map φ) R hfst hsnd
    (fun ω => lfppCrossingLength ξ (X ⟨ε, ε.property.1⟩ ω))
    (fun ψ => lfppCrossingLength ξ ψ)
    hAe (dg20_measurable_lfppCrossingLength ξ)
    C bLo bHi (C⁻¹ * bLo) (C * bHi) (ENNReal.ofReal (1 / 8 : ℝ))
    (by exact (ENNReal.mul_inv_cancel_left hC0 hCtop).le)
    le_rfl
    (by simpa only [C] using hbad)
    (by simpa only [bLo, hLam] using hmaptail.1)
    (by simpa only [bHi, hLam] using hmaptail.2)
  have hsum : ENNReal.ofReal (1 / 8 : ℝ) + ENNReal.ofReal (1 / 8 : ℝ) =
      ENNReal.ofReal (1 / 4 : ℝ) := by
    rw [← ENNReal.ofReal_add (by norm_num) (by norm_num)]
    norm_num
  simpa only [C, bLo, bHi, hsum] using hmain

end SupercriticalLQGUniqueness.B2.DG20Pt
