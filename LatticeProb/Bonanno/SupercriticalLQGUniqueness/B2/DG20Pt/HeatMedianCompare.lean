/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.B2.DG20Pt.HeatMedianCompare at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Pt.HeatCrossingTails
import LatticeProb.Bonanno.LQGMetric.Papers.DDDF.S6Thm11

 

set_option autoImplicit false
noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal
open LQGMetric LQGMetric.DDDF LQGMetric.WhiteNoise

namespace SupercriticalLQGUniqueness.B2.DG20Pt

theorem dg20_heat_median_white_noise_compare_of_perc
    (hPerc : SupercriticalLQGUniqueness.B2.Iface.DG20PercEstimate')
    (ξ : Ioi (0 : ℝ))
    (m : Ioi (0 : ℝ) → Ioi (0 : ℝ))
    (hm : ∀ ε, IsLFPPNormalizer ξ ε (m ε))
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (h : Ω → DistC)
    (hh : IsNormalizedWholePlaneGFF h P)
    (X : Ioi (0 : ℝ) → Ω → C(ℂ, ℝ))
    (hX : ∀ ε, IsHeatSmoothing P h ε (X ε)) :
    ∃ A ε₀ : ℝ, 0 < A ∧ 0 < ε₀ ∧
      ∀ ε : Ioo (0 : ℝ) 1, (ε : ℝ) < ε₀ →
        ∀ {Ω' : Type} [MeasurableSpace Ω'] (Q : Measure Ω')
          [IsProbabilityMeasure Q] (W : WNSpace → Ω' → ℝ),
          IsWhiteNoise Q W →
          A⁻¹ * lambdaDelta ξ W Q ε ≤ (m ⟨ε, ε.property.1⟩ : ℝ) ∧
          (m ⟨ε, ε.property.1⟩ : ℝ) ≤ A * lambdaDelta ξ W Q ε := by
  obtain ⟨M, s, ε₀, hε₀, htail⟩ :=
    dg20_heat_square_crossing_tails_of_perc hPerc ξ P h hh X hX
  let a : ℝ := |(ξ : ℝ)| * M
  let A : ℝ := Real.exp (a + s)
  have hA : 0 < A := Real.exp_pos _
  refine ⟨A, ε₀, hA, hε₀, ?_⟩
  intro ε hε Ω' _ Q _ W hW
  have hLam : 0 < lambdaDelta ξ W Q ε :=
    S6Thm.lambdaDelta_pos_of_698 hW
      (dg20_non_dyadic_median_compare_of_perc hPerc ξ Q W hW) ε.property
  let C : ℝ≥0∞ := ENNReal.ofReal (Real.exp a)
  let bLo : ℝ≥0∞ := ENNReal.ofReal
    (Real.exp (-s) * lambdaDelta ξ W Q ε)
  let bHi : ℝ≥0∞ := ENNReal.ofReal
    (Real.exp s * lambdaDelta ξ W Q ε)
  obtain ⟨hlo, hhi⟩ := htail ε hε Q W hW
  have hmed : IsMedian P
      (fun ω => lfppCrossingLength ξ (X ⟨ε, ε.property.1⟩ ω))
      (ENNReal.ofReal (m ⟨ε, ε.property.1⟩ : ℝ)) :=
    hm ⟨ε, ε.property.1⟩ P h hh (X ⟨ε, ε.property.1⟩)
      (hX ⟨ε, ε.property.1⟩)
  have hquarter : ENNReal.ofReal (1 / 4 : ℝ) < 2⁻¹ := by
    have hhalf : ENNReal.ofReal (1 / 2 : ℝ) = (2 : ℝ≥0∞)⁻¹ := by
      rw [show (1 / 2 : ℝ) = 2⁻¹ by norm_num,
        ENNReal.ofReal_inv_of_pos (by norm_num)]
      norm_num
    rw [← hhalf]
    exact (ENNReal.ofReal_lt_ofReal_iff (by norm_num)).2 (by norm_num)
  obtain ⟨hloMed, hhiMed⟩ :=
    dg20_median_between_strict_half_tails P _ _ _ _ hmed
      (lt_of_le_of_lt (by simpa only [C, a, bLo] using hlo) hquarter)
      (lt_of_le_of_lt (by simpa only [C, a, bHi] using hhi) hquarter)
  have hLoEq : C⁻¹ * bLo = ENNReal.ofReal (A⁻¹ * lambdaDelta ξ W Q ε) := by
    rw [show C⁻¹ = ENNReal.ofReal (Real.exp a)⁻¹ from
      (ENNReal.ofReal_inv_of_pos (Real.exp_pos a)).symm]
    rw [← ENNReal.ofReal_mul (inv_nonneg.mpr (Real.exp_pos a).le)]
    congr 1
    dsimp [A]
    rw [Real.exp_add, Real.exp_neg]
    field_simp
  have hHiEq : C * bHi = ENNReal.ofReal (A * lambdaDelta ξ W Q ε) := by
    rw [← ENNReal.ofReal_mul (Real.exp_pos a).le]
    congr 1
    dsimp [A]
    rw [Real.exp_add]
    ring
  constructor
  · rw [hLoEq] at hloMed
    exact (ENNReal.ofReal_le_ofReal_iff (m ⟨ε, ε.property.1⟩).property.le).1 hloMed
  · rw [hHiEq] at hhiMed
    exact (ENNReal.ofReal_le_ofReal_iff
      (mul_nonneg hA.le hLam.le)).1 hhiMed

end SupercriticalLQGUniqueness.B2.DG20Pt
