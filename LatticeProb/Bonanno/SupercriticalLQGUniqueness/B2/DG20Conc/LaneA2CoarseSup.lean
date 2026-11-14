/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.B2.DG20Conc.LaneA2CoarseSup at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Conc.LaneA2Motion3
import LatticeProb.Bonanno.LQGMetric.Papers.DDDF.FieldMax

 

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace SupercriticalLQGUniqueness.B2.DG20Conc

open LQGMetric.DDDF LQGMetric.WhiteNoise LQGMetric.SupTail

 

theorem laneA2_coarse_sup_three :
    ∃ C A : ℝ, 0 < C ∧ 0 < A ∧
      ∀ {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
        (W : WNSpace → Ω → ℝ) (hW : IsWhiteNoise P W)
        (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b)
        (ha1 : a ≤ 1) (hb1 : b ≤ 1) (M : ℝ) (hM : 0 < M),
        P {ω | M < ⨆ z : (rectAB a b).toSet, |phiMN W P 0 3 z ω|} ≤
          ENNReal.ofReal (C * Real.exp (-((M / A) ^ 2 * 3 / Real.log 4))) := by
  obtain ⟨C₀, hC₀, htail⟩ := prop2_tail
  let A : ℝ := 3 + C₀ * Real.sqrt 3
  have hA : 0 < A := by dsimp [A]; positivity
  refine ⟨C₀ * 4 ^ (3 : ℕ), A, by positivity, hA, ?_⟩
  intro Ω _ P W hW a b ha hb ha1 hb1 M hM
  have : IsProbabilityMeasure P := hW.isProbabilityMeasure
  have : Nonempty (rectAB a b).toSet := ⟨⟨0, by
    simp only [MarkedRect.toSet, rectAB, Complex.mem_reProdIm,
      Complex.zero_re, Complex.zero_im, mem_Icc, zero_add]
    exact ⟨⟨le_rfl, ha⟩, ⟨le_rfl, hb⟩⟩⟩⟩
  have hY := isPhiVersion_phiMN hW (Nat.zero_le 3)
  have hYae : ∀ x, (fun ω => phiMN W P 0 3 x ω) =ᵐ[P]
      phi W ((2 : ℝ) ^ (3 : ℕ))⁻¹ 1 x := by
    intro x
    simpa only [inv_pow, pow_zero, inv_one] using hY.ae_eq x
  have ht := htail hW 3 (phiMN W P 0 3) hYae hY.cont (M / A)
    (div_pos hM hA)
  have hset : {ω | M < ⨆ z : (rectAB a b).toSet, |phiMN W P 0 3 z ω|} ⊆
      {ω | M ≤ ⨆ z : ferniqueBox 0 1, |phiMN W P 0 3 z ω|} := by
    intro ω hω
    have hsub := LQGMetric.DDDF.S6AB.rectAB_toSet_sub ha1 hb1
    have hle : (⨆ z : (rectAB a b).toSet, |phiMN W P 0 3 z ω|) ≤
        ⨆ z : ferniqueBox 0 1, |phiMN W P 0 3 z ω| := by
      apply ciSup_le
      intro z
      exact le_ciSup
        (LQGMetric.SupTail.bddAbove_abs_of_compact (isCompact_ferniqueBox 0 1) (hY.cont ω))
        (⟨z.1, hsub z.2⟩ : ferniqueBox 0 1)
    exact hω.le.trans hle
  have hAeq : M / A * (3 + C₀ * Real.sqrt 3) = M := by
    dsimp [A]
    field_simp [ne_of_gt hA]
  have hset' : {ω | M < ⨆ z : (rectAB a b).toSet, |phiMN W P 0 3 z ω|} ⊆
      {ω | M / A * (3 + C₀ * Real.sqrt 3) ≤
        ⨆ z : ferniqueBox 0 1, |phiMN W P 0 3 z ω|} := by
    simpa only [hAeq] using hset
  have hreal := (measureReal_mono hset').trans ht
  rw [← ofReal_measureReal (measure_ne_top _ _)]
  apply ENNReal.ofReal_le_ofReal
  have he : -(M / A) ^ 2 * (3 : ℝ) / Real.log 4 =
      -((M / A) ^ 2 * 3 / Real.log 4) := by ring
  simpa only [Nat.cast_ofNat, he] using hreal

end SupercriticalLQGUniqueness.B2.DG20Conc
