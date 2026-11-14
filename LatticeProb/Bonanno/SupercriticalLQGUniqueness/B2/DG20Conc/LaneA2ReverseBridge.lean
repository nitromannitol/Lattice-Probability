/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.B2.DG20Conc.LaneA2ReverseBridge at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Conc.LaneA2Large
import LatticeProb.Bonanno.LQGMetric.Papers.DDDF.P18Step3

 






set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

open MeasureTheory
open scoped ENNReal

namespace SupercriticalLQGUniqueness.B2.DG20Conc

open LQGMetric.DDDF LQGMetric.WhiteNoise

 

theorem laneA2_reverse_three_octave {ξ : ℝ} (hξ : 0 < ξ) :
    ∃ p₀ : ℝ, 0 < p₀ ∧ ∀ p : ℝ, 0 < p → p ≤ p₀ →
      ∃ D : ℝ, 1 ≤ D ∧
        ∀ {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
          (W : WNSpace → Ω → ℝ) (_hW : IsWhiteNoise P W)
          (m : ℕ), 3 ≤ m →
            ellN ξ W P (m - 3) (ENNReal.ofReal p) ≤
              D * ellN ξ W P m (ENNReal.ofReal p) := by
  obtain ⟨W₀, hW₀⟩ := exists_isWhiteNoise
  let P₀ := LQGDimension.ExistAsm.stdP
  obtain ⟨p₀, hp₀, hstep⟩ := dddf_p18_step3 (P := P₀) hW₀ hξ
  refine ⟨min p₀ (1 / 4), lt_min hp₀ (by norm_num), ?_⟩
  intro p hp hp₀
  obtain ⟨C, hC, hcmp⟩ := hstep p hp (hp₀.trans (min_le_left _ _))
  let a : ℝ := (2 : ℝ) ^ (-(2 * ξ * 3)) *
    Real.exp (-(C * Real.sqrt (3 : ℝ)))
  have ha : 0 < a := by dsimp [a]; positivity
  let D : ℝ := max 1 a⁻¹
  refine ⟨D, le_max_left _ _, ?_⟩
  intro Ω _ P W hW m hm
  have hcanon := hcmp m 3 hm
  have hlocal : a * ellN ξ W P (m - 3) (ENNReal.ofReal p) ≤
      ellN ξ W P m (ENNReal.ofReal p) := by
    dsimp [a]
    rw [laneA_ellN_eq hW hW₀ ξ (m - 3) (ENNReal.ofReal p),
      laneA_ellN_eq hW hW₀ ξ m (ENNReal.ofReal p)]
    simpa only [P₀, Nat.cast_ofNat, mul_assoc, mul_left_comm, mul_comm]
      using hcanon
  have hnonneg : 0 ≤ ellN ξ W P m (ENNReal.ofReal p) := by
    have : IsProbabilityMeasure P := hW.isProbabilityMeasure
    exact (T20B.ellN_pos hW (ENNReal.ofReal_pos.mpr hp)
      (by
        rw [← ENNReal.ofReal_one]
        exact ENNReal.ofReal_lt_ofReal_iff (by norm_num) |>.mpr
          (lt_of_le_of_lt (hp₀.trans (min_le_right _ _)) (by norm_num))) m).le
  calc
    ellN ξ W P (m - 3) (ENNReal.ofReal p) =
        a⁻¹ * (a * ellN ξ W P (m - 3) (ENNReal.ofReal p)) := by
          field_simp
    _ ≤ a⁻¹ * ellN ξ W P m (ENNReal.ofReal p) :=
      mul_le_mul_of_nonneg_left hlocal (inv_nonneg.mpr ha.le)
    _ ≤ D * ellN ξ W P m (ENNReal.ofReal p) :=
      mul_le_mul_of_nonneg_right (le_max_right _ _) hnonneg

end SupercriticalLQGUniqueness.B2.DG20Conc
