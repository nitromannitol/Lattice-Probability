/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.B2.DG20Conc.LaneA2LowQuantile at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Conc.LaneA2LowGeom
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Conc.LaneALaw

 

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

open MeasureTheory
open scoped ENNReal

namespace SupercriticalLQGUniqueness.B2.DG20Conc

open LQGMetric.DDDF LQGMetric.WhiteNoise

theorem laneA2_low_quantile_bounds {ξ p : ℝ} (hp : 0 < p)
    (hpHalf : p < 2⁻¹) :
    ∃ E Q : ℝ, 0 < E ∧ 0 < Q ∧
      ∀ {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
        (W : WNSpace → Ω → ℝ) (hW : IsWhiteNoise P W)
        (m : ℕ), m ≤ 2 →
        ellN ξ W P m (ENNReal.ofReal p) ≤ E ∧
        Q ≤ LambdaN ξ W P m (ENNReal.ofReal p) *
          ellN ξ W P m (ENNReal.ofReal p) := by
  obtain ⟨W₀, hW₀⟩ := exists_isWhiteNoise
  let P₀ := LQGDimension.ExistAsm.stdP
  let e (m : ℕ) := ellN ξ W₀ P₀ m (ENNReal.ofReal p)
  let q (m : ℕ) := LambdaN ξ W₀ P₀ m (ENNReal.ofReal p) * e m
  have hpq0 : 0 < ENNReal.ofReal p := ENNReal.ofReal_pos.mpr hp
  have hpq1 : ENNReal.ofReal p < (1 : ℝ≥0∞) := by
    rw [ENNReal.ofReal_lt_one]
    linarith
  have he (m : ℕ) : 0 < e m := T20B.ellN_pos hW₀ hpq0 hpq1 m
  have hq (m : ℕ) : 0 < q m := by
    exact mul_pos (T20B.LambdaN_pos hW₀ hpq0
      (by
        have hh : ENNReal.ofReal p ≤ (2⁻¹ : ℝ≥0∞) := by
          rw [← show ENNReal.ofReal (1/2 : ℝ) = (2⁻¹ : ℝ≥0∞) by
            rw [show (1/2 : ℝ) = (2 : ℝ)⁻¹ by norm_num,
              ENNReal.ofReal_inv_of_pos (by norm_num)]; norm_num]
          exact ENNReal.ofReal_le_ofReal (by norm_num at hpHalf ⊢; exact hpHalf.le)
        exact hh) m) (he m)
  let E := max (e 0) (max (e 1) (e 2))
  let Q := min (q 0) (min (q 1) (q 2))
  have hE : 0 < E := lt_of_lt_of_le (he 0) (le_max_left _ _)
  have hQ : 0 < Q := lt_min (hq 0) (lt_min (hq 1) (hq 2))
  refine ⟨E, Q, hE, hQ, ?_⟩
  intro Ω _ P W hW m hm
  rw [laneA_ellN_eq hW hW₀ ξ m (ENNReal.ofReal p),
    laneA_LambdaN_eq hW hW₀ ξ m (ENNReal.ofReal p)]
  interval_cases m
  · exact ⟨le_max_left _ _, min_le_left _ _⟩
  · exact ⟨(le_max_left _ _).trans (le_max_right _ _),
      (min_le_right _ _).trans (min_le_left _ _)⟩
  · exact ⟨(le_max_right _ _).trans (le_max_right _ _),
      (min_le_right _ _).trans (min_le_right _ _)⟩

end SupercriticalLQGUniqueness.B2.DG20Conc
