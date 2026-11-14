/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.B2.DG20Conc.J1BlockUnion at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Conc.J1NearIdx

 

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

open MeasureTheory
open scoped ENNReal

namespace SupercriticalLQGUniqueness.B2.DG20Conc

open LQGMetric.DDDF

theorem j1_block_union_of_pointwise
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (K : ℕ) (hK : 16 ≤ K) (E : ℤ × ℤ → Set Ω)
    (q : ℝ≥0∞)
    (hblock : ∀ b ∈ T20B.nearIdx K, P (E b) ≤ q) :
    P {ω | ∃ b ∈ T20B.nearIdx K, ω ∈ E b} ≤
      ENNReal.ofReal ((5 : ℝ)^K) * q := by
  have hcard : ((T20B.nearIdx K).card : ℝ≥0∞) ≤
      ENNReal.ofReal ((5 : ℝ)^K) := by
    rw [← ENNReal.ofReal_natCast]
    exact ENNReal.ofReal_le_ofReal (by exact_mod_cast j1_nearIdx_card_le_five K hK)
  calc
    P {ω | ∃ b ∈ T20B.nearIdx K, ω ∈ E b} =
        P (⋃ b ∈ T20B.nearIdx K, E b) := by
          congr 1; ext ω; simp
    _ ≤ ((T20B.nearIdx K).card : ℝ≥0∞) * q := by
      refine (measure_biUnion_finset_le (T20B.nearIdx K) E).trans ?_
      rw [← nsmul_eq_mul, ← Finset.sum_const]
      exact Finset.sum_le_sum fun b hb => hblock b hb
    _ ≤ ENNReal.ofReal ((5 : ℝ)^K) * q :=
      mul_le_mul_of_nonneg_right hcard (zero_le : (0 : ℝ≥0∞) ≤ _)

end SupercriticalLQGUniqueness.B2.DG20Conc
