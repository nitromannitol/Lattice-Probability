/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.B2.DG20Conc.LaneA3Overlap at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DDDF.T20DDen

 








set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

open MeasureTheory Set Classical
open scoped ENNReal

namespace SupercriticalLQGUniqueness.B2.DG20Conc

open LQGMetric.DDDF

 


theorem laneA3_sum_paid_pieces_le
    {ι : Type*} (s : Finset ι) (U : ι → Set ℂ) (γ : ℝ → ℂ)
    (g : ℝ → ℝ≥0∞) (A : ι → ℝ≥0∞) (N : ℕ)
    (hcard : ∀ z : ℂ, (s.filter fun i => z ∈ U i).card ≤ N)
    (hA : ∀ i ∈ s, ∃ a c : ℝ,
      Icc a c ⊆ Icc (0 : ℝ) 1 ∧
      (∀ r ∈ Icc a c, γ r ∈ U i) ∧
      A i ≤ ∫⁻ r in Icc a c, g r) :
    ∑ i ∈ s, A i ≤ (N : ℝ≥0∞) *
      ∫⁻ r in Icc (0 : ℝ) 1, g r := by
  classical
  have hA' : ∀ i, ∃ a c : ℝ,
      i ∈ s → Icc a c ⊆ Icc (0 : ℝ) 1 ∧
        (∀ r ∈ Icc a c, γ r ∈ U i) ∧
        A i ≤ ∫⁻ r in Icc a c, g r := by
    intro i
    by_cases hi : i ∈ s
    · obtain ⟨a, c, h⟩ := hA i hi
      exact ⟨a, c, fun _ => h⟩
    · exact ⟨0, 0, fun h => False.elim (hi h)⟩
  choose a c hac using hA'
  have h1 : ∀ i ∈ s, A i ≤
      ∫⁻ r in Icc (0 : ℝ) 1, (Icc (a i) (c i)).indicator g r := by
    intro i hi
    obtain ⟨hsub, -, hle⟩ := hac i hi
    rw [lintegral_indicator measurableSet_Icc,
      Measure.restrict_restrict measurableSet_Icc,
      inter_eq_left.2 hsub]
    exact hle
  calc
    ∑ i ∈ s, A i ≤
        ∑ i ∈ s, ∫⁻ r in Icc (0 : ℝ) 1,
          (Icc (a i) (c i)).indicator g r := Finset.sum_le_sum h1
    _ ≤ ∫⁻ r in Icc (0 : ℝ) 1,
        ∑ i ∈ s, (Icc (a i) (c i)).indicator g r :=
          T20C.sum_lintegral_le s _
    _ ≤ ∫⁻ r in Icc (0 : ℝ) 1, (N : ℝ≥0∞) * g r := by
      refine lintegral_mono fun r => ?_
      calc
        ∑ i ∈ s, (Icc (a i) (c i)).indicator g r ≤
            ∑ i ∈ s, if γ r ∈ U i then g r else 0 := by
              refine Finset.sum_le_sum fun i hi => ?_
              by_cases hr : r ∈ Icc (a i) (c i)
              · rw [indicator_of_mem hr, if_pos ((hac i hi).2.1 r hr)]
              · rw [indicator_of_notMem hr]
                exact zero_le
        _ = ((s.filter fun i => γ r ∈ U i).card : ℝ≥0∞) * g r := by
          rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
        _ ≤ (N : ℝ≥0∞) * g r := by
          gcongr
          exact_mod_cast hcard (γ r)
    _ = (N : ℝ≥0∞) *
        ∫⁻ r in Icc (0 : ℝ) 1, g r :=
          lintegral_const_mul' _ _ (by simp)

end SupercriticalLQGUniqueness.B2.DG20Conc
