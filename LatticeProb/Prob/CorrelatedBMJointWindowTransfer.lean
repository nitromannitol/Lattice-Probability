import LatticeProb.Prob.CorrelatedBMRecenter
import LatticeProb.Prob.CorrelatedBMWindowBarrier

/-! # Joint Brownian barriers under translation and time reversal -/

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal
open MatedCRTHarmonic.MatedCRT

namespace LatticeProb.CorrelatedBM

/-- Both coordinates stay above a common barrier on a window starting at zero. -/
def jointZeroBarrier (q h : ℝ) : Set Path2 :=
  {ω | ∀ t ∈ Icc 0 h, -q ≤ coneIncr 0 t 0 ω} ∩
  {ω | ∀ t ∈ Icc 0 h, -q ≤ coneIncr 1 t 0 ω}

/-- The joint barrier is measurable on continuous path space. -/
theorem measurableSet_jointZeroBarrier (q h : ℝ) (hh : 0 ≤ h) :
    MeasurableSet (jointZeroBarrier q h) := by
  unfold jointZeroBarrier
  apply MeasurableSet.inter
  all_goals
    apply measurableSet_closedBarrier_of_local_evaluations _ _ hh
    · intro ω
      unfold coneIncr lrCoord
      split_ifs <;> fun_prop
    · intro t ht
      exact measurable_coneIncr _ _ _
    · exact measurable_const

/-- A joint bound uniform over correlated Brownian laws applies to every
translated forward window. -/
theorem measure_jointForwardBarrier_le {γ : ℝ} {μ : Measure Path2}
    (hμ : IsCorrelatedBM2 γ μ) (q h : ℝ) (hh : 0 ≤ h) (J : ℝ≥0∞)
    (hJ : ∀ ν : Measure Path2, IsCorrelatedBM2 γ ν → ν (jointZeroBarrier q h) ≤ J)
    (b : ℝ) :
    μ ({ω | ∀ t ∈ Icc b (b + h), -q ≤ coneIncr 0 t b ω} ∩
       {ω | ∀ t ∈ Icc b (b + h), -q ≤ coneIncr 1 t b ω}) ≤ J := by
  have hmap := hJ (μ.map (recenterPath b 1))
    (isCorrelatedBM2_map_recenterPath hμ b 1 (by norm_num))
  rw [Measure.map_apply (continuous_recenterPath b 1).measurable
    (measurableSet_jointZeroBarrier q h hh)] at hmap
  have heq : (recenterPath b 1) ⁻¹' jointZeroBarrier q h =
      ({ω | ∀ t ∈ Icc b (b + h), -q ≤ coneIncr 0 t b ω} ∩
       {ω | ∀ t ∈ Icc b (b + h), -q ≤ coneIncr 1 t b ω}) := by
    ext ω
    simp only [mem_preimage, jointZeroBarrier, mem_inter_iff, mem_ofPred_eq]
    have hc (i : Fin 2) (t : ℝ) :
        coneIncr i t 0 (recenterPath b 1 ω) = coneIncr i (b + t) b ω := by
      fin_cases i <;> simp [coneIncr, lrCoord, recenterPath]
    simp only [hc]
    constructor
    · rintro ⟨h0, h1⟩
      constructor <;> intro t ht
      · convert h0 (t - b) (by simp only [mem_Icc]; rcases ht with ⟨ht1, ht2⟩; constructor <;> linarith) using 1; congr 2; ring
      · convert h1 (t - b) (by simp only [mem_Icc]; rcases ht with ⟨ht1, ht2⟩; constructor <;> linarith) using 1; congr 2; ring
    · rintro ⟨h0, h1⟩
      constructor <;> intro t ht
      · exact h0 (b + t) (by simp only [mem_Icc]; rcases ht with ⟨ht1, ht2⟩; constructor <;> linarith)
      · exact h1 (b + t) (by simp only [mem_Icc]; rcases ht with ⟨ht1, ht2⟩; constructor <;> linarith)
  rwa [heq] at hmap

/-- A joint bound uniform over correlated Brownian laws applies to every
translated backward window. -/
theorem measure_jointBackwardBarrier_le {γ : ℝ} {μ : Measure Path2}
    (hμ : IsCorrelatedBM2 γ μ) (q h : ℝ) (hh : 0 ≤ h) (J : ℝ≥0∞)
    (hJ : ∀ ν : Measure Path2, IsCorrelatedBM2 γ ν → ν (jointZeroBarrier q h) ≤ J)
    (b : ℝ) :
    μ ({ω | ∀ t ∈ Icc (b - h) b,
          -q ≤ coneIncr 0 t (b - h) ω - coneIncr 0 b (b - h) ω} ∩
       {ω | ∀ t ∈ Icc (b - h) b,
          -q ≤ coneIncr 1 t (b - h) ω - coneIncr 1 b (b - h) ω}) ≤ J := by
  have hmap := hJ (μ.map (recenterPath b (-1)))
    (isCorrelatedBM2_map_recenterPath hμ b (-1) (by norm_num))
  rw [Measure.map_apply (continuous_recenterPath b (-1)).measurable
    (measurableSet_jointZeroBarrier q h hh)] at hmap
  have heq : (recenterPath b (-1)) ⁻¹' jointZeroBarrier q h =
      ({ω | ∀ t ∈ Icc (b - h) b,
          -q ≤ coneIncr 0 t (b - h) ω - coneIncr 0 b (b - h) ω} ∩
       {ω | ∀ t ∈ Icc (b - h) b,
          -q ≤ coneIncr 1 t (b - h) ω - coneIncr 1 b (b - h) ω}) := by
    ext ω
    simp only [mem_preimage, jointZeroBarrier, mem_inter_iff, mem_ofPred_eq]
    have hc (i : Fin 2) (t : ℝ) :
        coneIncr i t 0 (recenterPath b (-1) ω) = coneIncr i (b - t) b ω := by
      fin_cases i <;> simp [coneIncr, lrCoord, recenterPath, sub_eq_add_neg]
    simp only [hc]
    have hdiff (i : Fin 2) (t : ℝ) :
        coneIncr i t (b - h) ω - coneIncr i b (b - h) ω = coneIncr i t b ω := by
      simp only [coneIncr]
      ring
    simp only [hdiff]
    constructor
    · rintro ⟨h0, h1⟩
      constructor <;> intro t ht
      · convert h0 (b - t) (by simp only [mem_Icc]; rcases ht with ⟨ht1, ht2⟩; constructor <;> linarith) using 1; congr 2; ring
      · convert h1 (b - t) (by simp only [mem_Icc]; rcases ht with ⟨ht1, ht2⟩; constructor <;> linarith) using 1; congr 2; ring
    · rintro ⟨h0, h1⟩
      constructor <;> intro t ht
      · exact h0 (b - t) (by simp only [mem_Icc]; rcases ht with ⟨ht1, ht2⟩; constructor <;> linarith)
      · exact h1 (b - t) (by simp only [mem_Icc]; rcases ht with ⟨ht1, ht2⟩; constructor <;> linarith)
  rwa [heq] at hmap

end LatticeProb.CorrelatedBM
