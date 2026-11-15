import LatticeProb.Topology.RealFirstExitClock
import LatticeProb.Prob.BrownianOpenExitStopping

/-! # Measurability of rooted real first-exit endpoints -/

set_option autoImplicit false

open MeasureTheory Set
open scoped ENNReal NNReal

namespace LatticeProb

/-- The real forward first-exit endpoint is measurable, with value zero when
there is no exit. -/
theorem measurable_rooted_forward_real_exit
    {Ω : Type*} [MeasurableSpace Ω] {d : ℕ}
    {f : Ω → C(ℝ, EuclideanSpace ℝ (Fin d))} (hf : Measurable f)
    (U : Set (EuclideanSpace ℝ (Fin d))) (hU : IsOpen U) :
    Measurable (fun ω => sInf {t : ℝ | 0 ≤ t ∧ f ω t ∉ U}) := by
  let τ : Ω → ℝ≥0∞ := fun ω =>
    openExitTime (fun s (_ : Unit) => f ω (s : ℝ)) U ()
  have hτ : Measurable τ := by
    apply measurable_openExitTime (B := fun s ω => f ω (s : ℝ))
    · intro s
      exact ((ContinuousMap.measurable_eval _).comp hf).stronglyMeasurable
    · intro ω
      exact (f ω).continuous.comp NNReal.continuous_coe
    · exact hU
  have heq (ω : Ω) : sInf {t : ℝ | 0 ≤ t ∧ f ω t ∉ U} =
      ((τ ω).toNNReal : ℝ) := by
    by_cases hfin : τ ω ≠ ⊤
    · have hfin' : openExitTime (fun s (_ : Unit) => f ω (0 + (s : ℝ))) U () ≠ ⊤ := by
        simpa only [zero_add, τ] using hfin
      have h := sInf_outside_eq_forward_openExitTime (f ω) U 0 (f ω).continuous hU hfin'
      simpa only [zero_add, τ] using h
    · have htop : τ ω = ⊤ := not_ne_iff.mp hfin
      have hempty : {t : ℝ | 0 ≤ t ∧ f ω t ∉ U} = ∅ := by
        apply Set.eq_empty_of_forall_notMem
        intro t ht
        let s : ℝ≥0 := ⟨t, ht.1⟩
        have hle : τ ω ≤ (s : ℝ≥0∞) := openExitTime_le_of_not_mem ht.2
        rw [htop] at hle
        exact ENNReal.not_top_le_coe hle
      simp only [hempty, Real.sInf_empty, htop, ENNReal.toNNReal_top, NNReal.coe_zero]
  simp_rw [heq]
  exact NNReal.continuous_coe.measurable.comp (ENNReal.measurable_toNNReal.comp hτ)

/-- The real backward first-exit endpoint is measurable, with value zero when
there is no exit. -/
theorem measurable_rooted_backward_real_exit
    {Ω : Type*} [MeasurableSpace Ω] {d : ℕ}
    {f : Ω → C(ℝ, EuclideanSpace ℝ (Fin d))} (hf : Measurable f)
    (U : Set (EuclideanSpace ℝ (Fin d))) (hU : IsOpen U) :
    Measurable (fun ω => sSup {t : ℝ | t ≤ 0 ∧ f ω t ∉ U}) := by
  let τ : Ω → ℝ≥0∞ := fun ω =>
    openExitTime (fun s (_ : Unit) => f ω (-(s : ℝ))) U ()
  have hτ : Measurable τ := by
    apply measurable_openExitTime (B := fun s ω => f ω (-(s : ℝ)))
    · intro s
      exact ((ContinuousMap.measurable_eval _).comp hf).stronglyMeasurable
    · intro ω
      exact (f ω).continuous.comp NNReal.continuous_coe.neg
    · exact hU
  have heq (ω : Ω) : sSup {t : ℝ | t ≤ 0 ∧ f ω t ∉ U} =
      -((τ ω).toNNReal : ℝ) := by
    by_cases hfin : τ ω ≠ ⊤
    · have hfin' : openExitTime (fun s (_ : Unit) => f ω (0 - (s : ℝ))) U () ≠ ⊤ := by
        simpa only [zero_sub, τ] using hfin
      have h := sSup_outside_eq_backward_openExitTime (f ω) U 0 (f ω).continuous hU hfin'
      simpa only [zero_sub, τ] using h
    · have htop : τ ω = ⊤ := not_ne_iff.mp hfin
      have hempty : {t : ℝ | t ≤ 0 ∧ f ω t ∉ U} = ∅ := by
        apply Set.eq_empty_of_forall_notMem
        intro t ht
        let s : ℝ≥0 := ⟨-t, neg_nonneg.mpr ht.1⟩
        have hout : f ω (-(s : ℝ)) ∉ U := by
          change f ω (-(-t)) ∉ U
          simpa only [neg_neg] using ht.2
        have hle : τ ω ≤ (s : ℝ≥0∞) := openExitTime_le_of_not_mem hout
        rw [htop] at hle
        exact ENNReal.not_top_le_coe hle
      simp only [hempty, Real.sSup_empty, htop, ENNReal.toNNReal_top, NNReal.coe_zero, neg_zero]
  simp_rw [heq]
  exact (NNReal.continuous_coe.measurable.comp (ENNReal.measurable_toNNReal.comp hτ)).neg

end LatticeProb
