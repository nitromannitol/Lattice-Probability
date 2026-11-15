import LatticeProb.Prob.RealBallExitHistory
import LatticeProb.Topology.ObservedSegmentBall
import LatticeProb.Prob.OpenExitStoppedPath

/-! # Measurability of real-time exit segments -/

set_option autoImplicit false

open MeasureTheory Set Metric
open scoped ENNReal NNReal

namespace LatticeProb

/-- The real infimum convention agrees with the totalized open exit clock,
including when the path never exits. -/
theorem sInf_real_extension_eq_openExitTime_total {E : Type*} [TopologicalSpace E]
    (w : C(ℝ≥0, E)) (U : Set E) (hU : IsOpen U) :
    sInf {t : ℝ | 0 ≤ t ∧ w t.toNNReal ∉ U} =
      ((openExitTime (fun t (_ : Unit) => w t) U ()).toNNReal : ℝ) := by
  by_cases hfin : openExitTime (fun t (_ : Unit) => w t) U () ≠ ⊤
  · exact sInf_real_extension_eq_openExitTime (fun t (_ : Unit) => w t) () U
      w.continuous hU hfin
  · have htop : openExitTime (fun t (_ : Unit) => w t) U () = ⊤ := not_ne_iff.mp hfin
    have hempty : {t : ℝ | 0 ≤ t ∧ w t.toNNReal ∉ U} = ∅ := by
      apply Set.eq_empty_of_forall_notMem
      intro t ht
      have h := openExitTime_le_of_not_mem
        (B := fun t (_ : Unit) => w t) (ω := ()) ht.2
      rw [htop] at h
      exact (ENNReal.not_top_le_coe h)
    rw [hempty, Real.sInf_empty, htop]
    simp

/-- Containment of an open ball in a segment between two first exits is
measurable, including infinite exits and unordered endpoints. -/
theorem measurableSet_real_exit_segment_contains_ball
    {Ω : Type*} [MeasurableSpace Ω] {d : ℕ}
    {w : Ω → C(ℝ≥0, EuclideanSpace ℝ (Fin d))} (hw : Measurable w)
    (U V : Set (EuclideanSpace ℝ (Fin d))) (hU : IsOpen U) (hV : IsOpen V)
    (r : ℝ) :
    MeasurableSet {ω | ∃ z, ball z r ⊆ (fun t : ℝ => w ω t.toNNReal) '' Icc
      (sInf {t : ℝ | 0 ≤ t ∧ w ω t.toNNReal ∉ U})
      (sInf {t : ℝ | 0 ≤ t ∧ w ω t.toNNReal ∉ V})} := by
  by_cases hr : 0 < r
  · let f : Ω → C(ℝ, EuclideanSpace ℝ (Fin d)) := fun ω =>
      (w ω).comp ⟨Real.toNNReal, continuous_real_toNNReal⟩
    let τ : Set (EuclideanSpace ℝ (Fin d)) → Ω → ℝ≥0∞ := fun W ω =>
      openExitTime (fun t (_ : Unit) => w ω t) W ()
    have hτ (W : Set (EuclideanSpace ℝ (Fin d))) (hW : IsOpen W) : Measurable (τ W) := by
      have h := measurable_openExitTime
        (B := fun t ω => w ω t)
        (fun t => ((ContinuousMapBorel.ContinuousMap.measurable_eval t).comp hw).stronglyMeasurable)
        (fun ω => (w ω).continuous) hW
      exact h
    let a : Ω → ℝ := fun ω => ((τ U ω).toNNReal : ℝ)
    let b : Ω → ℝ := fun ω => ((τ V ω).toNNReal : ℝ)
    have hf : Measurable f := (ContinuousMap.continuous_precomp
      (⟨Real.toNNReal, continuous_real_toNNReal⟩ : C(ℝ, ℝ≥0))).measurable.comp hw
    have ha : Measurable a := NNReal.continuous_coe.measurable.comp
      (ENNReal.measurable_toNNReal.comp (hτ U hU))
    have hb : Measurable b := NNReal.continuous_coe.measurable.comp
      (ENNReal.measurable_toNNReal.comp (hτ V hV))
    have he := measurableSet_exists_closedBall_subset_segment (δ := fun _ : Ω => r)
      hf ha hb measurable_const
    convert he using 1
    ext ω
    simp only [mem_ofPred_eq, hr.le, true_and]
    rw [sInf_real_extension_eq_openExitTime_total (w ω) U hU,
      sInf_real_extension_eq_openExitTime_total (w ω) V hV]
    change (∃ z, ball z r ⊆ (f ω) '' Icc (a ω) (b ω)) ↔
      a ω ≤ b ω ∧ ∃ z, closedBall z r ⊆ (f ω) '' Icc (a ω) (b ω)
    constructor
    · rintro ⟨z, hz⟩
      have hab : a ω ≤ b ω := by
        by_contra h
        have hempty : Icc (a ω) (b ω) = ∅ := Icc_eq_empty h
        have : z ∈ (f ω) '' Icc (a ω) (b ω) := hz (mem_ball_self hr)
        simp [hempty] at this
      exact ⟨hab, z, (ball_subset_segment_iff_closedBall (f ω) (a ω) (b ω) r hr z).mp hz⟩
    · rintro ⟨_, z, hz⟩
      exact ⟨z, ball_subset_closedBall.trans hz⟩
  · have hr' : r ≤ 0 := le_of_not_gt hr
    have : {ω | ∃ z, ball z r ⊆ (fun t : ℝ => w ω t.toNNReal) '' Icc
        (sInf {t : ℝ | 0 ≤ t ∧ w ω t.toNNReal ∉ U})
        (sInf {t : ℝ | 0 ≤ t ∧ w ω t.toNNReal ∉ V})} = Set.univ := by
      ext ω
      simp only [mem_ofPred_eq, mem_univ, iff_true]
      exact ⟨0, by simp only [ball_eq_empty.mpr hr', empty_subset]⟩
    rw [this]
    exact MeasurableSet.univ

end LatticeProb
