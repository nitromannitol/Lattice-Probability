import Mathlib
import LatticeProb.Prob.MarkovPathKernelStrong
import LatticeProb.Analysis.CrossingTimes

/-!
# Crossing times of a continuous path are stopping times

For a continuous path `y : C(ℝ≥0, E)` in a separable metric space and `ε > 0`, the crossing time
`σ_{k+1} = inf {s > σ_k : ε ≤ dist (y s) (y σ_k)}` is attained when finite, and it is at most `u`
iff `σ_k ≤ u` and `sup_{s ∈ [σ_k, u]} dist (y s) (y σ_k) ≥ ε`.  Since the supremum over `[σ_k, u]`
is the supremum over a countable dense set of times, this exhibits `{σ_{k+1} ≤ u}` as a countable
combination of measurable events.  Hence

* `measurable_crossTime`: each crossing time is a measurable function on the path space;
* `isStoppingTime_crossTime`: each crossing time is a stopping time for the filtration generated
  by the stopped paths (`stoppedPathFiltration`).
-/

open MeasureTheory
open scoped BoundedContinuousFunction ENNReal NNReal

namespace LatticeProb

attribute [local instance] dUnifMetricSpace

section Dense

variable {E : Type*} [PseudoMetricSpace E]

/-- For a continuous path and `ε > 0`, the next `ε`-crossing time after `a` is at most `u` iff
`a ≤ u` and for each `n` some time `d m` of a dense sequence in `[a, u]` has
`dist (f (d m)) (f a) > ε - 1 / (n + 1)`. -/
theorem nextCrossTime_le_iff_dense {f : ℝ≥0 → E} (hf : Continuous f) {ε : ℝ} (hε : 0 < ε)
    {d : ℕ → ℝ≥0} (hd : DenseRange d) (a : ℝ≥0∞) (u : ℝ≥0) :
    nextCrossTime ε f a ≤ u ↔ a ≤ u ∧ ∀ n : ℕ, ∃ m : ℕ, a ≤ (d m : ℝ≥0∞) ∧ d m ≤ u ∧
      ε - 1 / ((n : ℝ) + 1) < dist (f (d m)) (f a.toNNReal) := by
  induction a using ENNReal.recTopCoe with
  | top =>
    rw [nextCrossTime_top]
    simp
  | coe a =>
    rw [nextCrossTime_le_iff_exists hf hε a u]
    simp only [ENNReal.toNNReal_coe, ENNReal.coe_le_coe]
    constructor
    · rintro ⟨s, has, hsu, hs⟩
      refine ⟨has.le.trans hsu, fun n => ?_⟩
      have hopen : IsOpen {x : ℝ≥0 | ε - 1 / ((n : ℝ) + 1) < dist (f x) (f a)} :=
        isOpen_lt continuous_const (hf.dist continuous_const)
      have hsV : s ∈ {x : ℝ≥0 | ε - 1 / ((n : ℝ) + 1) < dist (f x) (f a)} := by
        have : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
        simp only [Set.mem_ofPred_eq]
        linarith
      have hcl : s ∈ closure (Set.Ioo a s) := by
        rw [closure_Ioo has.ne]
        exact ⟨has.le, le_rfl⟩
      obtain ⟨t, htV, htI⟩ := mem_closure_iff.1 hcl _ hopen hsV
      obtain ⟨m, hm⟩ := hd.exists_mem_open (hopen.inter isOpen_Ioo) ⟨t, htV, htI⟩
      exact ⟨m, hm.2.1.le, hm.2.2.le.trans hsu, hm.1⟩
    · rintro ⟨hau, h⟩
      have hcomp : IsCompact (Set.Icc a u) := isCompact_Icc
      obtain ⟨s, hsmem, hsmax⟩ := hcomp.exists_isMaxOn ⟨a, le_rfl, hau⟩
        (hf.dist continuous_const).continuousOn
      have hbound : ε ≤ dist (f s) (f a) := by
        by_contra hlt
        push Not at hlt
        obtain ⟨n, hn⟩ := exists_nat_one_div_lt (sub_pos.2 hlt)
        obtain ⟨m, ham, hmu, hm⟩ := h n
        have := hsmax (show d m ∈ Set.Icc a u from ⟨ham, hmu⟩)
        simp only [Set.mem_ofPred_eq] at this
        linarith
      refine ⟨s, lt_of_le_of_ne hsmem.1 fun hsa => ?_, hsmem.2, hbound⟩
      rw [← hsa, dist_self] at hbound
      linarith

end Dense

section Measurability

variable {E : Type*} [MetricSpace E] [SecondCountableTopology E] [MeasurableSpace E] [BorelSpace E]
  [MeasurableSpace C(ℝ≥0, E)] [BorelSpace C(ℝ≥0, E)]

omit [SecondCountableTopology E] in
/-- Evaluating a path at a measurable random time is measurable. -/
theorem measurable_eval_pathTime {σ : C(ℝ≥0, E) → ℝ≥0∞} (hσ : Measurable σ) :
    Measurable fun y : C(ℝ≥0, E) => y (σ y).toNNReal := by
  have hcont : Continuous fun p : C(ℝ≥0, E) × ℝ≥0 => p.1 p.2 := ContinuousEval.continuous_eval
  have hpair : Measurable fun y : C(ℝ≥0, E) => (y, (σ y).toNNReal) :=
    measurable_id.prodMk (ENNReal.measurable_toNNReal.comp hσ)
  exact hcont.measurable.comp hpair

/-- Each `ε`-crossing time of a continuous path is a measurable function of the path. -/
theorem measurable_crossTime {ε : ℝ} (hε : 0 < ε) (k : ℕ) :
    Measurable fun y : C(ℝ≥0, E) => crossTime ε (fun s => y s) k := by
  induction k with
  | zero => simp [crossTime_zero]
  | succ k ih =>
    have hd := TopologicalSpace.denseRange_denseSeq ℝ≥0
    set d := TopologicalSpace.denseSeq ℝ≥0
    simp only [crossTime_succ]
    refine measurable_of_Iic fun x => ?_
    induction x using ENNReal.recTopCoe with
    | top => simp
    | coe u =>
      have hset : (fun y : C(ℝ≥0, E) => nextCrossTime ε (fun s => y s)
          (crossTime ε (fun s => y s) k)) ⁻¹' Set.Iic (u : ℝ≥0∞) =
          {y | crossTime ε (fun s => y s) k ≤ u} ∩ ⋂ n : ℕ, ⋃ m : ℕ,
            ({y | crossTime ε (fun s => y s) k ≤ (d m : ℝ≥0∞)} ∩
              {y | d m ≤ u ∧ ε - 1 / ((n : ℝ) + 1) <
                dist (y (d m)) (y (crossTime ε (fun s => y s) k).toNNReal)}) := by
        ext y
        simp only [Set.mem_preimage, Set.mem_Iic, Set.mem_inter_iff, Set.mem_ofPred_eq,
          Set.mem_iInter, Set.mem_iUnion]
        rw [nextCrossTime_le_iff_dense y.continuous hε hd]
      rw [hset]
      refine (measurableSet_le ih measurable_const).inter (MeasurableSet.iInter fun n =>
        MeasurableSet.iUnion fun m => (measurableSet_le ih measurable_const).inter ?_)
      by_cases hmu : d m ≤ u
      · simp only [hmu, true_and]
        exact measurableSet_lt measurable_const
          (((continuous_eval_const (d m)).measurable).dist (measurable_eval_pathTime ih))
      · simp [hmu]

/-- Each `ε`-crossing time of a continuous path is a stopping time of the filtration generated by
the stopped paths. -/
theorem isStoppingTime_crossTime {ε : ℝ} (hε : 0 < ε) (k : ℕ) :
    IsStoppingTime (stoppedPathFiltration (E := E))
      fun y : C(ℝ≥0, E) => crossTime ε (fun s => y s) k := by
  intro u
  have hmeas : MeasurableSet {z : C(ℝ≥0, E) | crossTime ε (fun s => z s) k ≤ (u : ℝ≥0∞)} :=
    measurableSet_le (measurable_crossTime hε k) measurable_const
  have hpre : {y : C(ℝ≥0, E) | crossTime ε (fun s => y s) k ≤ (u : ℝ≥0∞)} =
      (fun y : C(ℝ≥0, E) => stopPath y u) ⁻¹'
        {z : C(ℝ≥0, E) | crossTime ε (fun s => z s) k ≤ (u : ℝ≥0∞)} := by
    ext y
    simp only [Set.mem_ofPred_eq, Set.mem_preimage]
    exact crossTime_le_iff_stopped y.continuous hε u k
  have h : MeasurableSet[stoppedPathFiltration (E := E) u]
      ((fun y : C(ℝ≥0, E) => stopPath y u) ⁻¹'
        {z : C(ℝ≥0, E) | crossTime ε (fun s => z s) k ≤ (u : ℝ≥0∞)}) :=
    MeasurableSpace.measurableSet_comap.2 ⟨_, hmeas, rfl⟩
  rw [← hpre] at h
  exact h

end Measurability

end LatticeProb
