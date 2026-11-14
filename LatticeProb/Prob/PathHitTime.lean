/-
Copyright (c) 2026. All rights reserved.
-/
import Mathlib
import LatticeProb.Prob.MarkovPathKernelStrong

/-!
# First hitting time of a closed set by a continuous path

For a set `F` of a metric space `E` and a continuous path `x : C(ℝ≥0, E)` the first hitting time of
`F` is `pathHit F x = inf {s | x s ∈ F}` (`⊤` if the path never meets `F`).  The exit time of an
open ball `B` is `pathHit Bᶜ`.

* `pathHit_le_iff`: for closed `F`, `pathHit F x ≤ t` iff the path meets `F` on `[0, t]`;
* `isStoppingTime_pathHit`: for closed `F`, `pathHit F` is a stopping time of the filtration of
  stopped paths;
* `pathHit_mem`: the infimum is attained, so a path with a finite hitting time is in `F` then;
* `pathHit_stopPath`: stopping a path at its hitting time does not change the hitting time.
-/

set_option autoImplicit false

open MeasureTheory Filter Topology
open scoped NNReal ENNReal

noncomputable section

namespace LatticeProb

attribute [local instance] dUnifMetricSpace

variable {E : Type*} [MetricSpace E]

/-- The first time the path `x` lies in `F` (`⊤` if it never does). -/
def pathHit (F : Set E) (x : C(ℝ≥0, E)) : ℝ≥0∞ := ⨅ (s : ℝ≥0) (_ : x s ∈ F), (s : ℝ≥0∞)

theorem pathHit_le_of_mem {F : Set E} {x : C(ℝ≥0, E)} {s : ℝ≥0} (hs : x s ∈ F) :
    pathHit F x ≤ (s : ℝ≥0∞) :=
  iInf₂_le s hs

/-- For closed `F`, a finite hitting time is attained and is the least time at which the path is
in `F`. -/
theorem exists_attained {F : Set E} (hF : IsClosed F) {x : C(ℝ≥0, E)} (h : pathHit F x < ⊤) :
    ∃ a : ℝ≥0, x a ∈ F ∧ pathHit F x = (a : ℝ≥0∞) ∧ ∀ s, x s ∈ F → a ≤ s := by
  set S : Set ℝ≥0 := {s | x s ∈ F} with hS
  have hne : S.Nonempty := by
    rw [pathHit, iInf_lt_iff] at h
    obtain ⟨s, hs⟩ := h
    rw [iInf_lt_iff] at hs
    obtain ⟨hxs, -⟩ := hs
    exact ⟨s, hxs⟩
  have hcl : IsClosed S := hF.preimage x.continuous
  have hmem : sInf S ∈ S := hcl.csInf_mem hne (OrderBot.bddBelow S)
  refine ⟨sInf S, hmem, le_antisymm (pathHit_le_of_mem hmem) ?_, fun s hs => ?_⟩
  · refine le_iInf₂ fun s hs => ?_
    exact_mod_cast csInf_le (OrderBot.bddBelow S) hs
  · exact csInf_le (OrderBot.bddBelow S) hs

theorem pathHit_le_iff {F : Set E} (hF : IsClosed F) (x : C(ℝ≥0, E)) (t : ℝ≥0) :
    pathHit F x ≤ (t : ℝ≥0∞) ↔ ∃ s ≤ t, x s ∈ F := by
  constructor
  · intro h
    obtain ⟨a, ha, he, -⟩ := exists_attained hF (h.trans_lt ENNReal.coe_lt_top)
    refine ⟨a, ?_, ha⟩
    rw [he] at h
    exact_mod_cast h
  · rintro ⟨s, hst, hs⟩
    exact (pathHit_le_of_mem hs).trans (by exact_mod_cast hst)

/-- The point at which a path with finite hitting time hits the closed set `F` lies in `F`. -/
theorem pathHit_mem {F : Set E} (hF : IsClosed F) {x : C(ℝ≥0, E)} (h : pathHit F x < ⊤) :
    x (pathHit F x).toNNReal ∈ F := by
  obtain ⟨a, ha, he, -⟩ := exists_attained hF h
  rw [he, ENNReal.toNNReal_coe]
  exact ha

theorem measurableSet_hit_by {F : Set E} (hF : IsClosed F) (t : ℝ≥0) :
    MeasurableSet {y : C(ℝ≥0, E) | ∃ s ≤ t, y s ∈ F} := by
  have hopen : IsOpen {y : C(ℝ≥0, E) | Set.MapsTo y (Set.Icc (0 : ℝ≥0) t) Fᶜ} :=
    ContinuousMap.isOpen_setOfPred_mapsTo isCompact_Icc hF.isOpen_compl
  have hset : {y : C(ℝ≥0, E) | ∃ s ≤ t, y s ∈ F} =
      {y : C(ℝ≥0, E) | Set.MapsTo y (Set.Icc (0 : ℝ≥0) t) Fᶜ}ᶜ := by
    ext y
    simp only [Set.mem_ofPred_eq, Set.mem_compl_iff, Set.MapsTo, Set.mem_Icc, not_forall,
      Set.mem_compl_iff, not_not]
    constructor
    · rintro ⟨s, hs, hys⟩
      exact ⟨s, ⟨zero_le, hs⟩, hys⟩
    · rintro ⟨s, ⟨-, hs⟩, hys⟩
      exact ⟨s, hs, hys⟩
  rw [hset]
  exact hopen.measurableSet.compl

/-- Stopping a path at its (finite) hitting time of a closed set does not change the hitting time. -/
theorem pathHit_stopPath {F : Set E} (hF : IsClosed F) {x : C(ℝ≥0, E)} (h : pathHit F x < ⊤) :
    pathHit F (stopPath x (pathHit F x).toNNReal) = pathHit F x := by
  obtain ⟨a, ha, he, hmin⟩ := exists_attained hF h
  rw [he, ENNReal.toNNReal_coe]
  refine le_antisymm (pathHit_le_of_mem (s := a) (by simpa using ha)) ?_
  refine le_iInf₂ fun s hs => ?_
  have h1 : a ≤ min s a := hmin _ (by simpa using hs)
  exact_mod_cast (le_min_iff.1 h1).1

/-- **The hitting time of a closed set is a stopping time** of the filtration of stopped paths. -/
theorem isStoppingTime_pathHit {F : Set E} (hF : IsClosed F) :
    IsStoppingTime (stoppedPathFiltration (E := E)) (pathHit F) := by
  intro t
  have hset : {x : C(ℝ≥0, E) | pathHit F x ≤ (t : ℝ≥0∞)} =
      (fun x => stopPath x t) ⁻¹' {y : C(ℝ≥0, E) | ∃ s ≤ t, y s ∈ F} := by
    ext x
    simp only [Set.mem_ofPred_eq, Set.mem_preimage, pathHit_le_iff hF, stopPath_apply]
    constructor
    · rintro ⟨s, hs, hxs⟩
      exact ⟨s, hs, by rwa [min_eq_left hs]⟩
    · rintro ⟨s, hs, hxs⟩
      exact ⟨min s t, min_le_right _ _, hxs⟩
  show MeasurableSet[stoppedPathFiltration (E := E) t] {x : C(ℝ≥0, E) | pathHit F x ≤ (t : ℝ≥0∞)}
  rw [hset]
  exact ⟨_, measurableSet_hit_by hF t, rfl⟩

end LatticeProb

end
