/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module BouRabeeGwynne.ContinuousPathRange at commit fdb5cad; local import paths and a deprecated name are updated. -/
import LatticeProb.Bonanno.BouRabeeGwynne.StoppedCurveLaws
import Mathlib.Analysis.Normed.Group.Bounded
import Mathlib.MeasureTheory.Measure.Continuity

/-! Every finite measure on continuous paths gives arbitrarily high mass to
a deterministic bound on a fixed compact time interval. -/

open MeasureTheory Set Filter
open scoped NNReal ENNReal Topology

namespace BouRabeeGwynne

def pathRangeEvent {d : ℕ} (T : ℝ≥0) (R : ℝ) : Set (BrownianPath d) :=
  {ω | ∀ t ∈ Icc (0 : ℝ≥0) T, ‖ω t‖ ≤ R}

lemma isClosed_pathRangeEvent {d : ℕ} (T : ℝ≥0) (R : ℝ) :
    IsClosed (pathRangeEvent (d := d) T R) := by
  unfold pathRangeEvent
  simp_rw [ofPred_forall]
  exact isClosed_iInter fun t => isClosed_iInter fun _ =>
    isClosed_le (by fun_prop) continuous_const

lemma monotone_pathRangeEvent {d : ℕ} (T : ℝ≥0) :
    Monotone (pathRangeEvent (d := d) T) := by
  intro R S hRS ω hω t ht
  exact (hω t ht).trans hRS

lemma iUnion_pathRangeEvent_nat {d : ℕ} (T : ℝ≥0) :
    (⋃ n : ℕ, pathRangeEvent (d := d) T (n : ℝ)) = univ := by
  apply eq_univ_of_forall
  intro ω
  obtain ⟨R, hR⟩ := isCompact_Icc.exists_bound_of_continuousOn
    (ω.continuous.continuousOn : ContinuousOn ω (Icc 0 T))
  obtain ⟨n, hn⟩ := exists_nat_gt R
  exact mem_iUnion.mpr ⟨n, fun t ht => (hR t ht).trans hn.le⟩

theorem measure_compl_pathRangeEvent_tendsto_zero {d : ℕ}
    (μ : Measure (BrownianPath d)) [IsFiniteMeasure μ] (T : ℝ≥0) :
    Tendsto (fun n : ℕ => μ (pathRangeEvent T (n : ℝ))ᶜ) atTop (𝓝 0) := by
  have hanti : Antitone (fun n : ℕ => (pathRangeEvent (d := d) T (n : ℝ))ᶜ) := by
    intro n m hnm ω hω hgood
    exact hω ((monotone_pathRangeEvent T) (by exact_mod_cast hnm) hgood)
  have hinter : (⋂ n : ℕ, (pathRangeEvent (d := d) T (n : ℝ))ᶜ) = ∅ := by
    rw [← compl_iUnion, iUnion_pathRangeEvent_nat T, compl_univ]
  have hlim := tendsto_measure_iInter_atTop (μ := μ)
    (fun n : ℕ => (isClosed_pathRangeEvent (d := d) T (n : ℝ)).measurableSet.compl.nullMeasurableSet)
    hanti ⟨0, measure_ne_top _ _⟩
  simpa only [hinter, measure_empty, Function.comp_def] using hlim

theorem exists_pathRangeEvent_compl_lt {d : ℕ}
    (μ : Measure (BrownianPath d)) [IsFiniteMeasure μ] (T : ℝ≥0)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ R : ℝ, 1 ≤ R ∧ μ (pathRangeEvent T R)ᶜ < ENNReal.ofReal ε := by
  obtain ⟨n, hn⟩ := ((measure_compl_pathRangeEvent_tendsto_zero μ T).eventually
    (gt_mem_nhds (ENNReal.ofReal_pos.mpr hε))).exists
  refine ⟨max 1 (n : ℝ), le_max_left _ _, lt_of_le_of_lt ?_ hn⟩
  apply measure_mono
  exact compl_subset_compl.mpr ((monotone_pathRangeEvent T) (le_max_right _ _))

end BouRabeeGwynne
