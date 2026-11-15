import LatticeProb.Prob.DeterministicStoppedHistory
import LatticeProb.Prob.StoppedPathComposition

/-! # Strictly separated stopped histories -/

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal

namespace LatticeProb

/-- If countably many deterministic times separate two clocks pointwise, the raw
natural history at the first clock is observed by the second clock and its stopped path. -/
theorem stopped_history_le_comap_later_clock_path
    {Ω ι : Type*} [MeasurableSpace Ω] [Countable ι] {d : ℕ}
    {X : ℝ≥0 → Ω → EuclideanSpace ℝ (Fin d)}
    (hm : ∀ t, StronglyMeasurable (X t))
    (hc : ∀ ω, Continuous fun t => X t ω)
    {S : Ω → ℝ≥0∞} (hS : IsStoppingTime (natFiltration X hm) S)
    (T : Ω → ℝ≥0∞) (t : ι → ℝ≥0)
    (hsep : ∀ ω, ∃ i, S ω ≤ (t i : ℝ≥0∞) ∧ (t i : ℝ≥0∞) < T ω) :
    hS.measurableSpace ≤ MeasurableSpace.comap
      (fun ω => (T ω, stoppedPath (T ω) (pathMap X hc ω))) inferInstance := by
  classical
  intro A hA
  have hprefix (i : ι) : ∃ B : Set C(ℝ≥0, EuclideanSpace ℝ (Fin d)),
      MeasurableSet B ∧
      (fun ω => stoppedPath (t i : ℝ≥0∞) (pathMap X hc ω)) ⁻¹' B =
        A ∩ {ω | S ω ≤ (t i : ℝ≥0∞)} := by
    have h := (hS.measurableSet A).mp hA |>.2 (t i)
    rw [natFiltration_eq_comap_stoppedPath hm hc] at h
    exact MeasurableSpace.measurableSet_comap.mp h
  choose B hB hpre using hprefix
  let Y := fun ω => (T ω, stoppedPath (T ω) (pathMap X hc ω))
  let _ : MeasurableSpace Ω := MeasurableSpace.comap Y inferInstance
  have hY : Measurable Y := comap_measurable Y
  have hclock : Measurable T := measurable_fst.comp hY
  have hpath : Measurable (fun ω => stoppedPath (T ω) (pathMap X hc ω)) :=
    measurable_snd.comp hY
  have htest (i : ι) : MeasurableSet {ω | (t i : ℝ≥0∞) < T ω} :=
    measurableSet_lt measurable_const hclock
  have hobs (i : ι) : Measurable (fun ω =>
      stoppedPath (t i : ℝ≥0∞) (stoppedPath (T ω) (pathMap X hc ω))) :=
    (continuous_stoppedPath.measurable.comp (measurable_const.prodMk hpath))
  have hrep : A = ⋃ i, {ω | (t i : ℝ≥0∞) < T ω} ∩
      (fun ω => stoppedPath (t i : ℝ≥0∞)
        (stoppedPath (T ω) (pathMap X hc ω))) ⁻¹' B i := by
    ext ω
    simp only [mem_iUnion, mem_inter_iff, mem_ofPred_eq, mem_preimage]
    constructor
    · intro hω
      obtain ⟨i, hi, hit⟩ := hsep ω
      refine ⟨i, hit, ?_⟩
      rw [stoppedPath_stoppedPath, min_eq_right (le_of_lt hit)]
      have : ω ∈ A ∩ {ω | S ω ≤ (t i : ℝ≥0∞)} := ⟨hω, hi⟩
      rw [← hpre i] at this
      exact this
    · rintro ⟨i, hit, hmem⟩
      rw [stoppedPath_stoppedPath, min_eq_right (le_of_lt hit)] at hmem
      have : ω ∈ (fun ω => stoppedPath (t i : ℝ≥0∞) (pathMap X hc ω)) ⁻¹' B i := hmem
      rw [hpre i] at this
      exact this.1
  rw [hrep]
  exact MeasurableSet.iUnion fun i => (htest i).inter ((hobs i) (hB i))

/-- Strictly ordered clocks give inclusion of raw natural stopping history in the
later clock and stopped path, without assumptions on the sample space. -/
theorem stopped_history_le_comap_of_lt
    {Ω : Type*} [MeasurableSpace Ω] {d : ℕ}
    {X : ℝ≥0 → Ω → EuclideanSpace ℝ (Fin d)}
    (hm : ∀ t, StronglyMeasurable (X t))
    (hc : ∀ ω, Continuous fun t => X t ω)
    {S : Ω → ℝ≥0∞} (hS : IsStoppingTime (natFiltration X hm) S)
    (T : Ω → ℝ≥0∞) (hST : ∀ ω, S ω < T ω) :
    hS.measurableSpace ≤ MeasurableSpace.comap
      (fun ω => (T ω, stoppedPath (T ω) (pathMap X hc ω))) inferInstance := by
  apply stopped_history_le_comap_later_clock_path hm hc hS T
    (fun q : ℚ => Real.toNNReal (q : ℝ))
  intro ω
  obtain ⟨q, _, hleft, hright⟩ := ENNReal.lt_iff_exists_rat_btwn.mp (hST ω)
  exact ⟨q, le_of_lt hleft, hright⟩

end LatticeProb
