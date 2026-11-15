import LatticeProb.Prob.DeterministicStoppedHistory
import LatticeProb.Prob.StoppedPathComposition

/-! # Almost surely separated stopped histories with prefix representatives -/

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal

namespace LatticeProb

/-- An event with almost-sure natural-filtration prefix representatives has a
representative observable from a strictly later clock and stopped path. -/
theorem ae_prefix_history_representative_of_lt
    {Ω : Type*} [MeasurableSpace Ω] {d : ℕ}
    {X : ℝ≥0 → Ω → EuclideanSpace ℝ (Fin d)}
    (hm : ∀ t, StronglyMeasurable (X t))
    (hc : ∀ ω, Continuous fun t => X t ω)
    (S T : Ω → ℝ≥0∞) (μ : Measure Ω) (hST : ∀ᵐ ω ∂μ, S ω < T ω)
    {A : Set Ω} (hA : ∀ t : ℝ≥0, ∃ G : Set Ω,
      MeasurableSet[natFiltration X hm t] G ∧
      A ∩ {ω | S ω ≤ (t : ℝ≥0∞)} =ᵐ[μ] G) :
    ∃ B : Set Ω, MeasurableSet[MeasurableSpace.comap
      (fun ω => (T ω, stoppedPath (T ω) (pathMap X hc ω))) inferInstance] B ∧
      ∀ᵐ ω ∂μ, ω ∈ A ↔ ω ∈ B := by
  classical
  let t : ℚ → ℝ≥0 := fun q => Real.toNNReal (q : ℝ)
  have hprefix (q : ℚ) : ∃ B : Set C(ℝ≥0, EuclideanSpace ℝ (Fin d)),
      MeasurableSet B ∧
      A ∩ {ω | S ω ≤ (t q : ℝ≥0∞)} =ᵐ[μ]
        (fun ω => stoppedPath (t q : ℝ≥0∞) (pathMap X hc ω)) ⁻¹' B := by
    obtain ⟨G, hG, hGae⟩ := hA (t q)
    rw [natFiltration_eq_comap_stoppedPath hm hc] at hG
    obtain ⟨B, hB, hBG⟩ := MeasurableSpace.measurableSet_comap.mp hG
    exact ⟨B, hB, hBG ▸ hGae⟩
  choose B hB hpre using hprefix
  let Y := fun ω => (T ω, stoppedPath (T ω) (pathMap X hc ω))
  let m : MeasurableSpace Ω := MeasurableSpace.comap Y inferInstance
  have hY : @Measurable Ω _ m _ Y := comap_measurable Y
  have hclock : @Measurable Ω _ m _ T := measurable_fst.comp hY
  have hpath : @Measurable Ω _ m _ (fun ω => stoppedPath (T ω) (pathMap X hc ω)) :=
    measurable_snd.comp hY
  have htest (q : ℚ) : MeasurableSet[m] {ω | (t q : ℝ≥0∞) < T ω} :=
    measurableSet_lt measurable_const hclock
  have hobs (q : ℚ) : @Measurable Ω _ m _ (fun ω =>
      stoppedPath (t q : ℝ≥0∞) (stoppedPath (T ω) (pathMap X hc ω))) :=
    continuous_stoppedPath.measurable.comp (measurable_const.prodMk hpath)
  let C : Set Ω := ⋃ q, {ω | (t q : ℝ≥0∞) < T ω} ∩
    (fun ω => stoppedPath (t q : ℝ≥0∞)
      (stoppedPath (T ω) (pathMap X hc ω))) ⁻¹' B q
  refine ⟨C, MeasurableSet.iUnion (fun q => (htest q).inter ((hobs q) (hB q))), ?_⟩
  filter_upwards [hST, ae_all_iff.2 hpre] with ω hω hpreω
  simp only [C, mem_iUnion, mem_inter_iff, mem_ofPred_eq, mem_preimage]
  constructor
  · intro hmem
    obtain ⟨q, _, hleft, hright⟩ := ENNReal.lt_iff_exists_rat_btwn.mp hω
    refine ⟨q, hright, ?_⟩
    rw [stoppedPath_stoppedPath, min_eq_right (le_of_lt hright)]
    have h : ω ∈ A ∩ {ω | S ω ≤ (t q : ℝ≥0∞)} := ⟨hmem, le_of_lt hleft⟩
    exact (hpreω q).mp h
  · rintro ⟨q, hright, hmem⟩
    rw [stoppedPath_stoppedPath, min_eq_right (le_of_lt hright)] at hmem
    have h : ω ∈ (fun ω => stoppedPath (t q : ℝ≥0∞) (pathMap X hc ω)) ⁻¹' B q := hmem
    exact ((hpreω q).mpr h).1

end LatticeProb
