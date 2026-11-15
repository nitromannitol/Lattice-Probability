import LatticeProb.Bonanno.QuantumZipper.Proofs.Section5.TVLocal
import Mathlib.MeasureTheory.Measure.Sub

/-! Total variation convergence for dominated finite-measure approximations. -/

open MeasureTheory Filter
open scoped ENNReal Topology

namespace LatticeProb

/-- For a finite measure and a dominated measure, total variation is the
remaining mass. -/
theorem tvDist_eq_sub_measure_univ_of_le {α : Type*} [MeasurableSpace α]
    (μ ν : Measure α) [IsFiniteMeasure μ] (hν : ν ≤ μ) :
    QuantumZipper.TV.tvDist μ ν = μ Set.univ - ν Set.univ := by
  have : IsFiniteMeasure ν := isFiniteMeasure_of_le μ hν
  apply le_antisymm
  · unfold QuantumZipper.TV.tvDist
    refine iSup_le fun s => iSup_le fun hs => sup_le ?_ ?_
    · rw [← Measure.sub_apply hs hν, ← Measure.sub_apply MeasurableSet.univ hν]
      exact measure_mono (Set.subset_univ s)
    · rw [tsub_eq_zero_of_le (hν s)]
      exact bot_le
  · exact QuantumZipper.TV.le_tvDist MeasurableSet.univ

/-- Dominated measures converge in total variation when their total masses
converge to the mass of the finite dominating measure. -/
theorem tendsto_tvDist_of_le_of_tendsto_measure_univ {α τ : Type*}
    [MeasurableSpace α] (μ : Measure α) [IsFiniteMeasure μ]
    (ν : τ → Measure α) {l : Filter τ} (hν : ∀ t, ν t ≤ μ)
    (hmass : Tendsto (fun t => ν t Set.univ) l (𝓝 (μ Set.univ))) :
    Tendsto (fun t => QuantumZipper.TV.tvDist μ (ν t)) l (𝓝 0) := by
  have hsub : Tendsto (fun t => μ Set.univ - ν t Set.univ) l
      (𝓝 (μ Set.univ - μ Set.univ)) :=
    (ENNReal.tendsto_sub (Or.inl (measure_ne_top μ Set.univ))).comp
      (tendsto_const_nhds.prodMk_nhds hmass)
  simpa only [tsub_self, tvDist_eq_sub_measure_univ_of_le μ _ (hν _)] using hsub

end LatticeProb
