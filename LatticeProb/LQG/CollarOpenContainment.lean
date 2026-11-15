import LatticeProb.LQG.CollarEventSubopen
import LatticeProb.Topology.CompactThickeningEvent
import Mathlib.Topology.Compactness.SigmaCompact

/-! # Containment of fixed open sets in random collars -/

set_option autoImplicit false

open MeasureTheory Set Metric TopologicalSpace LQGMetric

namespace LatticeProb

/-- Containment of a sigma-compact set in a random thickening is measurable. -/
theorem measurableSet_sigmaCompact_subset_thickening {X Ω : Type*} [MetricSpace X]
    [MeasurableSpace Ω] [MeasurableSpace (NonemptyCompacts X)]
    [BorelSpace (NonemptyCompacts X)] {K : Ω → NonemptyCompacts X} (hK : Measurable K)
    {S : Set X} (hS : IsSigmaCompact S) (r : ℝ) :
    MeasurableSet {ω | S ⊆ thickening r (K ω : Set X)} := by
  obtain ⟨C, hC, hU⟩ := hS
  have heq : {ω | S ⊆ thickening r (K ω : Set X)} =
      ⋂ n, {ω | C n ⊆ thickening r (K ω : Set X)} := by
    ext ω
    simp only [mem_ofPred_eq, mem_iInter]
    rw [← hU, iUnion_subset_iff]
  rw [heq]
  exact MeasurableSet.iInter fun n => measurableSet_compact_subset_thickening hK (hC n) r

/-- Every open subset of a locally compact second-countable space is sigma-compact. -/
theorem isSigmaCompact_of_isOpen {X : Type*} [TopologicalSpace X]
    [LocallyCompactSpace X] [SecondCountableTopology X] {O : Set X} (hO : IsOpen O) :
    IsSigmaCompact O := by
  let : LocallyCompactSpace O := hO.locallyCompactSpace
  exact isSigmaCompact_iff_sigmaCompactSpace.mpr inferInstance

namespace LQG

/-- A fixed open set's containment in the sampled collar is observable from the code. -/
theorem measurableSet_open_subset_collar_of_collarFieldCode {Ω : Type}
    [MeasurableSpace (NonemptyCompacts ℂ)] [BorelSpace (NonemptyCompacts ℂ)]
    (h : Ω → DistC) (K : Ω → NonemptyCompacts ℂ) (ψ : ℕ → TestC)
    {p : ℝ} (hp : 0 < p) (k : ℕ) (O : Opens ℂ) :
    MeasurableSet[MeasurableSpace.comap (collarFieldCode h K localDenseTest ψ hp k)
      inferInstance] {ω | (O : Set ℂ) ⊆
        thickening (1 / ((k : ℝ) + 1)) (K ω : Set ℂ)} := by
  let : MeasurableSpace Ω := MeasurableSpace.comap
    (collarFieldCode h K localDenseTest ψ hp k) inferInstance
  have hK : Measurable K :=
    (comap_measurable (collarFieldCode h K localDenseTest ψ hp k)).fst
  exact measurableSet_sigmaCompact_subset_thickening hK
    (isSigmaCompact_of_isOpen O.isOpen) _

end LQG
end LatticeProb
