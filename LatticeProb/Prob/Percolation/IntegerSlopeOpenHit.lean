import LatticeProb.Prob.Percolation.IntegerSlopeCompactHit
import Mathlib.Topology.Compactness.SigmaCompact

/-!
# Open hits of integer-slope subgroups

Every open subset of finite-dimensional real slope space is a countable union of compact
sets contained in that subset. The compact-hit measurability theorem therefore gives
measurability of open hits for countably indexed measurable coefficient fields.
-/

namespace LatticeProb.Prob.Percolation

variable {Ω ι : Type*} {d : ℕ}

/-- Countably many measurable coefficient vectors give measurable hits of every open set. -/
theorem measurableSet_integerSlopeOpenHit [MeasurableSpace Ω] [Countable ι]
    (g : Ω → ι → Fin d → ℝ) (hg : ∀ e j, Measurable (fun ω => g ω e j))
    (U : Set (Fin d → ℝ)) (hU : IsOpen U) :
    MeasurableSet {ω | ∃ p ∈ U, p ∈ integerSlopeSubgroup (g ω)} := by
  letI : LocallyCompactSpace U := hU.locallyCompactSpace
  have hSigma : IsSigmaCompact U := isSigmaCompact_iff_sigmaCompactSpace.mpr inferInstance
  obtain ⟨K, hK, hcover⟩ := hSigma
  have hKU : ∀ n, K n ⊆ U := fun n => hcover ▸ Set.subset_iUnion K n
  have hevent : {ω | ∃ p ∈ U, p ∈ integerSlopeSubgroup (g ω)} =
      ⋃ n : ℕ, {ω | ∃ p ∈ K n, p ∈ integerSlopeSubgroup (g ω)} := by
    ext ω
    constructor
    · rintro ⟨p, hp, hpg⟩
      obtain ⟨n, hn⟩ := Set.mem_iUnion.mp (hcover.symm ▸ hp)
      exact Set.mem_iUnion.mpr ⟨n, p, hn, hpg⟩
    · intro h
      obtain ⟨n, p, hp, hpg⟩ := Set.mem_iUnion.mp h
      exact ⟨p, hKU n hp, hpg⟩
  rw [hevent]
  exact MeasurableSet.iUnion fun n => measurableSet_integerSlopeCompactHit g hg (K n) (hK n)

end LatticeProb.Prob.Percolation
