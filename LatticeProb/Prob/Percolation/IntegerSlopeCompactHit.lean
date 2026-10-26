import LatticeProb.Prob.Percolation.IntegerSlopeSubgroupMeasurable
import Mathlib.Topology.Maps.Proper.Basic

/-!
# Compact hits of integer-slope subgroups

In coefficient space, the relation imposing integer evaluations is closed. Projection along
a compact set of slopes is closed, so coordinatewise measurable coefficients give measurable
compact-hit events. The compact set may be empty.
-/

namespace LatticeProb.Prob.Percolation

open scoped BigOperators

variable {Ω ι : Type*} {d : ℕ}

/-- Coefficient fields admitting an integer slope in a fixed compact set form a closed set. -/
theorem isClosed_integerSlopeCompactHit (K : Set (Fin d → ℝ)) (hK : IsCompact K) :
    IsClosed {g : ι → Fin d → ℝ | ∃ p ∈ K, p ∈ integerSlopeSubgroup g} := by
  letI : CompactSpace K := isCompact_iff_compactSpace.mp hK
  have hrel : IsClosed {x : (ι → Fin d → ℝ) × K |
      (x.2 : Fin d → ℝ) ∈ integerSlopeSubgroup x.1} := by
    simp only [mem_integerSlopeSubgroup, Set.setOf_forall]
    apply isClosed_iInter
    intro e
    have heval : Continuous (fun x : (ι → Fin d → ℝ) × K =>
        ∑ j, (x.2 : Fin d → ℝ) j * x.1 e j) := by
      apply continuous_finsetSum
      intro j _
      exact ((continuous_apply j).comp
        (continuous_subtype_val.comp continuous_snd)).mul
        (by fun_prop)
    convert Int.isClosedEmbedding_coe_real.isClosed_range.preimage heval using 1
    ext x
    exact ⟨fun ⟨z, hz⟩ => ⟨z, hz.symm⟩, fun ⟨z, hz⟩ => ⟨z, hz.symm⟩⟩
  have hproj := isClosedMap_fst_of_compactSpace _ hrel
  convert hproj using 1
  ext g
  constructor
  · rintro ⟨p, hp, hpg⟩
    exact ⟨(g, ⟨p, hp⟩), hpg, rfl⟩
  · rintro ⟨⟨g', p⟩, hmem, rfl⟩
    exact ⟨p, p.property, hmem⟩

/-- Countably many measurable coefficient vectors give measurable hits of every compact set. -/
theorem measurableSet_integerSlopeCompactHit [MeasurableSpace Ω] [Countable ι]
    (g : Ω → ι → Fin d → ℝ) (hg : ∀ e j, Measurable (fun ω => g ω e j))
    (K : Set (Fin d → ℝ)) (hK : IsCompact K) :
    MeasurableSet {ω | ∃ p ∈ K, p ∈ integerSlopeSubgroup (g ω)} := by
  have hgm : Measurable g := measurable_pi_lambda _ fun e =>
    measurable_pi_lambda _ fun j => hg e j
  exact (isClosed_integerSlopeCompactHit K hK).measurableSet.preimage hgm

end LatticeProb.Prob.Percolation
