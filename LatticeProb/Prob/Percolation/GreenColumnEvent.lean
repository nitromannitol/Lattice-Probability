import LatticeProb.External.GreenColumnExistence
import LatticeProb.External.SupercriticalBondUniquenessInput


/-!
# A common Green-column event

The cited Green-column and cluster-uniqueness assumptions yield one almost-sure
event on which all poles have unique Green columns.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open MeasureTheory LatticeProb.External

namespace LatticeProb.Percolation

noncomputable section

/-- On a common full-measure event, every pole in the unique infinite component has a
unique Green column. -/
theorem ae_unique_green_column_for_all_poles (hg : SupercriticalBondGreenColumnExistence)
    (hu : SupercriticalBondUniqueness) (d : ℕ) [NeZero d] (hd : 2 ≤ d)
    (p : unitInterval) (hp : criticalProbability d < (p : ℝ)) (hp1 : (p : ℝ) < 1) :
    ∀ᵐ ω ∂latticeBondLaw d p,
      ∃ _h : HasUniqueInfiniteOpenComponent ω,
        ∀ h' : HasUniqueInfiniteOpenComponent ω,
          ∀ y : uniqueInfiniteComponent h',
            ∃! g : uniqueInfiniteComponent h' → ℝ,
              IsGreenColumn d hd (uniqueInfiniteComponent h') y g := by
  have huniq : ∀ᵐ ω ∂latticeBondLaw d p, HasUniqueInfiniteOpenComponent ω := by
    apply (ae_mem_iff_measure_eq (measurableSet_uniqueInfiniteComponentEvent d).nullMeasurableSet).2
    simpa using hu.2 d hd p hp hp1
  have hcols := ae_all_iff.mpr (hg d hd p hp hp1)
  filter_upwards [huniq, hcols] with ω hω hcolsω
  refine ⟨hω, ?_⟩
  intro h' y
  simpa only using hcolsω y.val h' y.property


end
end LatticeProb.Percolation
