import LatticeProb.Probability.Percolation.ActualCellFactorization
import LatticeProb.Probability.Percolation.FixedWalkJoined

/-!
# Probability of a vertical joined crossing

The critical product measure assigns probability at least one eighth to a
vertical square crossing connected to the left side of the centered square.
-/

open MeasureTheory ProbabilityTheory Percolation.Literature
open scoped ProbabilityTheory

noncomputable section

namespace EdgeCrossing

/-- A vertical square crossing joined to the left side has probability at least one eighth. -/
theorem eighth_le_vertical_joined (n : ℕ) (hn : 1 ≤ n) :
    (1 / 8 : ℝ) ≤
      (Measure.infinitePi (fun _ : (LatticeModels.zdGraph 2).edgeSet =>
        bernoulliMeasure True False half)).real
        (joinedCrossingIn (rectangle n n) (centeredSquare n)
          (bottomSide n n) (topSide n n) (outerLeft n)) := by
  classical
  choose c d Q hc hd hQ hbdry hopen using
    fun (D : Finset (LatticeModels.Site 2)) (hD : D ∈ verticalExposureIndices n) =>
      exists_fixed_boundaryWalk n hn D hD
  let E : Finset (LatticeModels.Site 2) → Set ((LatticeModels.zdGraph 2).edgeSet → Prop) :=
    fun D => if hD : D ∈ verticalExposureIndices n then firstContact n (Q D hD) (!true) else ∅
  apply eighth_le_vertical_joined_of_exposure n (verticalExposureIndices n)
    (verticalExposureCell n) E (vertical_crossing_subset_iUnion_exposureCell n)
    (pairwiseDisjoint_verticalExposureCell n) (fun D _ => measurableSet_verticalExposureCell n D)
  · intro D hD
    simpa [E, hD] using measurableSet_firstContact_component n (Q D hD) (!true)
  · intro D hD
    simpa [E, hD] using verticalExposureCell_real_inter_firstContact n hn D hD
      (Q D hD) (hc D hD) (hd D hD) (hQ D hD) (hbdry D hD)
  · intro D hD
    simpa [E, hD] using quarter_le_firstContact n (Q D hD) (hQ D hD) (hc D hD) (hd D hD)
  · intro D hD
    simpa [E, hD] using verticalExposureCell_inter_firstContact_subset_joined n D (Q D hD)
      (hc D hD) (hd D hD) (hQ D hD) (fun η hη => (hopen D hD η hη).1)

end EdgeCrossing
