import LatticeProb.Probability.Percolation.JoinedCrossingOrientationProbability

/-!
# A finite-exposure reduction for vertical joined crossings

A disjoint family of exposure events and independent connection events yields a
lower bound for a vertical crossing joined to the left side of the centered square.
-/

open MeasureTheory ProbabilityTheory Percolation.Literature
open scoped ProbabilityTheory

noncomputable section

namespace EdgeCrossing

private abbrev Config := (LatticeModels.zdGraph 2).edgeSet → Prop
private abbrev criticalMeasure : Measure Config :=
  Measure.infinitePi (fun _ : (LatticeModels.zdGraph 2).edgeSet =>
    bernoulliMeasure True False half)

/-- A finite measurable exposure with independent connection events of probability at
least one quarter gives the corresponding conditional joined-crossing estimate. -/
theorem vertical_crossing_div_four_le_joined_of_exposure {ι : Type*} (n : ℕ)
    (s : Finset ι) (D E : ι → Set Config)
    (hcover : crossingIn (rectangle n n) (bottomSide n n) (topSide n n) ⊆
      ⋃ i ∈ s, D i)
    (hdisj : (↑s : Set ι).PairwiseDisjoint D)
    (hD : ∀ i ∈ s, MeasurableSet (D i))
    (hE : ∀ i ∈ s, MeasurableSet (E i))
    (hindep : ∀ i ∈ s, criticalMeasure.real (D i ∩ E i) =
      criticalMeasure.real (D i) * criticalMeasure.real (E i))
    (hprob : ∀ i ∈ s, (1 / 4 : ℝ) ≤ criticalMeasure.real (E i))
    (hjoin : ∀ i ∈ s, D i ∩ E i ⊆
      joinedCrossingIn (rectangle n n) (centeredSquare n)
        (bottomSide n n) (topSide n n) (outerLeft n)) :
    criticalMeasure.real (crossingIn (rectangle n n) (bottomSide n n) (topSide n n)) / 4 ≤
      criticalMeasure.real (joinedCrossingIn (rectangle n n) (centeredSquare n)
        (bottomSide n n) (topSide n n) (outerLeft n)) := by
  classical
  have hdisj' : (↑s : Set ι).PairwiseDisjoint (fun i => D i ∩ E i) := by
    intro i hi j hj hij
    exact (hdisj hi hj hij).mono Set.inter_subset_left Set.inter_subset_left
  have hlow : criticalMeasure.real
      (crossingIn (rectangle n n) (bottomSide n n) (topSide n n)) ≤
      ∑ i ∈ s, criticalMeasure.real (D i) := by
    calc
      _ ≤ criticalMeasure.real (⋃ i ∈ s, D i) :=
        measureReal_mono hcover (measure_ne_top _ _)
      _ ≤ ∑ i ∈ s, criticalMeasure.real (D i) := measureReal_biUnion_finset_le s D
  have hup : (∑ i ∈ s, criticalMeasure.real (D i ∩ E i)) ≤
      criticalMeasure.real (joinedCrossingIn (rectangle n n) (centeredSquare n)
        (bottomSide n n) (topSide n n) (outerLeft n)) := by
    rw [← measureReal_biUnion_finset hdisj' (fun i hi => (hD i hi).inter (hE i hi))]
    exact measureReal_mono (Set.iUnion₂_subset hjoin) (measure_ne_top _ _)
  have hsum : (∑ i ∈ s, criticalMeasure.real (D i)) / 4 ≤
      ∑ i ∈ s, criticalMeasure.real (D i ∩ E i) := by
    rw [Finset.sum_div]
    apply Finset.sum_le_sum
    intro i hi
    rw [hindep i hi]
    have hn : 0 ≤ criticalMeasure.real (D i) := measureReal_nonneg
    nlinarith [hprob i hi]
  linarith

/-- Under the same finite-exposure hypotheses, the vertical joined event has critical
probability at least one eighth. -/
theorem eighth_le_vertical_joined_of_exposure {ι : Type*} (n : ℕ)
    (s : Finset ι) (D E : ι → Set Config)
    (hcover : crossingIn (rectangle n n) (bottomSide n n) (topSide n n) ⊆
      ⋃ i ∈ s, D i)
    (hdisj : (↑s : Set ι).PairwiseDisjoint D)
    (hD : ∀ i ∈ s, MeasurableSet (D i))
    (hE : ∀ i ∈ s, MeasurableSet (E i))
    (hindep : ∀ i ∈ s, criticalMeasure.real (D i ∩ E i) =
      criticalMeasure.real (D i) * criticalMeasure.real (E i))
    (hprob : ∀ i ∈ s, (1 / 4 : ℝ) ≤ criticalMeasure.real (E i))
    (hjoin : ∀ i ∈ s, D i ∩ E i ⊆
      joinedCrossingIn (rectangle n n) (centeredSquare n)
        (bottomSide n n) (topSide n n) (outerLeft n)) :
    (1 / 8 : ℝ) ≤ criticalMeasure.real
      (joinedCrossingIn (rectangle n n) (centeredSquare n)
        (bottomSide n n) (topSide n n) (outerLeft n)) := by
  have hv : (1 / 2 : ℝ) ≤ criticalMeasure.real
      (crossingIn (rectangle n n) (bottomSide n n) (topSide n n)) := by
    have h := half_le_translated_square_vertical n (0 : LatticeModels.Site 2)
    simpa [criticalMeasure] using h
  have h := vertical_crossing_div_four_le_joined_of_exposure n s D E
    hcover hdisj hD hE hindep hprob hjoin
  linarith

end EdgeCrossing
