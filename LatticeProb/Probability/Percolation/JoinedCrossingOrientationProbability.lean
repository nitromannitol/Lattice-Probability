import LatticeProb.Probability.Percolation.JoinedCrossingOrientation
import LatticeProb.Probability.Percolation.JoinedCrossingHarris
import LatticeProb.Probability.Percolation.SquareCrossing

/-!
# Probability transfer between joined crossing orientations

Harris' inequality and planar crossing intersection bound the probability of a
horizontal joined crossing using a vertical joined crossing and a square crossing.
-/

open MeasureTheory ProbabilityTheory Percolation.Literature
open scoped ProbabilityTheory

noncomputable section

namespace EdgeCrossing

private abbrev Site := LatticeModels.Site 2

/-- Opening additional edges preserves a horizontal crossing. -/
theorem isUpperSet_crossing (m n : ℕ) : IsUpperSet (crossing m n) := by
  intro η ξ hle hη
  obtain ⟨x, hx, y, hy, q, hq, ho⟩ := hη
  exact ⟨x, hx, y, hy, q, hq, fun e he => hle _ (ho e he)⟩

/-- A square crossing and a vertical joined crossing give a probability bound for a
horizontal joined crossing under the same Bernoulli product law. -/
theorem crossing_mul_vertical_joined_le_horizontal_joined (p : unitInterval) (n : ℕ)
    (R : Finset Site) (T : Set Site) (hSR : (rectangle n n : Set Site) ⊆ R) :
    (Measure.infinitePi (fun _ : (LatticeModels.zdGraph 2).edgeSet =>
      bernoulliMeasure True False p)).real (crossing n n) *
    (Measure.infinitePi (fun _ : (LatticeModels.zdGraph 2).edgeSet =>
      bernoulliMeasure True False p)).real
        (joinedCrossingIn (rectangle n n) R (bottomSide n n) (topSide n n) T) ≤
    (Measure.infinitePi (fun _ : (LatticeModels.zdGraph 2).edgeSet =>
      bernoulliMeasure True False p)).real
        (joinedCrossingIn (rectangle n n) R (leftSide n n) (rightSide n n) T) := by
  classical
  let : LinearOrder Prop := Prop.linearOrder
  let μ := Measure.infinitePi (fun _ : (LatticeModels.zdGraph 2).edgeSet =>
    bernoulliMeasure True False p)
  have : IsProbabilityMeasure μ := by
    dsimp [μ]
    infer_instance
  calc
    μ.real (crossing n n) * μ.real
        (joinedCrossingIn (rectangle n n) R (bottomSide n n) (topSide n n) T) ≤
        μ.real (crossing n n ∩
          joinedCrossingIn (rectangle n n) R (bottomSide n n) (topSide n n) T) :=
      LatticeProb.infinitePi_harris _ (isUpperSet_crossing n n)
        (isUpperSet_joinedCrossingIn _ _ _ _ _) (measurableSet_crossing n n)
        (measurableSet_joinedCrossingIn _ _ _ _ _)
    _ ≤ μ.real (joinedCrossingIn (rectangle n n) R (leftSide n n) (rightSide n n) T) := by
      apply measureReal_mono _ (measure_ne_top μ _)
      rintro η ⟨hH, hV⟩
      apply horizontal_joined_of_vertical_joined n R T hSR _ hV
      exact (mem_crossing_iff n n η).mp hH

/-- A vertical joined-crossing lower bound of one quarter implies the horizontal
joined-crossing lower bound of one eighth at the critical parameter. -/
theorem eighth_le_horizontal_joined_of_quarter_le_vertical_joined (n : ℕ)
    (hV : (1 / 4 : ℝ) ≤
      (Measure.infinitePi (fun _ : (LatticeModels.zdGraph 2).edgeSet =>
        bernoulliMeasure True False half)).real
          (joinedCrossingIn (rectangle n n) (centeredSquare n)
            (bottomSide n n) (topSide n n) (outerLeft n))) :
    (1 / 8 : ℝ) ≤
      (Measure.infinitePi (fun _ : (LatticeModels.zdGraph 2).edgeSet =>
        bernoulliMeasure True False half)).real
          (joinedCrossingIn (rectangle n n) (centeredSquare n)
            (leftSide n n) (rightSide n n) (outerLeft n)) := by
  have hSR : (rectangle n n : Set Site) ⊆ centeredSquare n := by
    intro x hx
    rw [Finset.mem_coe, centeredSquare, mem_centered_square]
    simp only [Finset.mem_coe, mem_rectangle_iff] at hx
    omega
  have h := crossing_mul_vertical_joined_le_horizontal_joined half n
    (centeredSquare n) (outerLeft n) hSR
  have hH := half_le_square_crossing n
  have hnonneg : (0 : ℝ) ≤
      (Measure.infinitePi (fun _ : (LatticeModels.zdGraph 2).edgeSet =>
        bernoulliMeasure True False half)).real (crossing n n) := measureReal_nonneg
  nlinarith

end EdgeCrossing
