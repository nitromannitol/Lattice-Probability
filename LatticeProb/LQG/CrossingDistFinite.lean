import Mathlib
import LatticeProb.LQG.HalfCrossingsOfSetDistance
import LatticeProb.LQG.InternalMetricCompactFinite
import LatticeProb.LQG.InternalMetricSquareTail
import LatticeProb.Topology.CornerSquareShells

/-!
# Finiteness of the strip crossing distances of a length metric

For a Euclidean length metric `D`, the internal distance `D(K₋, K₊; U)` between the two vertical sides of the strip
configuration at height `y₀` (`horizontalCrossingDist D y₀`), and the internal distance between the two horizontal sides
of the strip configuration at abscissa `x₀` (`verticalCrossingDist D x₀`), are finite: the open strip `U` is convex, hence
connected, and the internal metric of a Euclidean length metric is finite between any two points of a connected open set.

## Main statements

* `LatticeProb.LQG.IsEuclideanLengthMetric.horizontalCrossingDist_lt_top`, `…verticalCrossingDist_lt_top` : the
  deterministic statements.
* `LatticeProb.LQG.IsLQGMetric.ae_horizontalCrossingDist_lt_top`, `…ae_verticalCrossingDist_lt_top` : almost surely the
  strip crossing distances of the metric of the whole-plane Gaussian free field are finite.
-/

open MeasureTheory Filter Set LatticeProb.Gauss
open scoped ENNReal

namespace LatticeProb.LQG

/-- For a Euclidean length metric, the horizontal strip crossing distance is finite. -/
theorem IsEuclideanLengthMetric.horizontalCrossingDist_lt_top {D : ℂ → ℂ → ℝ} (hD : IsEuclideanLengthMetric D)
    (y₀ : ℝ) : horizontalCrossingDist D y₀ < ⊤ := by
  have hUc : Convex ℝ (Ioo (-1 : ℝ) 2 ×ℂ Ioo y₀ (y₀ + 1 / 2)) :=
    LatticeProb.Topology.convex_reProdIm (convex_Ioo _ _) (convex_Ioo _ _)
  have hUo : IsOpen (Ioo (-1 : ℝ) 2 ×ℂ Ioo y₀ (y₀ + 1 / 2)) := isOpen_Ioo.reProdIm isOpen_Ioo
  have hzU : (⟨-1 / 2, y₀ + 1 / 8⟩ : ℂ) ∈ Ioo (-1 : ℝ) 2 ×ℂ Ioo y₀ (y₀ + 1 / 2) :=
    Complex.mem_reProdIm.2 ⟨⟨by norm_num, by norm_num⟩, ⟨by linarith, by linarith⟩⟩
  have hwU : (⟨3 / 2, y₀ + 1 / 8⟩ : ℂ) ∈ Ioo (-1 : ℝ) 2 ×ℂ Ioo y₀ (y₀ + 1 / 2) :=
    Complex.mem_reProdIm.2 ⟨⟨by norm_num, by norm_num⟩, ⟨by linarith, by linarith⟩⟩
  have hzK : (⟨-1 / 2, y₀ + 1 / 8⟩ : ℂ) ∈
      ({-1 / 2} : Set ℝ) ×ℂ Icc (y₀ + 1 / 8) (y₀ + 3 / 8) :=
    Complex.mem_reProdIm.2 ⟨rfl, ⟨le_rfl, by linarith⟩⟩
  have hwK : (⟨3 / 2, y₀ + 1 / 8⟩ : ℂ) ∈
      ({3 / 2} : Set ℝ) ×ℂ Icc (y₀ + 1 / 8) (y₀ + 3 / 8) :=
    Complex.mem_reProdIm.2 ⟨rfl, ⟨le_rfl, by linarith⟩⟩
  calc horizontalCrossingDist D y₀
      ≤ internalMetric D (Ioo (-1 : ℝ) 2 ×ℂ Ioo y₀ (y₀ + 1 / 2)) ⟨-1 / 2, y₀ + 1 / 8⟩ ⟨3 / 2, y₀ + 1 / 8⟩ :=
        iInf₂_le_of_le _ hzK (iInf₂_le _ hwK)
    _ < ⊤ := hD.internalMetric_lt_top_of_isPreconnected hUc.isPreconnected hUo subset_rfl hzU hwU

/-- For a Euclidean length metric, the vertical strip crossing distance is finite. -/
theorem IsEuclideanLengthMetric.verticalCrossingDist_lt_top {D : ℂ → ℂ → ℝ} (hD : IsEuclideanLengthMetric D)
    (x₀ : ℝ) : verticalCrossingDist D x₀ < ⊤ := by
  have hUc : Convex ℝ (Ioo x₀ (x₀ + 1 / 2) ×ℂ Ioo (-1 : ℝ) 2) :=
    LatticeProb.Topology.convex_reProdIm (convex_Ioo _ _) (convex_Ioo _ _)
  have hUo : IsOpen (Ioo x₀ (x₀ + 1 / 2) ×ℂ Ioo (-1 : ℝ) 2) := isOpen_Ioo.reProdIm isOpen_Ioo
  have hzU : (⟨x₀ + 1 / 8, 3 / 2⟩ : ℂ) ∈ Ioo x₀ (x₀ + 1 / 2) ×ℂ Ioo (-1 : ℝ) 2 :=
    Complex.mem_reProdIm.2 ⟨⟨by linarith, by linarith⟩, ⟨by norm_num, by norm_num⟩⟩
  have hwU : (⟨x₀ + 1 / 8, -1 / 2⟩ : ℂ) ∈ Ioo x₀ (x₀ + 1 / 2) ×ℂ Ioo (-1 : ℝ) 2 :=
    Complex.mem_reProdIm.2 ⟨⟨by linarith, by linarith⟩, ⟨by norm_num, by norm_num⟩⟩
  have hzK : (⟨x₀ + 1 / 8, 3 / 2⟩ : ℂ) ∈ Icc (x₀ + 1 / 8) (x₀ + 3 / 8) ×ℂ ({3 / 2} : Set ℝ) :=
    Complex.mem_reProdIm.2 ⟨⟨le_rfl, by linarith⟩, rfl⟩
  have hwK : (⟨x₀ + 1 / 8, -1 / 2⟩ : ℂ) ∈ Icc (x₀ + 1 / 8) (x₀ + 3 / 8) ×ℂ ({-1 / 2} : Set ℝ) :=
    Complex.mem_reProdIm.2 ⟨⟨le_rfl, by linarith⟩, rfl⟩
  calc verticalCrossingDist D x₀
      ≤ internalMetric D (Ioo x₀ (x₀ + 1 / 2) ×ℂ Ioo (-1 : ℝ) 2) ⟨x₀ + 1 / 8, 3 / 2⟩ ⟨x₀ + 1 / 8, -1 / 2⟩ :=
        iInf₂_le_of_le _ hzK (iInf₂_le _ hwK)
    _ < ⊤ := hD.internalMetric_lt_top_of_isPreconnected hUc.isPreconnected hUo subset_rfl hzU hwU

variable {γ ξ : ℝ} {𝔇 : ((ℂ → ℝ) → ℝ) → ℂ → ℂ → ℝ} {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
  {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}

/-- Almost surely the horizontal strip crossing distance of the metric of the whole-plane Gaussian free field is
finite. -/
theorem IsLQGMetric.ae_horizontalCrossingDist_lt_top (h𝔇 : IsLQGMetric γ ξ 𝔇) (hG : IsWholePlaneGFF P hC hcirc)
    (y₀ : ℝ) : ∀ᵐ ω ∂P, horizontalCrossingDist (𝔇 (hC ω)) y₀ < ⊤ := by
  filter_upwards [h𝔇.ae_isEuclideanLengthMetric_self hG] with ω hω
  exact hω.horizontalCrossingDist_lt_top y₀

/-- Almost surely the vertical strip crossing distance of the metric of the whole-plane Gaussian free field is
finite. -/
theorem IsLQGMetric.ae_verticalCrossingDist_lt_top (h𝔇 : IsLQGMetric γ ξ 𝔇) (hG : IsWholePlaneGFF P hC hcirc)
    (x₀ : ℝ) : ∀ᵐ ω ∂P, verticalCrossingDist (𝔇 (hC ω)) x₀ < ⊤ := by
  filter_upwards [h𝔇.ae_isEuclideanLengthMetric_self hG] with ω hω
  exact hω.verticalCrossingDist_lt_top x₀

end LatticeProb.LQG
