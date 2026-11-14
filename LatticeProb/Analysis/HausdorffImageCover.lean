import Mathlib.Topology.MetricSpace.HausdorffDimension

/-!
# Hausdorff dimension of image covers

A set covered by countably many Lipschitz images and a countable exceptional set has dimension at most a common bound
for the dimensions of the source sets. The Lipschitz constants may depend on the index.
-/

open Set
open scoped ENNReal NNReal

namespace LatticeProb

/-- A countable exceptional set and countably many Lipschitz images do not increase a common Hausdorff-dimension
bound on the source sets. -/
theorem dimH_le_of_subset_countable_lipschitz_images
    {ι X Y : Type*} [Countable ι] [EMetricSpace X] [EMetricSpace Y]
    {S E : Set Y} {A : ι → Set X} {f : ι → X → Y} {K : ι → ℝ≥0} {d : ℝ≥0∞}
    (hE : E.Countable) (hf : ∀ i, LipschitzWith (K i) (f i))
    (hA : ∀ i, dimH (A i) ≤ d) (hS : S ⊆ E ∪ ⋃ i, f i '' A i) : dimH S ≤ d := by
  calc
    dimH S ≤ dimH (E ∪ ⋃ i, f i '' A i) := dimH_mono hS
    _ = max (dimH E) (⨆ i, dimH (f i '' A i)) := by rw [dimH_union, dimH_iUnion]
    _ ≤ d := max_le (hE.dimH_zero ▸ bot_le) (iSup_le fun i => ((hf i).dimH_image_le (A i)).trans (hA i))

end LatticeProb
