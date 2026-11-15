import LatticeProb.Prob.KernelTVContraction

/-! Stability of comparison between a measurable image and a Markov kernel. -/

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace LatticeProb

/-- Comparing the image of a finite measure with the result of a Markov kernel
is stable under total variation approximation of the input measure. -/
theorem tvDist_map_comp_le_of_approx {α β : Type*} [MeasurableSpace α]
    [MeasurableSpace β] (μ ν : Measure α) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    {f : α → β} (hf : Measurable f) (κ : Kernel α β) [IsMarkovKernel κ] :
    QuantumZipper.TV.tvDist (μ.map f) (κ ∘ₘ μ) ≤
      QuantumZipper.TV.tvDist (ν.map f) (κ ∘ₘ ν) +
        (QuantumZipper.TV.tvDist μ ν + QuantumZipper.TV.tvDist μ ν) := by
  calc
    _ ≤ QuantumZipper.TV.tvDist (μ.map f) (ν.map f) +
        QuantumZipper.TV.tvDist (ν.map f) (κ ∘ₘ μ) :=
      QuantumZipper.TV.tvDist_triangle
    _ ≤ QuantumZipper.TV.tvDist (μ.map f) (ν.map f) +
        (QuantumZipper.TV.tvDist (ν.map f) (κ ∘ₘ ν) +
          QuantumZipper.TV.tvDist (κ ∘ₘ ν) (κ ∘ₘ μ)) :=
      add_le_add le_rfl QuantumZipper.TV.tvDist_triangle
    _ ≤ QuantumZipper.TV.tvDist μ ν +
        (QuantumZipper.TV.tvDist (ν.map f) (κ ∘ₘ ν) +
          QuantumZipper.TV.tvDist ν μ) :=
      add_le_add (QuantumZipper.TV.tvDist_map_le hf)
        (add_le_add le_rfl (tvDist_comp_le ν μ κ))
    _ = _ := by rw [QuantumZipper.TV.tvDist_comm (μ := ν) (ν := μ)]; ac_rfl

end LatticeProb
