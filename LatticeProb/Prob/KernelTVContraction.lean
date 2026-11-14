import LatticeProb.Bonanno.QuantumZipper.Proofs.Section5.TVLocal
import Mathlib.Probability.Kernel.Composition.MeasureComp

/-!
# Total variation under a common kernel

Applying the same Markov kernel to two measures does not increase their
total variation distance.
-/

set_option autoImplicit false

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace LatticeProb

variable {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]

/-- A common Markov kernel contracts total variation. -/
theorem tvDist_comp_le (μ ν : Measure α) (κ : Kernel α β) [IsMarkovKernel κ] :
    QuantumZipper.TV.tvDist (κ ∘ₘ μ) (κ ∘ₘ ν) ≤ QuantumZipper.TV.tvDist μ ν := by
  refine iSup_le fun s => iSup_le fun hs => sup_le ?_ ?_
  · rw [Measure.bind_apply hs κ.aemeasurable, Measure.bind_apply hs κ.aemeasurable]
    exact tsub_le_iff_left.mpr (QuantumZipper.TV.lintegral_le_lintegral_add_tvDist
      (κ.measurable_coe hs) (fun x => prob_le_one))
  · rw [Measure.bind_apply hs κ.aemeasurable, Measure.bind_apply hs κ.aemeasurable]
    exact (tsub_le_iff_left.mpr (QuantumZipper.TV.lintegral_le_lintegral_add_tvDist
      (μ := ν) (ν := μ) (κ.measurable_coe hs) (fun x => prob_le_one))).trans_eq
      QuantumZipper.TV.tvDist_comm

end LatticeProb
