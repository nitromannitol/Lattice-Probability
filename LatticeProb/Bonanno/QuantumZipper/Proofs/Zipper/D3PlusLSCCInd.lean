/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module QuantumZipper.Proofs.Zipper.D3PlusLSCCInd at commit fdb5cad;
   trimmed to the product total variation bound. -/

import LatticeProb.Bonanno.QuantumZipper.Proofs.Section5.TVLocal

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal

namespace QuantumZipper
namespace D3Plus

/-- `d_TV(μ ⊗ ν, μ' ⊗ ν') ≤ d_TV(μ, μ') + d_TV(ν, ν')` (own elementary argument from
`TV.tvDist_prod_right_le` and the swap symmetry). -/
theorem lscc_tvDist_prod_le {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    {μ μ' : Measure α} {ν ν' : Measure β} [IsProbabilityMeasure μ] [IsProbabilityMeasure μ']
    [IsProbabilityMeasure ν] [IsProbabilityMeasure ν'] :
    TV.tvDist (μ.prod ν) (μ'.prod ν') ≤ TV.tvDist μ μ' + TV.tvDist ν ν' := by
  refine TV.tvDist_triangle.trans (add_le_add TV.tvDist_prod_right_le ?_)
  rw [← Measure.prod_swap (μ := ν) (ν := μ'), ← Measure.prod_swap (μ := ν') (ν := μ')]
  exact (TV.tvDist_map_le measurable_swap).trans TV.tvDist_prod_right_le

end D3Plus
end QuantumZipper
