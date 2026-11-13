/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.Frozen.Disconnects at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.Frozen.EuclideanAnnulusDilate

/-! Scratch freeze split of SLUMetric.lean:202. -/
set_option autoImplicit false
noncomputable section

open Set Filter Topology MeasureTheory
open scoped ENNReal

namespace SupercriticalLQGUniqueness

/-- `K` disconnects `E` from `F` (DG l. 551, 556; Euclidean topology by DG l. 985): no connected
subset of the complement of `K` meets both `E` and `F`. -/
def Disconnects {X : Type*} [TopologicalSpace X] (K E F : Set X) : Prop :=
  ¬ ∃ S : Set X, IsPreconnected S ∧ S ⊆ Kᶜ ∧ (S ∩ E).Nonempty ∧ (S ∩ F).Nonempty
end SupercriticalLQGUniqueness
