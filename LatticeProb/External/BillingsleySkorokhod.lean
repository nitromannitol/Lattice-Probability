import LatticeProb.Prob.Cadlag.Measurable
import Mathlib.Topology.MetricSpace.Polish

/-!
# Billingsley: the finite-horizon Skorokhod space is Polish

P. Billingsley, *Convergence of Probability Measures*, second edition, Wiley (1999),
Theorem 12.1 (the metrics `d` and `d°` are equivalent) and Theorem 12.2 (`D` is separable under
`d` and `d°` and complete under `d°`), with the range-space amendments on p. 131 (a separable
complete metric range space) and the extension from `D[0,1]` to `D[0,t]` on p. 166. The
proposition is stated so that a formalization citing it can carry it as an explicit hypothesis;
it is not proved here.
-/

namespace LatticeProb.External

open TopologicalSpace

/-- **Billingsley, Theorems 12.1–12.2 with pp. 131 and 166.** For a separable complete normed
range space and a positive horizon, the J1 Skorokhod space is separable and completely
metrizable. -/
def BillingsleySkorokhodPolish : Prop :=
  ∀ (E : Type) [NormedAddCommGroup E] [SeparableSpace E] [CompleteSpace E],
    ∀ T : ℝ, 0 < T →
      SeparableSpace (Cadlag.D T E) ∧ IsCompletelyMetrizableSpace (Cadlag.D T E)

end LatticeProb.External
