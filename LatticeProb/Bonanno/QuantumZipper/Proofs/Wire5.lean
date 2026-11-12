/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module QuantumZipper.Proofs.Wire5 at commit fdb5cad; only the module paths of local imports are changed.
   Declarations, examples and checks that the copied results do not use are omitted.
   Imports of copied modules that this file does not need are replaced by their own imports. -/
import LatticeProb.Bonanno.QuantumZipper.Proofs.Probability.Williams.W6Main
import LatticeProb.Bonanno.QuantumZipper.Proofs.LQG.ZoomRadialFinal

/-!
# Wire5: the consumers of `WilliamsDriftDecomposition`, made unconditional

`QuantumZipper.Williams.williamsDriftDecomposition_holds`
(`Proofs/Probability/Williams/W6Main.lean`) proves the Williams drift decomposition (L14,

```
∀ μ σ c > 0, Ω, P, b, b' : the pasting path `Zp` of `X = σ b - μ·` at its first hit of `-c`
with the reversed path `Yh` of `Y' = σ b' + μ·` has the law of `Yh`)
```

see D. Williams, *Path decomposition and continuity of local time for one-dimensional
diffusions I*, Proc. LMS 28 (1974), and L. C. G. Rogers, J. W. Pitman, *Markov functions*,
Ann. Probab. 9 (1981), Thm 1; Revuz–Yor, *Continuous Martingales and Brownian Motion*, VII.4.

Six theorems in the repository take that decomposition as an explicit hypothesis
`(hW : WilliamsDriftDecomposition)`. This file discharges that hypothesis in each of them,
producing unconditional statements (`*_uncond`) with the same conclusions and the same
remaining hypotheses, valid at universe `0` (as the originals, since
`WilliamsDriftDecomposition` quantifies over `Ω : Type`):

* `WedgeTrans.translation_good` → `Wire5.translation_good_uncond`
* `WedgeTrans.wedge_translation` → `Wire5.wedge_translation_uncond`
  (the same statement as `QuantumZipper.Williams.wedge_translation_uncond`, reproduced here so
  that a consumer needs only this module)
* `ZoomRadial.prob_Tc_lt_le_prob_wedge_high` → `Wire5.prob_Tc_lt_le_prob_wedge_high_uncond`
* `ZoomRadial.abs_prob_zoomRadial_sub_le` → `Wire5.abs_prob_zoomRadial_sub_le_uncond`
* `ZoomRadial.prob_trunc_Rw_eq_prob_trunc_wedge` → `Wire5.prob_trunc_Rw_eq_prob_trunc_wedge_uncond`
* `ZoomRadial.williams_law` → `Wire5.williams_law_uncond`

Every proof is the original theorem applied to `williamsDriftDecomposition_holds`; no
mathematics is added here.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology

namespace QuantumZipper
namespace Wire5

open QuantumZipper.ZoomRadial QuantumZipper.WedgeTrans

/-- **B4(c), unconditional.** `WedgeTrans.wedge_translation` with the Williams drift
decomposition (L14) discharged: wedge translation invariance. (Same statement as
`QuantumZipper.Williams.wedge_translation_uncond`.) -/
theorem wedge_translation_uncond {Ω : Type} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {α Q : ℝ} {A : ℝ → Ω → ℝ}
    (hA : IsWedgeProcess α Q A P) (hαQ : α < Q) {c : ℝ} (hc : 0 < c) :
    P.map (fun ω t => A (sInf {s | 0 ≤ s ∧ A s ω ≤ -c} + t) ω + c) =
      P.map (fun ω t => A t ω) :=
  WedgeTrans.wedge_translation (hW := QuantumZipper.Williams.williamsDriftDecomposition_holds)
    hA hαQ hc

end Wire5
end QuantumZipper
