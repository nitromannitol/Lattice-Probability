/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module QuantumZipper.Proofs.LQG.RegularSampleDefs at commit 31e7483; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.QuantumZipper.Field.Sample
import Mathlib.Topology.UniformSpace.LocallyUniformConvergence

/-!
# Regular field samples (blueprint `M4_BLUEPRINT.md`, §0 and node M4-R4)

A field sample `x` is *regular* when its folded-circle averages at **every** centre
`w ∈ Hbar` and **every** radius `r > 0` are given by one function `F`, continuous on
`Hbar × (0,∞)`, in the following sense:

* (i) at dyadic radii `2^{-k}`, the raw values `x (foldedCircle (dyadicRoundC n z) 2^{-k})`
  converge to `F (z, 2^{-k})` (so `avgReg x k z = F (z, 2^{-k})`) for every `z ∈ Hbar`;
* (ii) the smoothed values `∫ F(u, ρ) d(foldedCircle w r)(u)` converge to `F (w, r)` as
  `ρ → 0⁺`, locally uniformly in `(w, r) ∈ Hbar × (0,∞)`.

Clause (i) is stated with convergence (not just with the value of `avgReg`, which is a
`limUnder` and would be junk without convergence), so that regularity is stable under the
deterministic operations of node M4-R4. Consequence (proved in `RegularClosure`):
`evalReg x (foldedCircle w r) = F (w, r)` for every `w ∈ Hbar`, `r > 0`.
-/

noncomputable section

open MeasureTheory Filter
open scoped Topology

namespace QuantumZipper

/-- `x` is regular with witness `F` (blueprint §0, "Regular sample"). -/
def IsRegularWith (x : FieldSample) (F : ℂ × ℝ → ℝ) : Prop :=
  ContinuousOn F (Hbar ×ˢ Set.Ioi 0) ∧
    (∀ k : ℕ, ∀ z ∈ Hbar,
      Tendsto (fun n => x (foldedCircle (dyadicRoundC n z) (radius k))) atTop
        (𝓝 (F (z, radius k)))) ∧
    TendstoLocallyUniformlyOn (fun (ρ : ℝ) (p : ℂ × ℝ) => ∫ u, F (u, ρ) ∂foldedCircle p.1 p.2)
      F (𝓝[>] 0) (Hbar ×ˢ Set.Ioi 0)

/-- **Regular sample** (blueprint §0 / M4-R4): some `F`, continuous on `Hbar × (0,∞)`,
represents all dyadic circle averages of `x` and is recovered from itself by vanishing
circle smoothing, locally uniformly. -/
def IsRegularSample (x : FieldSample) : Prop := ∃ F : ℂ × ℝ → ℝ, IsRegularWith x F

end QuantumZipper
