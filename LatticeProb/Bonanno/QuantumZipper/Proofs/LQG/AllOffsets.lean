/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module QuantumZipper.Proofs.LQG.AllOffsets at commit fdb5cad; only the module paths of local imports are changed.
   Declarations, examples and checks that the copied results do not use are omitted.
   Opens of namespaces with no copied declaration are removed (BdryVague, GaussTK). -/
import LatticeProb.Bonanno.QuantumZipper.Proofs.LQG.AllOffsetsModulus

/-!
Blueprint `M4_BLUEPRINT.md`, nodes M4-B4 and M4-T2.

* `ae_hasBdryLimit`: for the free field (any additive-constant convention), almost surely
  `HasBdryLimit γ (X ω) (qBoundaryMeasure γ (X ω))`, i.e. the approximations `ν_{a 2^{-k}}`
  converge vaguely to `qBoundaryMeasure γ (X ω)` **uniformly in `a ∈ [1,2]`**.
  Proof (grid plus modulus): for `f` in the countable test family and a level-`n` dyadic offset
  `a`, `|ν_{aε}(f) − ν(f)| ≤ ∫ |f| d_{2ε} · chainT + ∑_{grid} |ν_{cε}(f) − ν(f)|`
  (`pathwise_bound`); the expectation of the right side is `≤ C θ^m + (2^m+1) C 2^{-βk}`
  uniformly in `n` (`lintegral_sup_level_le`); with `m = ⌊βk/2⌋` this is summable in `k`, and the
  continuity of the densities in the radius (every-circle regularity) passes from dyadic
  offsets to all of `[1,2]`.
* M4-T2: `qBoundaryMeasure_translate` and `qBoundaryMeasure_reflectH` (for good samples and
  every real `t` at once).
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Real Set
open scoped NNReal ENNReal

namespace QuantumZipper
namespace AllOffsets

open BdryExist TwoRadius GoodSample

/-! ## C0. Countable test family along `goodFilter` -/

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {X : Ω → FieldSample}

/-! ## C1. Pathwise bound -/

/-! ## C2. Expectation at a fixed level -/

/-! ## C3. Summation over the scales -/

theorem dpt_double (n i : ℕ) : dpt n i = dpt (n + 1) (2 * i) := by
  unfold dpt; push_cast; rw [pow_succ]; field_simp

/-! ## C4. Almost sure uniform convergence for the normalized field -/

/-! ## C5. Back to the free field -/

/-! ## T2. Translation and reflection (M4-T2) -/

section T2

variable {x : FieldSample} {γ : ℝ}

end T2

end AllOffsets
end QuantumZipper
