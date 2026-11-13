/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module QuantumZipper.Statements.Thm13 at commit fdb5cad; only the module paths of local imports are changed.
   Declarations, examples and checks that the copied results do not use are omitted. -/
import LatticeProb.Bonanno.QuantumZipper.SLE.Defs
import LatticeProb.Bonanno.QuantumZipper.GFF.Defs
import LatticeProb.Bonanno.QuantumZipper.LQG.Measures
import Mathlib.Probability.BrownianMotion.Basic
import Mathlib.Probability.Independence.Basic
import Mathlib.Analysis.Calculus.Deriv.Basic

/-!
# The field of the reverse coupling (setting of Theorems 1.2 to 1.4)

Sheffield, *Conformal weldings of random surfaces*, §1.4.

Setting (`κ ∈ (0,4)`, `γ = √κ`, `T > 0`): `B` is a standard Brownian motion, `f_T` the reverse
centered Loewner map driven by `W = √κ B` (`revMap W T`), `h̃` an independent free-boundary
GFF on `ℍ` (modulo additive constants), and
`h = 𝔥_T + h̃∘f_T`, where `𝔥_T(z) = (2/√κ) log|f_T(z)| + Q log|f_T'(z)|`, `Q = 2/γ + γ/2`.
The coordinate change of the GFF part carries no `Q`-term (it sits in `𝔥_T`), FOUNDATIONS §8.
-/

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace QuantumZipper

/-- The field of the reverse coupling (Theorem 1.2/1.3) for a deterministic driving function
`W` and a free-field sample `x`: `h = 𝔥_T + x∘f_T` with
`𝔥_T(z) = (2/√κ) log|f_T(z)| + Q log|f_T'(z)|`, `Q = Qc (√κ)`, and `f_T = revMap W T`.
The coordinate change of `x` carries no `Q`-term. (Local copy of the field of
`Statements/CouplingFields.lean`, kept independent on purpose.) -/
noncomputable def couplingFieldRev (κ : ℝ) (W : ℝ → ℝ) (T : ℝ) (x : FieldSample) :
    FieldSample :=
  ofFun (fun z => (2 / Real.sqrt κ) * Real.log ‖revMap W T z‖ +
      Qc (Real.sqrt κ) * Real.log ‖deriv (revMap W T) z‖) +
    coordChange x (revMap W T) 0

end QuantumZipper
