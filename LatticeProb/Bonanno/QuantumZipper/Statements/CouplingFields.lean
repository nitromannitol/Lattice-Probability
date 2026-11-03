/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module QuantumZipper.Statements.CouplingFields at commit 31e7483; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.QuantumZipper.Field.Sample
import LatticeProb.Bonanno.QuantumZipper.Loewner.Forward
import LatticeProb.Bonanno.QuantumZipper.Loewner.Reverse
import Mathlib.Analysis.SpecialFunctions.Complex.Arg
import Mathlib.Analysis.Calculus.Deriv.Basic

/-!
# The deterministic fields of the SLE/GFF couplings (Theorems 1.1 and 1.2)

Sheffield, *Conformal weldings of random surfaces*, §1.4 and §4.1.

* Reverse coupling (Theorem 1.2): `𝔥₀(z) = (2/√κ) log|z|` and
  `𝔥_T(z) = 𝔥₀(f_T(z)) + Q log|f_T'(z)|`, with `Q = 2/√κ + √κ/2` and `f_T` the reverse
  centered Loewner map.
* Forward coupling (Theorem 1.1): `𝔥₀(z) = −(2/√κ) arg z` and
  `𝔥_T(z) = 𝔥₀(f_T(z)) − χ arg f_T'(z)` on `ℍ \ K_T`, with `χ = 2/√κ − √κ/2` and `f_T` the
  forward centered Loewner map. `arg f_T'` is `(logDerivFwd W T z).im` (STATEMENT_SPEC A4).
* The `κ ∈ (4,8)` extension of `𝔥_T` to swallowed points, `𝔥_T(z) := lim_{s↑τ(z)} 𝔥_s(z)`.
* `coordChangeOn`: the composition `h̃∘f_T` of a field with a map that is only defined on a
  subset `D` (STATEMENT_SPEC A5): the test measure is restricted to `D` and pushed forward.

These are specification definitions only.
-/

open MeasureTheory Filter Classical
open scoped Topology ENNReal

namespace QuantumZipper

/-! ## Reverse coupling (Theorem 1.2) -/

/-- `𝔥₀(z) = (2/√κ) log|z|`, the deterministic part of the reverse coupling (Theorem 1.2). -/
noncomputable def h0rev (κ : ℝ) (z : ℂ) : ℝ := 2 / Real.sqrt κ * Real.log ‖z‖

/-- `𝔥_T(z) = 𝔥₀(f_T(z)) + Q log|f_T'(z)|` with `Q = 2/√κ + √κ/2` and `f_T = revMap W T` the
reverse centered Loewner map (Theorem 1.2). `log|f_T'|` is literally `log ‖deriv f_T z‖`
(STATEMENT_SPEC A4). -/
noncomputable def hTrev (κ : ℝ) (W : ℝ → ℝ) (T : ℝ) (z : ℂ) : ℝ :=
  h0rev κ (revMap W T z) + Qc (Real.sqrt κ) * Real.log ‖deriv (revMap W T) z‖

/-! ## Forward coupling (Theorem 1.1) -/

/-- `𝔥₀(z) = −(2/√κ) arg z`, the deterministic part of the forward coupling (Theorem 1.1).
On `ℍ` mathlib's `Complex.arg` takes values in `(0, π)`, which is the paper's branch; the
values off `ℍ` are irrelevant since all test functions are supported in `ℍ`. -/
noncomputable def h0fwd (κ : ℝ) (z : ℂ) : ℝ := -(2 / Real.sqrt κ) * Complex.arg z

/-- `𝔥_T(z) = 𝔥₀(f_T(z)) − χ arg f_T'(z)` for `z ∈ ℍ \ K_T`, with `χ = 2/√κ − √κ/2`,
`f_T = fwdMap W T` the forward centered Loewner map and `arg f_T' = (logDerivFwd W T z).im`
(the continuous branch vanishing at `∞`, STATEMENT_SPEC A4). The value `0` on `K_T` and off `ℍ`
is a junk value; for `κ ≤ 4` the hull `K_T = η_T` is Lebesgue-null. -/
noncomputable def hTfwd (κ : ℝ) (W : ℝ → ℝ) (T : ℝ) (z : ℂ) : ℝ :=
  if z ∈ H \ fwdHull W T then
    h0fwd κ (fwdMap W T z) - chiC κ * (logDerivFwd W T z).im
  else 0

/-- The extension of `𝔥_T` used in the `κ ∈ (4,8)` addendum of Theorem 1.1: for a point `z ∈ ℍ`
swallowed at time `τ(z) ≤ T`, `𝔥_T(z) := lim_{s ↑ τ(z)} 𝔥_s(z)` (left limit, `limUnder`,
junk value if the limit fails to exist); otherwise `hTfwd κ W T z`. For `s < τ(z)`,
`z` is not yet swallowed, so the expression under the limit is the formula of `hTfwd` at
time `s`. -/
noncomputable def hTfwdExt (κ : ℝ) (W : ℝ → ℝ) (T : ℝ) (z : ℂ) : ℝ :=
  if z ∈ fwdHull W T then
    limUnder (𝓝[<] (swallowTime W z).toReal)
      (fun s : ℝ => h0fwd κ (fwdMap W s z) - chiC κ * (logDerivFwd W s z).im)
  else hTfwd κ W T z

/-! ## Composition with a partially defined map -/

/-- `coordChangeOn x ψ D` is the field `h∘ψ` (no `Q`-term) for a map `ψ` defined only on `D`:
it pairs with `μ` by the regularized evaluation of `x` at the pushforward under `ψ` of `μ`
restricted to `D` (STATEMENT_SPEC A5). With `ψ = f_T` and `D = ℍ \ K_T` this is the paper's
`h̃∘f_T` as a distribution on `ℍ`, also for test functions whose support meets `η_T`. -/
noncomputable def coordChangeOn (x : FieldSample) (ψ : ℂ → ℂ) (D : Set ℂ) : FieldSample :=
  fun μ => evalReg x ((μ.restrict D).map ψ)

end QuantumZipper
