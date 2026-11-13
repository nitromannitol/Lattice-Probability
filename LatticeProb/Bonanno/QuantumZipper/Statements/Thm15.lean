/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module QuantumZipper.Statements.Thm15 at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.QuantumZipper.Statements.ConfigLaw
import LatticeProb.Bonanno.QuantumZipper.Statements.CouplingFields
import LatticeProb.Bonanno.QuantumZipper.GFF.Defs
import LatticeProb.Bonanno.QuantumZipper.SLE.Defs
import Mathlib.Probability.BrownianMotion.Basic
import Mathlib.Probability.Independence.Basic

/-!
# Corollary 1.5 (capacity quantum zipper)

Sheffield, *Conformal weldings of random surfaces*, Corollary 1.5. Specification only.

Fix `κ ∈ (0,4)` and `γ = √κ`. Let `h = 𝔥₀ + h̃` be Theorem 1.2's field modulo additive
constants (`𝔥₀ = h0rev κ = (2/√κ) log|·|`, `h̃` a free-boundary GFF on `ℍ`) and `η` an
independent SLE_κ from `0` to `∞`, with driving function `W = √κ B`. The pair of quantum
surfaces `((D₁,h|D₁),(D₂,h|D₂))` is encoded by the configuration `(h, W)` (A8), and the capacity
zipper `Z^CAP_t` is `zipCap γ t` (`Zipper/Maps.lean`): zip up by the welding-determined reverse
flow `f^h_t` for `t ≥ 0`, unzip by the forward flow `f^η_{−t}` for `t < 0`.

Claims: (a) the law of the pair is invariant under `Z^CAP_t` for all `t ∈ ℝ`;
(b) `Z^CAP_{s+t} = Z^CAP_s Z^CAP_t` a.s. for all `s, t ∈ ℝ`.
-/

open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace QuantumZipper

/-- **Corollary 1.5** (Sheffield). For `κ ∈ (0,4)`, `γ = √κ`, a Brownian motion `B` and a
free-boundary GFF `X` on `ℍ` modulo additive constants, independent of `B`, let
`c ω = (𝔥₀ + X ω, √κ B(·, ω))` be the configuration encoding the pair of quantum surfaces cut
out of `(ℍ, h)` by the SLE_κ curve `η` driven by `√κ B`. Then:

* (a) for every `t ∈ ℝ`, `Z^CAP_t c` has the same law as `c`: joint law of the field modulo
  additive constants (raw pairings with mass-zero test functions on `ℍ`) and of the driving
  function on `[0,∞)` (`configLawMod0`, A8 + A14);
* (b) for all `s, t ∈ ℝ`, almost surely `Z^CAP_{s+t} c = Z^CAP_s (Z^CAP_t c)`, up to equality of
  regularized fields and of drivers on `[0,∞)` (`ConfigEq`, A13).

Design notes. The field is modulo additive constants because Theorem 1.2's `h` is; `zipCap`
depends on the constant only through the welding `R_h`, which is invariant under scaling `ν_h`.
In (a), raw pairings are legitimate on both sides: the fields produced by `zipCap` are
coordinate changes, whose raw values are regularized evaluations of the input field (A14).
`Measure.map` returns a Dirac mass for maps that are not a.e.-measurable
(`MeasureTheory.Measure.map_of_not_aemeasurable_of_ne_zero`); since the right-hand side
`configLawMod0 c P` is not a Dirac mass, (a) also asserts
a.e.-measurability of the zipped configuration (the choice `weldDriver` enters only through
its values on `[0,t]`, which are a.s. unique by Theorem 1.4). -/
def theorem1_5 : Prop :=
  ∀ κ : ℝ, 0 < κ → κ < 4 →
  ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (B : ℝ≥0 → Ω → ℝ) (X : Ω → FieldSample),
    IsBrownianReal B P → IsFreeGFFModConstH X P → IndepFun (pathOf B) X P →
    let γ := Real.sqrt κ
    let c : Ω → FieldSample × (ℝ → ℝ) := fun ω => (ofFun (h0rev κ) + X ω, drive κ B ω)
    -- (a) law invariance under `Z^CAP_t`, `t ∈ ℝ`
    (∀ t : ℝ, configLawMod0 (fun ω => zipCap γ t (c ω)) P = configLawMod0 c P) ∧
    -- (b) group property, almost surely for each fixed `s, t`
    (∀ s t : ℝ, ∀ᵐ ω ∂P, ConfigEq (zipCap γ (s + t) (c ω)) (zipCap γ s (zipCap γ t (c ω))))

end QuantumZipper
