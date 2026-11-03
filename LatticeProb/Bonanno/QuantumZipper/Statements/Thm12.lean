/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module QuantumZipper.Statements.Thm12 at commit 31e7483; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.QuantumZipper.Statements.CouplingFields
import LatticeProb.Bonanno.QuantumZipper.Field.Law
import LatticeProb.Bonanno.QuantumZipper.GFF.Defs
import LatticeProb.Bonanno.QuantumZipper.SLE.Defs
import Mathlib.Probability.BrownianMotion.Basic
import Mathlib.Probability.Independence.Basic

/-!
# Theorem 1.2 (reverse coupling; SLE/LQG)

Sheffield, *Conformal weldings of random surfaces*, Theorem 1.2. Fix `κ > 0`, `T > 0`, let
`f_t` be the reverse centered Loewner flow driven by `W = √κ B`, and let `h̃` be a
free-boundary GFF on `ℍ` independent of `B`. Then `h := 𝔥₀ + h̃` and
`h∘f_T + Q log|f_T'| = 𝔥_T + h̃∘f_T` agree in law as random distributions on `ℍ` modulo
additive constants.
-/

open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace QuantumZipper

/-- **Theorem 1.2** (Sheffield). For `κ > 0`, `T > 0`, a Brownian motion `B`, and a free-boundary
GFF `X` on `ℍ` modulo additive constants independent of `B` (independence of the path
`pathOf B : Ω → (ℝ≥0 → ℝ)` and of `X : Ω → FieldSample`, both with the product σ-algebra), the
random fields `𝔥₀ + h̃` and `𝔥_T + h̃∘f_T` have the same law modulo additive constants, i.e.
the same joint law of pairings with all mass-zero test functions supported in `ℍ`.

The driving function is `W = drive κ B ω = √κ B(·, ω)` and `f_T = revMap W T`. The term
`Q log|f_T'|` is part of `hTrev`, so the coordinate change of the GFF part `h̃∘f_T` carries
`Q = 0` (STATEMENT_SPEC A5). -/
def theorem1_2 : Prop :=
  ∀ κ T : ℝ, 0 < κ → 0 < T →
  ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (B : ℝ≥0 → Ω → ℝ) (X : Ω → FieldSample),
    IsBrownianReal B P → IsFreeGFFModConstH X P → IndepFun (pathOf B) X P →
    fieldLawMod0 H (fun ω => ofFun (h0rev κ) + X ω) P =
      fieldLawMod0 H
        (fun ω => ofFun (hTrev κ (drive κ B ω) T) + coordChange (X ω) (revMap (drive κ B ω) T) 0)
        P

end QuantumZipper
