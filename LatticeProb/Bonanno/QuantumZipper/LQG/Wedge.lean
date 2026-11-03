/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module QuantumZipper.LQG.Wedge at commit 31e7483; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.QuantumZipper.Field.CoordsFull
import LatticeProb.Bonanno.QuantumZipper.LQG.Surfaces
import LatticeProb.Bonanno.QuantumZipper.GFF.Defs

/-!
# The α-quantum wedge (canonical description)
-/

noncomputable section

open MeasureTheory ProbabilityTheory

namespace QuantumZipper

/-- `Y` under `P` is an α-quantum wedge: the canonical description of Sheffield §1.6, (1.10).
Its law (through circle coordinates jointly with test pairings, STATEMENT_SPEC A16) equals that
of `canonical γ (h† + Q·(-log|·|) + A_{-log|·|})`, with `h†` the lateral part of a free GFF on
`ℍ` and `A` the independent wedge radial process. The reference law is unique, so this pins
down the law of `Y`. The range `α < Q` is the corrected range (STATEMENT_SPEC B1). -/
def IsQuantumWedge (γ α : ℝ) {Ω : Type*} [MeasurableSpace Ω] (Y : Ω → FieldSample)
    (P : Measure Ω) : Prop :=
  α < Qc γ ∧ ∃ (Ω' : Type) (_ : MeasurableSpace Ω') (P' : Measure Ω') (X : Ω' → FieldSample)
    (A : ℝ → Ω' → ℝ), IsProbabilityMeasure P' ∧ IsFreeGFFModConstH X P' ∧
    IsWedgeProcess α (Qc γ) A P' ∧ IndepFun X (fun ω t => A t ω) P' ∧
    fieldLawFull H Y P = fieldLawFull H
      (fun ω => canonical γ (wedgeField (lateralPart (X ω)) (fun t => A t ω) (Qc γ))) P'

end QuantumZipper
