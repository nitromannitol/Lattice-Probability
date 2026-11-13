/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module QuantumZipper.Statements.ConfigLaw at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.QuantumZipper.Zipper.Maps
import LatticeProb.Bonanno.QuantumZipper.Field.CoordsFull

/-!
# Laws and equality of zipper configurations

Shared helpers for the statements of Corollary 1.5 (`Statements/Thm15.lean`) and Theorem 1.8
(`Statements/Thm18.lean`). `FOUNDATIONS.md` §7, `STATEMENT_SPEC.md` A8, A12, A13, A14, A16.

A *configuration* is a pair `c = (x, W) : FieldSample × (ℝ → ℝ)`: a field `x` on `ℍ` and the
driving function `W` of a curve `η` from `0` to `∞` (A8). It encodes the pair of quantum
surfaces `((D₁, h|D₁), (D₂, h|D₂))` cut out by `η`. Only the values of `W` on `[0,∞)` carry
meaning: `Zipper/Maps.lean` clamps negative times, and `drive` sets `W t = 0` for `t < 0`.
Hence laws compare drivers only through their restriction to `[0,∞)` (as functions
`ℝ≥0 → ℝ`), and equality of configurations compares drivers on `[0,∞)` only.

* `configLawMod0`: joint law of (raw pairings with mass-zero test functions, driver on
  `[0,∞)`) (A14; fields modulo additive constants, Corollary 1.5).
* `lawData`: the law-relevant data of a random field of wedge type (positive-radius circle
  coordinates `coordsFull` and raw pairings); used for independence in Theorem 1.8.
* `configLawFull`: joint law of (`lawData` of the field, driver on `[0,∞)`)
  (A16; wedge-type fields, Theorem 1.8).
* `ConfigEq`: equality of regularized fields and of drivers on `[0,∞)` (A13).
* `unzippedField`: the field unzipped by capacity time `s` (A12).

The length zipper `Z^LEN_t` of Theorem 1.8 is defined constructively in
`Zipper/LengthZip.lean` (`zipLenC`). The earlier choice-based inverse (`IsWeldableConfig`,
`zipLenWeld`) was retired after audit AUDIT-1 §3.
-/

noncomputable section

open MeasureTheory Filter Set
open scoped Topology NNReal ENNReal

namespace QuantumZipper

open CoordsFull

variable {Ω : Type*} [MeasurableSpace Ω]

/-- The law of a random configuration `c : Ω → FieldSample × (ℝ → ℝ)` with the field taken
modulo additive constants (Corollary 1.5, "the law of the pair", A8 + A14): the joint law of
the raw pairings of the field with all mass-zero test functions supported in `ℍ` and of the
driving function restricted to `[0,∞)`. -/
def configLawMod0 (c : Ω → FieldSample × (ℝ → ℝ)) (P : Measure Ω) :
    Measure ((TestFun0 H → ℝ) × (ℝ≥0 → ℝ)) :=
  P.map fun ω => (fun ρ => pairRaw (c ω).1 ρ.1.1, fun t : ℝ≥0 => (c ω).2 t)

/-- The law-relevant data of a random field `Y` of wedge type at `ω` (A16, AUDIT-1 §1–2): the
raw values `coordsFull (Y ω)` at all dyadic folded circles of positive radius, together with the
raw pairings of `Y ω` with all test functions supported in `ℍ`. Laws, and independence, of
wedge-type fields are stated through this map. Raw values at other measures (e.g. point
masses) are deliberately not included: they are junk for regularized fields and can leak
non-intrinsic data such as an embedding scale. -/
def lawData (Y : Ω → FieldSample) (ω : Ω) : (ℕ → ℝ) × (TestFun H → ℝ) :=
  (coordsFull (Y ω), fun ρ => pairRaw (Y ω) ρ.1)

/-- The law of a random configuration whose field is of wedge type (Theorem 1.8, A8 + A16):
the joint law of the full circle coordinates `coordsFull` of the field (positive radii), its
raw pairings with all test functions supported in `ℍ` (together: `lawData`), and the driving
function restricted to `[0,∞)`. Circle coordinates are included because test pairings alone
do not determine the boundary measure (A16), and Theorem 1.8's zipper reads the boundary
measure. The field is not taken modulo
constants: a wedge's canonical description fixes the additive constant. -/
def configLawFull (c : Ω → FieldSample × (ℝ → ℝ)) (P : Measure Ω) :
    Measure (((ℕ → ℝ) × (TestFun H → ℝ)) × (ℝ≥0 → ℝ)) :=
  P.map fun ω => (lawData (fun ω => (c ω).1) ω, fun t : ℝ≥0 => (c ω).2 t)

/-- Equality of configurations (A13): the fields agree after regularization (`RegEq`: all
regularized circle averages agree) and the driving functions agree on `[0,∞)` (their values at
negative times carry no meaning). Corollary 1.5 (b) and Theorem 1.8 (1)–(2) (round trips and
group property of the zippers) are stated up to this relation. -/
def ConfigEq (c c' : FieldSample × (ℝ → ℝ)) : Prop :=
  RegEq c.1 c'.1 ∧ ∀ u : ℝ, 0 ≤ u → c.2 u = c'.2 u

/-- The field of a configuration unzipped by capacity time `s` along its own curve:
`h ∘ f_s⁻¹ + Q log|(f_s⁻¹)'|`, with `f_s` the centered forward map of the driver and
`Q = Qc γ`. It is the field whose boundary measure defines `unzipLengths γ c s` (A12). -/
def unzippedField (γ : ℝ) (c : FieldSample × (ℝ → ℝ)) (s : ℝ) : FieldSample :=
  coordChange c.1 (fwdMapInv c.2 s) (Qc γ)

/-- `unzipLengths` measures lengths with `unzippedField`. -/
theorem unzipLengths_eq_unzippedField (γ : ℝ) (c : FieldSample × (ℝ → ℝ)) (t : ℝ) :
    unzipLengths γ c t =
      (qBoundaryMeasure γ (unzippedField γ c t) (Icc (sideImages c.2 t).1 0),
        qBoundaryMeasure γ (unzippedField γ c t) (Icc 0 (sideImages c.2 t).2)) := rfl

end QuantumZipper
