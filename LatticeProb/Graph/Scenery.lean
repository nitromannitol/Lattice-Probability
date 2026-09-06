/-
The i.i.d. initial masses and the moment vocabulary of
`ssec:notation`.

How the paper's objects are modelled here:

- The common marginal is a probability measure `ν` on `ℝ`, and the field
  `(σ(v))_{v ∈ V}` is distributed as `iidLaw V ν`, the product measure on
  `V → ℝ`.  The walk is independent of the field because the two live on
  different spaces, which is how every statement below reads them.
- `extMean ν` is the extended expectation `E[σ] ∈ [-∞,∞]` of `ssec:notation`,
  built as the difference of the two `lintegral`s of the positive and the
  negative part, so `+∞` and `-∞` are values and not junk.  The indeterminate
  case, where both parts are infinite, is excluded by the hypothesis
  `HasExtMean`, exactly as the paper excludes it.
- `posMoment ν p` is `E[(σ⁺)^p]` and `absMoment ν p` is `E[|σ|^p]`, in `ℝ≥0∞`,
  so that "finite `p`-th moment" is the statement that they are not `⊤`.
- `Symmetric ν` is symmetry of the law about `0`.
-/
import LatticeProb.Graph.Basic
import Mathlib.Probability.ProductMeasure
import Mathlib.Probability.Moments.Variance


open MeasureTheory
open scoped ENNReal

namespace LatticeProb.Graph

/-- The law of an i.i.d. field indexed by `V` with common marginal `ν`. -/
noncomputable def iidLaw (V : Type*) (ν : Measure ℝ) : Measure (V → ℝ) :=
  Measure.infinitePi fun _ : V => ν

/-- `E[σ⁺]`, in `[0,∞]`. -/
noncomputable def posPart (ν : Measure ℝ) : ℝ≥0∞ := ∫⁻ z, ENNReal.ofReal z ∂ν

/-- `E[σ⁻]`, in `[0,∞]`. -/
noncomputable def negPart (ν : Measure ℝ) : ℝ≥0∞ := ∫⁻ z, ENNReal.ofReal (-z) ∂ν

/-- The extended expectation `E[σ] ∈ [-∞,∞]` of `ssec:notation`. -/
noncomputable def extMean (ν : Measure ℝ) : EReal := (posPart ν : EReal) - (negPart ν : EReal)

/-- The convention of `ssec:notation`: the indeterminate case
`E[σ⁺] = E[σ⁻] = ∞` is excluded. -/
def HasExtMean (ν : Measure ℝ) : Prop := posPart ν ≠ ⊤ ∨ negPart ν ≠ ⊤

/-- `E[(σ⁺)^p]`, in `[0,∞]`. -/
noncomputable def posMoment (ν : Measure ℝ) (p : ℝ) : ℝ≥0∞ :=
  ∫⁻ z, ENNReal.ofReal (max z 0 ^ p) ∂ν

/-- `E[|σ|^p]`, in `[0,∞]`. -/
noncomputable def absMoment (ν : Measure ℝ) (p : ℝ) : ℝ≥0∞ :=
  ∫⁻ z, ENNReal.ofReal (|z| ^ p) ∂ν

/-- `E[|σ - m|^p]`, in `[0,∞]`. -/
noncomputable def centeredMoment (ν : Measure ℝ) (m p : ℝ) : ℝ≥0∞ :=
  ∫⁻ z, ENNReal.ofReal (|z - m| ^ p) ∂ν

/-- The law `ν` is symmetric about `0`. -/
def IsSymmetric (ν : Measure ℝ) : Prop := ν.map (fun z => -z) = ν

/-- The variance of the marginal, in `[0,∞]`. -/
noncomputable def evar (ν : Measure ℝ) : ℝ≥0∞ := ProbabilityTheory.evariance id ν

end LatticeProb.Graph
