/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module MatedCRTHarmonic.GMSLemma27.SLEInterfaces at commit 31e7483; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.MatedCRTHarmonic.GMSLemma27.CellModel

/-!
# SLE-dependent inputs of [18] Lemma 2.7 ( bundle inputs)

: every ingredient that needs SLE is an input, stated faithfully with its source line, and will be collected
into the audited bundle `MatedCRT.MatingOfTreesInput γ`. The proof of [18] Lemma 2.7 uses exactly one
SLE fact (the cell-model argument "Inputs", §5 item S8(a)):

* `SegmentsContainBalls M` — [GHM15, Proposition 3.4 and Remark 3.9, (3.8)] , for the curve of the cell model: for `r ∈ (0, 1)` and `R > 0`, except on an event of probability
  `o^∞_ε(ε)`, every segment `η([a, b])` contained in `B_R(0)` with `diam ≥ δ^{1−r}` (`δ ∈ (0, ε]`) contains a ball of
  radius `≥ δ`.

It is an imaginary-geometry statement about the unparametrized curve (the curve geometry argument): the segments `η([a, b])`, `a < b`,
of the `μ_h`-mass parametrization are those of any increasing reparametrization, and the cell alignment is irrelevant.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Metric Filter Topology Asymptotics
open scoped ENNReal

namespace MatedCRTHarmonic.GMSLemma27

variable {γ : ℝ}

/-- The event `E_ε = E_ε(R, r)` of [GHM15, Proposition 3.4] for the curve of the cell
model: "For each `δ ∈ (0, ε]` and each `a < b ∈ ℝ` such that `η'([a, b]) ⊂ B_R(0)` and `diam η'([a, b]) ≥ δ^{1−r}`,
The set `η'([a, b])` contains a ball of radius at least `δ`." -/
def segmentBallEvent (M : CellModel γ) (R r ε : ℝ) : Set M.Ω :=
  {ω | ∀ δ ∈ Ioc (0 : ℝ) ε, ∀ a b : ℝ, a < b → M.curve ω '' Icc a b ⊆ ball (0 : ℂ) R →
    δ ^ (1 - r) ≤ diam (M.curve ω '' Icc a b) →
      ∃ c : ℂ, ∃ t : ℝ, δ ≤ t ∧ ball c t ⊆ M.curve ω '' Icc a b}

/-- **SLE input** ([GHM15, Proposition 3.4 + Remark 3.9]; used in the proof of [18]
Lemma 2.7, `[18]`). Verbatim source: Proposition 3.4, "Let `η'` be a
space-filling SLE_{κ'} from `∞` to `∞` in `ℂ`. For `r ∈ (0, 1)`, `R > 0`, and `ε > 0`, let `E_ε = E_ε(R, r)` be the
event that the following is true. For each `δ ∈ (0, ε]` and each `a < b ∈ ℝ` such that `η'([a, b]) ⊂ B_R(0)` and
`diam η'([a, b]) ≥ δ^{1−r}`, the set `η'([a, b])` contains a ball of radius at least `δ`", strengthened by Remark 3.9
 to "`P(E_εᶜ) = o^∞_ε(ε)`, as `ε → 0`, i.e., this probability decays faster than any positive power of
`ε`" (Notation 1.4, : `a = o^∞_x(b)` if `a = o_x(b^s)` for each `s ∈ ℝ`). Stated for the curve `η` of the cell
model (the whole-plane space-filling SLE_{κ'}, `κ' = 16/γ²`, parametrized by `μ_h`-mass; only its segments enter);
`P(E_εᶜ)` is the outer measure. Producer: the bundle `MatingOfTreesInput`. -/
def SegmentsContainBalls (M : CellModel γ) : Prop :=
  ∀ r ∈ Ioo (0 : ℝ) 1, ∀ R : ℝ, 0 < R → ∀ s : ℝ,
    (fun ε : ℝ => (M.P (segmentBallEvent M R r ε)ᶜ).toReal) =o[𝓝[>] (0 : ℝ)] fun ε => ε ^ s

end MatedCRTHarmonic.GMSLemma27
