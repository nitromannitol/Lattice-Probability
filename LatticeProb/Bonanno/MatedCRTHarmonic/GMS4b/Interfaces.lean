/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module MatedCRTHarmonic.GMS4b.Interfaces at commit fdb5cad; only the module paths of local imports are changed.
   Declarations, examples and checks that the copied results do not use are omitted. -/
import LatticeProb.Bonanno.MatedCRTHarmonic.GMS4b.Packing
import LatticeProb.Bonanno.MatedCRTHarmonic.GMSLemma27.Lemma27

/-!
# Named inputs of [18] §4

The definitions below state inputs from [18] or its cited literature. Each names the mathematical property used later.

SLE-dependent input supplied by `MatingOfTreesInput`:
* `SpaceFillingGeometry` — the curve is surjective, transient and (as an increasing reparametrization of the
  Lebesgue-parametrized space-filling SLE) has Lebesgue-null overlaps of time-disjoint segments.

SLE-free (listed below):
* `UpperMassBound` — the upper mass estimate: `[16]` Lemma A.3 plus a union bound over a grid.
* `CircleAverageSupBound` — [MS16b] Proposition 2.4 with a covering (as used in Proposition 4.5).

The inner-degree conclusion of [18] Lemma 4.6 is used in Proposition 4.5:
* `InnerDegreeBound` — [18] Lemma 4.6, (4.12).

The L27 interfaces `GMSLemma27.SegmentsContainBalls` (bundle S8(a)), `GMSLemma27.GMCLowerTail` and
`GMSLemma27.AreaDominatesWholePlaneGFF` (SLE-free) are reused unchanged.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Metric Filter Topology
open scoped ENNReal

namespace MatedCRTHarmonic.GMS4b

open MatedCRTHarmonic.GMSLemma27

variable {γ : ℝ}

/-- ** bundle input (via MTC)** — the space-filling SLE of the cell model, parametrized by `γ`-LQG mass, is a.s.
surjective and transient (`η(t) → ∞` as `|t| → ∞`) (`[18]`: "a well-defined continuous curve `η : ℝ → ℂ`
which traces the points of `ℚ²`"; whole-plane space-filling SLE from `∞` to `∞`; DMS Lemma 8.11, `DMS`),
and segments over time intervals with disjoint interiors intersect in a Lebesgue-null set (`[18]`,
"different segments of the form `η([a, b])` as above intersect only along their boundaries"; it follows from the
Lebesgue parametrization `area(η_L([a, b])) = b − a`, `[18]`, by `nullOverlaps_of_reparam`).
Producer: the bundle fields `spaceFilling` and `areaParam`/`areaParam₀` of `MatingOfTreesInput` (MTC adapter). -/
def SpaceFillingGeometry (M : CellModel γ) : Prop :=
  ∀ᵐ ω ∂M.P, Function.Surjective (M.curve ω) ∧ Tendsto (M.curve ω) (cocompact ℝ) (cocompact ℂ) ∧
    NullOverlaps (M.curve ω)

/-- **SLE-free, to prove** — the upper LQG-mass bound used for the lower diameter bound in (4.18) (as used in Lemma 4.7,
and Details (c7): "By [16, Lem A.3] with `α = 0`, `P[μ_h(B_δ(z)) > δ^ξ] ≤ δ^{−pξ} δ^{p(2+γ²/2)−γ²p²/2}`. Over a
`δ`-grid of `B_ρ` … the failure is `≤ δ^{f(p)}` … `f(p*) > 0 ⟺ ξ < (2−γ)²/2`"). Stated for the cell model's area
measure: there are exponents `ξ, β > 0` such that for each `ρ ∈ (0, 1)`, with polynomially small failure probability
`O(δ^β)`, every ball `B_δ(z)` with `z ∈ B_ρ(0)` has mass at most `δ^ξ`. Producer: the GMC estimate from
`[16]` Lemma A.3 for the whole-plane GFF and the `0`-quantum cone. -/
def UpperMassBound (M : CellModel γ) : Prop :=
  ∃ ξ β : ℝ, 0 < ξ ∧ 0 < β ∧ ∀ ρ ∈ Ioo (0 : ℝ) 1, ∃ C : ℝ, ∀ δ ∈ Ioo (0 : ℝ) 1,
    M.P {ω | ∃ z ∈ ball (0 : ℂ) ρ, ENNReal.ofReal (δ ^ ξ) < M.area ω (ball z δ)} ≤ ENNReal.ofReal (C * δ ^ β)

/-- **SLE-free, to prove** — [MS16b] Proposition 2.4 (the supremum of circle averages; cited at `[18]` as
"[MS16b, Corollary 2.5]", corrected to Proposition 2.4: "`P[sup_{B(0,1/2)}|h_r| ≥ (2+δ′) log r⁻¹] ≤
c₀ r^{2δ′(1−ξ)}` …, with a covering and normalisation argument for `B_ρ`"). For a circle-average process `H r z ω`
(`= h_r(z)`) of a whole-plane GFF normalized by `h_1(0) = 0` (or of a field agreeing with it in law on `𝔻`): for each
`δ′ > 0` there is `β > 0` such that for each `ρ ∈ (0, 1)`,
`P[∃ z ∈ B_ρ(0), |h_r(z)| > (2 + δ′) log r⁻¹] = O(r^β)` for `r ∈ (0, 1)`. Producer: the GFF estimate ( LQGMetric's
DFGPS `lem2_2`, Borell–TIS `tail_iSup_abs_le`). -/
def CircleAverageSupBound {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (H : ℝ → ℂ → Ω → ℝ) : Prop :=
  ∀ δ' : ℝ, 0 < δ' → ∃ β : ℝ, 0 < β ∧ ∀ ρ ∈ Ioo (0 : ℝ) 1, ∃ C : ℝ, ∀ r ∈ Ioo (0 : ℝ) 1,
    P {ω | ∃ z ∈ ball (0 : ℂ) ρ, (2 + δ') * Real.log r⁻¹ < |H r z ω|} ≤ ENNReal.ofReal (C * r ^ β)

end MatedCRTHarmonic.GMS4b
