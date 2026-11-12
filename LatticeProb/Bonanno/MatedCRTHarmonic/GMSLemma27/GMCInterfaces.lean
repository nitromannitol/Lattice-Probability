/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module MatedCRTHarmonic.GMSLemma27.GMCInterfaces at commit 31e7483; only the module paths of local imports are changed.
   Changed: docstring wording of GMCLowerTail. -/
import LatticeProb.Bonanno.MatedCRTHarmonic.GMSLemma27.CellModel
import LatticeProb.Bonanno.LQGDimension.Statement.Defs

/-!
# SLE-free (GFF / LQG-measure) inputs of [18] Lemmas 2.7 and 2.8

: every SLE-free ingredient (GFF, circle averages, GMC/LQG area and its moments) is to be proved. The circle
averages of a whole-plane GFF are reused from the host libraries: `LQGDimension.IsGFFCircleAverage H P` (the circle
average process `H ε z = h_ε(z)` of a whole-plane GFF normalized by `h_1(0) = 0`: centered Gaussian, covariance
`gffCircleCov`, continuous in `z`), which LQGMetric produces from a normalized whole-plane GFF
(`LQGMetric.CircleAvg.exists_isGFFCircleAverage_normalized`). No whole-plane `γ`-LQG area measure exists in any
importable library (QuantumZipper's `qAreaMeasure` lives on `ℍ`, LQGMetric's GMC on
The unit square for a zero-boundary GFF), so this file

* defines the LQG area measure of a whole-plane GFF from its circle averages (`IsLQGAreaOf`, `[18]`,
  `[14]`: `μ_h = lim ε^{γ²/2} e^{γ h_ε(z)} dz` a.s. as `ε → 0` along powers of two), and
* states the two missing SLE-free facts as named interfaces, **SLE-free, to prove** (not bundle inputs):
  - `GMCLowerTail γ` — [GHM15, Lemma 3.12] , for every whole-plane GFF and its LQG
    measure (a closed statement; its proof is [GHM15]'s (3.15)–(3.19): coordinate change, [DS11, Lemma 4.5],
    Lemma 3.11);
  - `AreaDominatesWholePlaneGFF M` — the reduction in [18]'s proof of Lemma 2.8 from the quantum
    cone to the whole-plane GFF: the model's area measure dominates, on Borel subsets of `𝔻`, the LQG measure of a
    whole-plane GFF on the same sample space. It is a property of the model (an instance obligation), produced from the
    law of the field and `μ_{h̃ − γ log|·|} ≥ μ_{h̃}` on `𝔻`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Metric Filter Topology
open scoped ENNReal

namespace MatedCRTHarmonic.GMSLemma27

/-- The dyadic radius `2⁻ᵏ`. -/
def dyadicRadius (k : ℕ) : ℝ := (2 : ℝ) ^ (-(k : ℤ))

/-- The circle-average approximation `ε^{γ²/2} e^{γ h_ε(z)} dz` of the `γ`-LQG area measure at `ε = 2⁻ᵏ`
(`[18]`, `[14]`), for a circle-average process `H ε z ω = h_ε(z)`. -/
def lqgApprox {Ω : Type*} (γ : ℝ) (H : ℝ → ℂ → Ω → ℝ) (k : ℕ) (ω : Ω) : Measure ℂ :=
  volume.withDensity fun z =>
    ENNReal.ofReal (dyadicRadius k ^ (γ ^ 2 / 2) * Real.exp (γ * H (dyadicRadius k) z ω))

/-- **The `γ`-LQG area measure of a whole-plane GFF**, defined from its circle averages: almost surely `μ ω` is a
locally finite measure and the vague limit of `ε^{γ²/2} e^{γ h_ε(z)} dz` as `ε → 0` along powers of two (`[18]`:
"`μ_h = lim_{ε→0} ε^{γ²/2} e^{γ h_ε(z)} dz` in the Prokhorov distance (or local Prokhorov distance, if `D` is unbounded)
as `ε → 0` along powers of 2 [DS11]"; `[14]`: "The limit is shown to exist a.s. when `ε` is restricted to powers
of two"). Vague limits of locally finite measures on `ℂ` are unique, so `μ` is determined almost surely by `H`. -/
def IsLQGAreaOf {Ω : Type*} [MeasurableSpace Ω] (γ : ℝ) (H : ℝ → ℂ → Ω → ℝ) (μ : Ω → Measure ℂ)
    (P : Measure Ω) : Prop :=
  ∀ᵐ ω ∂P, IsLocallyFiniteMeasure (μ ω) ∧
    ∀ f : ℂ → ℝ, Continuous f → HasCompactSupport f →
      Tendsto (fun k : ℕ => ∫ z, f z ∂(lqgApprox γ H k ω)) atTop (𝓝 (∫ z, f z ∂(μ ω)))

/-- **SLE-free, to prove** — [GHM15, Lemma 3.12] (the whole-plane GMC construction): "Let `h` be a
whole-plane GFF, let `μ_h` be its `γ`-quantum area measure, and let `(h_ε)` be its circle average process. For each
`z ∈ ℂ`, each `ε ∈ (0, 1)`, and each `δ ∈ (0, 1)`, `P(μ_h(B_ε(z)) < δ ε^{2+γ²/2} e^{γ h_ε(z)}) = o^∞_δ(δ)`"
(uniformly in `z` and `ε`: by (3.16), the probability equals `P(μ_h(B_1(0)) < δ)` for a normalized
`h`; the source's "rate depending only on `r` and `R`" refers to unused parameters).

Stated for the circle average process `H` of a whole-plane GFF normalized by `h_1(0) = 0` and its LQG measure `μ`
(`IsLQGAreaOf`), with `o^∞_δ(δ)` written out: for every `s ∈ ℝ` and `c > 0` there is `δ₀ > 0` with probability
`≤ c δ^s` for all `δ ∈ (0, δ₀)`, `z ∈ ℂ`, `ε ∈ (0, 1)`. To be proved for `γ ∈ (0, 2)` (the standing range of
[GHM15] and [18]; for `γ ≥ 2` the vague limit is `μ = 0`). Producer: the SLE-free GMC construction
(whole-plane LQG measure; [DS11, Prop. 2.1, Lemma 4.5]; [GHM15, Lemma 3.11]). -/
def GMCLowerTail (γ : ℝ) : Prop :=
  ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) (H : ℝ → ℂ → Ω → ℝ) (μ : Ω → Measure ℂ),
    LQGDimension.IsGFFCircleAverage H P → IsLQGAreaOf γ H μ P →
      ∀ s c : ℝ, 0 < c → ∃ δ₀ : ℝ, 0 < δ₀ ∧ ∀ δ ∈ Ioo (0 : ℝ) δ₀, ∀ z : ℂ, ∀ ε ∈ Ioo (0 : ℝ) 1,
        (P {ω | μ ω (ball z ε) <
          ENNReal.ofReal (δ * ε ^ (2 + γ ^ 2 / 2) * Real.exp (γ * H ε z ω))}).toReal ≤ c * δ ^ s

variable {γ : ℝ}

/-- **SLE-free, to prove** (an obligation of the cell-model instance) — the reduction in [18]'s proof of Lemma 2.8: "If `h` is a circle-average embedding of an `α`-quantum cone, then `h|_𝔻` agrees in law with a
whole-plane GFF normalized so that its circle average over `∂𝔻` is 0 plus `−α log|·|`. If `h` is a whole-plane GFF, then
`μ_{h−α log|·|}(A) ≥ μ_h(A)` for each Borel set `A ⊂ 𝔻`. So, we can restrict attention to the case when `h` is a
whole-plane GFF normalized so that its circle average over `∂𝔻` is 0." In coupling form: the model's sample space
carries the circle average process `H` of a normalized whole-plane GFF `h̃` and its LQG measure `μ̃`, and almost surely
`μ̃(A) ≤ μ_h(A)` for every Borel `A ⊆ 𝔻`. Producer: for the `γ`-quantum cone of the quantum-cone case, the circle-average
embedding's law on `𝔻` (DMS `[14]`, realized as an a.s. identity `h|_𝔻 = (h̃ − γ log|·|)|_𝔻` on the instance's
sample space) and `μ_{h̃ − γ log|·|} = |·|^{−γ²} μ_{h̃} ≥ μ_{h̃}` on `𝔻`; for `h` a normalized whole-plane GFF,
`μ̃ = μ_h`. -/
def AreaDominatesWholePlaneGFF (M : CellModel γ) : Prop :=
  ∃ (H : ℝ → ℂ → M.Ω → ℝ) (μ : M.Ω → Measure ℂ),
    LQGDimension.IsGFFCircleAverage H M.P ∧ IsLQGAreaOf γ H μ M.P ∧
      ∀ᵐ ω ∂M.P, ∀ A : Set ℂ, MeasurableSet A → A ⊆ ball (0 : ℂ) 1 → μ ω A ≤ M.area ω A

end MatedCRTHarmonic.GMSLemma27
