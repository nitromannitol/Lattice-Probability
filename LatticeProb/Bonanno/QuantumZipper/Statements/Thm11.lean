/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module QuantumZipper.Statements.Thm11 at commit 31e7483; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.QuantumZipper.Statements.CouplingFields
import LatticeProb.Bonanno.QuantumZipper.Field.Law
import LatticeProb.Bonanno.QuantumZipper.GFF.Defs
import LatticeProb.Bonanno.QuantumZipper.SLE.Defs
import Mathlib.Probability.BrownianMotion.Basic
import Mathlib.Probability.Independence.Basic
import Mathlib.Analysis.SpecialFunctions.Exp

/-!
# Theorem 1.1 (forward coupling; SLE/GFF, "AC geometry")

Sheffield, *Conformal weldings of random surfaces*, Theorem 1.1.

* Main statement (`κ ∈ (0,4]`): for `f_t` the forward centered Loewner flow driven by `√κ B`
  and `h̃` a zero-boundary GFF on `ℍ` independent of `B`, the random distributions
  `𝔥₀ + h̃` and `𝔥_T + h̃∘f_T` on `ℍ` agree in law.
* Addendum (`κ ∈ (4,8)`): the same holds with `h̃∘f_T` replaced by a field which,
  conditionally on `B`, is a zero-boundary GFF on `ℍ \ η([0,T])` (STATEMENT_SPEC B4), and with
  `𝔥_T(z) := lim_{s↑τ(z)} 𝔥_s(z)` for points swallowed at time `τ(z) ≤ T`.
-/

open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace QuantumZipper

/-! ## Auxiliary notions for the addendum -/

/-- The measure `ρ⁺(z) dz` of the positive part of a test function (as in `pairTest`). -/
noncomputable def testMeasPos (ρ : ℂ → ℝ) : Measure ℂ :=
  volume.withDensity fun z => ENNReal.ofReal (ρ z)

/-- The measure `ρ⁻(z) dz` of the negative part of a test function (as in `pairTest`). -/
noncomputable def testMeasNeg (ρ : ℂ → ℝ) : Measure ℂ :=
  volume.withDensity fun z => ENNReal.ofReal (-ρ z)

/-- `Cov(⟨h,ρ⟩, ⟨h,σ⟩)` for `h` a zero-boundary GFF on the open set `U`: the dual Dirichlet
covariance `dualCov U (zeroSpace U)` of `IsZeroBoundaryGFFOn U`, expanded bilinearly on the
signed measures `ρ⁺ − ρ⁻` and `σ⁺ − σ⁻`. -/
noncomputable def zeroGFFTestCov (U : Set ℂ) (ρ σ : ℂ → ℝ) : ℝ :=
  dualCov U (zeroSpace U) (testMeasPos ρ) (testMeasPos σ)
    - dualCov U (zeroSpace U) (testMeasPos ρ) (testMeasNeg σ)
    - dualCov U (zeroSpace U) (testMeasNeg ρ) (testMeasPos σ)
    + dualCov U (zeroSpace U) (testMeasNeg ρ) (testMeasNeg σ)

/-- `IsCondZeroBoundaryGFFH U Y X' P`: conditionally on the random element `Y`, the field `X'`
is a zero-boundary GFF on the (random, `Y`-determined) open set `U ω`, as seen through its
pairings with test functions supported in `ℍ`. Conditional laws are expressed by conditional
characteristic functions: for every bounded measurable `F` of `Y`, finitely many test
functions `ρⱼ` and reals `tⱼ`,
`E[F(Y) exp(i Σ tⱼ ⟨X',ρⱼ⟩)] = E[F(Y) exp(−½ Σⱼₖ tⱼ tₖ Cov_{U ω}(ρⱼ,ρₖ))]`. The coordinates of
`X'` are required to be measurable, as in the other GFF predicates. The pairing `⟨X',ρ⟩` is the
raw pairing `pairRaw`, the same one `fieldLaw` uses (STATEMENT_SPEC A14), so the hypothesis
constrains exactly the coordinates the conclusion observes. -/
structure IsCondZeroBoundaryGFFH {Ω E : Type*} [MeasurableSpace Ω] [MeasurableSpace E]
    (U : Ω → Set ℂ) (Y : Ω → E) (X' : Ω → FieldSample) (P : Measure Ω) : Prop where
  measurable_coord : ∀ μ : Measure ℂ, Measurable fun ω => X' ω μ
  condCharFun : ∀ (n : ℕ) (ρ : Fin n → TestFun H) (t : Fin n → ℝ) (F : E → ℝ),
    Measurable F → (∃ C : ℝ, ∀ y, |F y| ≤ C) →
    ∫ ω, (F (Y ω) : ℂ) * Complex.exp (Complex.I * ((∑ j, t j * pairRaw (X' ω) (ρ j).1 : ℝ) : ℂ))
        ∂P =
      ∫ ω, (F (Y ω) : ℂ) *
          ((Real.exp (-(1 / 2) * ∑ j, ∑ k, t j * t k * zeroGFFTestCov (U ω) (ρ j).1 (ρ k).1) : ℝ)
            : ℂ) ∂P

/-- The open set `U_T = ℍ \ closure η([0,T])` of the SLE_κ trace driven by `B` at `ω`. -/
def sleComplement (κ : ℝ) {Ω : Type*} (B : ℝ≥0 → Ω → ℝ) (ω : Ω) (T : ℝ) : Set ℂ :=
  H \ closure (sleTrace κ B ω '' Set.Icc 0 T)

/-! ## The statement -/

/-- **Theorem 1.1, main statement** (Sheffield). For `κ ∈ (0,4]`, `T > 0`, a Brownian motion `B`
and a zero-boundary GFF `X` on `ℍ` independent of `B`, the random distributions `𝔥₀ + h̃` and
`𝔥_T + h̃∘f_T` on `ℍ` have the same law. Here `W = drive κ B ω`, `f_T = fwdMap W T`,
`𝔥_T = hTfwd κ W T`, and `h̃∘f_T` pairs with `μ` via the regularized evaluation of `X ω` at the
pushforward under `f_T` of `μ` restricted to `ℍ \ K_T` (`coordChangeOn`, STATEMENT_SPEC A5). -/
def theorem1_1_main : Prop :=
  ∀ κ T : ℝ, 0 < κ → κ ≤ 4 → 0 < T →
  ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (B : ℝ≥0 → Ω → ℝ) (X : Ω → FieldSample),
    IsBrownianReal B P → IsZeroBoundaryGFFH X P → IndepFun (pathOf B) X P →
    fieldLaw H (fun ω => ofFun (h0fwd κ) + X ω) P =
      fieldLaw H
        (fun ω => ofFun (hTfwd κ (drive κ B ω) T) +
          coordChangeOn (X ω) (fwdMap (drive κ B ω) T) (H \ fwdHull (drive κ B ω) T)) P

/-- **Theorem 1.1, addendum for `κ ∈ (4,8)`** (Sheffield). For `T > 0`, a Brownian motion `B`, a
zero-boundary GFF `X` on `ℍ`, and any field `X'` which, conditionally on `B`, is a zero-boundary
GFF on `ℍ \ η([0,T])` (STATEMENT_SPEC B4), the random distributions `𝔥₀ + h̃` and `𝔥_T + X'`
on `ℍ` have the same law, where `𝔥_T = hTfwdExt κ W T` is extended to swallowed points `z` by
`lim_{s↑τ(z)} 𝔥_s(z)`. -/
def theorem1_1_addendum : Prop :=
  ∀ κ T : ℝ, 4 < κ → κ < 8 → 0 < T →
  ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (B : ℝ≥0 → Ω → ℝ) (X X' : Ω → FieldSample),
    IsBrownianReal B P → IsZeroBoundaryGFFH X P →
    IsCondZeroBoundaryGFFH (fun ω => sleComplement κ B ω T) (pathOf B) X' P →
    fieldLaw H (fun ω => ofFun (h0fwd κ) + X ω) P =
      fieldLaw H (fun ω => ofFun (hTfwdExt κ (drive κ B ω) T) + X' ω) P

/-- **Theorem 1.1** (Sheffield): the main statement for `κ ∈ (0,4]` and the addendum for
`κ ∈ (4,8)`. -/
def theorem1_1 : Prop := theorem1_1_main ∧ theorem1_1_addendum

end QuantumZipper
