/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DFGPS.Nodes at commit fdb5cad; only the module paths of local imports are changed.
   Changed: docstring wording of a comment. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DFGPS.Defs
import LatticeProb.Bonanno.LQGMetric.Blueprint.DFGPSEstimatesF
import LatticeProb.Bonanno.LQGMetric.Field.StandardBorelDistOn
import LatticeProb.Bonanno.LQGMetric.Blueprint.DFGPSEstimates
import LatticeProb.Bonanno.LQGMetric.Field.Measurable
import Mathlib.Analysis.Distribution.TestFunction
import Mathlib.Topology.ContinuousMap.SecondCountableSpace
import Mathlib.Topology.ContinuousMap.Compact
import Mathlib.LinearAlgebra.Multilinear.FiniteDimensional
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Topology.Compactness.SigmaCompact
import Mathlib.Topology.Instances.RealVectorSpace
import Mathlib.Topology.Algebra.IsUniformGroup.Basic
import Mathlib.MeasureTheory.Constructions.Polish.Basic
import Mathlib.Analysis.LocallyConvex.WithSeminorms
import Mathlib.Data.Finsupp.Encodable

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# DFGPS: the exported nodes of the proof plan (`blueprint/DF.md` §3, §5)

Statements of the DFGPS nodes that cross work packages (P3.1, L3.6, P3.9, P3.10, L3.19, L3.21,
L4.5, L1.3, L2.6, L2.12, L2.13, L2.14, L2.17, L2.20) and the assembly types. A package that needs a node of
an unfinished package takes it as an argument of exactly this type; the assembly discharges it.
Source: DFGPS arXiv:1905.00380, `lqg-metric-estimates-final.tex` ("T"), lines in the docstrings.
D90 (decisions/DEC-90.md, DV-D90): in `Lem2_13`, `Lem2_17`, `Lem2_20` the joint convergence in law of
`(h, 𝔞⁻¹D^ε_h)` is tested in the coordinates `pairJ ⊤ ∘ h` of the field (Polish), not in mathlib's
compact-convergence topology on `DistC`.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal

namespace LQGMetric.DFGPS
open Blueprint

/-! ## §3–4 (weak metric part) -/

/-- **DFGPS Prop 3.1** (`prop-two-set-dist`, T:1414–1420); `U` connected (the proof uses it, T:1580,
and the statement fails for disconnected `U`: DEV-DFGPS-L35 (a)) -/
def Prop3_1 : Prop :=
  ∀ γ : ℝ, 0 < γ → γ < 2 → ∀ (D : DistC → ContMetric) (c : ℝ → ℝ), IsWeakLQGMetric γ D c →
    ∀ (U K₁ K₂ : Set ℂ), IsOpen U → IsConnected U → IsCompact K₁ → IsCompact K₂ → IsConnected K₁ →
      IsConnected K₂ → K₁ ⊆ U → K₂ ⊆ U → Disjoint K₁ K₂ → ¬ K₁.Subsingleton →
      ¬ K₂.Subsingleton →
    ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] (h : Ω → DistC),
      IsNormalizedWPGFF h P → SuperPolyHighProbA P fun A 𝕣 => {ω |
        ENNReal.ofReal (A⁻¹ * scaleFac (xiGamma γ) c (h ω) 𝕣 0) ≤
            setDistIn (D (h ω)) (scaleSet 𝕣 0 K₁) (scaleSet 𝕣 0 K₂) (scaleSet 𝕣 0 U) ∧
          setDistIn (D (h ω)) (scaleSet 𝕣 0 K₁) (scaleSet 𝕣 0 K₂) (scaleSet 𝕣 0 U) ≤
            ENNReal.ofReal (A * scaleFac (xiGamma γ) c (h ω) 𝕣 0)}

/-- **DFGPS Lemma 3.6** (`lem-lfpp-dist`, T:1628–1650; GFF only) -/
def Lem3_6 : Prop :=
  ∀ γ : ℝ, 0 < γ → γ < 2 → ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (h : Ω → DistC), IsNormalizedWPGFF h P → ∀ ζ ∈ Ioo (0 : ℝ) 1,
    ∀ η : ℝ, 0 < η → ∃ δ₀ : ℝ, 0 < δ₀ ∧ ∀ δ ∈ Ioo (0 : ℝ) δ₀, ∀ 𝕣 : ℝ, 0 < 𝕣 →
      P {ω | ¬ (δ ^ (-xiGamma γ * Q γ + ζ) * Real.exp (xiGamma γ * circleAvg (h ω) 𝕣 0) ≤
          graphLFPP (xiGamma γ) (δ * 𝕣) (fun x => circleAvg (h ω) (δ * 𝕣) x)
            (leftVerts (δ * 𝕣) 𝕣) (rightVerts (δ * 𝕣) 𝕣) (rS 𝕣) ∧
        graphLFPP (xiGamma γ) (δ * 𝕣) (fun x => circleAvg (h ω) (δ * 𝕣) x)
            (leftVerts (δ * 𝕣) 𝕣) (rightVerts (δ * 𝕣) 𝕣) (rS 𝕣) ≤
          δ ^ (-xiGamma γ * Q γ - ζ) * Real.exp (xiGamma γ * circleAvg (h ω) 𝕣 0))} ≤
        ENNReal.ofReal η

/-- **DFGPS Prop 3.10** (`prop-moment-square`, T:1757–1762) -/
def Prop3_10 : Prop :=
  ∀ γ : ℝ, 0 < γ → γ < 2 → ∀ (D : DistC → ContMetric) (c : ℝ → ℝ), IsWeakLQGMetric γ D c →
    ∀ p : ℝ, p < 4 * dGamma γ / γ ^ 2 → ∃ Cp : ℝ, ∀ {Ω : Type} [MeasurableSpace Ω]
      (P : Measure Ω) [IsProbabilityMeasure P] (h : Ω → DistC), IsNormalizedWPGFF h P →
      ∀ 𝕣 : ℝ, 0 < 𝕣 → ∫⁻ ω, (ENNReal.ofReal (scaleFac (xiGamma γ) c (h ω) 𝕣 0)⁻¹ *
          internalDiam (D (h ω)) (rS 𝕣) (rS 𝕣)) ^ p ∂P ≤ ENNReal.ofReal Cp

/-- **DFGPS Prop 3.9** (`prop-moment`, T:1747–1755) -/
def Prop3_9 : Prop :=
  ∀ γ : ℝ, 0 < γ → γ < 2 → ∀ (D : DistC → ContMetric) (c : ℝ → ℝ), IsWeakLQGMetric γ D c →
    ∀ (U K : Set ℂ), IsOpen U → IsCompact K → IsConnected K → K ⊆ U → ¬ K.Subsingleton →
    ∀ p : ℝ, p < 4 * dGamma γ / γ ^ 2 → ∃ Cp : ℝ, ∀ {Ω : Type} [MeasurableSpace Ω]
      (P : Measure Ω) [IsProbabilityMeasure P] (h : Ω → DistC), IsNormalizedWPGFF h P →
      ∀ 𝕣 : ℝ, 0 < 𝕣 → ∫⁻ ω, (ENNReal.ofReal (scaleFac (xiGamma γ) c (h ω) 𝕣 0)⁻¹ *
          internalDiam (D (h ω)) (scaleSet 𝕣 0 K) (scaleSet 𝕣 0 U)) ^ p ∂P ≤ ENNReal.ofReal Cp

/-- the square of side `s` centred at `z` -/
def sqCentred (s : ℝ) (z : ℂ) : Set ℂ :=
  scaleSet s (z - ((s / 2 : ℝ) : ℂ) * (1 + Complex.I)) {x | 0 < x.re ∧ x.re < 1 ∧ 0 < x.im ∧ x.im < 1}

/-! ## §2 (LFPP part) -/

/-- **DFGPS Lemma 1.3** (`lem-prob-conv`, T:381–385) -/
def Lem1_3 : Prop :=
  ∀ {Ω α β : Type} [MeasurableSpace Ω] [TopologicalSpace α] [MeasurableSpace α] [BorelSpace α]
    [PolishSpace α] [MetricSpace β] [MeasurableSpace β] [BorelSpace β] [PolishSpace β]
    (P : Measure Ω) [IsProbabilityMeasure P] (X : Ω → α) (Y : Ω → β) (Yn : ℕ → Ω → β),
    Measurable X → Measurable Y → (∀ n, Measurable (Yn n)) →
    (∀ φ : α × β → ℝ, Continuous φ → (∃ C, ∀ x, |φ x| ≤ C) →
      Tendsto (fun n => ∫ ω, φ (X ω, Yn n ω) ∂P) atTop (𝓝 (∫ ω, φ (X ω, Y ω) ∂P))) →
    AEDeterminedBy Y X P → TendstoInMeasure P Yn atTop Y

-- DFGPS Lemma 2.6 (T:837–856) is proved: `DFGPS.lem2_6` (a.s. for a whole-plane GFF, with
-- `h^r = affineComp r 0 h`) and `DFGPS.lem2_6_law` in `Papers/DFGPS/L2_6*.lean`.

/-- **DFGPS Lemma 2.12** (`lem-weyl-scaling`, T:1026–1031; factor `𝔞⁻¹` restored, DEV-DFGPS-3),
for a Skorokhod coupling of the convergence along `εn` -/
def Lem2_12 : Prop :=
  ∀ γ : ℝ, 0 < γ → γ < 2 → ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (h : Ω → DistC) (Dh : Ω → ContMetric) (εn : ℕ → ℝ),
    IsGFFPlusBddCont h P → (∀ n, 0 < εn n) → Tendsto εn atTop (𝓝 0) →
    (∀ᵐ ω ∂P, ∀ R : ℝ, 0 < R → TendstoUniformlyOn
      (fun n p => (aEpsDF (xiGamma γ) (εn n))⁻¹ * lfppDist (xiGamma γ) (εn n) (h ω) p)
      (fun p => (Dh ω).1 p) atTop (Metric.closedBall 0 R ×ˢ Metric.closedBall 0 R)) →
    ∀ᵐ ω ∂P, ∀ (fn : ℕ → C(ℂ, ℝ)) (f : C(ℂ, ℝ)) (M : ℝ), (∀ n z, |fn n z| ≤ M) →
      (∀ z, |f z| ≤ M) →
      (∀ R : ℝ, 0 < R → TendstoUniformlyOn (fun n => ⇑(fn n)) ⇑f atTop (Metric.closedBall 0 R)) →
      ∀ R : ℝ, 0 < R → TendstoUniformlyOn
        (fun n (p : ℂ × ℂ) => (aEpsDF (xiGamma γ) (εn n))⁻¹ *
          lfppDist (xiGamma γ) (εn n) (addFun (h ω) (fn n)) p)
        (fun p => (weylScale (xiGamma γ) f (Dh ω) p.1 p.2).toReal) atTop
        (Metric.closedBall 0 R ×ˢ Metric.closedBall 0 R)

/-- **DFGPS Lemma 2.14** (`lem-lfpp-constant`, T:1073–1098), in the form D78: for every sequence
`εn → 0` there are constants `𝔠_r > 0`, each a cluster point of `r 𝔞_{εn/r}/𝔞_{εn}`, with the
Λ-bounds (eqn-scaling-constant', T:1065–1066). The paper asserts the limit exists (T:1077); its
argument (T:1080–1095) needs the median of the internal crossing of the limit metric, which is not
a function of the limit (T:999–1000) and need not be unique (S8), and no consumer needs the limit
(Lemma 2.13 only uses a subsequential limit of the ratio): DEC-78, DV-D78 -/
def Lem2_14 : Prop :=
  ∀ γ : ℝ, 0 < γ → γ < 2 → ∀ (εn : ℕ → ℝ), (∀ n, 0 < εn n) → Tendsto εn atTop (𝓝 0) →
    ∃ (c : ℝ → ℝ) (Λ : ℝ), 1 < Λ ∧
      (∀ r : ℝ, 0 < r → 0 < c r ∧ MapClusterPt (c r) atTop
        (fun n => r * aEpsDF (xiGamma γ) (εn n / r) / aEpsDF (xiGamma γ) (εn n))) ∧
      ∀ δ ∈ Ioo (0 : ℝ) 1, ∀ r : ℝ, 0 < r →
        Λ⁻¹ * δ ^ Λ ≤ c (δ * r) / c r ∧ c (δ * r) / c r ≤ Λ * δ ^ (-Λ)

/-- **DFGPS Lemma 2.13** (`lem-lfpp-coord`, T:1060–1071; proof T:1101–1119), D78: for a sequence
`εn → 0` there are deterministic `𝔠_r` (those of `Lem2_14`) such that for every coupling of the
normalized field `h` with a subsequential limit `D_h` of `(h, 𝔞_{εn}⁻¹ D^{εn}_h)` in law (joint
convergence, the hypothesis of the paper's statement T:1062 and of `Lem2_17`, `Lem2_20`), the laws
of `𝔠_r⁻¹ e^{−ξ h_r(0)} D_h(r·,r·)`, `r > 0`, are tight, their Prokhorov closure is carried by
continuous metrics, and the Λ-bounds hold: Axiom V (`TightAcrossScales`) for normalized `h`. -/
def Lem2_13 : Prop :=
  ∀ γ : ℝ, 0 < γ → γ < 2 → ∀ (εn : ℕ → ℝ), (∀ n, 0 < εn n) → Tendsto εn atTop (𝓝 0) →
    ∃ (c : ℝ → ℝ) (Λ : ℝ), 1 < Λ ∧
      (∀ r : ℝ, 0 < r → 0 < c r ∧ MapClusterPt (c r) atTop
        (fun n => r * aEpsDF (xiGamma γ) (εn n / r) / aEpsDF (xiGamma γ) (εn n))) ∧
      (∀ δ ∈ Ioo (0 : ℝ) 1, ∀ r : ℝ, 0 < r →
        Λ⁻¹ * δ ^ Λ ≤ c (δ * r) / c r ∧ c (δ * r) / c r ≤ Λ * δ ^ (-Λ)) ∧
      ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
        (h : Ω → DistC) (Dh : Ω → ContMetric),
        IsNormalizedWPGFF h P → Measurable Dh →
        (∀ φ : (CoordJ → ℝ) × C(ℂ × ℂ, ℝ) → ℝ, Continuous φ → (∃ C, ∀ x, |φ x| ≤ C) →
          Tendsto (fun n => ∫ ω, φ (pairJ ⊤ (h ω), toCMap fun p =>
              (aEpsDF (xiGamma γ) (εn n))⁻¹ * lfppDist (xiGamma γ) (εn n) (h ω) p) ∂P) atTop
            (𝓝 (∫ ω, φ (pairJ ⊤ (h ω), (Dh ω).1) ∂P))) →
        let X : ℝ → Ω → C(ℂ × ℂ, ℝ) := fun r ω =>
          ((c r)⁻¹ * Real.exp (-xiGamma γ * circleAvg (h ω) r 0)) • (Dh ω).1.comp (scaleArgs r)
        IsTightMeasureSet {μ | ∃ r : ℝ, 0 < r ∧ μ = P.map (X r)} ∧
        ∀ μ : ProbabilityMeasure C(ℂ × ℂ, ℝ),
          μ ∈ closure {ν : ProbabilityMeasure C(ℂ × ℂ, ℝ) |
            ∃ r : ℝ, 0 < r ∧ (ν : Measure C(ℂ × ℂ, ℝ)) = P.map (X r)} →
          ∀ᵐ d ∂(μ : Measure C(ℂ × ℂ, ℝ)), IsContinuousMetric d

/-- **DFGPS Lemma 2.20** (`lem-lfpp-msrble`, T:1297–1302), with **DFGPS Thm 2.21** = `LMCor1_8`:
a subsequential limit `D_h` (coupled with `h`) is a.s. determined by `h` -/
def Lem2_20 : Prop :=
  ∀ γ : ℝ, 0 < γ → γ < 2 → ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (h : Ω → DistC) (Dh : Ω → ContMetric) (εn : ℕ → ℝ),
    IsNormalizedWPGFF h P → Measurable Dh → (∀ n, 0 < εn n) → Tendsto εn atTop (𝓝 0) →
    (∀ φ : (CoordJ → ℝ) × C(ℂ × ℂ, ℝ) → ℝ, Continuous φ → (∃ C, ∀ x, |φ x| ≤ C) →
      Tendsto (fun n => ∫ ω, φ (pairJ ⊤ (h ω), toCMap fun p =>
          (aEpsDF (xiGamma γ) (εn n))⁻¹ * lfppDist (xiGamma γ) (εn n) (h ω) p) ∂P) atTop
        (𝓝 (∫ ω, φ (pairJ ⊤ (h ω), (Dh ω).1) ∂P))) →
    AEDeterminedBy Dh h P ∧
      TendstoInProbLU P (fun n ω => (aEpsDF (xiGamma γ) (εn n))⁻¹ •
        lfppDist (xiGamma γ) (εn n) (h ω)) atTop (fun ω => (Dh ω).1)

/-- **DFGPS Lemma 2.17** (`lem-lfpp-local`, T:1150–1155): the limit is a ξ-additive local metric
(LM Def 1.5, through `LMLem2_3`) -/
def Lem2_17 : Prop :=
  ∀ γ : ℝ, 0 < γ → γ < 2 → ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (h : Ω → DistC) (Dh : Ω → ContMetric) (εn : ℕ → ℝ),
    IsNormalizedWPGFF h P → Measurable Dh → (∀ n, 0 < εn n) → Tendsto εn atTop (𝓝 0) →
    (∀ φ : (CoordJ → ℝ) × C(ℂ × ℂ, ℝ) → ℝ, Continuous φ → (∃ C, ∀ x, |φ x| ≤ C) →
      Tendsto (fun n => ∫ ω, φ (pairJ ⊤ (h ω), toCMap fun p =>
          (aEpsDF (xiGamma γ) (εn n))⁻¹ * lfppDist (xiGamma γ) (εn n) (h ω) p) ∂P) atTop
        (𝓝 (∫ ω, φ (pairJ ⊤ (h ω), (Dh ω).1) ∂P))) →
    IsXiAdditive1 (xiGamma γ) P h Dh

/-! ## Assembly -/

end LQGMetric.DFGPS
