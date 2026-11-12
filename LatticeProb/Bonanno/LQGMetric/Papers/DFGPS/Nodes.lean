/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DFGPS.Nodes at commit fdb5cad; only the module paths of local imports are changed.
   Declarations, examples and checks that the copied results do not use are omitted.
   Imports of copied modules that this file does not need are replaced by their own imports. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DFGPS.Defs
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

-- DFGPS Lemma 2.6 (T:837–856) is proved: `DFGPS.lem2_6` (a.s. for a whole-plane GFF, with
-- `h^r = affineComp r 0 h`) and `DFGPS.lem2_6_law` in `Papers/DFGPS/L2_6*.lean`. The earlier node
-- form (`affineComp r⁻¹`, every `h : DistC`) was false (D54, DEV-DFGPS-B1a).

/-! ## Assembly -/

end LQGMetric.DFGPS
