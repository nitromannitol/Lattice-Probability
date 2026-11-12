/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DFGPS.L3_19 at commit fdb5cad; only the module paths of local imports are changed.
   Declarations, examples and checks that the copied results do not use are omitted. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DFGPS.Nodes

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# DFGPS Lemmas 3.19 and 3.21 with constants before the field (task P2-DFA7)

Dubédat–Falconet–Gwynne–Pfeffer–Sun, arXiv:1905.00380, `lqg-metric-estimates-final.tex` ("T"):
Lemma 3.19 (`lem-ep-diam`, T:2264–2272) and Lemma 3.21 (`lem-ep-cross`, T:2337–2343).

The nodes `DFGPS.Lem3_19`, `Lem3_19Sq`, `Lem3_21` (`Nodes.lean`) choose `ε₀` after the probability
space. The Blueprint consumers `DFGPSLem3_20`, `DFGPSLem3_22`, `DFGPSProp3_18` quantify their
constants before the field (`PolyHighProbU`, decision D57), so the union bounds of T:2324–2330
and T:2375 need the rates of L3.19/L3.21 uniform in the field as well. This is what the paper's
proofs give ("uniformly over the choices of `𝕣` and `z ∈ 𝕣K`", the moment bound (3.31) depends
only on `p`, Prop 3.9's constants and Theorem 1.5's rate). `ProbExpRateU` is `ProbExpRate` with
`ε₀` chosen before `(Ω, P, h)`; the `U` forms imply the nodes (`Lem3_19U.toNode`, …).
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal

namespace LQGMetric.DFGPS
open Blueprint

/-- "w.p. `≥ 1 − ε^{a + o_ε(1)}` as `ε → 0`, uniformly in `𝕣`, `z ∈ 𝕣K` and the field" -/
def ProbExpRateU (K : Set ℂ) (a : ℝ) (E : ℝ → ℝ → ℂ → Set DistC) : Prop :=
  ∀ ζ : ℝ, 0 < ζ → ∃ ε₀ : ℝ, 0 < ε₀ ∧
    ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] (h : Ω → DistC),
      IsNormalizedWPGFF h P → ∀ ε ∈ Ioo (0 : ℝ) ε₀, ∀ 𝕣 : ℝ, 0 < 𝕣 →
        ∀ z ∈ scaleSet 𝕣 0 K, P (h ⁻¹' E ε 𝕣 z)ᶜ ≤ ENNReal.ofReal (ε ^ (a - ζ))

/-- **DFGPS Lemma 3.19**, ball part (`eqn-ep-diam`, T:2264–2268), constants uniform in the field -/
def Lem3_19U : Prop :=
  ∀ γ : ℝ, 0 < γ → γ < 2 → ∀ (D : DistC → ContMetric) (c : ℝ → ℝ), IsWeakLQGMetric γ D c →
    ∀ K : Set ℂ, IsCompact K → ∀ s : ℝ, 0 < s → s < xiGamma γ * Q γ →
      ProbExpRateU K ((xiGamma γ * Q γ - s) ^ 2 / (2 * xiGamma γ ^ 2)) fun ε 𝕣 z => {g |
        internalDiam (D g) (Metric.ball z (ε * 𝕣)) (Metric.ball z (2 * ε * 𝕣)) ≤
          ENNReal.ofReal (ε ^ s * scaleFac (xiGamma γ) c g 𝕣 0)}

/-- **DFGPS Lemma 3.19**, square part (`eqn-ep-diam-square`, T:2269–2272), constants uniform in
the field -/
def Lem3_19SqU : Prop :=
  ∀ γ : ℝ, 0 < γ → γ < 2 → ∀ (D : DistC → ContMetric) (c : ℝ → ℝ), IsWeakLQGMetric γ D c →
    ∀ K : Set ℂ, IsCompact K → ∀ s : ℝ, 0 < s → s < xiGamma γ * Q γ →
      ProbExpRateU K ((xiGamma γ * Q γ - s) ^ 2 / (2 * xiGamma γ ^ 2)) fun ε 𝕣 z => {g |
        internalDiam (D g) (sqCentred (ε * 𝕣) z) (sqCentred (ε * 𝕣) z) ≤
          ENNReal.ofReal (ε ^ s * scaleFac (xiGamma γ) c g 𝕣 0)}

end LQGMetric.DFGPS
