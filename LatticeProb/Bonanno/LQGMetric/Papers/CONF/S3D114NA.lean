/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.CONF.S3D114NA at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.CONF.S3L36H
import LatticeProb.Bonanno.LQGMetric.Blueprint.StoppingAE

/-!
# CONF Lemma 3.6: the two nodes with an almost sure stopping time (D120)

Gwynne–Miller, *Confluence of geodesics in LQG*, arXiv:1905.00381 (CONF),
`literature/src/1905.00381/confluence-final.tex`, Lemma 3.6 (C:1308–1448); decisions D114
(`decisions/DEC-114.md` §4) and D120 (`decisions/DEC-120.md` §3: the radii `σ^ε_{τ,𝕣}` are
stopping times only a.s., so the hypothesis `IsFilledBallStoppingTime D h z₀ τ` becomes
`IsFilledBallStoppingTimeAE P D h z₀ τ`).

`Conf36MeasNodeAE`, `Conf36StepNodeAE`: the text of `Conf36MeasNodeD`, `Conf36StepNodeD`
(S3D114N) with that one hypothesis changed; `conf36MeasNodeD_of_AE`, `conf36StepNodeD_of_AE`:
the sure versions follow (`IsFilledBallStoppingTime.ae`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Metric Filter Topology
open scoped ENNReal

namespace LQGMetric.CONF

open Blueprint

/-- **Step 1 node, D114/D120 form** (CONF C:1341–1368; DEC-114 §4 C3) -/
def Conf36MeasNodeAE (γ : ℝ) (D : DistC → ContMetric) (c : ℝ → ℝ) (p : CONFParams)
    (Fat : ContMetric → ℝ → ℝ → ℂ → Finset (ℤ × ℤ) → Prop) : Prop :=
  IsWeakLQGMetric γ D c →
  ∀ {Ω : Type} [mΩ : MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] (h : Ω → DistC),
    IsWholePlaneGFF h P → ∀ (z₀ : ℂ) (R : ℝ), 0 < R → ∀ τ : Ω → ℝ,
      IsFilledBallStoppingTimeAE P D h z₀ τ →
      IsLocalSetDet0 P h (fun ω => filledBall (D (h ω)) z₀ (τ ω)) →
      localSigma0 h (fun ω => filledBall (D (h ω)) z₀ (τ ω)) ≤ mΩ →
      ∀ (x : Ω → ℂ) (ε : Ω → ℝ),
      @Measurable Ω ℂ (localSigma0 h (fun ω => filledBall (D (h ω)) z₀ (τ ω))) _ x →
      @Measurable Ω ℝ (localSigma0 h (fun ω => filledBall (D (h ω)) z₀ (τ ω))) _ ε →
      (∀ ω, ε ω ∈ Ioo 0 1) → (Set.range ε).Countable →
      AEEventIn P (filledBallSigmaAt0 D h z₀
          (fun ω => confSigma (xiGamma γ) c D P h p z₀ R (ε ω) (τ ω) ω))
        (conf36G Fat (xiGamma γ) c D P h p ε (fun ω => ε ω * R)
          (fun ω => conf36Grid (ε ω * R / 4) (x ω)) (fun ω => filledBall (D (h ω)) z₀ (τ ω))) ∧
      ∀ n, AEEventIn P mΩ (conf36Gt Fat (xiGamma γ) c D P h p (fun ω => ε ω * R)
          (fun ω => conf36Grid (ε ω * R / 4) (x ω)) (fun ω => filledBall (D (h ω)) z₀ (τ ω)) n)

/-- **Step 3 node, D114/D120 form** (CONF (3.24)–(3.25), C:1425–1447; DEC-114 §4 C2) -/
def Conf36StepNodeAE (γ : ℝ) (D : DistC → ContMetric) (c : ℝ → ℝ) (p : CONFParams)
    (Fat : ContMetric → ℝ → ℝ → ℂ → Finset (ℤ × ℤ) → Prop) : Prop :=
  ∀ 𝔭 : ℝ, 0 < 𝔭 → 𝔭 < 1 → L33GenAt γ D c p Fat 𝔭 → IsWeakLQGMetric γ D c →
  ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] (h : Ω → DistC),
    IsWholePlaneGFF h P → ∀ (z₀ : ℂ) (R : ℝ), 0 < R → ∀ τ : Ω → ℝ,
      IsFilledBallStoppingTimeAE P D h z₀ τ →
      IsLocalSetDet0 P h (fun ω => filledBall (D (h ω)) z₀ (τ ω)) →
      localSigma0 h (fun ω => filledBall (D (h ω)) z₀ (τ ω)) ≤ ‹MeasurableSpace Ω› →
      ∀ (x : Ω → ℂ) (ε : Ω → ℝ),
      @Measurable Ω ℂ (localSigma0 h (fun ω => filledBall (D (h ω)) z₀ (τ ω))) _ x →
      @Measurable Ω ℝ (localSigma0 h (fun ω => filledBall (D (h ω)) z₀ (τ ω))) _ ε →
      (∀ᵐ ω ∂P, x ω ∈ frontier (filledBall (D (h ω)) z₀ (τ ω))) →
      (∀ ω, ε ω ∈ Ioo 0 1) → (Set.range ε).Countable →
      ∀ j : ℕ, ∀ n < j, ∀ A : Set Ω,
        MeasurableSet[localSigma0 h (fun ω => filledBall (D (h ω)) z₀ (τ ω))] A →
        A ⊆ {ω | confN p (ε ω) = j} →
        ENNReal.ofReal 𝔭 * P (conf36Avoid (conf36Gt Fat (xiGamma γ) c D P h p (fun ω => ε ω * R)
            (fun ω => conf36Grid (ε ω * R / 4) (x ω)) (fun ω => filledBall (D (h ω)) z₀ (τ ω))) A n) ≤
          P (conf36Avoid (conf36Gt Fat (xiGamma γ) c D P h p (fun ω => ε ω * R)
              (fun ω => conf36Grid (ε ω * R / 4) (x ω)) (fun ω => filledBall (D (h ω)) z₀ (τ ω))) A n ∩
            conf36Gt Fat (xiGamma γ) c D P h p (fun ω => ε ω * R)
              (fun ω => conf36Grid (ε ω * R / 4) (x ω)) (fun ω => filledBall (D (h ω)) z₀ (τ ω)) (n + 1))

end LQGMetric.CONF
