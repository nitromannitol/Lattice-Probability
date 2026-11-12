/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.CONF.S3T39H2 at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.CONF.S3T39H1

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# CONF Lemma 3.7 (true form, D113) and its proof from Lemma 3.6

Gwynne–Miller, *Confluence of geodesics in LQG* (arXiv:1905.00381), Lemma 3.7 (`lem-geo-kill`,
`confluence-final.tex` C:1452–1462), proof C:1463–1471.

`CONFLem3_7AtAE0` is Lemma 3.7 in the D108/D110/D113/D114 form of `CONFLem3_6AtAE0`: σ-algebras
modulo additive constants (`localSigma0`, `filledBallSigmaAt0`), `𝓑^•_τ` a local set modulo
constants, `localSigma0 h 𝓑^•_τ ≤ mΩ`, a.s. hypotheses, the `ε`-hypotheses of `CONFLem3_6AtAE0`
verbatim (`ε ∈ (0,1)`, countably valued), `G` an a.s. event of `σ(𝓑^•_σ, h|) mod const`
(`AEEventIn`, D114 (g)), and property A for targets
outside `int 𝓑^•_σ` (D113 S2). The point `x ∈ ∂𝓑^•_τ` that CONF's proof chooses "in a manner
depending only on `(𝓑^•_τ, h|_{𝓑^•_τ})`" (C:1467) is an explicit `localSigma0`-measurable input;
the event `G = G^ε_x` (C:1468) then works for **every** `I ⊆ ∂𝓑^•_τ` disconnected from `∞` by a
ball `B_ρ(x)`, `ρ < ε𝕣` (so no measurability of `I` is needed). Property A carries the a.s. facts
used in C:1469–1470 as premises at `ω`: `τ > 0`, geodesics from `𝕫` to every point, bounded
`D_h`-balls.

* `t39h_lem37_of_G`: the L3.6 event for `(x, ε)` is an L3.7 event (C:1468–1471), for any
  version of L3.6 with this output (robust to the `ε`-hypotheses of L3.6, DEC-114);
* **`confLem3_7AtAE0_of_36`**: `CONFLem3_6AtAE0 → CONFLem3_7AtAE0`;
* `CONFLem3_7AtAE0E`, **`confLem3_7AtAE0E_of_AE0`**: the on-event form (D113 S3): `x ∈ ∂𝓑^•_τ`
  only a.s. on a `localSigma0`-event `E`, property A on `G ∩ E`.
-/

noncomputable section

open MeasureTheory Set Metric
open LQGMetric.Blueprint LQGMetric.GM
open scoped ENNReal

namespace LQGMetric
namespace CONF

/-- property A of CONF Lemma 3.7 for the centre `x`, at `ω` (C:1460, D113) -/
def T39HPropA (γ : ℝ) (D : DistC → ContMetric) (c : ℝ → ℝ) (p : CONFParams) {Ω : Type}
    [MeasurableSpace Ω] (P : Measure Ω) (h : Ω → DistC) (z₀ : ℂ) (R : ℝ) (τ : Ω → ℝ)
    (x : Ω → ℂ) (ε : Ω → ℝ) (ω : Ω) : Prop :=
  ∀ (I : Set ℂ) (ρ : ℝ), 0 < τ ω →
    (∀ w, ∃ (Q : ℝ → ℂ) (L : ℝ), IsGeodesicL (D (h ω)) Q L z₀ w) →
    (∀ s : ℝ, Bornology.IsBounded (ballM (D (h ω)) z₀ s)) →
    x ω ∈ frontier (filledBall (D (h ω)) z₀ (τ ω)) →
    I ⊆ frontier (filledBall (D (h ω)) z₀ (τ ω)) → 0 ≤ ρ → ρ < ε ω * R →
    DisconnectsFromInfty (filledBall (D (h ω)) z₀ (τ ω)) (ball (x ω) ρ) I →
    confRK (xiGamma γ) c D P h p R (ε ω) (filledBall (D (h ω)) z₀ (τ ω)) ω ≤
      Metric.ediam (filledBall (D (h ω)) z₀ (τ ω)) →
    ∀ (y : ℂ) (Q : ℝ → ℂ) (L : ℝ),
      y ∉ interior (filledBallE (D (h ω)) z₀
        (confSigma (xiGamma γ) c D P h p z₀ R (ε ω) (τ ω) ω)) →
      IsGeodesicL (D (h ω)) Q L z₀ y → ∀ u ∈ Icc 0 L, Q u ∉ I

/-- the body of CONF Lemma 3.7 (true form) for the constants `α, C₀` -/
def T39HL37 (γ : ℝ) (D : DistC → ContMetric) (c : ℝ → ℝ) (p : CONFParams) (α C₀ : ℝ) : Prop :=
  ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] (h : Ω → DistC),
    IsWholePlaneGFF h P → ∀ (z₀ : ℂ) (R : ℝ), 0 < R → ∀ τ : Ω → ℝ,
      IsFilledBallStoppingTimeAE P D h z₀ τ →
      IsLocalSetDet0 P h (fun ω => filledBall (D (h ω)) z₀ (τ ω)) →
      localSigma0 h (fun ω => filledBall (D (h ω)) z₀ (τ ω)) ≤ ‹MeasurableSpace Ω› →
      ∀ (x : Ω → ℂ) (ε : Ω → ℝ),
      @Measurable Ω ℂ (localSigma0 h (fun ω => filledBall (D (h ω)) z₀ (τ ω))) _ x →
      @Measurable Ω ℝ (localSigma0 h (fun ω => filledBall (D (h ω)) z₀ (τ ω))) _ ε →
      (∀ᵐ ω ∂P, x ω ∈ frontier (filledBall (D (h ω)) z₀ (τ ω))) → (∀ ω, ε ω ∈ Ioo 0 1) →
      (Set.range ε).Countable →
      ∃ G : Set Ω,
        AEEventIn P (filledBallSigmaAt0 D h z₀
          (fun ω => confSigma (xiGamma γ) c D P h p z₀ R (ε ω) (τ ω) ω)) G ∧
        (∀ ω ∈ G, T39HPropA γ D c p P h z₀ R τ x ε ω) ∧
        ∀ᵐ ω ∂P, 1 - C₀ * ε ω ^ α ≤
          (P[G.indicator (fun _ => (1 : ℝ)) |
            localSigma0 h (fun ω => filledBall (D (h ω)) z₀ (τ ω))]) ω

/-- **CONF Lemma 3.7, true form** (D113; C:1452–1462 with the point `x` of C:1467 explicit) -/
def CONFLem3_7AtAE0 (γ : ℝ) (D : DistC → ContMetric) (c : ℝ → ℝ) (p : CONFParams) : Prop :=
  ∃ α C₀ : ℝ, 0 < α ∧ 1 < C₀ ∧ T39HL37 γ D c p α C₀

/-- **C:1468–1471**: an event with property A of Lemma 3.6 for `(x, ε)` has property A of
Lemma 3.7 -/
theorem t39h_lem37_of_G {γ : ℝ} {D : DistC → ContMetric} {c : ℝ → ℝ} {p : CONFParams}
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} {h : Ω → DistC} {z₀ : ℂ} {R : ℝ}
    {τ : Ω → ℝ} {x : Ω → ℂ} {ε : Ω → ℝ} {G : Set Ω}
    (hGA : ∀ ω ∈ G, x ω ∈ frontier (filledBall (D (h ω)) z₀ (τ ω)) →
      confRK (xiGamma γ) c D P h p R (ε ω) (filledBall (D (h ω)) z₀ (τ ω)) ω ≤
        Metric.ediam (filledBall (D (h ω)) z₀ (τ ω)) →
      ∀ (y : ℂ) (Q : ℝ → ℂ) (L : ℝ),
        y ∉ enbhd (confRK (xiGamma γ) c D P h p R (ε ω) (filledBall (D (h ω)) z₀ (τ ω)) ω)
          (filledBall (D (h ω)) z₀ (τ ω)) →
        IsGeodesicL (D (h ω)) Q L z₀ y → ∀ u ∈ Icc 0 L,
          Q u ∉ Metric.ball (x ω) (ε ω * R) \ filledBall (D (h ω)) z₀ (τ ω)) :
    ∀ ω ∈ G, T39HPropA γ D c p P h z₀ R τ x ε ω := by
  intro ω hω I ρ hτ0 hgeo hbd hx hI hρ0 hρ hdis hRK
  exact t39h_A_of_36 hτ0 hgeo hbd hx hI hρ0 hρ hdis (hGA ω hω hx hRK)

/-- **CONF Lemma 3.7 from Lemma 3.6** (C:1463–1471) -/
theorem confLem3_7AtAE0_of_36 {γ : ℝ} {D : DistC → ContMetric} {c : ℝ → ℝ} {p : CONFParams}
    (H : CONFLem3_6AtAE0 γ D c p) : CONFLem3_7AtAE0 γ D c p := by
  obtain ⟨α, C₀, hα, hC₀, H⟩ := H
  refine ⟨α, C₀, hα, hC₀, ?_⟩
  intro Ω _ P _ h hh z₀ R hR τ hτ hdet hsub x ε hx hεm hxf hε hεc
  obtain ⟨G, hGm, hGA, hGB⟩ := H P h hh z₀ R hR τ hτ hdet hsub x ε hx hεm hxf hε hεc
  exact ⟨G, hGm, t39h_lem37_of_G hGA, hGB⟩

end CONF
end LQGMetric
