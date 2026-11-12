/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.CONF.S3L36H at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.CONF.S3L36E
import LatticeProb.Bonanno.LQGMetric.Papers.CONF.S3L36G
import Mathlib.MeasureTheory.Function.Floor

/-!
# CONF Lemma 3.6: assembly

Gwynne–Miller, *Confluence of geodesics in LQG*, arXiv:1905.00381 (CONF),
`literature/src/1905.00381/confluence-final.tex`, Lemma 3.6 (C:1308–1448), decisions D106, D108,
D110.

`conf36_lem3_6AtAE0_of` : `CONFLem3_6AtAE0 γ D c p` from
* the Lemma 3.3 / square-chain input (`L36Step2Input p Fat`, `L33Gen γ D c p Fat`; S3L36In),
* positivity of the scaling constants,
* the two Step 1 / Step 3 nodes for the event `G^ε_x = conf36G Fat …` of S3L36D:
  - `Conf36MeasNode` (Step 1, C:1362–1368): `G^ε_x ∈ σ(𝓑^•_{σ^ε}, h|_{𝓑^•_{σ^ε}})` mod constants,
    the `G̃^n` are events, and `σ(𝓑^•_τ, h|_{𝓑^•_τ})` mod constants is a sub-σ-algebra;
  - `Conf36StepNode` (Step 3, (3.24)–(3.25), C:1433–1447): the Lemma 3.3 bound at `𝔭` gives the
    one-step bound `𝔭 P(A ∩ ⋂_{m ≤ n} (G̃^m)ᶜ) ≤ P(A ∩ ⋂_{m ≤ n} (G̃^m)ᶜ ∩ G̃^{n+1})` for
    `A ∈ σ(𝓑^•_τ, h|_{𝓑^•_τ})`, `A ⊆ {⌊η log ε⁻¹⌋ = j}`, `n < j`.
Property A is `conf36_propA` (S3L36E), property B is `conf36_propB_of_steps` (S3L36G) with the
rate `conf36_rate` (S3L36F); `α = η log(1/(1−𝔭'))`, `C₀ = 2/(1−𝔭')`, `𝔭' = min 𝔭 (1/2)`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Metric Filter Topology
open scoped ENNReal

namespace LQGMetric.CONF

open Blueprint

/-- the bound of `L33Gen` at a given `𝔭` -/
def L33GenAt (γ : ℝ) (D : DistC → ContMetric) (c : ℝ → ℝ) (p : CONFParams)
    (Fat : ContMetric → ℝ → ℝ → ℂ → Finset (ℤ × ℤ) → Prop) (𝔭 : ℝ) : Prop :=
  ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] (h : Ω → DistC),
    IsWholePlaneGFF h P → ∀ (z : ℂ) (r : ℝ), 0 < r → ∀ T : Finset (ℤ × ℤ),
      (∀ k ∈ T, k ∈ confSqIdx (p.δ * r) z (annulus z (3 * r) (4 * r))) →
      ∀ (ρ : ℝ) (w : ℂ), 0 < ρ → Disjoint (confU r p.δ z T) (sphere w ρ) →
      ∀ B : Set Ω, MeasurableSet[recSigma h ρ w (confU r p.δ z T)ᶜ] B →
        ENNReal.ofReal 𝔭 * P (B ∩ confEU (xiGamma γ) c D P h p r z T) ≤
          P (B ∩ confEU (xiGamma γ) c D P h p r z T ∩
            {ω | Fat (D (h ω)) (scaleFac (xiGamma γ) c (h ω) r z) r z T})

theorem l33GenAt_mono {γ : ℝ} {D : DistC → ContMetric} {c : ℝ → ℝ} {p : CONFParams}
    {Fat : ContMetric → ℝ → ℝ → ℂ → Finset (ℤ × ℤ) → Prop} {𝔭 𝔭' : ℝ} (h𝔭 : 𝔭' ≤ 𝔭)
    (H : L33GenAt γ D c p Fat 𝔭) : L33GenAt γ D c p Fat 𝔭' :=
  fun P _ h hh z r hr T hT ρ w hρ hd B hB =>
    (mul_le_mul' (ENNReal.ofReal_le_ofReal h𝔭) le_rfl).trans (H P h hh z r hr T hT ρ w hρ hd B hB)

end LQGMetric.CONF
