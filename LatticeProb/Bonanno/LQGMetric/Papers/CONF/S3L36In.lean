/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.CONF.S3L36In at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.CONF.S3L36A

/-!
# CONF Lemma 3.6: the one abstract input from Lemma 3.3 and the square chains

Gwynne–Miller, *Confluence of geodesics in LQG*, arXiv:1905.00381 (CONF),
`literature/src/1905.00381/confluence-final.tex`, Lemma 3.6 (C:1308–1448). The proof of Lemma 3.6
uses Lemma 3.3 only through a "small internal diameter" event `G^U` (CONF (3.9), C:1205) and two
of its properties:

* **Step 2** (C:1392–1396): on `G^U` together with condition 2 of `E^U_r(z)`, every point of
  `𝔸_{3r,4r}(z)` is at internal distance `< c 𝔠_r e^{ξh_r(z)}` in `𝔸_{2r,5r}(z)` from the set
  `𝓑` whose squares were removed (the bound (3.21); CONF's C:1208 path claim, D108 (b));
* **Step 3** (C:1433–1447): Lemma 3.3's conditional bound `P[G^U | h|_{ℂ∖U}, E^U] ≥ 𝔭` (C:1440).

Since the exact form of `G^U` is being corrected (D108 (b) `confFatEv`; P2-CONF33W's per-component
`confFatEvC`, decision D112 pending), Lemma 3.6 is proved from **`L36Input γ D c p`**: there is a
predicate `Fat d s r z T` ("`G^U` for the metric `d` at scale `s = 𝔠_re^{ξh_r(z)}`") with
`L36Step2Input p Fat` (the deterministic bound) and `L33Gen γ D c p Fat` (Lemma 3.3 for the event
`{Fat (D_h) (𝔠_re^{ξh_r(z)}) r z T}`, in the integrated form of `CONFLem3_3W`). The adapter
`S3L36Ad.lean` proves `L36Input` from `CONFLem3_3W` and `CONFFatChainA/B 12` (D108).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Metric Filter Topology
open scoped ENNReal

namespace LQGMetric.CONF

open Blueprint

/-- **Step 2 input** (CONF (3.21) before the first-hit step, C:1392–1396): for a set `𝓑` whose
meeting squares are exactly `T` (`T ≠ ∅`), condition 2 of `E^U_r(z)` at scale `s` and the
`G^U`-type event `Fat d s r z T` give, for every `u ∈ 𝔸_{3r,4r}(z)`, a point `b ∈ 𝓑` with
`D(u, b; 𝔸_{2r,5r}(z)) < c s`. -/
def L36Step2Input (p : CONFParams)
    (Fat : ContMetric → ℝ → ℝ → ℂ → Finset (ℤ × ℤ) → Prop) : Prop :=
  ∀ (d : ContMetric) (s r : ℝ) (z : ℂ) (T : Finset (ℤ × ℤ)) (𝓑 : Set ℂ), 0 < s → 0 < r →
    (∀ k ∈ T, k ∈ confSqIdx (p.δ * r) z (annulus z (3 * r) (4 * r))) →
    (∀ k ∈ T, (confSq (p.δ * r) z k ∩ 𝓑).Nonempty) →
    (∀ k ∈ confSqIdx (p.δ * r) z (annulus z (3 * r) (4 * r)),
      (confSq (p.δ * r) z k ∩ 𝓑).Nonempty → k ∈ T) →
    T.Nonempty →
    (∀ k ∈ confSqIdx (p.δ * r) z (annulus z (3 * r) (4 * r)),
      internalDiam d (confSq (p.δ * r) z k) (annulus z (2 * r) (5 * r)) ≤
        ENNReal.ofReal (p.c / 100 * s)) →
    Fat d s r z T →
    ∀ u ∈ (annulus z (3 * r) (4 * r) : Set ℂ), ∃ b ∈ 𝓑,
      d.internal (annulus z (2 * r) (5 * r)) u b < ENNReal.ofReal (p.c * s)

/-- **Lemma 3.3 for the event `Fat`** (the integrated form of `CONFLem3_3W`, at the parameters
`p`): `𝔭 · P(B ∩ E^U_r(z)) ≤ P(B ∩ E^U_r(z) ∩ {Fat})` for `B ∈ σ((h − h_ρ(w))|_{ℂ∖U})`. -/
def L33Gen (γ : ℝ) (D : DistC → ContMetric) (c : ℝ → ℝ) (p : CONFParams)
    (Fat : ContMetric → ℝ → ℝ → ℂ → Finset (ℤ × ℤ) → Prop) : Prop :=
  ∃ 𝔭 : ℝ, 0 < 𝔭 ∧
    ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] (h : Ω → DistC),
      IsWholePlaneGFF h P → ∀ (z : ℂ) (r : ℝ), 0 < r → ∀ T : Finset (ℤ × ℤ),
        (∀ k ∈ T, k ∈ confSqIdx (p.δ * r) z (annulus z (3 * r) (4 * r))) →
        ∀ (ρ : ℝ) (w : ℂ), 0 < ρ → Disjoint (confU r p.δ z T) (sphere w ρ) →
        ∀ B : Set Ω, MeasurableSet[recSigma h ρ w (confU r p.δ z T)ᶜ] B →
          ENNReal.ofReal 𝔭 * P (B ∩ confEU (xiGamma γ) c D P h p r z T) ≤
            P (B ∩ confEU (xiGamma γ) c D P h p r z T ∩
              {ω | Fat (D (h ω)) (scaleFac (xiGamma γ) c (h ω) r z) r z T})

end LQGMetric.CONF
