/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.CONF.S3D108M6 at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.CONF.S3D108M5

/-!
# CONF Proposition 2.8 in the frozen form of Lemma 3.3, Step 3 (`CONFFKGFrozenEU`, countable `A`)

Gwynne–Miller, *Confluence of geodesics in LQG*, arXiv:1905.00381 (CONF),
`literature/src/1905.00381/confluence-final.tex`, Lemma 3.3, Step 3 (C:1236–1243), from
Proposition 2.8 (C:656–669) through `zbDiamSet_fkg_frozen` (S3D108M4) and `confEU_ae_eq_chain`
(S3D108M5).

* `CONFFKGFrozenEUc`: `CONFFKGFrozenEU` (S3D112L3) with the extra hypothesis that the sets `A i`
  are countable (the consumer `l33Gen_fatG` uses the finite sets `K_C`). For uncountable `A i` the
  event `zbDiamSet` is not known to be measurable, and the a.s. identification of `Fm i` with an
  internal metric (a sample-level, non-measurable predicate) does not transfer to the law of `X`.
* Open inputs, both CONF claims made in one sentence:
  - `CONFEUOutside13` (C:1238, "`1_{F_r(z)}` depends also on `h|_{ℂ∖U}`"): conditions 1 and 3 of
    `E^U` are a.s. equal to an event of `h|_{ℂ∖U}` (`recSigma`-measurable);
  - `CONFEUSContLaw` (C:1240–1241, "A similar justification holds for `F_r(z)`"): for a.e.
    frozen outside field, the square diameters of condition 2 a.s. do not hit their threshold.
* **`confFKGFrozenEUc_of`**: `CONFFKGFrozenEUc γ D c p` from `CONFLem2_10` and these two inputs.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Metric Filter Topology TopologicalSpace
open scoped ENNReal

namespace LQGMetric.CONF

open Blueprint

/-- `CONFFKGFrozenEU` (S3D112L3) for countable `A i` -/
def CONFFKGFrozenEUc (γ : ℝ) (D : DistC → ContMetric) (c : ℝ → ℝ) (p : CONFParams) : Prop :=
  ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] (h : Ω → DistC),
    IsWholePlaneGFF h P → ∀ (z : ℂ) (r : ℝ), 0 < r → ∀ T : Finset (ℤ × ℤ),
    (∀ k ∈ T, k ∈ confSqIdx (p.δ * r) z (annulus z (3 * r) (4 * r))) →
    ∀ (ρ : ℝ) (w : ℂ), 0 < ρ → Disjoint (confU r p.δ z T) (sphere w ρ) →
    ∀ X G : Ω → DistC, IsL33ZBPart P h ρ w (confU r p.δ z T) (isOpen_confU r p.δ z T) X →
    Measurable[recSigma h ρ w (confU r p.δ z T)ᶜ] G → (∀ ω, X ω = recField h ρ w ω - G ω) →
    IsZBExtField (toOpens (confU r p.δ z T) (isOpen_confU r p.δ z T)) X P →
    ∃ SF : Set (SigOmega Ω (recSigma h ρ w (confU r p.δ z T)ᶜ) × DistC), MeasurableSet SF ∧
      confEU (xiGamma γ) c D P h p r z T =ᵐ[P]
        {ω | (toSig (recSigma h ρ w (confU r p.δ z T)ᶜ) ω, X ω) ∈ SF} ∧
      ∀ {ι : Type} [Finite ι] (V : ι → Opens ℂ),
        (∀ i, closure (V i : Set ℂ) ⊆ confU r p.δ z T) →
        ∀ Fm : ∀ i, DistOn (V i) → ℂ → ℂ → ℝ≥0∞, (∀ i, Measurable (Fm i)) →
        (∀ i, ∀ᵐ ω ∂P, ∀ 𝔥 : ℂ → ℝ, InnerProductSpace.HarmonicOnNhd 𝔥 (confU r p.δ z T) →
          (∀ φ : TestOn (toOpens (confU r p.δ z T) (isOpen_confU r p.δ z T)),
            restrictTo (toOpens (confU r p.δ z T) (isOpen_confU r p.δ z T))
              (recField h ρ w ω - X ω) φ = ∫ x, 𝔥 x * φ x) →
          ∀ f : C(ℂ, ℝ), tsupport ⇑f ⊆ confU r p.δ z T → EqOn ⇑f 𝔥 (V i : Set ℂ) →
          ∀ u ∈ V i, ∀ v ∈ V i,
            (D (addFun (recField h ρ w ω) (-f))).internal (V i) u v =
              Fm i (restrictTo (V i) (X ω)) u v) →
        ∀ A : ι → Set ℂ, (∀ i, A i ⊆ V i) → (∀ i, (A i).Countable) → ∀ t : ℝ, 0 < t →
        ∀ᵐ v ∂(P.map (toSig (recSigma h ρ w (confU r p.δ z T)ᶜ))),
          P.map X (zbDiamSet V Fm A t) * P.map X (Prod.mk v ⁻¹' SF) ≤
            P.map X (zbDiamSet V Fm A t ∩ Prod.mk v ⁻¹' SF)

/-- **Conditions 1 and 3 of `E^U` are events of `h|_{ℂ∖U}`** (CONF C:1238). Open input. -/
def CONFEUOutside13 (γ : ℝ) (D : DistC → ContMetric) (c : ℝ → ℝ) (p : CONFParams) : Prop :=
  ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] (h : Ω → DistC),
    IsWholePlaneGFF h P → ∀ (z : ℂ) (r : ℝ), 0 < r → ∀ T : Finset (ℤ × ℤ),
    (∀ k ∈ T, k ∈ confSqIdx (p.δ * r) z (annulus z (3 * r) (4 * r))) →
    ∀ (ρ : ℝ) (w : ℂ), 0 < ρ → Disjoint (confU r p.δ z T) (sphere w ρ) →
    ∃ B : Set Ω, MeasurableSet[recSigma h ρ w (confU r p.δ z T)ᶜ] B ∧
      {ω | ENNReal.ofReal (p.c * scaleFac (xiGamma γ) c (h ω) r z) ≤
          setDist (D (h ω)) (sphere z (2 * r)) (sphere z (3 * r)) ∧
        ∀ u ∈ innerPart (confU r p.δ z T) (p.δ * r / 4),
          |harmPart P h (confU r p.δ z T) ω u - circleAvg (h ω) r z| ≤ p.A} =ᵐ[P] B

/-- **S-cont-law for condition 2 of `E^U` under the conditional law given `h|_{ℂ∖U}`** (CONF
C:1240–1241, C:667–669): for a.e. frozen outside field `v`, a.s. no square diameter
`diam(S; D_{recField}(·,·; 𝔸_{2r,5r}))` equals its threshold `(c/100) 𝔠_r e^{ξ recField_r(z)}`.
Open input. -/
def CONFEUSContLaw (γ : ℝ) (D : DistC → ContMetric) (c : ℝ → ℝ) (p : CONFParams) : Prop :=
  ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] (h : Ω → DistC),
    IsWholePlaneGFF h P → ∀ (z : ℂ) (r : ℝ), 0 < r → ∀ T : Finset (ℤ × ℤ),
    (∀ k ∈ T, k ∈ confSqIdx (p.δ * r) z (annulus z (3 * r) (4 * r))) →
    ∀ (ρ : ℝ) (w : ℂ), 0 < ρ → Disjoint (confU r p.δ z T) (sphere w ρ) →
    ∀ X G : Ω → DistC, IsL33ZBPart P h ρ w (confU r p.δ z T) (isOpen_confU r p.δ z T) X →
    Measurable[recSigma h ρ w (confU r p.δ z T)ᶜ] G → (∀ ω, X ω = recField h ρ w ω - G ω) →
    IsZBExtField (toOpens (confU r p.δ z T) (isOpen_confU r p.δ z T)) X P →
    ∀ k ∈ confSqIdx (p.δ * r) z (annulus z (3 * r) (4 * r)),
      ∀ᵐ v ∂(P.map (toSig (recSigma h ρ w (confU r p.δ z T)ᶜ))), ∀ᵐ x ∂(P.map X),
        internalDiam (D (G v.val + x)) (confSq (p.δ * r) z k) (annulus z (2 * r) (5 * r)) ≠
          euThr (xiGamma γ) c p h ρ w r z v.val

lemma sphere_subset_compl_confU {r : ℝ} (hr : 0 < r) (δ : ℝ) (z : ℂ) (T : Finset (ℤ × ℤ)) :
    sphere z |r| ⊆ (confU r δ z T)ᶜ := fun x hx hxU => by
  have h1 := hxU.1.1
  rw [mem_sphere, Complex.dist_eq, abs_of_pos hr] at hx
  linarith

lemma isBounded_annulus_m6 (z : ℂ) (a b : ℝ) : Bornology.IsBounded (annulus z a b : Set ℂ) :=
  (isBounded_ball (x := z) (r := b)).subset fun x hx => by
    rw [mem_ball, Complex.dist_eq]; exact hx.2

end LQGMetric.CONF
