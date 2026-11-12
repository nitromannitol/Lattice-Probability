/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.CONF.S3D108K3 at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.CONF.S3D108K1
import LatticeProb.Bonanno.LQGMetric.Papers.CONF.S3D108K2
import LatticeProb.Bonanno.LQGMetric.Papers.DFGPS.L2_17Core2H
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S1.Subseq
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S1.FieldAux

/-!
# CONF Proposition 2.8 for internal-diameter events, frozen form (Lemma 3.3, Step 3)

Gwynne–Miller, *Confluence of geodesics in LQG*, arXiv:1905.00381 (CONF),
`literature/src/1905.00381/confluence-final.tex`, Proposition 2.8 (C:656–661, proof C:748–752)
applied as in Step 3 of Lemma 3.3 (C:1236–1243): under the conditional law given the outside
field `w`, the events `G^U` and `F_r(z)` are non-increasing, a.s. continuous functions of the
zero-boundary field, hence positively correlated.

Setting (the consumer's, `condFKG_freeze2` of S3D108A): `W : Ω → β` the frozen outside datum,
`X : Ω → 𝒟'(ℂ)` the zero-boundary part (`IsZBExtField U X P`), `W ⊥ X`, `G : β → 𝒟'(ℂ)` measurable
with `G ∘ W + X` a whole-plane GFF (the normalized field `recField = 𝔥^U + h̊^U` of the Markov
decomposition). Events `{p | Fz p.1 ∧ ∀ i ∈ I, diam(A i; D_{G p.1 + p.2}(·,·;V i)) ≤ T p.1 i}`
(`I` finite, `V i` open bounded; `Fz` a frozen condition) — the shape of `fatG` (S3D112A) and of
conditions 1–3 of `E^U_r(z)` once condition 1, 3 are written as functions of `w`.

* `ae_ae_weylAt`: Axiom III on the product law: for a.e. `w`, a.e. `x`, `WeylAt ξ D (G w + x)`
  (the product law is the law of `(W, X)` by independence, and `(w, x) ↦ G w + x` is a whole-plane
  GFF under it; `Measure.ae_ae_of_ae_prod`);
* **`confProp2_8_diam`**: CONF Prop 2.8 in the frozen form `hfkg` of `condFKG_freeze2`, from
  `CONFLem2_10` (S3D108K1), Axiom III, and the frozen S-cont-law hypotheses
  (`∀ᵐ w, ∀ᵐ x, diam ≠ threshold`; CONF C:667–669, C:1239–1241).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped ENNReal

namespace LQGMetric.CONF

open Blueprint

variable {Ω β : Type} [MeasurableSpace Ω] [MeasurableSpace β] {P : Measure Ω}
  [IsProbabilityMeasure P]

/-- `(w, x) ↦ G w + x` is measurable -/
lemma measurable_add_frozen {G : β → DistC} (hG : Measurable G) :
    Measurable fun p : β × DistC => G p.1 + p.2 :=
  GFFInv.measurable_distC_iff.2 fun φ =>
    ((GFFInv.measurable_pair φ).comp (hG.comp measurable_fst)).add
      ((GFFInv.measurable_pair φ).comp measurable_snd)

/-- **Axiom III under the frozen law**: for a.e. outside datum `w` and a.e. zero-boundary sample
`x`, the Weyl identity holds at `G w + x` for every continuous `f`. -/
theorem ae_ae_weylAt {γ : ℝ} {D : DistC → ContMetric} {c : ℝ → ℝ} (hD : IsWeakLQGMetric γ D c)
    {W : Ω → β} {X : Ω → DistC} (hW : Measurable W) (hX : Measurable X) (hind : IndepFun W X P)
    {G : β → DistC} (hG : Measurable G) (hh : IsWholePlaneGFF (fun ω => G (W ω) + X ω) P) :
    ∀ᵐ w ∂(P.map W), ∀ᵐ x ∂(P.map X), WeylAt (xiGamma γ) D (G w + x) := by
  have hμ : P.map (fun ω => (W ω, X ω)) = (P.map W).prod (P.map X) :=
    (indepFun_iff_map_prod_eq_prod_map_map hW.aemeasurable hX.aemeasurable).1 hind
  have hHm := measurable_add_frozen hG
  have hH : IsWholePlaneGFF (fun p : β × DistC => G p.1 + p.2) ((P.map W).prod (P.map X)) := by
    refine DFGPS.L217.isWholePlaneGFF_of_map_eq hHm hh ?_
    rw [← hμ, Measure.map_map hHm (hW.prodMk hX)]
    rfl
  have : IsProbabilityMeasure ((P.map W).prod (P.map X)) := by
    rw [← hμ]; exact (Measure.isProbabilityMeasure_map_iff (hW.prodMk hX).aemeasurable).2 ‹_›
  exact Measure.ae_ae_of_ae_prod (hD.weyl _ _ (GM.isGFFPlusCont_of_isWholePlaneGFF hH))

omit [MeasurableSpace β] in
/-- the frozen internal-diameter event `{Fz w ∧ ∀ i ∈ I, diam(A i; D_{G w + x}(·,·;V i)) ≤ T w i}` -/
def frozenDiamEv (D : DistC → ContMetric) (G : β → DistC) (Fz : β → Prop) {ι : Type}
    (I : Set ι) (A V : ι → Set ℂ) (T : β → ι → ℝ≥0∞) : Set (β × DistC) :=
  {p | Fz p.1 ∧ ∀ i ∈ I, internalDiam (D (G p.1 + p.2)) (A i) (V i) ≤ T p.1 i}

omit [MeasurableSpace β] in
/-- the hypotheses `hGm`, `hGc` of `confProp2_8_frozen` for a frozen diameter event, at a frozen
datum `w` and a sample `x` where Axiom III holds and no diameter equals its threshold -/
lemma frozenDiamEv_mono_cont {ξ : ℝ} (hξ : 0 ≤ ξ) {D : DistC → ContMetric} {G : β → DistC}
    {Fz : β → Prop} {ι : Type} {I : Set ι} (hI : I.Finite) {A V : ι → Set ℂ}
    (hV : ∀ i, IsOpen (V i)) (hVb : ∀ i, Bornology.IsBounded (V i)) {T : β → ι → ℝ≥0∞}
    {w : β} {x : DistC} (hw : WeylAt ξ D (G w + x))
    (hne : ∀ i ∈ I, internalDiam (D (G w + x)) (A i) (V i) ≠ T w i) :
    (∀ f g : C(ℂ, ℝ), f ≤ g → (w, addFun x g) ∈ frozenDiamEv D G Fz I A V T →
      (w, addFun x f) ∈ frozenDiamEv D G Fz I A V T) ∧
    (∀ fn : ℕ → C(ℂ, ℝ), Tendsto fn atTop (𝓝 0) → ∀ᶠ n in atTop,
      ((w, addFun x (fn n)) ∈ frozenDiamEv D G Fz I A V T ↔ (w, x) ∈ frozenDiamEv D G Fz I A V T)) := by
  have e : ∀ f : C(ℂ, ℝ), G w + addFun x f = addFun (G w + x) f := fun f => by
    simp only [addFun, add_assoc]
  refine ⟨fun f g hfg hg => ⟨hg.1, ?_⟩, fun fn hfn => ?_⟩
  · have h2 := hg.2
    simp only [e] at h2 ⊢
    exact diamEvent_weyl_mono hξ hw I A V hV (T w) hfg h2
  · filter_upwards [diamEvent_weyl_cont hξ hw hI A V hV hVb (T w) hne hfn] with n hn
    simp only [frozenDiamEv, mem_ofPred_eq, e]
    exact and_congr_right fun _ => hn

end LQGMetric.CONF
