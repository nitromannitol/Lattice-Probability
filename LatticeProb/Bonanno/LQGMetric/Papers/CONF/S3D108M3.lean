/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.CONF.S3D108M3 at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.CONF.S3D108M2

/-!
# CONF Proposition 2.8 (frozen, chain-formula events) from Axiom III on the frozen law

Gwynne–Miller, *Confluence of geodesics in LQG*, arXiv:1905.00381 (CONF),
`literature/src/1905.00381/confluence-final.tex`, Proposition 2.8 (C:656–669, C:748–752) in the
frozen form of Lemma 3.3, Step 3 (C:1236–1243).

`confProp2_8_chain_test` (S3D108M2) asks that `G ∘ W + X` be a whole-plane GFF. In Lemma 3.3 the
zero-boundary metric event `G^U` lives on the field `h − φ𝔥` (the harmonic part cut off near
`W_C`, C:1213), i.e. `G w + x` minus a continuous function of the frozen datum. This file states
Proposition 2.8 with the only input on the frozen fields being Axiom III on the frozen law
(`∀ᵐ w, ∀ᵐ x, WeylAt ξ D (G w + x)`), separately for the two events:

* `isLength_of_weylAt`: Axiom III at `k` makes every `D_{k+f}` (and `D_k`) a length metric;
* `ae_ae_diam_ne_of_weyl`, `ae_ae_diam_ne_family_of_weyl`: S-cont-law (C:667–669) from Axiom III
  and Cameron–Martin (as `ae_ae_diam_ne`, S3D108K5);
* `ae_ae_weylAt_addFun`: Axiom III on the frozen law for `G w + g w + x` (`g` continuous,
  measurable in `w`), from `G ∘ W + X` being a whole-plane GFF;
* `chainEv_mono_cont`: the monotonicity and continuity hypotheses of `confProp2_8_frozen`;
* **`confProp2_8_chain_weyl`**: CONF Prop 2.8, frozen, for two chain-formula events on two frozen
  fields `G₁ w + x`, `G₂ w + x`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped ENNReal

namespace LQGMetric.CONF

open Blueprint

lemma isLength_of_weylAt {ξ : ℝ} {D : DistC → ContMetric} {k : DistC} (hw : WeylAt ξ D k)
    (f : C(ℂ, ℝ)) : (D (addFun k f)).IsLength :=
  isLength_of_eq_weylScale (D (addFun k f)) (fun a b => (hw f a b).symm)

lemma isLength_of_weylAt0 {ξ : ℝ} {D : DistC → ContMetric} {k : DistC} (hw : WeylAt ξ D k) :
    (D k).IsLength := by
  simpa only [GM.addFun_zero_eq] using isLength_of_weylAt hw 0

variable {Ω β : Type} [MeasurableSpace Ω] [MeasurableSpace β] {P : Measure Ω}
  [IsProbabilityMeasure P]

/-- **Axiom III on the frozen law for `G w + g w + x`** -/
theorem ae_ae_weylAt_addFun {γ : ℝ} {D : DistC → ContMetric} {c : ℝ → ℝ}
    (hD : IsWeakLQGMetric γ D c) {W : Ω → β} {X : Ω → DistC} (hW : Measurable W)
    (hX : Measurable X) (hind : IndepFun W X P) {G : β → DistC} (hG : Measurable G)
    (hh : IsWholePlaneGFF (fun ω => G (W ω) + X ω) P) {g : β → C(ℂ, ℝ)} (hg : Measurable g) :
    ∀ᵐ w ∂(P.map W), ∀ᵐ x ∂(P.map X), WeylAt (xiGamma γ) D (addFun (G w) (g w) + x) := by
  have hμ : P.map (fun ω => (W ω, X ω)) = (P.map W).prod (P.map X) :=
    (indepFun_iff_map_prod_eq_prod_map_map hW.aemeasurable hX.aemeasurable).1 hind
  have hHm := measurable_add_frozen hG
  have hH : IsWholePlaneGFF (fun p : β × DistC => G p.1 + p.2) ((P.map W).prod (P.map X)) := by
    refine DFGPS.L217.isWholePlaneGFF_of_map_eq hHm hh ?_
    rw [← hμ, Measure.map_map hHm (hW.prodMk hX)]
    rfl
  have : IsProbabilityMeasure ((P.map W).prod (P.map X)) := by
    rw [← hμ]; exact (Measure.isProbabilityMeasure_map_iff (hW.prodMk hX).aemeasurable).2 ‹_›
  have hG' : Measurable fun w => addFun (G w) (g w) :=
    measurable_addFun.comp (hG.prodMk hg)
  have hpc : IsGFFPlusCont (fun p : β × DistC => addFun (G p.1) (g p.1) + p.2)
      ((P.map W).prod (P.map X)) := by
    refine ⟨measurable_add_frozen hG', fun p => g p.1, hg.comp measurable_fst, ?_⟩
    have e : (fun p : β × DistC => addFun (G p.1) (g p.1) + p.2 - ofCont (g p.1)) =
        fun p => G p.1 + p.2 := funext fun p => by simp only [addFun]; abel
    rw [e]; exact hH
  exact Measure.ae_ae_of_ae_prod (hD.weyl _ _ hpc)

/-- **S-cont-law, frozen form, from Axiom III on the frozen law** (CONF C:667–669; the proof of
`ae_ae_diam_ne`, S3D108K5) -/
theorem ae_ae_diam_ne_of_weyl {γ : ℝ} (hγ : 0 < γ) {D : DistC → ContMetric}
    (hDm : Measurable D) {U : TopologicalSpace.Opens ℂ} {W : Ω → β} {X : Ω → DistC}
    (hX : IsZBExtField U X P) {G : β → DistC}
    (hwe : ∀ᵐ w ∂(P.map W), ∀ᵐ x ∂(P.map X), WeylAt (xiGamma γ) D (G w + x)) {A V : Set ℂ}
    (hA : A.Countable) (hV : IsOpen V) {φ : C(ℂ, ℝ)} (hφ : ∀ x ∈ V, φ x = 1)
    (hac : CONFZBShiftAC U φ) {T : β → ℝ≥0∞} (hT0 : ∀ w, T w ≠ 0) (hTt : ∀ w, T w ≠ ⊤) :
    ∀ᵐ w ∂(P.map W), ∀ᵐ x ∂(P.map X), internalDiam (D (G w + x)) A V ≠ T w := by
  have hξ : xiGamma γ ≠ 0 := (GM.xiGamma_pos hγ).ne'
  obtain ⟨F, hFm, hF⟩ := measurable_internal hV
  filter_upwards [hwe] with w hw1
  set Y' : DistC → ℝ≥0∞ := fun x => ⨆ u ∈ A, ⨆ v ∈ A, F (D (G w + x), u, v) with hY'
  have hGw : Measurable fun x : DistC => G w + x :=
    GFFInv.measurable_distC_iff.2 fun ψ => measurable_const.add (GFFInv.measurable_pair ψ)
  have hY'm : Measurable Y' := Measurable.biSup _ hA fun u _ => Measurable.biSup _ hA fun v _ =>
    hFm.comp ((hDm.comp hGw).prodMk measurable_const)
  have hYY : ∀ x, (D (G w + x)).IsLength → internalDiam (D (G w + x)) A V = Y' x := fun x hx => by
    simp only [internalDiam, hY', hF _ hx]
  have e : ∀ x (f : C(ℂ, ℝ)), G w + addFun x f = addFun (G w + x) f := fun x f => by
    simp only [addFun, add_assoc]
  have hscale : ∀ᵐ x ∂(P.map X), ∀ t : ℝ,
      Y' (addFun x (t • φ)) = ENNReal.ofReal (Real.exp (xiGamma γ * t)) * Y' x := by
    filter_upwards [hw1] with x hx1 t
    have hl : (D (G w + addFun x (t • φ))).IsLength := by
      rw [e]; exact isLength_of_weylAt hx1 _
    rw [← hYY _ hl, ← hYY _ (isLength_of_weylAt0 hx1), e]
    exact internalDiam_addFun_const hx1 hV hφ A t
  have : IsProbabilityMeasure (P.map X) :=
    (Measure.isProbabilityMeasure_map_iff hX.measurable.aemeasurable).2 ‹_›
  have h0 := measure_level_eq_zero hξ hY'm (hT0 w) (hTt w) hscale (hac P X hX)
  have h0' : ∀ᵐ x ∂(P.map X), Y' x ≠ T w := by
    rw [ae_iff]; simpa using h0
  filter_upwards [h0', hw1] with x hx1 hx2
  rw [hYY x (isLength_of_weylAt0 hx2)]; exact hx1

theorem ae_ae_diam_ne_family_of_weyl {γ : ℝ} (hγ : 0 < γ) {D : DistC → ContMetric}
    (hDm : Measurable D) {U : TopologicalSpace.Opens ℂ} (hU : Bornology.IsBounded (U : Set ℂ))
    {W : Ω → β} {X : Ω → DistC} (hX : IsZBExtField U X P) {G : β → DistC}
    (hwe : ∀ᵐ w ∂(P.map W), ∀ᵐ x ∂(P.map X), WeylAt (xiGamma γ) D (G w + x)) {ι : Type}
    {I : Set ι} (hI : I.Finite) {A V : ι → Set ℂ} (hA : ∀ i ∈ I, (A i).Countable)
    (hV : ∀ i, IsOpen (V i)) (F : ι → TestC) (hF : ∀ i ∈ I, ∀ x ∈ V i, F i x = 1)
    (hFU : ∀ i ∈ I, tsupport (F i : ℂ → ℝ) ⊆ U) {T : β → ι → ℝ≥0∞} (hT0 : ∀ w i, T w i ≠ 0)
    (hTt : ∀ w i, T w i ≠ ⊤) :
    ∀ᵐ w ∂(P.map W), ∀ᵐ x ∂(P.map X), ∀ i ∈ I, internalDiam (D (G w + x)) (A i) (V i) ≠ T w i := by
  have h : ∀ i ∈ I, ∀ᵐ w ∂(P.map W), ∀ᵐ x ∂(P.map X),
      internalDiam (D (G w + x)) (A i) (V i) ≠ T w i := fun i hi =>
    ae_ae_diam_ne_of_weyl hγ hDm hX hwe (hA i hi) (hV i) (φ := testCont (F i)) (hF i hi)
      (confZBShiftAC_of_test hU (F i) (hFU i hi)) (fun w => hT0 w i) (fun w => hTt w i)
  filter_upwards [(eventually_all_finite hI).2 h] with w hw
  exact (eventually_all_finite hI).2 hw

omit [IsProbabilityMeasure P] in
/-- the monotonicity and continuity hypotheses of `confProp2_8_frozen` for a chain-formula event,
from Axiom III and S-cont-law on the frozen law -/
theorem chainEv_mono_cont {γ : ℝ} (hγ : 0 < γ) {D : DistC → ContMetric} {W : Ω → β}
    {X : Ω → DistC} {G : β → DistC}
    (hwe : ∀ᵐ w ∂(P.map W), ∀ᵐ x ∂(P.map X), WeylAt (xiGamma γ) D (G w + x))
    {κ : Type} {J : Set κ} (hJ : J.Finite) {A₀ V₀ : κ → Set ℂ}
    (hV₀ : ∀ i, IsOpen (V₀ i)) (hVb₀ : ∀ i, Bornology.IsBounded (V₀ i)) {T₀ : β → κ → ℝ≥0∞}
    {Fz : β → Prop}
    (hne : ∀ᵐ w ∂(P.map W), ∀ᵐ x ∂(P.map X),
      ∀ i ∈ J, internalDiam (D (G w + x)) (A₀ i) (V₀ i) ≠ T₀ w i) :
    ∀ᵐ w ∂(P.map W), ∀ᵐ x ∂(P.map X),
      (∀ f g : C(ℂ, ℝ), f ≤ g → (w, addFun x g) ∈ frozenChainEv D G Fz J A₀ V₀ T₀ →
        (w, addFun x f) ∈ frozenChainEv D G Fz J A₀ V₀ T₀) ∧
      (∀ fn : ℕ → C(ℂ, ℝ), Tendsto fn atTop (𝓝 0) → ∀ᶠ n in atTop,
        ((w, addFun x (fn n)) ∈ frozenChainEv D G Fz J A₀ V₀ T₀ ↔
          (w, x) ∈ frozenChainEv D G Fz J A₀ V₀ T₀)) := by
  have hξ : 0 ≤ xiGamma γ := (GM.xiGamma_pos hγ).le
  filter_upwards [hwe, hne] with w h1 h2
  filter_upwards [h1, h2] with x hx1 hx2
  obtain ⟨hm, hc⟩ := frozenDiamEv_mono_cont (Fz := Fz) (A := A₀) (T := T₀) hξ hJ hV₀ hVb₀
    hx1 hx2
  refine ⟨fun f g hfg hg => ?_, fun fn hfn => ?_⟩
  · rw [mem_frozenChainEv_iff_addFun hV₀ hx1] at hg ⊢
    exact hm f g hfg hg
  · filter_upwards [hc fn hfn] with n hn
    rw [mem_frozenChainEv_iff_addFun hV₀ hx1, mem_frozenChainEv_iff hV₀ hx1]
    exact hn

end LQGMetric.CONF
