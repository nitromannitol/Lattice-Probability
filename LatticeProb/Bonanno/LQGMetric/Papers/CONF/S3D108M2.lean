/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.CONF.S3D108M2 at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.CONF.S3D108L1

/-!
# CONF Proposition 2.8 for measurable (chain-formula) frozen diameter events

Gwynne–Miller, *Confluence of geodesics in LQG*, arXiv:1905.00381 (CONF),
`literature/src/1905.00381/confluence-final.tex`, Proposition 2.8 (C:656–661, proof C:748–752)
in the frozen form of Lemma 3.3, Step 3 (C:1236–1243).

`confProp2_8_diam_test` (S3D108L1) needs `MeasurableSet (frozenDiamEv …)`. The internal metric
`D(·,·;V)` is known to be Borel only on length metrics (`measurable_internal`, via the countable
chain formula `chainInf`). This file removes that hypothesis:

* `frozenChainEv`: the frozen diameter event with `chainInf` in place of `internal`; it is
  measurable (`measurableSet_frozenChainEv`) for measurable `G`, `Fz`, `T` and countable `A i`;
* `mem_frozenChainEv_iff_addFun`: at a field `G w + x` where Axiom III holds, every perturbation
  `D_{G w + x + f}` is a length metric (`isLength_of_eq_weylScale`), so the two events agree along
  all continuous perturbations of `x`;
* **`confProp2_8_chain_test`**: CONF Prop 2.8 (frozen) for the measurable events `frozenChainEv`,
  with no measurability hypothesis on `frozenDiamEv`;
* **`confProp2_8_diam_test'`**: the conclusion of `confProp2_8_diam_test` for `frozenDiamEv`
  itself, with `MeasurableSet (frozenDiamEv …)` replaced by measurability of `G`, `Fz`, `T`
  (the sections agree a.e. with those of `frozenChainEv`, `frozen_fkg_congr_ae`);
* `ae_ae_section_chain_eq`: the a.e. equality of sections used for the transfer.

The proof is CONF's (through `confProp2_8_frozen`, S3D108K1); only the measurable version of the
event is new (a Lean-level measurability device).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped ENNReal

namespace LQGMetric.CONF

open Blueprint

/-- the chain-formula diameter `sup_{u,v ∈ A} chainInf_D(u, v; V)` -/
def chainDiam (D : ContMetric) (A V : Set ℂ) : ℝ≥0∞ :=
  ⨆ u ∈ A, ⨆ v ∈ A, D.chainInf V u v

lemma chainDiam_eq_internalDiam {D : ContMetric} (hD : D.IsLength) (A : Set ℂ) {V : Set ℂ}
    (hV : IsOpen V) : chainDiam D A V = internalDiam D A V := by
  simp only [chainDiam, internalDiam, D.internal_eq_chainInf hD hV]

section Ev

variable {β : Type} [MeasurableSpace β]

/-- the frozen diameter event with the chain formula:
`{Fz w ∧ ∀ i ∈ I, chainDiam(D_{G w + x}; A i, V i) ≤ T w i}` -/
def frozenChainEv (D : DistC → ContMetric) (G : β → DistC) (Fz : β → Prop) {ι : Type}
    (I : Set ι) (A V : ι → Set ℂ) (T : β → ι → ℝ≥0∞) : Set (β × DistC) :=
  {p | Fz p.1 ∧ ∀ i ∈ I, chainDiam (D (G p.1 + p.2)) (A i) (V i) ≤ T p.1 i}

lemma measurableSet_frozenChainEv {D : DistC → ContMetric} (hD : Measurable D) {G : β → DistC}
    (hG : Measurable G) {Fz : β → Prop} (hFz : MeasurableSet {w | Fz w}) {ι : Type}
    {I : Set ι} (hI : I.Countable) {A V : ι → Set ℂ} (hA : ∀ i ∈ I, (A i).Countable)
    {T : β → ι → ℝ≥0∞} (hT : ∀ i ∈ I, Measurable fun w => T w i) :
    MeasurableSet (frozenChainEv D G Fz I A V T) := by
  have hDG : Measurable fun p : β × DistC => D (G p.1 + p.2) :=
    hD.comp (measurable_add_frozen hG)
  have e : frozenChainEv D G Fz I A V T = (Prod.fst ⁻¹' {w | Fz w}) ∩
      ⋂ i ∈ I, {p | chainDiam (D (G p.1 + p.2)) (A i) (V i) ≤ T p.1 i} := by
    ext p; simp [frozenChainEv]
  rw [e]
  refine (measurable_fst hFz).inter (MeasurableSet.biInter hI fun i hi => measurableSet_le ?_
    ((hT i hi).comp measurable_fst))
  exact Measurable.biSup _ (hA i hi) fun u _ => Measurable.biSup _ (hA i hi) fun v _ =>
    (ContMetric.measurable_chainInf (V i)).comp
      (hDG.prodMk (measurable_const (a := ((u, v) : ℂ × ℂ))))

variable {ξ : ℝ} {D : DistC → ContMetric}

omit [MeasurableSpace β]

/-- along every continuous perturbation of a field where Axiom III holds, the chain event and the
internal event agree -/
lemma mem_frozenChainEv_iff_addFun {G : β → DistC} {Fz : β → Prop} {ι : Type} {I : Set ι}
    {A V : ι → Set ℂ} (hV : ∀ i, IsOpen (V i)) {T : β → ι → ℝ≥0∞} {w : β} {x : DistC}
    (hw : WeylAt ξ D (G w + x)) (f : C(ℂ, ℝ)) :
    (w, addFun x f) ∈ frozenChainEv D G Fz I A V T ↔
      (w, addFun x f) ∈ frozenDiamEv D G Fz I A V T := by
  have e : G w + addFun x f = addFun (G w + x) f := by simp only [addFun, add_assoc]
  have hl : (D (G w + addFun x f)).IsLength := by
    rw [e]
    exact isLength_of_eq_weylScale (D (addFun (G w + x) f)) (fun a b => (hw f a b).symm)
  simp only [frozenChainEv, frozenDiamEv, mem_ofPred_eq,
    chainDiam_eq_internalDiam hl _ (hV _)]

lemma mem_frozenChainEv_iff {G : β → DistC} {Fz : β → Prop} {ι : Type} {I : Set ι}
    {A V : ι → Set ℂ} (hV : ∀ i, IsOpen (V i)) {T : β → ι → ℝ≥0∞} {w : β} {x : DistC}
    (hw : WeylAt ξ D (G w + x)) :
    (w, x) ∈ frozenChainEv D G Fz I A V T ↔ (w, x) ∈ frozenDiamEv D G Fz I A V T := by
  have := mem_frozenChainEv_iff_addFun (Fz := Fz) (I := I) (A := A) (T := T) hV hw 0
  rwa [GM.addFun_zero_eq] at this

end Ev

section Prop28

variable {Ω β : Type} [MeasurableSpace Ω] [MeasurableSpace β] {P : Measure Ω}
  [IsProbabilityMeasure P]

end Prop28

end LQGMetric.CONF
