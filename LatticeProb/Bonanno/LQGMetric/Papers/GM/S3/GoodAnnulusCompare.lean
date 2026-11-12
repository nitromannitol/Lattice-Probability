/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.GM.S3.GoodAnnulusCompare at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S3.GoodAnnulus
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S3.GoodAnnulusUnique
import LatticeProb.Bonanno.LQGMetric.Meas.UM
import LatticeProb.Bonanno.LQGMetric.Field.StandardBorelRange

/-!
# Condition 1 of `𝖤_r(z)` is universally measurable (task P2-M2E, decision D48)

GM l. 1327 (condition 1) and l. 1345–1360 (proof of Lemma 3.7). `gaCompareB` is condition 1 with
"the `D_h`-geodesic from `u` to `v` is unique and contained in `cl 𝔸_{αr,r}(z)`" replaced by
"`MidUnique` (a Borel condition, `measurableSet_midUnique`) and some geodesic from `u` to `v` lies
in `cl 𝔸_{αr,r}(z)`".

* `mem_gaCompare_iff`: the two agree whenever `D_g` has geodesics between all pairs — a.s. for a
  weak LQG metric (boundedly compact length metric: `gm_S1_1_bcpt`, `exists_isGeod01_of_bcpt`).
* `uMeasurableSet_gaCompareB`: `gaCompareB` is universally measurable: it is
  `{g | ∀ (u, v, η), (g, (u, v, η)) ∈ S}` for a Borel `S` (coanalytic, `UMeasurableSet.setOf_forall`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Metric

namespace LQGMetric.GM
open Blueprint

/-- condition 1 of `𝖤_r(z)` in Borel form -/
def gaCompareB (D D' : DistC → ContMetric) (α C' r : ℝ) (z : ℂ) : Set DistC :=
  {g | ∀ u ∈ sphere z (α * r), ∀ v ∈ sphere z r, ∀ η : C(unitInterval, ℂ),
    MidUnique (D g) u v → (D g).IsGeod01 u v η →
    (∀ t, η t ∈ closure (annulus z (α * r) r : Set ℂ)) → (D' g).1 (u, v) ≤ C' * (D g).1 (u, v)}

/-- condition 1 equals its Borel form when geodesics exist between all pairs -/
theorem mem_gaCompare_iff {D D' : DistC → ContMetric} {α C' r : ℝ} {z : ℂ} {g : DistC}
    (hex : ∀ a b : ℂ, ∃ η, (D g).IsGeod01 a b η) :
    g ∈ gaCompare D D' α C' r z ↔ g ∈ gaCompareB D D' α C' r z := by
  constructor
  · intro h u hu v hv η hm hη hK
    have hU := geodUnique_of_midUnique hm
    refine h u hu v hv ⟨⟨η, hη, fun η' hη' => hU η' η hη' hη⟩, fun η' hη' => ?_⟩
    rintro _ ⟨t, rfl⟩
    rw [hU η' η hη' hη]
    exact hK t
  · intro h u hu v hv ⟨⟨η, hη, huniq⟩, hin⟩
    have hU : (D g).GeodUnique u v := fun a b ha hb => (huniq a ha).trans (huniq b hb).symm
    exact h u hu v hv η (midUnique_of_geodUnique hex hU) hη
      (fun t => hin η hη ⟨t, rfl⟩)

/-- the geodesic relation with varying endpoints is closed -/
theorem isClosed_geodRel3 :
    IsClosed {q : ContMetric × (ℂ × ℂ) × C(unitInterval, ℂ) |
      q.1.IsGeod01 q.2.1.1 q.2.1.2 q.2.2} := by
  have he : ∀ s : unitInterval,
      Continuous fun q : ContMetric × (ℂ × ℂ) × C(unitInterval, ℂ) => q.2.2 s :=
    fun s => (continuous_eval_const s).comp continuous_snd.snd
  simp only [ContMetric.IsGeod01, ofPred_and, ofPred_forall]
  refine (isClosed_eq (he 0) continuous_snd.fst.fst).inter
    ((isClosed_eq (he 1) continuous_snd.fst.snd).inter
    (isClosed_iInter fun s => isClosed_iInter fun t => isClosed_eq ?_ ?_))
  · exact continuous_contMetric_apply.comp (continuous_fst.prodMk ((he s).prodMk (he t)))
  · exact continuous_const.mul (continuous_contMetric_apply.comp
      (continuous_fst.prodMk continuous_snd.fst))

/-- **condition 1 is universally measurable** (Borel form) -/
theorem uMeasurableSet_gaCompareB {D D' : DistC → ContMetric} (hD : Measurable D)
    (hD' : Measurable D') (α C' r : ℝ) (z : ℂ) :
    UMeasurableSet (gaCompareB D D' α C' r z) := by
  set K := closure (annulus z (α * r) r : Set ℂ)
  let T := DistC × (ℂ × ℂ) × C(unitInterval, ℂ)
  have m1 : Measurable fun p : T => (p.2.1.1, p.2.1.2) := measurable_snd.fst
  have mDuv : Measurable fun p : T => (D p.1, p.2.1.1, p.2.1.2) :=
    (hD.comp measurable_fst).prodMk m1
  have mGeo : Measurable fun p : T => (D p.1, p.2) := (hD.comp measurable_fst).prodMk measurable_snd
  have hS1 : MeasurableSet {p : T | p.2.1.1 ∈ sphere z (α * r)} :=
    isClosed_sphere.measurableSet.preimage measurable_snd.fst.fst
  have hS2 : MeasurableSet {p : T | p.2.1.2 ∈ sphere z r} :=
    isClosed_sphere.measurableSet.preimage measurable_snd.fst.snd
  have hM : MeasurableSet {p : T | MidUnique (D p.1) p.2.1.1 p.2.1.2} :=
    measurableSet_midUnique.preimage mDuv
  have hG : MeasurableSet {p : T | (D p.1).IsGeod01 p.2.1.1 p.2.1.2 p.2.2} :=
    isClosed_geodRel3.measurableSet.preimage mGeo
  have hKc : IsClosed {η : C(unitInterval, ℂ) | ∀ t, η t ∈ K} := by
    simp only [ofPred_forall]
    exact isClosed_iInter fun t => isClosed_closure.preimage (continuous_eval_const t)
  have hK : MeasurableSet {p : T | ∀ t, p.2.2 t ∈ K} :=
    hKc.measurableSet.preimage measurable_snd.snd
  have fD : ∀ E : DistC → ContMetric, Measurable E →
      Measurable fun p : T => (E p.1).1 (p.2.1.1, p.2.1.2) := fun E hE =>
    continuous_contMetric_apply.measurable.comp ((hE.comp measurable_fst).prodMk m1)
  have hR : MeasurableSet {p : T | (D' p.1).1 (p.2.1.1, p.2.1.2) ≤
      C' * (D p.1).1 (p.2.1.1, p.2.1.2)} :=
    measurableSet_le (fD D' hD') ((fD D hD).const_mul C')
  have hS : MeasurableSet ({p : T | p.2.1.1 ∈ sphere z (α * r)}ᶜ ∪
      {p : T | p.2.1.2 ∈ sphere z r}ᶜ ∪ {p : T | MidUnique (D p.1) p.2.1.1 p.2.1.2}ᶜ ∪
      {p : T | (D p.1).IsGeod01 p.2.1.1 p.2.1.2 p.2.2}ᶜ ∪ {p : T | ∀ t, p.2.2 t ∈ K}ᶜ ∪
      {p : T | (D' p.1).1 (p.2.1.1, p.2.1.2) ≤ C' * (D p.1).1 (p.2.1.1, p.2.1.2)}) :=
    ((((hS1.compl.union hS2.compl).union hM.compl).union hG.compl).union hK.compl).union hR
  convert UMeasurableSet.setOf_forall hS using 1
  ext g
  simp only [gaCompareB, mem_ofPred_eq, mem_union, mem_compl_iff, Prod.forall]
  constructor
  · intro h u v η
    by_contra hc
    simp only [not_or, not_not] at hc
    exact hc.2 (h u hc.1.1.1.1.1 v hc.1.1.1.1.2 η hc.1.1.1.2 hc.1.1.2 hc.1.2)
  · intro h u hu v hv η hm hη hk
    rcases h u v η with ((((h1 | h1) | h1) | h1) | h1) | h1
    · exact absurd hu h1
    · exact absurd hv h1
    · exact absurd hm h1
    · exact absurd hη h1
    · exact absurd hk h1
    · exact h1

end LQGMetric.GM
