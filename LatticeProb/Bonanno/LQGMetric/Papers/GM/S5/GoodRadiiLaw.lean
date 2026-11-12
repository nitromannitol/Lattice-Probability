/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.GM.S5.GoodRadiiLaw at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S5.Defs
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S3.GoodAnnulusL38Trans

/-!
# GM §5.1: the probability of `attainedLow` does not depend on the GFF (task P2-M2L2)

GM = Gwynne–Miller, arXiv:1905.00383, `literature/src/1905.00383/uniqueness-final.tex`.
The set `𝓡_0` of GM (5.1) (l. 2662–2668, `goodRadii`) asks that `P[attainedLow] ≥ p₀` for
"the" whole-plane GFF `h`; GM fix one `h`. In our convention (BP-M2-6) the condition is required
for every whole-plane GFF on every probability space, and the density statement S5.1 (from GM
P3.5, which counts radii for one field) needs that `P[h ∈ attainedLow]` is the same for all of
them. This is GM's own argument of l. 1200–1203 ("determined by `h` viewed modulo additive
constant … the law of `h` modulo additive constant is unique"), here for the event `attainedLow`:

* `attainedLowB`: the Borel form of `attainedLow` (uniqueness of the `D̃`-geodesic replaced by the
  midpoint condition `MidUnique`, decision D48, `GoodAnnulusUnique.lean`); it is universally
  measurable (`uMeasurableSet_attainedLowB`, projection of a Borel set) and agrees with
  `attainedLow` whenever `D̃_g` has geodesics between all pairs (`mem_attainedLow_iff_B`), which
  holds a.s. (GM.S1.1, `gm_S1_1`, from `DFGPSLem3_8`);
* `attainedLowB` is invariant under scaling `D_g`, `D̃_g` by a common factor
  (`mem_attainedLowB_of_scale`), hence a.s. under adding constants to `h` (Axiom III, Weyl
  scaling, `IsWeakLQGMetric.ae_dist_addConst`);
* the law transfer for universally measurable events `prob_eq_of_ae_addConst_iff_um`
  (`GoodAnnulusL38Trans.lean`, reused);
* `prob_attainedLow_eq`: the conclusion.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Metric
open scoped ENNReal

namespace LQGMetric.GM
open Blueprint

/-- Borel form of `attainedLow` (GM P3.5 (A′), l. 1276) -/
def attainedLowB (D D' : DistC → ContMetric) (α r c' : ℝ) : Set DistC :=
  {g | ∃ u ∈ sphere (0 : ℂ) (α * r), ∃ v ∈ sphere (0 : ℂ) r, ∃ η : C(unitInterval, ℂ),
    (D' g).1 (u, v) ≤ c' * (D g).1 (u, v) ∧ MidUnique (D' g) u v ∧ (D' g).IsGeod01 u v η ∧
    ∀ t, η t ∈ closure (annulus 0 (α * r) r : Set ℂ)}

/-- `attainedLow` equals its Borel form when `D̃_g`-geodesics exist between all pairs -/
theorem mem_attainedLow_iff_B {D D' : DistC → ContMetric} {α r c' : ℝ} {g : DistC}
    (hex : ∀ a b : ℂ, ∃ η, (D' g).IsGeod01 a b η) :
    g ∈ attainedLow D D' α r c' ↔ g ∈ attainedLowB D D' α r c' := by
  constructor
  · rintro ⟨u, hu, v, hv, hle, ⟨η, hη, huniq⟩, hin⟩
    have hU : (D' g).GeodUnique u v := fun a b ha hb => (huniq a ha).trans (huniq b hb).symm
    exact ⟨u, hu, v, hv, η, hle, midUnique_of_geodUnique hex hU, hη,
      fun t => hin η hη ⟨t, rfl⟩⟩
  · rintro ⟨u, hu, v, hv, η, hle, hm, hη, hK⟩
    have hU := geodUnique_of_midUnique hm
    refine ⟨u, hu, v, hv, hle, ⟨η, hη, fun η' hη' => hU η' η hη' hη⟩, fun η' hη' => ?_⟩
    rintro _ ⟨t, rfl⟩
    rw [hU η' η hη' hη]
    exact hK t

/-- **the Borel form is universally measurable** (projection of a Borel set) -/
theorem uMeasurableSet_attainedLowB {D D' : DistC → ContMetric} (hD : Measurable D)
    (hD' : Measurable D') (α r c' : ℝ) : UMeasurableSet (attainedLowB D D' α r c') := by
  set K := closure (annulus (0 : ℂ) (α * r) r : Set ℂ)
  let T := DistC × (ℂ × ℂ) × C(unitInterval, ℂ)
  have m1 : Measurable fun p : T => (p.2.1.1, p.2.1.2) := measurable_snd.fst
  have mDuv : Measurable fun p : T => (D' p.1, p.2.1.1, p.2.1.2) :=
    (hD'.comp measurable_fst).prodMk m1
  have mGeo : Measurable fun p : T => (D' p.1, p.2) :=
    (hD'.comp measurable_fst).prodMk measurable_snd
  have hS1 : MeasurableSet {p : T | p.2.1.1 ∈ sphere (0 : ℂ) (α * r)} :=
    isClosed_sphere.measurableSet.preimage measurable_snd.fst.fst
  have hS2 : MeasurableSet {p : T | p.2.1.2 ∈ sphere (0 : ℂ) r} :=
    isClosed_sphere.measurableSet.preimage measurable_snd.fst.snd
  have hM : MeasurableSet {p : T | MidUnique (D' p.1) p.2.1.1 p.2.1.2} :=
    measurableSet_midUnique.preimage mDuv
  have hG : MeasurableSet {p : T | (D' p.1).IsGeod01 p.2.1.1 p.2.1.2 p.2.2} :=
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
      c' * (D p.1).1 (p.2.1.1, p.2.1.2)} :=
    measurableSet_le (fD D' hD') ((fD D hD).const_mul c')
  have hS := hS1.inter (hS2.inter (hR.inter (hM.inter (hG.inter hK))))
  convert UMeasurableSet.setOf_exists hS using 1
  ext g
  simp only [attainedLowB, mem_ofPred_eq, mem_inter_iff, Prod.exists]
  constructor
  · rintro ⟨u, hu, v, hv, η, h1, h2, h3, h4⟩
    exact ⟨u, v, η, hu, hv, h1, h2, h3, h4⟩
  · rintro ⟨u, v, η, hu, hv, h1, h2, h3, h4⟩
    exact ⟨u, hu, v, hv, η, h1, h2, h3, h4⟩

lemma midPt_of_scale {d₁ d₂ : ContMetric} {e : ℝ} (he : 0 < e)
    (h : ∀ u v, d₂.1 (u, v) = e * d₁.1 (u, v)) (u v : ℂ) (t : ℝ) (x : ℂ) :
    midPt d₂ u v t x ↔ midPt d₁ u v t x := by
  simp only [midPt, h]
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨mul_left_cancel₀ he.ne' (by rw [h1]; ring),
      mul_left_cancel₀ he.ne' (by rw [h2]; ring)⟩
  · rintro ⟨h1, h2⟩
    exact ⟨by rw [h1]; ring, by rw [h2]; ring⟩

lemma midUnique_of_scale {d₁ d₂ : ContMetric} {e : ℝ} (he : 0 < e)
    (h : ∀ u v, d₂.1 (u, v) = e * d₁.1 (u, v)) (u v : ℂ) :
    MidUnique d₂ u v ↔ MidUnique d₁ u v := by
  simp only [MidUnique, midPt_of_scale he h]

lemma cm_isGeod01_iff_of_scale {d₁ d₂ : ContMetric} {e : ℝ} (he : 0 < e)
    (h : ∀ u v, d₂.1 (u, v) = e * d₁.1 (u, v)) (u v : ℂ) (η : C(unitInterval, ℂ)) :
    d₂.IsGeod01 u v η ↔ d₁.IsGeod01 u v η := by
  simp only [ContMetric.IsGeod01, h]
  refine and_congr Iff.rfl (and_congr Iff.rfl (forall₂_congr fun s t => ?_))
  constructor
  · intro h1; exact mul_left_cancel₀ he.ne' (by rw [h1]; ring)
  · intro h1; rw [h1]; ring

/-- `attainedLowB` is invariant under scaling `D_g` and `D̃_g` by a common factor -/
theorem mem_attainedLowB_of_scale {D D' : DistC → ContMetric} {α r c' : ℝ} {g₁ g₂ : DistC}
    {e : ℝ} (he : 0 < e) (h : ∀ u v, (D g₂).1 (u, v) = e * (D g₁).1 (u, v))
    (h' : ∀ u v, (D' g₂).1 (u, v) = e * (D' g₁).1 (u, v)) :
    g₂ ∈ attainedLowB D D' α r c' ↔ g₁ ∈ attainedLowB D D' α r c' := by
  have hr : ∀ u v, (D' g₂).1 (u, v) ≤ c' * (D g₂).1 (u, v) ↔
      (D' g₁).1 (u, v) ≤ c' * (D g₁).1 (u, v) := fun u v => by
    rw [h, h', show c' * (e * (D g₁).1 (u, v)) = e * (c' * (D g₁).1 (u, v)) by ring]
    exact mul_le_mul_iff_right₀ he
  simp only [attainedLowB, mem_ofPred_eq, hr, midUnique_of_scale he h', cm_isGeod01_iff_of_scale he h']

/-- **GM §5.1, law invariance of `𝓡_0`**: `P[h ∈ attainedLow]` is the same for every whole-plane
GFF (with `DFGPSLem3_8`, for GM.S1.1). -/
theorem prob_attainedLow_eq (h38 : DFGPSLem3_8) {γ : ℝ} {D D' : DistC → ContMetric}
    {c : ℝ → ℝ} (hPS : PairSetting γ D D' c) (α r c' : ℝ)
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] (h : Ω → DistC)
    (hh : IsWholePlaneGFF h P)
    {Ω' : Type} [MeasurableSpace Ω'] (P' : Measure Ω') [IsProbabilityMeasure P'] (h' : Ω' → DistC)
    (hh' : IsWholePlaneGFF h' P') :
    P (h ⁻¹' attainedLow D D' α r c') = P' (h' ⁻¹' attainedLow D D' α r c') := by
  obtain ⟨hγ0, hγ2, hD, hD'⟩ := hPS
  have key : ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      (h : Ω → DistC), IsWholePlaneGFF h P →
      P (h ⁻¹' attainedLow D D' α r c') = P (h ⁻¹' attainedLowB D D' α r c') ∧
      ∀ᵐ ω ∂P, ∀ a : ℝ, addConst (h ω) a ∈ attainedLowB D D' α r c' ↔
        h ω ∈ attainedLowB D D' α r c' := by
    intro Ω _ P _ h hh
    have hgp := Tight.isGFFPlusCont_of_wp hh
    refine ⟨measure_congr ?_, ?_⟩
    · filter_upwards [gm_S1_1 h38 hγ0 hγ2 hD' P h hh] with ω hω
      exact propext (mem_attainedLow_iff_B hω)
    · filter_upwards [hD.ae_dist_addConst hgp, hD'.ae_dist_addConst hgp] with ω h1 h2 a
      exact mem_attainedLowB_of_scale (Real.exp_pos _) (h1 a) (h2 a)
  obtain ⟨k1, k2⟩ := key P h hh
  obtain ⟨k1', k2'⟩ := key P' h' hh'
  rw [k1, k1']
  exact prob_eq_of_ae_addConst_iff_um hh hh'
    (uMeasurableSet_attainedLowB hD.measurable hD'.measurable α r c') k2 k2'

end LQGMetric.GM
