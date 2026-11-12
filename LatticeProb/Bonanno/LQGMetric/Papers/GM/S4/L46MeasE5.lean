/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.GM.S4.L46MeasE5 at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S4.L46MeasE4

/-!
# `GMArcRelAn` (task P2-E3d)

GM = Gwynne–Miller, arXiv:1905.00383v3, (4.7) and GM.S4.1 (l. 1648–1654): the relation
`x ∈ Conf(s,t)`, `y ∈ arcOf x` is analytic on `lenSet` (`gm_arcRelAn`). GM do not discuss
measurability; own descriptive-set-theory argument (decision D65): the relation is the projection
of the Borel set of `((d, s, t), x, y)` and witnesses `((y', w'), w)` satisfying `gmFrF`
(`x ∈ ∂𝓑^•_s`, `y ∈ ∂𝓑^•_t`) and `gmHitF` (leftmost geodesics to `y'`, `y` through `x`,
`gmE_hit_iff`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Filter Topology Set Metric
open scoped ENNReal
open LQGMetric.Blueprint

namespace LQGMetric.GM
open LocalEvent

local notation "𝕋" => AddCircle (2 * Real.pi)

instance gmE_sb_hitW : StandardBorelSpace GMHitW := by
  unfold GMHitW
  have h1 : StandardBorelSpace (C(𝕋, ℂ) × C(𝕋, ℝ)) := inferInstance
  have h2 : StandardBorelSpace (ℕ → ℝ × C(unitInterval, ℂ)) := inferInstance
  have h3 : StandardBorelSpace unitInterval := inferInstance
  have h4 : StandardBorelSpace C(unitInterval, ℂ) := inferInstance
  have h5 : StandardBorelSpace ((ℕ → ℝ × C(unitInterval, ℂ)) × unitInterval) :=
    @StandardBorelSpace.prod _ _ _ _ h2 h3
  have h6 : StandardBorelSpace (ℝ × (ℕ → ℝ × C(unitInterval, ℂ)) × unitInterval) :=
    @StandardBorelSpace.prod _ _ _ _ inferInstance h5
  have h7 := @StandardBorelSpace.prod _ _ _ _ h1 h6
  exact @StandardBorelSpace.prod _ _ _ _ h4 h7

instance gmE_sb_arcW : StandardBorelSpace ((ℂ × GMHitW) × GMHitW) := by
  have : StandardBorelSpace (ℂ × GMHitW) := inferInstance
  infer_instance

lemma gmE_measurable_geoF_comp {X : Type} [MeasurableSpace X] {f : X → ContMetric} {t : X → ℝ}
    {y : X → ℂ} {η : X → C(unitInterval, ℂ)} (hf : Measurable f) (ht : Measurable t)
    (hy : Measurable y) (hη : Measurable η) (𝕫 : ℂ) :
    Measurable fun q => gmGeoF (f q) (t q) 𝕫 (y q) (η q) := by
  have ev : ∀ a : unitInterval, Measurable fun q => η q a := fun a =>
    (continuous_eval_const a).measurable.comp hη
  exact (measurableSet_setOfPred.1 (measurableSet_le measurable_const ht)).and
    ((measurableSet_setOfPred.1 (measurableSet_eq_fun (ev 0) measurable_const)).and
    ((measurableSet_setOfPred.1 (measurableSet_eq_fun (ev 1) hy)).and
    (Measurable.forall fun a => Measurable.forall fun b => measurableSet_setOfPred.1
      (measurableSet_eq_fun (continuous_contMetric_apply.measurable.comp
        (hf.prodMk ((ev _).prodMk (ev _)))) (ht.mul measurable_const)))))

lemma gmE_measurable_hitF_comp {X : Type} [MeasurableSpace X] {f : X → ContMetric} {t : X → ℝ}
    {y x : X → ℂ} {w : X → GMHitW} (hf : Measurable f) (ht : Measurable t) (hy : Measurable y)
    (hx : Measurable x) (hw : Measurable w) (𝕫 : ℂ) :
    Measurable fun q => gmHitF (f q) 𝕫 (t q) (y q) (x q) (w q) := by
  have hη : Measurable fun q => (w q).1 := measurable_fst.comp hw
  have hw2 : Measurable fun q => (w q).2 := measurable_snd.comp hw
  have hφ : Measurable fun q => (w q).2.1.1 := measurable_fst.comp (measurable_fst.comp hw2)
  have hψ : Measurable fun q => (w q).2.1.2 := measurable_snd.comp (measurable_fst.comp hw2)
  have hw3 : Measurable fun q => (w q).2.2 := measurable_snd.comp hw2
  have ht₀ : Measurable fun q => (w q).2.2.1 := measurable_fst.comp hw3
  have hsq : Measurable fun q => (w q).2.2.2.1 := measurable_fst.comp (measurable_snd.comp hw3)
  have hv : Measurable fun q => (w q).2.2.2.2 := measurable_snd.comp (measurable_snd.comp hw3)
  have hsqn : ∀ n, Measurable fun q => ((w q).2.2.2.1 n) := fun n =>
    (measurable_pi_apply n).comp hsq
  have hev : ∀ {g : X → C(𝕋, ℂ)} {s : X → ℝ}, Measurable g → Measurable s →
      Measurable fun q => g q (s q : 𝕋) := fun hg hs =>
    continuous_eval.measurable.comp (hg.prodMk (gmE_continuous_coe.measurable.comp hs))
  refine (gmE_measurable_frF_comp hf ht hy 𝕫).and ((gmE_measurable_geoF_comp hf ht hy hη 𝕫).and
    ((gmE_measurable_jordF_comp hf ht hφ hψ 𝕫).and
    ((measurableSet_setOfPred.1 (measurableSet_eq_fun (hev hφ ht₀) hy)).and
    ((measurableSet_setOfPred.1 (measurableSet_tendsto (𝓝 (0 : ℝ))
      (f := fun n q => dist ((w q).2.2.2.1 n).1 (w q).2.2.1)
      fun n => (measurable_fst.comp (hsqn n)).dist ht₀)).and
    ((Measurable.forall fun n => measurableSet_setOfPred.1
      (measurableSet_lt ht₀ (measurable_fst.comp (hsqn n)))).and
    ((Measurable.forall fun n => gmE_measurable_geoF_comp hf ht
      (hev hφ (measurable_fst.comp (hsqn n))) (measurable_snd.comp (hsqn n)) 𝕫).and
    ((measurableSet_setOfPred.1 (measurableSet_tendsto (𝓝 (0 : ℝ))
      (f := fun n q => dist ((w q).2.2.2.1 n).2 (w q).1)
      fun n => (measurable_snd.comp (hsqn n)).dist hη)).and
    (measurableSet_setOfPred.1 (measurableSet_eq_fun
      (continuous_eval.measurable.comp (hη.prodMk hv)) hx)))))))))

/-- **`GMArcRelAn` holds** -/
theorem gm_arcRelAn (𝕫 : ℂ) : GMArcRelAn 𝕫 := by
  refine ⟨(ℂ × GMHitW) × GMHitW, inferInstance, inferInstance,
    {q | gmFrF q.1.1.1 𝕫 q.1.1.2.1 q.1.2.1 ∧
      gmHitF q.1.1.1 𝕫 q.1.1.2.2 q.2.1.1 q.1.2.1 q.2.1.2 ∧
      gmFrF q.1.1.1 𝕫 q.1.1.2.2 q.1.2.2 ∧ gmHitF q.1.1.1 𝕫 q.1.1.2.2 q.1.2.2 q.1.2.1 q.2.2},
    ?_, ?_⟩
  · have hp : Measurable fun q : ((ContMetric × ℝ × ℝ) × ℂ × ℂ) × (ℂ × GMHitW) × GMHitW => q.1 :=
      measurable_fst
    have hd : Measurable fun q : ((ContMetric × ℝ × ℝ) × ℂ × ℂ) × (ℂ × GMHitW) × GMHitW =>
      q.1.1.1 := measurable_fst.comp (measurable_fst.comp hp)
    have hs : Measurable fun q : ((ContMetric × ℝ × ℝ) × ℂ × ℂ) × (ℂ × GMHitW) × GMHitW =>
      q.1.1.2.1 := measurable_fst.comp (measurable_snd.comp (measurable_fst.comp hp))
    have ht : Measurable fun q : ((ContMetric × ℝ × ℝ) × ℂ × ℂ) × (ℂ × GMHitW) × GMHitW =>
      q.1.1.2.2 := measurable_snd.comp (measurable_snd.comp (measurable_fst.comp hp))
    have hx : Measurable fun q : ((ContMetric × ℝ × ℝ) × ℂ × ℂ) × (ℂ × GMHitW) × GMHitW =>
      q.1.2.1 := measurable_fst.comp (measurable_snd.comp hp)
    have hy : Measurable fun q : ((ContMetric × ℝ × ℝ) × ℂ × ℂ) × (ℂ × GMHitW) × GMHitW =>
      q.1.2.2 := measurable_snd.comp (measurable_snd.comp hp)
    have hb : Measurable fun q : ((ContMetric × ℝ × ℝ) × ℂ × ℂ) × (ℂ × GMHitW) × GMHitW =>
      q.2 := measurable_snd
    exact measurableSet_setOfPred.2 ((gmE_measurable_frF_comp hd hs hx 𝕫).and
      ((gmE_measurable_hitF_comp hd ht (measurable_fst.comp (measurable_fst.comp hb)) hx
        (measurable_snd.comp (measurable_fst.comp hb)) 𝕫).and
      ((gmE_measurable_frF_comp hd ht hy 𝕫).and
        (gmE_measurable_hitF_comp hd ht hy hx (measurable_snd.comp hb) 𝕫))))
  · rintro ⟨⟨d, s, t⟩, x, y⟩ hd
    simp only [mem_ofPred_eq] at hd ⊢
    show (x ∈ confPts d 𝕫 s t ∧ y ∈ arcOf d 𝕫 t x) ↔ _
    unfold confPts hitSet arcOf
    simp only [mem_ofPred_eq]
    rw [gmE_mem_frontier_iff hd, gmE_mem_frontier_iff hd]
    constructor
    · rintro ⟨⟨hx, y', P, hP⟩, hy, hQ⟩
      obtain ⟨w', hw'⟩ := (gmE_hit_iff hd 𝕫 t y' x).1 ⟨P, hP⟩
      obtain ⟨w, hw⟩ := (gmE_hit_iff hd 𝕫 t y x).1 hQ
      exact ⟨((y', w'), w), hx, hw', hy, hw⟩
    · rintro ⟨⟨⟨y', w'⟩, w⟩, hx, hw', hy, hw⟩
      obtain ⟨P, hP⟩ := (gmE_hit_iff hd 𝕫 t y' x).2 ⟨w', hw'⟩
      exact ⟨⟨hx, y', P, hP⟩, hy, (gmE_hit_iff hd 𝕫 t y x).2 ⟨w, hw⟩⟩

end LQGMetric.GM
