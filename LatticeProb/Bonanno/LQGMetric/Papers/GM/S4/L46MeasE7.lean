/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.GM.S4.L46MeasE7 at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S4.L46MeasE6

/-!
# `GMAvoidRelAn` (task P2-E3d, decision D65 (iii))

GM = Gwynne–Miller, arXiv:1905.00383v3, l. 1695–1696: `D_h(·,·;ℂ∖cl B_r(z))`-geodesics from
`𝕫` to `∂B_r(z)` (`IsAvoidGeod`). GM do not discuss measurability; own descriptive-set-theory
argument:

* `gmE_min_iff`: on `lenSet`, the minimality clause "`ℓ ≤ len(Q')` for every path `Q'` from `𝕫`
  to `x` in `ℂ ∖ B_r(z)`" is `ℓ ≤ sup_m chainInf(ℂ ∖ B̄_{r−1/(m+1)}(z))(𝕫, x)` (`gmAvInf`, Borel),
  by `gmE_exists_avoid_path` (Arzelà–Ascoli) and `ContMetric.internal_eq_chainInf`;
* the avoiding geodesic `Q` is encoded by `η ∈ C([0,1], ℂ)` (affine reparametrization as in
  `exists_reparam`), "`Q(u) ∉ B̄_r(z)` for `u < T`" in countable form (`gmE_avoidOpen_iff`);
* `gm_avoidRelAn`: the relation is analytic on `lenSet` (case `𝕫 ∈ B̄_r(z)` separately: then the
  only avoiding geodesic is the constant one, when `𝕫 ∈ ∂B_r(z)`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Filter Topology Set Metric
open scoped ENNReal NNReal
open LQGMetric.Blueprint

namespace LQGMetric.GM
open LocalEvent MetricGeometry

/-- `exists_reparam` (GoodAnnulusMeas4a) on `[0, T]`, exposing the formula -/
lemma gmE_reparam {P : ℝ → ℂ} {T : ℝ} (hT : 0 ≤ T) (hP : ContinuousOn P (Icc 0 T)) :
    ∃ η : C(unitInterval, ℂ), (∀ v : unitInterval, η v = P (0 + v * (T - 0))) ∧
      ∀ d : ContMetric, d.len (fun t => η (pj t)) 0 1 = d.len P 0 T := by
  set φ : ℝ → ℝ := fun t => 0 + t * (T - 0)
  have hφm : ∀ t : unitInterval, φ t ∈ Icc 0 T := fun t => by
    have := t.2.1; have := t.2.2
    exact ⟨by simp only [φ]; nlinarith, by simp only [φ]; nlinarith⟩
  let η : C(unitInterval, ℂ) := ⟨fun t => P (φ t), hP.comp_continuous (by fun_prop) hφm⟩
  refine ⟨η, fun v => rfl, fun d => ?_⟩
  unfold ContMetric.len curveLength
  have heq : EqOn (d.pt ∘ fun t => η (pj t)) ((d.pt ∘ P) ∘ φ) (Icc 0 1) := fun t ht => by
    simp only [Function.comp_apply, η, ContinuousMap.coe_mk, pj_coe_of_mem ht]
  rw [eVariationOn.eq_of_eqOn heq, eVariationOn.comp_eq_of_monotoneOn _ φ
    (fun s _ t _ hst => by simp only [φ]; nlinarith [sub_nonneg.2 hT]), image_affine_Icc hT]

lemma gmE_avoidOpen_iff (η : C(unitInterval, ℂ)) (z : ℂ) (r : ℝ) :
    (∀ u ∈ Ico (0 : ℝ) 1, r < dist (η (pj u)) z) ↔
      ∀ n : ℕ, ∃ m : ℕ, ∀ q : ℚ, 0 ≤ (q : ℝ) → (q : ℝ) ≤ 1 - 1 / ((n : ℝ) + 1) →
        r + 1 / ((m : ℝ) + 1) ≤ dist (η (pj q)) z := by
  have hg : Continuous fun u : ℝ => dist (η (pj u)) z :=
    (η.continuous.comp continuous_projIcc).dist continuous_const
  constructor
  · intro h n
    have hn1 : 1 / ((n : ℝ) + 1) ≤ 1 := by
      rw [div_le_one (by positivity)]; linarith [(n.cast_nonneg : (0 : ℝ) ≤ n)]
    have hn0 : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
    obtain ⟨u₀, hu₀, hmin⟩ := isCompact_Icc.exists_isMinOn
      (nonempty_Icc.2 (by linarith : (0 : ℝ) ≤ 1 - 1 / ((n : ℝ) + 1))) hg.continuousOn
    have hlt := h u₀ ⟨hu₀.1, by linarith [hu₀.2]⟩
    obtain ⟨m, hm⟩ := exists_nat_one_div_lt (sub_pos.2 hlt)
    refine ⟨m, fun q hq0 hq1 => ?_⟩
    have : dist (η (pj u₀)) z ≤ dist (η (pj q)) z := hmin ⟨hq0, hq1⟩
    linarith
  · intro H u hu
    obtain ⟨n, hn⟩ := exists_nat_one_div_lt (sub_pos.2 hu.2)
    obtain ⟨m, hm⟩ := H n
    by_contra hle
    push Not at hle
    have hm0 : (0 : ℝ) < 1 / ((m : ℝ) + 1) := by positivity
    obtain ⟨δ, hδ, hc⟩ := Metric.continuous_iff.1 hg u _ hm0
    obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn (lt_min (lt_add_of_pos_right u hδ)
      (show u < 1 - 1 / ((n : ℝ) + 1) by linarith))
    have hq0 : (0 : ℝ) ≤ q := hu.1.trans hq1.le
    have h1 := hm q hq0 (hq2.trans_le (min_le_right _ _)).le
    have h2 := hc q (by
      rw [Real.dist_eq, abs_of_pos (sub_pos.2 hq1)]
      linarith [hq2.trans_le (min_le_left _ _)])
    rw [Real.dist_eq] at h2
    have := (abs_lt.1 h2).2
    linarith

/-- `sup_m D(𝕫, x; ℂ ∖ B̄_{r−1/(m+1)}(z))` through the Borel `chainInf` -/
def gmAvInf (d : ContMetric) (𝕫 x z : ℂ) (r : ℝ) : ℝ≥0∞ :=
  ⨆ m : ℕ, d.chainInf (closedBall z (r - 1 / ((m : ℝ) + 1)))ᶜ 𝕫 x

/-- **the minimality clause of `IsAvoidGeod` in Borel form** -/
theorem gmE_min_iff {d : ContMetric} (hd : d ∈ lenSet) (𝕫 x z : ℂ) (r : ℝ) (ℓ : ℝ≥0∞) :
    (∀ (Q' : ℝ → ℂ) (a b : ℝ), a ≤ b → ContinuousOn Q' (Icc a b) → Q' a = 𝕫 → Q' b = x →
      MapsTo Q' (Icc a b) (ball z r)ᶜ → ℓ ≤ d.len Q' a b) ↔ ℓ ≤ gmAvInf d 𝕫 x z r := by
  have hlen := isLength_of_mem_lenSet hd
  have he : ∀ m : ℕ, d.chainInf (closedBall z (r - 1 / ((m : ℝ) + 1)))ᶜ 𝕫 x =
      d.internal (closedBall z (r - 1 / ((m : ℝ) + 1)))ᶜ 𝕫 x := fun m =>
    (ContMetric.internal_eq_chainInf d hlen isClosed_closedBall.isOpen_compl 𝕫 x).symm
  constructor
  · intro H
    by_contra hlt
    push Not at hlt
    have hLt : gmAvInf d 𝕫 x z r ≠ ∞ := (hlt.trans_le le_top).ne
    obtain ⟨η, h0, h1, hr, hle⟩ := gmE_exists_avoid_path hd hLt fun m => by
      rw [← he]
      exact le_iSup (fun m : ℕ => d.chainInf (closedBall z (r - 1 / ((m : ℝ) + 1)))ᶜ 𝕫 x) m
    have := H (fun t => η (pj t)) 0 1 zero_le_one (pjPath_continuousOn η)
      (by rw [pjPath_zero, h0]) (by rw [pjPath_one, h1]) fun t _ => by
        simp only [mem_compl_iff, mem_ball, not_lt]; exact hr _
    exact absurd (this.trans hle) (not_le.2 hlt)
  · intro H Q' a b hab hc ha hb hmap
    refine H.trans (iSup_le fun m => ?_)
    rw [he]
    have hmap' : MapsTo (d.pt ∘ Q') (Icc a b)
        (d.pt '' (closedBall z (r - 1 / ((m : ℝ) + 1)))ᶜ) := fun t ht => by
      refine ⟨Q' t, ?_, rfl⟩
      have h1 := hmap ht
      have h2 : (0 : ℝ) < 1 / ((m : ℝ) + 1) := by positivity
      simp only [mem_compl_iff, mem_ball, not_lt, mem_closedBall, not_le] at h1 ⊢
      linarith
    have := internalEDist_le_curveLength hab (d.continuous_pt.comp_continuousOn hc) hmap'
    simp only [Function.comp_apply, ha, hb] at this
    exact this

/-- the Borel condition, case `𝕫 ∉ B̄_r(z)` -/
def gmAvF (d : ContMetric) (𝕫 z : ℂ) (r : ℝ) (y : ℂ) (w : ℂ × C(unitInterval, ℂ) × unitInterval) :
    Prop :=
  w.2.1 0 = 𝕫 ∧ w.2.1 1 = w.1 ∧ dist w.1 z = r ∧
  (∀ n : ℕ, ∃ m : ℕ, ∀ q : ℚ, 0 ≤ (q : ℝ) → (q : ℝ) ≤ 1 - 1 / ((n : ℝ) + 1) →
      r + 1 / ((m : ℝ) + 1) ≤ dist (w.2.1 (pj q)) z) ∧
  d.len (fun t => w.2.1 (pj t)) 0 1 ≤ gmAvInf d 𝕫 w.1 z r ∧ w.2.1 w.2.2 = y

theorem gmE_onAvoid_iff {d : ContMetric} (hd : d ∈ lenSet) {𝕫 z : ℂ} {r : ℝ}
    (h𝕫 : 𝕫 ∉ closedBall z r) (y : ℂ) :
    gmOnAvoid d 𝕫 z r y ↔ ∃ w, gmAvF d 𝕫 z r y w := by
  constructor
  · rintro ⟨x, Q, T, ⟨hT, hc, h0, hx, hxs, hav, hmin⟩, u, hu, rfl⟩
    have hTpos : 0 < T := by
      rcases hT.lt_or_eq with h | h
      · exact h
      · subst h
        have e : 𝕫 = x := h0.symm.trans hx
        exact absurd (e ▸ sphere_subset_closedBall hxs) h𝕫
    obtain ⟨η, hη, hlen⟩ := gmE_reparam hT hc
    refine ⟨(x, η, ⟨u / T, div_nonneg hu.1 hT, (div_le_one hTpos).2 hu.2⟩), ?_, ?_, hxs,
      ?_, ?_, ?_⟩
    · rw [hη]; simp [h0]
    · rw [hη]; simp [hx]
    · refine (gmE_avoidOpen_iff η z r).1 fun v hv => ?_
      rw [hη, pj_coe_of_mem ⟨hv.1, hv.2.le⟩]
      have := hav (0 + v * (T - 0)) ⟨by nlinarith [hv.1], by nlinarith [hv.2]⟩
      simpa [mem_closedBall, not_le] using this
    · show d.len (fun t => η (pj t)) 0 1 ≤ gmAvInf d 𝕫 x z r
      rw [hlen]
      exact (gmE_min_iff hd 𝕫 x z r _).1 hmin
    · show η _ = Q u
      rw [hη]
      congr 1
      simp only [zero_add, sub_zero]
      field_simp
  · rintro ⟨⟨x, η, v⟩, h0, h1, hxs, hav, hmin, rfl⟩
    refine ⟨x, fun t => η (pj t), 1, ⟨zero_le_one, pjPath_continuousOn η,
      by show η (pj 0) = 𝕫; rw [pjPath_zero]; exact h0,
      by show η (pj 1) = x; rw [pjPath_one]; exact h1, mem_sphere.2 hxs,
      fun u hu => ?_, fun Q' a b hab hc ha hb hmap =>
        (gmE_min_iff hd 𝕫 x z r _).2 hmin Q' a b hab hc ha hb hmap⟩, v, v.2, ?_⟩
    · have := (gmE_avoidOpen_iff η z r).2 hav u hu
      simpa [mem_closedBall, not_le] using this
    · show η (pj v) = η v
      rw [show pj (v : ℝ) = v from Subtype.ext (pj_coe_of_mem v.2)]

instance gmE_sb_avW : StandardBorelSpace (ℂ × C(unitInterval, ℂ) × unitInterval) := by
  have h1 : StandardBorelSpace C(unitInterval, ℂ) := inferInstance
  have h2 : StandardBorelSpace unitInterval := inferInstance
  have h3 := @StandardBorelSpace.prod _ _ _ _ h1 h2
  exact @StandardBorelSpace.prod _ _ _ _ inferInstance h3

/-- **`GMAvoidRelAn` holds** -/
theorem gm_avoidRelAn (𝕫 z : ℂ) (r : ℝ) : GMAvoidRelAn 𝕫 z r := by
  by_cases h𝕫 : 𝕫 ∈ closedBall z r
  · refine gmAn_congr (gmAn_of_measurableSet (A := {p : ContMetric × ℂ | p.2 = 𝕫 ∧
      𝕫 ∈ sphere z r}) ((measurableSet_eq_fun measurable_snd measurable_const).inter
        (MeasurableSet.const _))) ?_
    rintro ⟨d, y⟩ _
    simp only [mem_ofPred_eq]
    constructor
    · rintro ⟨hy, hs⟩
      rw [hy]
      refine ⟨𝕫, fun _ => 𝕫, 0, ⟨le_rfl, continuousOn_const, rfl, rfl, hs,
        fun u hu => absurd hu.2 (not_lt.2 hu.1), fun Q' a b _ _ _ _ _ => ?_⟩, 0,
        ⟨le_rfl, le_rfl⟩, rfl⟩
      rw [ContMetric.len, curveLength_self]
      exact bot_le
    · rintro ⟨x, Q, T, ⟨hT, hc, h0, hx, hxs, hav, -⟩, u, hu, rfl⟩
      rcases hT.lt_or_eq with hT' | hT'
      · have := hav 0 ⟨le_rfl, hT'⟩
        rw [h0] at this
        exact absurd h𝕫 this
      · subst hT'
        have hu0 : u = 0 := le_antisymm hu.2 hu.1
        subst hu0
        refine ⟨h0, ?_⟩
        rw [← h0, hx]
        exact hxs
  · refine ⟨ℂ × C(unitInterval, ℂ) × unitInterval, inferInstance, inferInstance,
      {q | gmAvF q.1.1 𝕫 z r q.1.2 q.2}, ?_, fun p hp => gmE_onAvoid_iff hp h𝕫 p.2⟩
    have hd : Measurable fun q : (ContMetric × ℂ) × ℂ × C(unitInterval, ℂ) × unitInterval =>
      q.1.1 := measurable_fst.comp measurable_fst
    have hy : Measurable fun q : (ContMetric × ℂ) × ℂ × C(unitInterval, ℂ) × unitInterval =>
      q.1.2 := measurable_snd.comp measurable_fst
    have hx : Measurable fun q : (ContMetric × ℂ) × ℂ × C(unitInterval, ℂ) × unitInterval =>
      q.2.1 := measurable_fst.comp measurable_snd
    have hη : Measurable fun q : (ContMetric × ℂ) × ℂ × C(unitInterval, ℂ) × unitInterval =>
      q.2.2.1 := measurable_fst.comp (measurable_snd.comp measurable_snd)
    have hv : Measurable fun q : (ContMetric × ℂ) × ℂ × C(unitInterval, ℂ) × unitInterval =>
      q.2.2.2 := measurable_snd.comp (measurable_snd.comp measurable_snd)
    have ev : ∀ a : unitInterval, Measurable fun q :
        (ContMetric × ℂ) × ℂ × C(unitInterval, ℂ) × unitInterval => q.2.2.1 a := fun a =>
      (continuous_eval_const a).measurable.comp hη
    have hinf : Measurable fun q : (ContMetric × ℂ) × ℂ × C(unitInterval, ℂ) × unitInterval =>
        gmAvInf q.1.1 𝕫 q.2.1 z r :=
      Measurable.iSup fun m => measurable_chainInf_comp hd measurable_const hx _
    exact measurableSet_setOfPred.2
      ((measurableSet_setOfPred.1 (measurableSet_eq_fun (ev 0) measurable_const)).and
      ((measurableSet_setOfPred.1 (measurableSet_eq_fun (ev 1) hx)).and
      ((measurableSet_setOfPred.1 (measurableSet_eq_fun (hx.dist measurable_const)
        measurable_const)).and
      ((Measurable.forall fun n => Measurable.exists fun m => Measurable.forall fun q =>
        measurable_const.imp (measurable_const.imp (measurableSet_setOfPred.1
          (measurableSet_le measurable_const ((ev _).dist measurable_const))))).and
      ((measurableSet_setOfPred.1 (measurableSet_le (measurable_lenPath_comp hd hη) hinf)).and
      (measurableSet_setOfPred.1 (measurableSet_eq_fun
        (continuous_eval.measurable.comp (hη.prodMk hv)) hy)))))))

end LQGMetric.GM
