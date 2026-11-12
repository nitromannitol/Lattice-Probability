/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.GM.S4.L46MeasD4 at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S4.L46MeasD2

/-!
# GM Lemma 4.6 (c): the arc of `𝓘_k` containing `P(t_k)` as a metric event (task P2-E3c)

Source: GM = Gwynne–Miller, arXiv:1905.00383v3, `literature/src/1905.00383/uniqueness-final.tex`,
proof of Lemma 4.6, l. 1709–1714: "on `Stab_{k,r}(z) ∩ {P ∩ B_r(z) ≠ ∅}`, the arc of `𝓘_k` which
contains `P(t_k)` is the same as the arc of `𝓘_k` which is hit by every
`D_h(·,·;ℂ∖cl B_r(z))`-geodesic from `𝕫` to `∂B_r(z)` [GM.S4.2] … so it is determined by
`h|_{ℂ∖B_r(z)}`".

* `gmHitU d 𝕫 s t z r V`: some arc `arcOf x`, `x ∈ Conf(s,t)`, hit by an avoiding geodesic, meets
  `V` (the "arc hit by the avoiding geodesics", existentially, see `L46MeasD1`);
* `gm_arcHit_iff_hitU`: GM's pathwise identification (via `gm_L4_6_arc`);
* `gm_hitU_transfer`, `gm_uMeasurableSet_hitU`: locality and measurability on `lenSet`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Filter Topology Set Metric
open scoped ENNReal
open LQGMetric.Blueprint

namespace LQGMetric.GM
open LocalEvent

/-- an arc of `𝓘 = {arcOf x : x ∈ Conf(s,t)}` hit by an avoiding geodesic meets `V` -/
def gmHitU (d : ContMetric) (𝕫 : ℂ) (s t : ℝ) (z : ℂ) (r : ℝ) (V : Set ℂ) : Prop :=
  ∃ x ∈ confPts d 𝕫 s t, gmHitArc d 𝕫 t z r x ∧ (arcOf d 𝕫 t x ∩ V).Nonempty

/-- **GM l. 1709–1712**: on `Stab ∩ {P ∩ B_r(z) ≠ ∅}`, the arc `arcOf(P(s))` of `𝓘` (the one
containing `P(t)`) is the arc hit by the avoiding geodesics -/
theorem gm_arcHit_iff_hitU {D : ContMetric} {𝕫 w z : ℂ} {r : ℝ} {P : ℝ → ℂ} {L : ℝ}
    (hU : UniqueGeod D 𝕫 w) (hP : IsGeodesicL D P L 𝕫 w) {s t : ℝ}
    (hs : 0 < s) (hst : s < t) (hw : w ∉ filledBall D 𝕫 t)
    (hleft : ∀ y ∈ frontier (filledBall D 𝕫 t), ∃ Q, IsLeftmostGeod D 𝕫 t y Q)
    (hdisj : (confPts D 𝕫 s t).PairwiseDisjoint (arcOf D 𝕫 t))
    (hball : Disjoint (closedBall z r) (filledBall D 𝕫 t))
    (hent : ∃ u ∈ Icc 0 L, P u ∈ ball z r) (hstab : stabCond D 𝕫 s t z r) (V : Set ℂ) :
    (arcOf D 𝕫 t (P s) ∩ V).Nonempty ↔ gmHitU D 𝕫 s t z r V := by
  obtain ⟨x₀, hx₀, hall⟩ := hstab
  obtain ⟨harc, e⟩ := gm_L4_6_arc hU hP hs hst hw hleft hdisj hball hent hx₀ hall
  subst e
  have ht : 0 < t := hs.trans hst
  have hz : 𝕫 ∈ filledBall D 𝕫 t := by
    refine Or.inl (subset_closure ?_)
    show D.1 (𝕫, 𝕫) < t
    rw [D.2.self_eq_zero]
    exact ht
  have h𝕫 : 𝕫 ∉ closedBall z r := fun h' => hball.ne_of_mem h' hz rfl
  obtain ⟨T, hT, hav⟩ := gm_S4_2 hP h𝕫 hent
  have htT : t ≤ T := by
    by_contra hle
    replace hle := (not_le.mp hle).le
    have hPT : P T ∈ filledBall D 𝕫 t := by
      rcases eq_or_lt_of_le hT.1 with h0 | h0
      · rw [← h0, hP.2.1]; exact hz
      · exact Or.inl (gm_closure_ballM_mono D 𝕫 hle (gm_geod_mem_closure_ballM hP h0 hT.2))
    exact hball.ne_of_mem (sphere_subset_closedBall hav.2.2.2.2.1) hPT rfl
  constructor
  · intro hV
    exact ⟨P s, hx₀, ⟨P t, harc, P T, P, T, hav, t, ⟨ht.le, htT⟩, rfl⟩, hV⟩
  · rintro ⟨x, hx, ⟨y, hy, x', Q, T', hQ, hyQ⟩, hV⟩
    have hy₀ := hall x' Q T' hQ ⟨hyQ, hy.1⟩
    by_cases hxe : x = P s
    · rw [← hxe]; exact hV
    · exact absurd rfl ((hdisj hx hx₀ hxe).ne_of_mem hy hy₀)

theorem gm_hitU_transfer {d₁ d₂ : ContMetric} {U : Set ℂ} {𝕫 : ℂ} {T : ℝ}
    (H : GMAgree d₁ d₂ U 𝕫 T) {z : ℂ} {r : ℝ} (hUr : (ball z r)ᶜ ⊆ U) {s t : ℝ} (hs : s ≤ T)
    (ht : t ≤ T) {V : Set ℂ} (h : gmHitU d₁ 𝕫 s t z r V) : gmHitU d₂ 𝕫 s t z r V := by
  obtain ⟨x, hx, hh, y, hy, hyV⟩ := h
  exact ⟨x, gm_hitSet_transfer H hs ht hx, gm_hitArc_transfer H hUr ht hh,
    y, gm_arcOf_transfer H ht hy, hyV⟩

/-- the metric event `{(z,r) ∈ 𝒵_k} ∩ HitU(V)` -/
def gmHitUSet (𝕫 : ℂ) (R c₁ c lam1 lam4 ε ν 𝕣 : ℝ) (Rads : Set ℝ) (z : ℂ) (r : ℝ)
    (V : Set ℂ) : Set ContMetric :=
  {d | candEvD d 𝕫 R c lam1 lam4 ε ν 𝕣 Rads z r ∧
    gmHitU d 𝕫 (tauD d 𝕫 R * c₁) (tauD d 𝕫 R * c) z r V}

/-- locality of `gmHitUSet` -/
theorem gm_hitUSet_of_internal_eq {d₁ d₂ : ContMetric} (h₁ : d₁.IsLength) (h₂ : d₂.IsLength)
    {𝕫 : ℂ} {R c₁ c lam1 lam4 ε ν 𝕣 : ℝ} {Rads : Set ℝ} {z : ℂ} {r ρ : ℝ} {V : Set ℂ}
    (hc : 1 < c) (hc₁ : c₁ ≤ c) (ha : 0 < lam4 * ε * 𝕣) (hρ : ρ ≤ lam4 * ε * 𝕣) (hρr : ρ ≤ r)
    {U : Set ℂ} (hU : IsOpen U) (hUρ : (Metric.ball z ρ)ᶜ ⊆ U)
    (heq : ∀ x ∈ U, ∀ y ∈ U, d₁.internal U x y = d₂.internal U x y)
    (H : d₁ ∈ gmHitUSet 𝕫 R c₁ c lam1 lam4 ε ν 𝕣 Rads z r V) :
    d₂ ∈ gmHitUSet 𝕫 R c₁ c lam1 lam4 ε ν 𝕣 Rads z r V := by
  obtain ⟨hA, hτ⟩ := gm_agree_of_candEvD h₁ h₂ hc ha hρ hU hUρ heq H.1
  refine ⟨gm_candEvD_of_internal_eq h₁ h₂ hc ha hρ hU hUρ heq H.1, ?_⟩
  rw [hτ]
  have hτ0 : 0 ≤ tauD d₁ 𝕫 R := by
    by_contra hneg
    have := hA.pos
    nlinarith [not_le.1 hneg]
  have hUr : (ball z r)ᶜ ⊆ U :=
    (compl_subset_compl.2 (ball_subset_ball hρr)).trans hUρ
  exact gm_hitU_transfer hA hUr (mul_le_mul_of_nonneg_left hc₁ hτ0) le_rfl H.2

/-- **`gmHitUSet` is universally measurable on `lenSet`** (`V` Borel) -/
theorem gm_uMeasurableSet_hitUSet {𝕫 z : ℂ} {r : ℝ} (hA : GMArcRelAn 𝕫)
    (hV : GMAvoidRelAn 𝕫 z r) (R c₁ c lam1 lam4 ε ν 𝕣 : ℝ) (Rads : Set ℝ) {V : Set ℂ}
    (hVm : MeasurableSet V) :
    UMeasurableSet (lenSet ∩ gmHitUSet 𝕫 R c₁ c lam1 lam4 ε ν 𝕣 Rads z r V) := by
  obtain ⟨β₁, m₁, sb₁, SA, hSA, hA⟩ := hA
  obtain ⟨β₂, m₂, sb₂, SV, hSV, hV⟩ := hV
  let g : ContMetric → ContMetric × ℝ × ℝ := fun d => (d, gmTauB 𝕫 R d * c₁, gmTauB 𝕫 R d * c)
  have hg : Measurable g := measurable_id.prodMk
    (((gm_measurable_tauB 𝕫 R).mul_const c₁).prodMk ((gm_measurable_tauB 𝕫 R).mul_const c))
  let W := ℂ × (ℂ × ℂ) × (β₁ × β₁) × β₂
  let S : Set (ContMetric × W) := {q | q.1 ∈ lenSet ∧
    ((g q.1, (q.2.1, q.2.2.1.1)), q.2.2.2.1.1) ∈ SA ∧
    ((g q.1, (q.2.1, q.2.2.1.2)), q.2.2.2.1.2) ∈ SA ∧
    ((q.1, q.2.2.1.1), q.2.2.2.2) ∈ SV ∧ q.2.2.1.2 ∈ V}
  have hS : MeasurableSet S := by
    have m1 : Measurable fun q : ContMetric × W => q.1 := measurable_fst
    have mw : Measurable fun q : ContMetric × W => q.2 := measurable_snd
    have mx : Measurable fun q : ContMetric × W => q.2.1 := measurable_fst.comp mw
    have my : Measurable fun q : ContMetric × W => q.2.2.1 :=
      measurable_fst.comp (measurable_snd.comp mw)
    have ma : Measurable fun q : ContMetric × W => q.2.2.2.1 :=
      measurable_fst.comp (measurable_snd.comp (measurable_snd.comp mw))
    have mb : Measurable fun q : ContMetric × W => q.2.2.2.2 :=
      measurable_snd.comp (measurable_snd.comp (measurable_snd.comp mw))
    refine (measurableSet_lenSet.preimage m1).inter ((hSA.preimage ?_).inter
      ((hSA.preimage ?_).inter ((hSV.preimage ?_).inter
        (hVm.preimage (measurable_snd.comp my)))))
    · exact ((hg.comp m1).prodMk (mx.prodMk (measurable_fst.comp my))).prodMk
        (measurable_fst.comp ma)
    · exact ((hg.comp m1).prodMk (mx.prodMk (measurable_snd.comp my))).prodMk
        (measurable_snd.comp ma)
    · exact (m1.prodMk (measurable_fst.comp my)).prodMk mb
  have e : lenSet ∩ {d | gmHitU d 𝕫 (tauD d 𝕫 R * c₁) (tauD d 𝕫 R * c) z r V} =
      {d | ∃ w, (d, w) ∈ S} := by
    ext d
    simp only [mem_inter_iff, mem_ofPred_eq]
    constructor
    · rintro ⟨hd, x, hx, ⟨y₁, hy₁, hv₁⟩, y₂, hy₂, hy₂V⟩
      rw [gm_tauD_eq_tauB hd] at hx hy₁ hy₂
      obtain ⟨a₁, ha₁⟩ := (hA ((g d), (x, y₁)) hd).1 ⟨hx, hy₁⟩
      obtain ⟨a₂, ha₂⟩ := (hA ((g d), (x, y₂)) hd).1 ⟨hx, hy₂⟩
      obtain ⟨b, hb⟩ := (hV (d, y₁) hd).1 hv₁
      exact ⟨(x, (y₁, y₂), (a₁, a₂), b), hd, ha₁, ha₂, hb, hy₂V⟩
    · rintro ⟨⟨x, ⟨y₁, y₂⟩, ⟨a₁, a₂⟩, b⟩, hd, ha₁, ha₂, hb, hy₂V⟩
      obtain ⟨hx, hy₁⟩ := (hA ((g d), (x, y₁)) hd).2 ⟨a₁, ha₁⟩
      obtain ⟨-, hy₂⟩ := (hA ((g d), (x, y₂)) hd).2 ⟨a₂, ha₂⟩
      have hv₁ := (hV (d, y₁) hd).2 ⟨b, hb⟩
      refine ⟨hd, ?_⟩
      rw [gm_tauD_eq_tauB hd]
      exact ⟨x, hx, ⟨y₁, hy₁, hv₁⟩, y₂, hy₂, hy₂V⟩
  have e2 : lenSet ∩ gmHitUSet 𝕫 R c₁ c lam1 lam4 ε ν 𝕣 Rads z r V =
      (lenSet ∩ {d | candEvD d 𝕫 R c lam1 lam4 ε ν 𝕣 Rads z r}) ∩
        (lenSet ∩ {d | gmHitU d 𝕫 (tauD d 𝕫 R * c₁) (tauD d 𝕫 R * c) z r V}) := by
    ext d
    simp only [gmHitUSet, mem_inter_iff, mem_ofPred_eq]
    tauto
  rw [e2, e]
  exact (gm_uMeasurableSet_candEvD 𝕫 _ _ _ _ _ _ _ _ z r).inter (UMeasurableSet.setOf_exists hS)

end LQGMetric.GM
