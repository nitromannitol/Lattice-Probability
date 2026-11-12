/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.CONF.S3L214P1 at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.CONF.S3T39I3

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# CONF Lemma 2.14 for connected subsets of the circle (decision D120 §1.3, packet J1)

Gwynne–Miller, *Confluence of geodesics in LQG* (arXiv:1905.00381), Lemma 2.14,
`confluence-final.tex` C:832–894, in the located form `confL214Loc_of_jordanMap` (S3T39I3),
applied to arbitrary pairwise disjoint nonempty connected subsets `Jᵢ` of the unit circle instead
of arcs `circArc θᵢ ℓᵢ` (CONF allows open, half-open and closed arcs, C:1516; degenerate arcs as in
DEC-120 §1.3):

* `t39p_circle_preconnected`: a preconnected proper nonempty subset of `S¹` lies between an open
  arc and its closure (`circArcOpen θ ℓ ⊆ J ⊆ circArc θ ℓ`, `ℓ ≥ 0`); own elementary argument
  (via `arg`), standard.
* `t39p_point_good`: a one-point arc `{Φ b}` is disconnected from `0` in `U = Φ(𝔻)` by a set of
  arbitrarily small diameter near `∂U` (`t39i_arc_loc` with `ℓ → 0`, continuity of `Φ` at `b`).
* `t39p_L214_conn`: Lemma 2.14 (located) for the family `Φ(Jᵢ)`; L2.14 is applied to the
  positive-length arcs with `C' = C (n/n')^{-1/2}`, the one-point arcs are all good.
-/

namespace LQGMetric
namespace CONF

open Set Metric Filter Complex MeasureTheory
open scoped Topology Real ComplexConjugate ENNReal

/-- A preconnected nonempty subset of the unit circle missing a point of the circle lies between
an open arc and the closed arc (own elementary argument). -/
theorem t39p_circle_preconnected {J : Set ℂ} (hJS : J ⊆ sphere 0 1) (hJc : IsPreconnected J)
    (hJn : J.Nonempty) {p : ℂ} (hp : p ∈ sphere (0 : ℂ) 1) (hpJ : p ∉ J) :
    ∃ θ ℓ : ℝ, 0 ≤ ℓ ∧ circArcOpen θ ℓ ⊆ J ∧ J ⊆ circArc θ ℓ := by
  have hp1 : ‖p‖ = 1 := by simpa using hp
  set c : ℂ := -p with hc
  have hc1 : ‖c‖ = 1 := by rw [hc, norm_neg, hp1]
  have hcc : c * conj c = 1 := by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, hc1]; simp
  set v : ℂ → ℂ := fun w => w * conj c with hv
  set t : ℂ → ℝ := fun w => arg c + arg (v w) with ht
  have hslit : ∀ w ∈ J, v w ∈ slitPlane := by
    intro w hw
    have hw1 : ‖w‖ = 1 := by simpa using hJS hw
    have hv1 : ‖v w‖ = 1 := by simp [hv, hw1, hc1]
    rw [mem_slitPlane_iff]
    by_contra hcon
    push Not at hcon
    obtain ⟨hre, him⟩ := hcon
    have hsq : (v w).re * (v w).re + (v w).im * (v w).im = 1 := by
      rw [← Complex.normSq_apply, ← Complex.sq_norm, hv1]; norm_num
    rw [him] at hsq
    have hre1 : (v w).re = -1 := by nlinarith
    have hvw : v w = -1 := Complex.ext (by simp [hre1]) (by simp [him])
    apply hpJ
    have : w = v w * c := by
      simp only [hv]; rw [mul_assoc, mul_comm (conj c), hcc, mul_one]
    rw [hvw, hc] at this
    have hwp : w = p := by rw [this]; ring
    exact hwp ▸ hw
  have htc : ContinuousOn t J := fun w hw =>
    (continuousAt_const.add ((continuousAt_arg (hslit w hw)).comp
      (by fun_prop : ContinuousAt v w))).continuousWithinAt
  set T : Set ℝ := t '' J with hT
  have hTc : IsPreconnected T := hJc.image t htc
  have hexp : ∀ w ∈ J, exp ((t w : ℂ) * I) = w := by
    intro w hw
    have hw1 : ‖w‖ = 1 := by simpa using hJS hw
    have hv1 : ‖v w‖ = 1 := by simp [hv, hw1, hc1]
    have e1 : exp ((arg c : ℂ) * I) = c := by
      have := norm_mul_exp_arg_mul_I c; rwa [hc1, ofReal_one, one_mul] at this
    have e2 : exp ((arg (v w) : ℂ) * I) = v w := by
      have := norm_mul_exp_arg_mul_I (v w); rwa [hv1, ofReal_one, one_mul] at this
    simp only [ht]
    rw [ofReal_add, add_mul, Complex.exp_add, e1, e2]
    show c * (w * conj c) = w
    rw [mul_comm w, ← mul_assoc, hcc, one_mul]
  have hJT : J = (fun s : ℝ => exp (s * I)) '' T := by
    ext w; constructor
    · intro hw; exact ⟨t w, mem_image_of_mem t hw, hexp w hw⟩
    · rintro ⟨_, ⟨w, hw, rfl⟩, rfl⟩; show exp ((t w : ℂ) * I) ∈ J; rw [hexp w hw]; exact hw
  have hbdd : BddBelow T ∧ BddAbove T := by
    refine ⟨⟨arg c - π, ?_⟩, ⟨arg c + π, ?_⟩⟩ <;> rintro _ ⟨w, -, rfl⟩ <;> simp only [ht]
    · linarith [neg_pi_lt_arg (v w)]
    · linarith [arg_le_pi (v w)]
  have hTn : T.Nonempty := hJn.image t
  refine ⟨sInf T, sSup T - sInf T, sub_nonneg.2 (csInf_le_csSup hTn hbdd.1 hbdd.2), ?_, ?_⟩
  · rw [hJT, circArcOpen, add_sub_cancel]
    refine image_mono fun x hx => ?_
    obtain ⟨a, haT, hax⟩ := exists_lt_of_csInf_lt hTn hx.1
    obtain ⟨b, hbT, hxb⟩ := exists_lt_of_lt_csSup hTn hx.2
    exact hTc.Icc_subset haT hbT ⟨hax.le, hxb.le⟩
  · rw [hJT, circArc, add_sub_cancel]
    exact image_mono fun x hx => ⟨csInf_le hbdd.1 hx, le_csSup hbdd.2 hx⟩

theorem t39p_disconnectsIn_mono {U X E F F' : Set ℂ} (h : DisconnectsIn U X E F) (hF : F' ⊆ F) :
    DisconnectsIn U X E F' := fun x y γ hx hy hγ =>
  h x y γ hx (hF hy) (hγ.trans (union_subset_union_right _ hF))

theorem t39p_exp_arg {b : ℂ} (hb : ‖b‖ = 1) : exp ((arg b : ℂ) * I) = b := by
  have := norm_mul_exp_arg_mul_I b; rwa [hb, ofReal_one, one_mul] at this

/-- **One-point arcs** (DEC-120 §1.3): `{Φ b}`, `b ∈ S¹`, is disconnected from `0` in `Φ(𝔻)` by a
set of diameter `≤ δ` all of whose points are within `δ` of `ℂ ∖ Φ(𝔻)`, for every `δ > 0`
(`t39i_arc_loc` with a short arc around `b`; `d_I → 0` by continuity of `Φ` at `b`). -/
theorem t39p_point_good (Φ : ℂ → ℂ) {b : ℂ} {δ : ℝ} (hc : ContinuousOn Φ (closedBall 0 1))
    (hinj : InjOn Φ (closedBall 0 1)) (hd : DifferentiableOn ℂ Φ (ball 0 1)) (h0 : Φ 0 = 0)
    (hb : ‖b‖ = 1) (hδ : 0 < δ) :
    ∃ X : Set ℂ, Metric.ediam X ≤ ENNReal.ofReal δ ∧
      (∀ x ∈ X, infDist x (Φ '' ball 0 1)ᶜ ≤ δ) ∧ DisconnectsIn (Φ '' ball 0 1) X {0} {Φ b} := by
  obtain ⟨R, hR1, hR⟩ := t39i_arc_loc
  have hR0 : 0 < R := by linarith
  have hbB : b ∈ closedBall (0 : ℂ) 1 := by simp [hb]
  obtain ⟨η, hη, hηΦ⟩ := Metric.continuousWithinAt_iff.1 (hc b hbB) (δ / (2 * R)) (by positivity)
  set ℓ : ℝ := min (1 / 10) (η / 2) with hℓdef
  have hℓ0 : 0 < ℓ := lt_min (by norm_num) (by linarith)
  have hℓ1 : ℓ ≤ 1 / 10 := min_le_left _ _
  have hℓη : ℓ < η := lt_of_le_of_lt (min_le_right _ _) (by linarith)
  set θ : ℝ := arg b - ℓ / 2
  obtain ⟨X, hX, hsep⟩ := hR Φ θ ℓ hc hinj hd h0 hℓ0 hℓ1
  have hpt : arcPt θ ℓ = ((1 - ℓ : ℝ) : ℂ) * b := by
    simp only [arcPt, arcCenter]
    rw [show θ + ℓ / 2 = arg b by simp only [θ]; ring, t39p_exp_arg hb]
  have hbArc : b ∈ circArc θ ℓ := ⟨arg b, ⟨by simp only [θ]; linarith, by simp only [θ]; linarith⟩,
    t39p_exp_arg hb⟩
  have hptB : arcPt θ ℓ ∈ closedBall (0 : ℂ) 1 := by
    rw [hpt, mem_closedBall_zero_iff, norm_mul, hb, mul_one, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (by linarith)]
    linarith
  have hdist : dist (arcPt θ ℓ) b < η := by
    rw [hpt, dist_eq_norm, show ((1 - ℓ : ℝ) : ℂ) * b - b = -((ℓ : ℂ) * b) by push_cast; ring,
      norm_neg, norm_mul, hb, mul_one, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hℓ0]
    exact hℓη
  have hΦb : Φ b ∈ (Φ '' ball 0 1)ᶜ := by
    rintro ⟨v, hv, hvb⟩
    have := hinj (ball_subset_closedBall hv) hbB hvb
    rw [this, mem_ball_zero_iff, hb] at hv
    exact lt_irrefl _ hv
  set d := infDist (Φ (arcPt θ ℓ)) (Φ '' ball 0 1)ᶜ with hd'
  have hd0 : 0 ≤ d := infDist_nonneg
  have hdδ : d < δ / (2 * R) :=
    (infDist_le_dist_of_mem hΦb).trans_lt (hηΦ hptB hdist)
  have h2 : 2 * (R * d) ≤ δ := by
    have := (lt_div_iff₀ (by positivity)).1 hdδ; nlinarith
  refine ⟨X, (l214_ediam_le_of_subset_closedBall hX).trans (ENNReal.ofReal_le_ofReal h2),
    fun x hx => ?_, t39p_disconnectsIn_mono hsep (singleton_subset_iff.2 (mem_image_of_mem Φ hbArc))⟩
  have h3 := infDist_le_infDist_add_dist (x := x) (y := Φ (arcPt θ ℓ)) (s := (Φ '' ball 0 1)ᶜ)
  have h4 := mem_closedBall.1 (hX hx)
  nlinarith

open Classical in
/-- **CONF Lemma 2.14, located, for connected subsets of the circle** (C:832–894; DEC-120 §1.3):
`confL214Loc_of_jordanMap` for pairwise disjoint nonempty preconnected `Jᵢ ⊆ S¹`, none of them the
whole circle. -/
theorem t39p_L214_conn : ∃ A N₀ : ℝ, 0 < A ∧ 0 ≤ N₀ ∧
    ∀ {ι : Type*} (S : Finset ι) (Φ : ℂ → ℂ) (J : ι → Set ℂ) (C : ℝ),
      DifferentiableOn ℂ Φ (ball 0 1) → ContinuousOn Φ (closedBall 0 1) →
      InjOn Φ (closedBall 0 1) → Φ 0 = 0 →
      (∀ i ∈ S, J i ⊆ sphere 0 1) → (∀ i ∈ S, (J i).Nonempty) → (∀ i ∈ S, IsPreconnected (J i)) →
      (S : Set ι).PairwiseDisjoint J → (∀ i ∈ S, ∃ p ∈ sphere (0 : ℂ) 1, p ∉ J i) → 0 < C →
      (1 - A / C ^ 2 * (volume (Φ '' ball 0 1)).toReal) * S.card - N₀ ≤
        ((S.filter fun i => ∃ X : Set ℂ,
          Metric.ediam X ≤ ENNReal.ofReal (C * (S.card : ℝ) ^ (-(1 / 2 : ℝ))) ∧
          (∀ x ∈ X, infDist x (Φ '' ball 0 1)ᶜ ≤ C * (S.card : ℝ) ^ (-(1 / 2 : ℝ))) ∧
          DisconnectsIn (Φ '' ball 0 1) X {0} (Φ '' J i)).card : ℝ) := by
  obtain ⟨A, N₀, hA, hN₀, hmain⟩ := confL214Loc_of_jordanMap
  refine ⟨A, N₀, hA, hN₀, ?_⟩
  intro ι S Φ J C hd hc hinj h0 hJS hJn hJc hJd hfree hC
  have hθℓ : ∀ i, ∃ θ ℓ : ℝ, i ∈ S → 0 ≤ ℓ ∧ circArcOpen θ ℓ ⊆ J i ∧ J i ⊆ circArc θ ℓ := by
    intro i
    by_cases hi : i ∈ S
    · obtain ⟨p, hp, hpJ⟩ := hfree i hi
      obtain ⟨θ, ℓ, h⟩ := t39p_circle_preconnected (hJS i hi) (hJc i hi) (hJn i hi) hp hpJ
      exact ⟨θ, ℓ, fun _ => h⟩
    · exact ⟨0, 0, fun h => absurd h hi⟩
  choose θ ℓ hθℓ using hθℓ
  set U := Φ '' ball (0 : ℂ) 1 with hU
  set V : ℝ := (volume U).toReal with hV
  have hV0 : 0 ≤ V := ENNReal.toReal_nonneg
  set n : ℝ := (S.card : ℝ) with hn
  set P : ι → Prop := fun i => ∃ X : Set ℂ,
    Metric.ediam X ≤ ENNReal.ofReal (C * n ^ (-(1 / 2 : ℝ))) ∧
    (∀ x ∈ X, infDist x Uᶜ ≤ C * n ^ (-(1 / 2 : ℝ))) ∧
    DisconnectsIn U X {0} (Φ '' J i) with hP
  show (1 - A / C ^ 2 * V) * n - N₀ ≤ ((S.filter P).card : ℝ)
  rcases Nat.eq_zero_or_pos S.card with h0n | hnpos
  · have : n = 0 := by rw [hn, h0n]; simp
    rw [this, mul_zero, zero_sub]
    exact le_trans (neg_nonpos.2 hN₀) (Nat.cast_nonneg _)
  have hn0 : 0 < n := by rw [hn]; exact_mod_cast hnpos
  set q : ℝ := n ^ (-(1 / 2 : ℝ)) with hq
  have hq0 : 0 < q := Real.rpow_pos_of_pos hn0 _
  have hq2 : q ^ 2 * n = 1 := by
    rw [hq, Real.rpow_neg hn0.le, ← Real.sqrt_eq_rpow, inv_pow, Real.sq_sqrt hn0.le,
      inv_mul_cancel₀ hn0.ne']
  -- the one-point arcs are good
  set S₀ := S.filter fun i => ¬ 0 < ℓ i with hS₀
  set S' := S.filter fun i => 0 < ℓ i with hS'
  have hgood₀ : ∀ i ∈ S₀, P i := by
    intro i hi
    obtain ⟨hiS, hℓi⟩ := Finset.mem_filter.1 hi
    obtain ⟨hℓ0, -, hsub⟩ := hθℓ i hiS
    have hℓe : ℓ i = 0 := le_antisymm (not_lt.1 hℓi) hℓ0
    obtain ⟨b, hb⟩ := hJn i hiS
    have hJb : J i ⊆ {b} := by
      intro w hw
      have hw' := hsub hw
      have hb' := hsub hb
      rw [circArc, hℓe, add_zero, Icc_self, image_singleton] at hw' hb'
      exact (mem_singleton_iff.1 hw').trans (mem_singleton_iff.1 hb').symm
    have hb1 : ‖b‖ = 1 := by simpa using hJS i hiS hb
    obtain ⟨X, h1, h2, h3⟩ := t39p_point_good Φ hc hinj hd h0 hb1 (mul_pos hC hq0)
    refine ⟨X, h1, h2, t39p_disconnectsIn_mono h3 ?_⟩
    rw [← image_singleton]; exact image_mono hJb
  have hsplit : ((S'.card : ℕ) : ℝ) + (S₀.card : ℝ) = n := by
    rw [hn]; exact_mod_cast Finset.card_filter_add_card_filter_not _
  have haN : (1 - A / C ^ 2 * V) * n = n - A / C ^ 2 * V * n := by ring
  have ha0 : 0 ≤ A / C ^ 2 * V * n := by positivity
  rcases Nat.eq_zero_or_pos S'.card with h0' | hpos'
  · have hS'e : S' = ∅ := Finset.card_eq_zero.1 h0'
    have hsub : S ⊆ S.filter P := fun i hi => Finset.mem_filter.2 ⟨hi, hgood₀ i
      (Finset.mem_filter.2 ⟨hi, fun hℓ => by
        have : i ∈ S' := Finset.mem_filter.2 ⟨hi, hℓ⟩
        rw [hS'e] at this; simp at this⟩)⟩
    have : n ≤ (S.filter P).card := by rw [hn]; exact_mod_cast Finset.card_le_card hsub
    linarith
  set n' : ℝ := (S'.card : ℝ) with hn'
  have hn'0 : 0 < n' := by rw [hn']; exact_mod_cast hpos'
  set q' : ℝ := n' ^ (-(1 / 2 : ℝ)) with hq'
  have hq'0 : 0 < q' := Real.rpow_pos_of_pos hn'0 _
  have hq'2 : q' ^ 2 * n' = 1 := by
    rw [hq', Real.rpow_neg hn'0.le, ← Real.sqrt_eq_rpow, inv_pow, Real.sq_sqrt hn'0.le,
      inv_mul_cancel₀ hn'0.ne']
  set C' : ℝ := C * q / q' with hC'
  have hC'0 : 0 < C' := by positivity
  have hC'q : C' * q' = C * q := by rw [hC']; field_simp
  have hdisj' : (S' : Set ι).PairwiseDisjoint fun i => circArcOpen (θ i) (ℓ i) := by
    intro i hi j hj hij
    have hi' := (Finset.mem_filter.1 (Finset.mem_coe.1 hi)).1
    have hj' := (Finset.mem_filter.1 (Finset.mem_coe.1 hj)).1
    exact (hJd hi' hj' hij).mono (hθℓ i hi').2.1 (hθℓ j hj').2.1
  have hm := hmain S' U Φ θ ℓ C' hd hc hinj h0 rfl (fun i hi => (Finset.mem_filter.1 hi).2)
    hdisj' hC'0
  rw [← hn', ← hq', hC'q, ← hV] at hm
  set P' : ι → Prop := fun i => ∃ X : Set ℂ, Metric.ediam X ≤ ENNReal.ofReal (C * q) ∧
    (∀ x ∈ X, infDist x Uᶜ ≤ C * q) ∧ DisconnectsIn U X {0} (Φ '' circArc (θ i) (ℓ i)) with hP'
  have hsub : S'.filter P' ∪ S₀ ⊆ S.filter P := by
    intro i hi
    rcases Finset.mem_union.1 hi with hi | hi
    · obtain ⟨hiS', X, h1, h2, h3⟩ := Finset.mem_filter.1 hi
      have hiS := (Finset.mem_filter.1 hiS').1
      exact Finset.mem_filter.2 ⟨hiS, X, h1, h2,
        t39p_disconnectsIn_mono h3 (image_mono (hθℓ i hiS).2.2)⟩
    · exact Finset.mem_filter.2 ⟨(Finset.mem_filter.1 hi).1, hgood₀ i hi⟩
  have hdj : Disjoint (S'.filter P') S₀ := by
    rw [Finset.disjoint_left]
    intro i hi hi0
    exact (Finset.mem_filter.1 hi0).2 (Finset.mem_filter.1 (Finset.mem_filter.1 hi).1).2
  have hcard : ((S'.filter P').card : ℝ) + (S₀.card : ℝ) ≤ (S.filter P).card := by
    have := Finset.card_le_card hsub
    rw [Finset.card_union_of_disjoint hdj] at this
    exact_mod_cast this
  have hnq : n = (q ^ 2)⁻¹ := eq_inv_of_mul_eq_one_right hq2
  have hnq' : n' = (q' ^ 2)⁻¹ := eq_inv_of_mul_eq_one_right hq'2
  have e : A / C' ^ 2 * V * n' = A / C ^ 2 * V * n := by
    rw [hnq, hnq', hC']; field_simp
  have e2 : (1 - A / C' ^ 2 * V) * n' = n' - A / C ^ 2 * V * n := by rw [← e]; ring
  linarith

end CONF
end LQGMetric
