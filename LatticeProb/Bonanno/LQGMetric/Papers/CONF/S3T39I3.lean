/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.CONF.S3T39I3 at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.CONF.L214FinalArc
import LatticeProb.Bonanno.LQGMetric.Papers.CONF.L214Count
import LatticeProb.Bonanno.LQGMetric.Complex.JordanMap

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# CONF Lemma 2.14, located form (decision D119 S6)

Gwynne–Miller, *Confluence of geodesics in LQG* (arXiv:1905.00381), Lemma 2.14,
`confluence-final.tex` C:832–894. `confL214` (L214Final) is true but its conclusion is trivially
satisfiable (`t39h_disconnectsIn_trivial`: a small circle around `0`). CONF's proof (C:862–870)
produces a set near the arc: `φ(closure W) ⊆ B_{R d_I}(φ(w_I))`, `d_I = dist(φ(w_I), ∂U)`
(`l214_arc_normalized`, L214FinalArc). Copy-and-adapt of L214FinalArc / L214Final keeping this:

* `t39i_arc_normalized_loc`, `t39i_arc_loc`: (2.13) with `X ⊆ closedBall (φ w_I) (R d_I)`;
* **`confL214Loc_of_jordanMap`**, **`confL214Loc`**: Lemma 2.14 (D36 form) with, in addition,
  `infDist x (ℂ ∖ U) ≤ C n^{-1/2}` for every `x ∈ X` (from `R ≥ 1`, `d_I < t = C n^{-1/2}/(2R)`).
  This is the form needed for the inversion of Lemma 2.15 (C:912–924): `X` stays near `∂U`,
  hence away from `0 = ι(∞)`.
-/

namespace LQGMetric
namespace CONF

open Set Metric Filter Complex MeasureTheory
open scoped Topology Real ComplexConjugate ENNReal

/-- **CONF (2.13) in normalized coordinates, located** (`X ⊆ closedBall (Φ w) (R d)`) (arc `circArc (π/2 − ℓ/2) ℓ` centred at `i`,
`w = (1 − ℓ) i`). -/
theorem t39i_arc_normalized_loc : ∃ R : ℝ, 1 ≤ R ∧ ∀ (Φ : ℂ → ℂ) (ℓ : ℝ),
    ContinuousOn Φ (closedBall 0 1) → InjOn Φ (closedBall 0 1) →
    DifferentiableOn ℂ Φ (ball 0 1) → Φ 0 = 0 → 0 < ℓ → ℓ ≤ 1 / 10 →
    ∃ X : Set ℂ, X ⊆ closedBall (Φ (((1 - ℓ : ℝ) : ℂ) * I)) (R *
        infDist (Φ (((1 - ℓ : ℝ) : ℂ) * I)) (Φ '' ball 0 1)ᶜ) ∧
      DisconnectsIn (Φ '' ball 0 1) X {0} (Φ '' circArc (π / 2 - ℓ / 2) ℓ) := by
  obtain ⟨R, hR1, hR⟩ := l214_reach
  refine ⟨R, hR1, ?_⟩
  intro Φ ℓ hc hinj hd h0 hℓ hℓ1
  have hcos := l214_cos_ge hℓ hℓ1
  have hMim : ℓ / 4 ≤ (l214CenterM ℓ).im := by rw [l214CenterM_im]; linarith
  have hPim : ℓ / 4 ≤ (l214CenterP ℓ).im := by
    rw [← l214_neg_conj_centerM, neg_im, conj_im, neg_neg]; exact hMim
  obtain ⟨m1, m2, m3, m4⟩ := l214_minorant hℓ hℓ1
  obtain ⟨p1, p2, p3, p4⟩ := l214_minorant_plus hℓ hℓ1
  obtain ⟨Wm, hWmo, hWmc, hWmH, hwm, hWmB, a, ha, ha1, hac⟩ :=
    hR Φ ℓ (l214CenterM ℓ) (l214Harm ℓ) hc hinj hd hℓ hℓ1 hMim m1 m2 m3 m4
  obtain ⟨Wp, hWpo, hWpc, hWpH, hwp, hWpB, b, hb, hb1, hbc⟩ :=
    hR Φ ℓ (l214CenterP ℓ) (fun z => l214Harm ℓ (-conj z)) hc hinj hd hℓ hℓ1 hPim p1 p2 p3 p4
  set w : ℂ := ((1 - ℓ : ℝ) : ℂ) * I
  set d : ℝ := infDist (Φ w) (Φ '' ball 0 1)ᶜ
  set W := Wm ∪ Wp with hW
  have hWH : W ⊆ upperHalfDisc := union_subset hWmH hWpH
  have hA : ∀ q' ∈ circArc (π / 2 - ℓ / 2) ℓ,
      ‖q'‖ = 1 ∧ 0 < q'.im ∧ (a * conj q').im < 0 ∧ 0 < (b * conj q').im := by
    intro q' hq'
    have hs := l214_signs hℓ hℓ1 hac hbc hq'
    obtain ⟨ψ, -, rfl⟩ := hq'
    exact ⟨norm_exp_ofReal_mul_I ψ, hs⟩
  have hsep := l214_pull hc hinj h0 (hWmo.union hWpo) (IsPreconnected.union w hwm hwp hWmc hWpc)
    (fun z hz => hWH hz) (closure_mono subset_union_left ha)
    (closure_mono subset_union_right hb) ha1 hb1 hA
  refine ⟨Φ '' closure W, ?_, hsep⟩
  -- `Φ(closure W) ⊆ closure Φ(W) ⊆ closedBall (Φ w) (R d)`
  have hWB : W ⊆ closedBall (0 : ℂ) 1 :=
    hWH.trans (upperHalfDisc_subset_ball.trans ball_subset_closedBall)
  have hΦW : Φ '' W ⊆ closedBall (Φ w) (R * d) :=
    (image_union _ _ _).symm ▸ union_subset (hWmB.trans ball_subset_closedBall)
      (hWpB.trans ball_subset_closedBall)
  rintro _ ⟨z, hz, rfl⟩
  have hzB : z ∈ closedBall (0 : ℂ) 1 := closure_minimal hWB isClosed_closedBall hz
  have := ((hc z hzB).mono hWB).mem_closure_image hz
  exact closure_minimal hΦW isClosed_closedBall this

/-- **CONF (2.13), located** (C:862–870; the set lies in `closedBall (Φ w_I) (R d_I)`): for `0 < ℓ ≤ 1/10`, the arc `Φ(circArc θ ℓ)` is disconnected
from `0` in `U = Φ(𝔻)` by a set of diameter `≤ 2R · dist(Φ(w_I), ∂U)`, `w_I = arcPt θ ℓ`. -/
theorem t39i_arc_loc : ∃ R : ℝ, 1 ≤ R ∧ ∀ (Φ : ℂ → ℂ) (θ ℓ : ℝ),
    ContinuousOn Φ (closedBall 0 1) → InjOn Φ (closedBall 0 1) →
    DifferentiableOn ℂ Φ (ball 0 1) → Φ 0 = 0 → 0 < ℓ → ℓ ≤ 1 / 10 →
    ∃ X : Set ℂ, X ⊆ closedBall (Φ (arcPt θ ℓ)) (R *
        infDist (Φ (arcPt θ ℓ)) (Φ '' ball 0 1)ᶜ) ∧
      DisconnectsIn (Φ '' ball 0 1) X {0} (Φ '' circArc θ ℓ) := by
  obtain ⟨R, hR1, hR⟩ := t39i_arc_normalized_loc
  refine ⟨R, hR1, ?_⟩
  intro Φ θ ℓ hc hinj hd h0 hℓ hℓ1
  set α : ℝ := θ + ℓ / 2 - π / 2
  set r : ℂ := exp ((α : ℂ) * I) with hrdef
  have hr : ‖r‖ = 1 := norm_exp_ofReal_mul_I α
  have hmaps : MapsTo (fun z => r * z) (closedBall (0 : ℂ) 1) (closedBall 0 1) := fun z hz => by
    rw [mem_closedBall_zero_iff, norm_mul, hr, one_mul]; exact mem_closedBall_zero_iff.1 hz
  have hr0 : r ≠ 0 := Complex.exp_ne_zero _
  set ψ : ℂ → ℂ := Φ ∘ fun z => r * z with hψ
  have hψc : ContinuousOn ψ (closedBall 0 1) := hc.comp (by fun_prop) hmaps
  have hψi : InjOn ψ (closedBall 0 1) := fun z hz z' hz' h =>
    mul_left_cancel₀ hr0 (hinj (hmaps hz) (hmaps hz') h)
  have hψd : DifferentiableOn ℂ ψ (ball 0 1) :=
    hd.comp (by fun_prop) (fun z hz => by rw [← l214_rot_ball hr]; exact mem_image_of_mem _ hz)
  have hψ0 : ψ 0 = 0 := by simp [hψ, h0]
  obtain ⟨X, hX, hsep⟩ := hR ψ ℓ hψc hψi hψd hψ0 hℓ hℓ1
  have hU : ψ '' ball 0 1 = Φ '' ball 0 1 := by rw [hψ, image_comp, l214_rot_ball hr]
  have hA : ψ '' circArc (π / 2 - ℓ / 2) ℓ = Φ '' circArc θ ℓ := by
    rw [hψ, image_comp, hrdef, l214_rot_circArc]; congr 2; ring
  have hw : ψ (((1 - ℓ : ℝ) : ℂ) * I) = Φ (arcPt θ ℓ) := by
    simp only [hψ, Function.comp_apply, arcPt, arcCenter]
    congr 1
    rw [hrdef, show ((1 - ℓ : ℝ) : ℂ) * exp (((θ + ℓ / 2 : ℝ) : ℂ) * I) =
      ((1 - ℓ : ℝ) : ℂ) * (exp ((α : ℂ) * I) * exp (((π / 2 : ℝ) : ℂ) * I)) by
        rw [← Complex.exp_add]; congr 2; simp only [α]; push_cast; ring]
    rw [show exp (((π / 2 : ℝ) : ℂ) * I) = I by
      rw [exp_mul_I]; push_cast; simp [Complex.cos_pi_div_two, Complex.sin_pi_div_two]]
    ring
  rw [hU, hA] at hsep
  rw [hw, hU] at hX
  exact ⟨X, hX, hsep⟩

open Classical in
/-- **CONF Lemma 2.14, located** (corrected form D36 + D119 S6) for a conformal map `Φ : 𝔻 → U` that extends
continuously and injectively to the closed disc. -/
theorem confL214Loc_of_jordanMap : ∃ A N₀ : ℝ, 0 < A ∧ 0 ≤ N₀ ∧
    ∀ {ι : Type*} (s : Finset ι) (U : Set ℂ) (Φ : ℂ → ℂ) (θ ℓ : ι → ℝ) (C : ℝ),
      DifferentiableOn ℂ Φ (ball 0 1) → ContinuousOn Φ (closedBall 0 1) →
      InjOn Φ (closedBall 0 1) → Φ 0 = 0 → Φ '' ball 0 1 = U →
      (∀ i ∈ s, 0 < ℓ i) → (s : Set ι).PairwiseDisjoint (fun i => circArcOpen (θ i) (ℓ i)) →
      0 < C →
      (1 - A / C ^ 2 * (volume U).toReal) * s.card - N₀ ≤
        ((s.filter fun i => ∃ X : Set ℂ,
          Metric.ediam X ≤ ENNReal.ofReal (C * (s.card : ℝ) ^ (-(1 / 2 : ℝ))) ∧
          (∀ x ∈ X, infDist x Uᶜ ≤ C * (s.card : ℝ) ^ (-(1 / 2 : ℝ))) ∧
          DisconnectsIn U X {0} (Φ '' circArc (θ i) (ℓ i))).card : ℝ) := by
  obtain ⟨R, hR1, hR⟩ := t39i_arc_loc
  have hA0 := confL214CountConst_pos
  refine ⟨4 * R ^ 2 * confL214CountConst, (100 / (1 / 10 : ℝ)) ^ 2, by positivity,
    by positivity, ?_⟩
  intro ι s U Φ θ ℓ C hd hc hinj h0 hU hℓ hdisj hC
  subst hU
  have hpi := Real.pi_gt_three
  set A₀ := confL214CountConst
  set N₀ : ℝ := (100 / (1 / 10 : ℝ)) ^ 2 with hN₀
  set P : ι → Prop := fun i => ∃ X : Set ℂ,
    Metric.ediam X ≤ ENNReal.ofReal (C * (s.card : ℝ) ^ (-(1 / 2 : ℝ))) ∧
    (∀ x ∈ X, infDist x (Φ '' ball 0 1)ᶜ ≤ C * (s.card : ℝ) ^ (-(1 / 2 : ℝ))) ∧
    DisconnectsIn (Φ '' ball 0 1) X {0} (Φ '' circArc (θ i) (ℓ i)) with hP
  set m : ℝ := (s.card : ℝ) with hm
  -- volume is finite
  have hfin : volume (Φ '' ball (0 : ℂ) 1) < ∞ :=
    (measure_mono (image_mono ball_subset_closedBall)).trans_lt
      ((isCompact_closedBall 0 1).image_of_continuousOn hc).measure_lt_top
  set V : ℝ := (volume (Φ '' ball (0 : ℂ) 1)).toReal with hV
  have hV0 : 0 ≤ V := ENNReal.toReal_nonneg
  rcases Nat.eq_zero_or_pos s.card with hn | hn
  · have : m = 0 := by rw [hm, hn]; simp
    rw [this, mul_zero, zero_sub]
    refine le_trans ?_ (Nat.cast_nonneg _)
    rw [neg_nonpos]; positivity
  have hm0 : 0 < m := by rw [hm]; exact_mod_cast hn
  obtain ⟨q, hq⟩ : ∃ q : ℝ, q = m ^ (-(1 / 2 : ℝ)) := ⟨_, rfl⟩
  have hq2 : q ^ 2 * m = 1 := by
    rw [hq, Real.rpow_neg hm0.le, ← Real.sqrt_eq_rpow, inv_pow, Real.sq_sqrt hm0.le,
      inv_mul_cancel₀ hm0.ne']
  have hq0 : 0 < q := hq ▸ Real.rpow_pos_of_pos hm0 _
  set t : ℝ := C * q / (2 * R) with ht
  have hR0 : 0 < R := by linarith
  have ht0 : 0 < t := by positivity
  -- the bad arcs are long or have `d_I ≥ t`
  set bad1 := s.filter fun i => 1 / 10 < ℓ i
  set short := s.filter fun i => ℓ i ≤ 1 / 10
  set bad2 := short.filter fun i =>
    t ≤ infDist (Φ (arcPt (θ i) (ℓ i))) (Φ '' ball 0 1)ᶜ
  have hsub : (s.filter fun i => ¬ P i) ⊆ bad1 ∪ bad2 := by
    intro i hi
    obtain ⟨his, hPi⟩ := Finset.mem_filter.1 hi
    rw [Finset.mem_union]
    by_cases hl : 1 / 10 < ℓ i
    · exact Or.inl (Finset.mem_filter.2 ⟨his, hl⟩)
    · push Not at hl
      refine Or.inr (Finset.mem_filter.2 ⟨Finset.mem_filter.2 ⟨his, hl⟩, ?_⟩)
      by_contra hlt
      push Not at hlt
      obtain ⟨X, hX, hsep⟩ := hR Φ (θ i) (ℓ i) hc hinj hd h0 (hℓ i his) hl
      set d := infDist (Φ (arcPt (θ i) (ℓ i))) (Φ '' ball 0 1)ᶜ with hd'
      have hd0 : 0 ≤ d := infDist_nonneg
      have h2 : 2 * (R * t) = C * q := by rw [ht]; field_simp
      have hRd : 2 * (R * d) ≤ C * q := by nlinarith
      refine hPi ⟨X, (l214_ediam_le_of_subset_closedBall hX).trans
        (ENNReal.ofReal_le_ofReal (by rw [← hq]; exact hRd)), fun x hx => ?_, hsep⟩
      have h3 := infDist_le_infDist_add_dist (x := x) (y := Φ (arcPt (θ i) (ℓ i)))
        (s := (Φ '' ball 0 1)ᶜ)
      have h4 := mem_closedBall.1 (hX hx)
      rw [← hq]
      nlinarith
  have hcard : ((s.filter fun i => ¬ P i).card : ℝ) ≤ bad1.card + bad2.card := by
    exact_mod_cast (Finset.card_le_card hsub).trans (Finset.card_union_le _ _)
  have hsubs : ∀ p : ι → Prop, ∀ [DecidablePred p],
      ((s.filter p : Finset ι) : Set ι) ⊆ (s : Set ι) :=
    fun p _ => Finset.coe_subset.2 (Finset.filter_subset _ _)
  have hb1 : (bad1.card : ℝ) ≤ N₀ :=
    confL214_long_arcs_of_le bad1 θ ℓ (by norm_num) (by linarith)
      (fun i hi => (Finset.mem_filter.1 hi).2.le) (hdisj.subset (hsubs _))
  have hcount := confL214_count short θ ℓ hd (hinj.mono ball_subset_closedBall)
    (fun i hi => ⟨hℓ i (Finset.filter_subset _ _ hi),
      (Finset.mem_filter.1 hi).2.trans (by linarith)⟩) (hdisj.subset (hsubs _)) ht0
  rw [← ENNReal.ofReal_toReal hfin.ne, ← hV, ← ENNReal.ofReal_natCast,
    ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul hA0.le,
    ENNReal.ofReal_le_ofReal_iff (by positivity)] at hcount
  -- `#bad2 ≤ 4 R² A₀ V m / C²`
  have hkey : (bad2.card : ℝ) * C ^ 2 ≤ A₀ * V * (4 * R ^ 2 * m) := by
    have e2 : t ^ 2 * (4 * R ^ 2 * m) = C ^ 2 := by
      calc t ^ 2 * (4 * R ^ 2 * m) = C ^ 2 * (q ^ 2 * m) := by rw [ht]; field_simp; ring
        _ = C ^ 2 := by rw [hq2, mul_one]
    have e : (bad2.card : ℝ) * C ^ 2 = (bad2.card : ℝ) * t ^ 2 * (4 * R ^ 2 * m) := by
      rw [mul_assoc, e2]
    rw [e]
    exact mul_le_mul_of_nonneg_right hcount (by positivity)
  have hb2 : (bad2.card : ℝ) ≤ 4 * R ^ 2 * A₀ / C ^ 2 * V * m := by
    have : 4 * R ^ 2 * A₀ / C ^ 2 * V * m = A₀ * V * (4 * R ^ 2 * m) / C ^ 2 := by ring
    rw [this, le_div_iff₀ (by positivity)]; exact hkey
  show (1 - 4 * R ^ 2 * A₀ / C ^ 2 * V) * m - N₀ ≤ ((s.filter P).card : ℝ)
  have hsplit : ((s.filter P).card + (s.filter fun i => ¬ P i).card : ℕ) = s.card :=
    Finset.card_filter_add_card_filter_not P
  have hsplit' : ((s.filter P).card : ℝ) + ((s.filter fun i => ¬ P i).card : ℝ) = m := by
    rw [hm]; exact_mod_cast hsplit
  have k1 : ((s.filter fun i => ¬ P i).card : ℝ) ≤ N₀ + 4 * R ^ 2 * A₀ / C ^ 2 * V * m := by
    exact le_trans hcard (add_le_add hb1 hb2)
  have k2 : ((s.filter P).card : ℝ) = m - ((s.filter fun i => ¬ P i).card : ℝ) := by
    linarith [hsplit']
  rw [k2]
  have k3 : (1 - 4 * R ^ 2 * A₀ / C ^ 2 * V) * m - N₀ =
      m - (N₀ + 4 * R ^ 2 * A₀ / C ^ 2 * V * m) := by ring
  rw [k3]
  exact sub_le_sub_left k1 m

end CONF
end LQGMetric
