/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DFGPS.L2_9ProofGeom at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DFGPS.L2_9
import LatticeProb.Bonanno.LQGMetric.Papers.DFGPS.L2_8ProofCont

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# DFGPS Lemma 2.9: geometry of finite unions of closed squares (T:914–925)

DFGPS (arXiv:1905.00380, `lqg-metric-estimates-final.tex`), proof of Lemma 2.9, T:914–925:
"we can choose a finite collection `𝒮` of closed squares such that `⋃_{S∈𝒮} S = W̄` … If `δ` is
sufficiently small (depending only on `𝒮`), then we can find squares `S, S' ∈ 𝒮` such that
`z ∈ S`, `w ∈ S'` and `S ∩ S' ≠ ∅`. Since `S` and `S'` are closed squares, geometric
considerations show that there is a `u ∈ S ∩ S'` such that `|z − u| ≤ δ` and `|w − u| ≤ δ`."

* `closure_dyadicDomain_eq`: `W̄ = ⋃_{S∈𝒮} S` for `W = int ⋃_{S∈𝒮} S`;
* `exists_mem_inter_closedSq_near`: the point `u` (coordinatewise clamp; own elementary
  argument for the paper's "geometric considerations");
* `exists_lfppDOn_union_le`: `D_φ(z, w; W̄) ≤ 2B|z − w|` for `|z − w| < δ` (the square bound
  `D(·,·;S) ≤ B|·−·|` on each square, as in the paper's restriction argument);
* `lfppDOn_union_ne_top`, `continuous_lfppDOn_union_toReal`: finiteness (`W̄` connected) and
  continuity of the internal metric on `W̄`.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set Metric
open scoped ENNReal

namespace LQGMetric.DFGPS

open Blueprint LFPP

theorem lfppDOn_anti_set {ξ : ℝ} {φ : ℂ → ℝ} {S T : Set ℂ} (hST : S ⊆ T) (x y : ℂ) :
    lfppDOn ξ φ T x y ≤ lfppDOn ξ φ S x y :=
  le_iInf fun P => iInf_le_of_le ⟨P.1, P.2.1, fun t ht => hST (P.2.2 t ht)⟩ le_rfl

theorem dfDyadicSq_eq_closedSq (k : ℤ) (j : ℤ × ℤ) :
    dfDyadicSq k j = closedSq ⟨(j.1 : ℝ) * 2 ^ k, (j.2 : ℝ) * 2 ^ k⟩ (2 ^ k) := by
  ext x
  simp only [dfDyadicSq, closedSq, mem_ofPred_eq, add_one_mul]

theorem center_mem_interior_closedSq (a : ℂ) {s : ℝ} (hs : 0 < s) :
    (⟨a.re + s / 2, a.im + s / 2⟩ : ℂ) ∈ interior (closedSq a s) := by
  rw [mem_interior_iff_mem_nhds]
  refine mem_of_superset (ball_mem_nhds _ (half_pos hs)) fun z hz => ?_
  rw [mem_ball, dist_eq_norm] at hz
  have h1 := Complex.abs_re_le_norm (z - ⟨a.re + s / 2, a.im + s / 2⟩)
  have h2 := Complex.abs_im_le_norm (z - ⟨a.re + s / 2, a.im + s / 2⟩)
  simp only [Complex.sub_re, Complex.sub_im] at h1 h2
  rw [abs_le] at h1 h2
  exact ⟨by linarith [h1.1], by linarith [h1.2], by linarith [h2.1], by linarith [h2.2]⟩

theorem closure_interior_closedSq (a : ℂ) {s : ℝ} (hs : 0 < s) :
    closure (interior (closedSq a s)) = closedSq a s := by
  rw [(convex_closedSq a s).closure_interior_eq_closure_of_nonempty_interior
    ⟨_, center_mem_interior_closedSq a hs⟩, (isCompact_closedSq a hs.le).isClosed.closure_eq]

/-- `int(⋃ S)` has closure `⋃ S` for a finite union of nondegenerate closed squares -/
theorem closure_interior_biUnion_closedSq (𝒮 : Finset (Set ℂ))
    (h𝒮 : ∀ S ∈ 𝒮, ∃ a s, 0 < s ∧ S = closedSq a s) :
    closure (interior (⋃ S ∈ 𝒮, S)) = ⋃ S ∈ 𝒮, S := by
  have hcl : IsClosed (⋃ S ∈ 𝒮, S) := isClosed_biUnion_finset fun S hS => by
    obtain ⟨a, s, hs, rfl⟩ := h𝒮 S hS
    exact (isCompact_closedSq a hs.le).isClosed
  refine subset_antisymm ((closure_mono interior_subset).trans hcl.closure_eq.subset) ?_
  refine iUnion₂_subset fun S hS => ?_
  obtain ⟨a, s, hs, rfl⟩ := h𝒮 S hS
  rw [← closure_interior_closedSq a hs]
  exact closure_mono (interior_mono (subset_biUnion_of_mem (u := fun S : Set ℂ => S) hS))

theorem closure_dyadicDomain_eq {𝒮 : Finset (Set ℂ)} (h𝒮 : ∀ S ∈ 𝒮, IsDyadicSquare S) :
    closure (interior (⋃ S ∈ 𝒮, S)) = ⋃ S ∈ 𝒮, S :=
  closure_interior_biUnion_closedSq 𝒮 fun S hS => by
    obtain ⟨k, j, rfl⟩ := h𝒮 S hS
    exact ⟨_, _, zpow_pos two_pos k, dfDyadicSq_eq_closedSq k j⟩

theorem abs_le_of_between {x u y : ℝ} (h : (x ≤ u ∧ u ≤ y) ∨ (y ≤ u ∧ u ≤ x)) :
    |u - x| ≤ |y - x| ∧ |y - u| ≤ |y - x| := by
  have := le_abs_self (y - x); have := neg_abs_le (y - x)
  rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;>
    exact ⟨abs_le.2 ⟨by linarith, by linarith⟩, abs_le.2 ⟨by linarith, by linarith⟩⟩

/-- the 1D clamp -/
theorem exists_clamp {a s b t x y : ℝ} (hx : a ≤ x ∧ x ≤ a + s) (hy : b ≤ y ∧ y ≤ b + t)
    (hne : max a b ≤ min (a + s) (b + t)) :
    ∃ u, (a ≤ u ∧ u ≤ a + s) ∧ (b ≤ u ∧ u ≤ b + t) ∧ |u - x| ≤ |y - x| ∧ |y - u| ≤ |y - x| := by
  have hm := max_le_iff.1 hne
  have h1 := le_min_iff.1 hm.1
  have h2 := le_min_iff.1 hm.2
  by_cases hL : x < b
  · exact ⟨b, ⟨by linarith, h2.1⟩, ⟨le_rfl, by linarith⟩, abs_le_of_between (Or.inl ⟨hL.le, hy.1⟩)⟩
  by_cases hH : b + t < x
  · exact ⟨b + t, ⟨by linarith, by linarith⟩, ⟨by linarith, le_rfl⟩,
      abs_le_of_between (Or.inr ⟨hy.2, hH.le⟩)⟩
  push_neg at hL hH
  exact ⟨x, hx, ⟨hL, hH⟩, by simp, le_rfl⟩

theorem norm_le_of_abs_re_im {z w : ℂ} (h1 : |z.re| ≤ |w.re|) (h2 : |z.im| ≤ |w.im|) :
    ‖z‖ ≤ ‖w‖ := by
  have e1 := sq_le_sq.2 h1
  have e2 := sq_le_sq.2 h2
  have hz := Complex.sq_norm z
  have hw := Complex.sq_norm w
  rw [Complex.normSq_apply] at hz hw
  by_contra hc
  push_neg at hc
  have := mul_self_lt_mul_self (norm_nonneg w) hc
  nlinarith

/-- **DFGPS T:921–922** ("geometric considerations"): for `z ∈ S`, `w ∈ S'` and closed squares
`S, S'` with `S ∩ S' ≠ ∅`, some `u ∈ S ∩ S'` has `|z − u|, |w − u| ≤ |z − w|`. -/
theorem exists_mem_inter_closedSq_near {a b : ℂ} {s t : ℝ} {x y : ℂ} (hx : x ∈ closedSq a s)
    (hy : y ∈ closedSq b t) (hne : (closedSq a s ∩ closedSq b t).Nonempty) :
    ∃ u ∈ closedSq a s ∩ closedSq b t, ‖u - x‖ ≤ ‖y - x‖ ∧ ‖y - u‖ ≤ ‖y - x‖ := by
  obtain ⟨v, ⟨v1, v2, v3, v4⟩, ⟨v5, v6, v7, v8⟩⟩ := hne
  obtain ⟨x1, x2, x3, x4⟩ := hx
  obtain ⟨y1, y2, y3, y4⟩ := hy
  obtain ⟨ur, hr1, hr2, hr3, hr4⟩ := exists_clamp (a := a.re) (s := s) (b := b.re) (t := t)
    ⟨x1, x2⟩ ⟨y1, y2⟩ (max_le (le_min (by linarith) (by linarith)) (le_min (by linarith)
      (by linarith)))
  obtain ⟨ui, hi1, hi2, hi3, hi4⟩ := exists_clamp (a := a.im) (s := s) (b := b.im) (t := t)
    ⟨x3, x4⟩ ⟨y3, y4⟩ (max_le (le_min (by linarith) (by linarith)) (le_min (by linarith)
      (by linarith)))
  refine ⟨⟨ur, ui⟩, ⟨⟨hr1.1, hr1.2, hi1.1, hi1.2⟩, ⟨hr2.1, hr2.2, hi2.1, hi2.2⟩⟩,
    norm_le_of_abs_re_im ?_ ?_, norm_le_of_abs_re_im ?_ ?_⟩ <;>
    simpa only [Complex.sub_re, Complex.sub_im]

/-- positive separation of disjoint compact sets -/
theorem exists_sep_of_isCompact {S T : Set ℂ} (hS : IsCompact S) (hT : IsCompact T) :
    ∃ δ > (0 : ℝ), S ∩ T = ∅ → ∀ x ∈ S, ∀ y ∈ T, δ ≤ dist x y := by
  by_cases hd : S ∩ T = ∅
  · rcases (S ×ˢ T).eq_empty_or_nonempty with he | hne
    · exact ⟨1, one_pos, fun _ x hx y hy => absurd (mk_mem_prod hx hy) (he ▸ notMem_empty _)⟩
    · obtain ⟨p, hp, hmin⟩ := (hS.prod hT).exists_isMinOn hne continuous_dist.continuousOn
      refine ⟨dist p.1 p.2, dist_pos.2 fun e => ?_, fun _ x hx y hy => hmin (mk_mem_prod hx hy)⟩
      exact (eq_empty_iff_forall_notMem.1 hd) p.1 ⟨hp.1, e ▸ hp.2⟩
  · exact ⟨1, one_pos, fun h => absurd h hd⟩

/-- **DFGPS T:914–925, deterministic core**: on a finite union `K` of closed squares,
`D_φ(z, w; K) ≤ 2B|z − w|` whenever `|z − w| < δ`. -/
theorem exists_lfppDOn_union_le {ξ : ℝ} {φ : ℂ → ℝ} (hφ : Continuous φ) (𝒮 : Finset (Set ℂ))
    (h𝒮 : ∀ S ∈ 𝒮, ∃ a s, 0 < s ∧ S = closedSq a s) :
    ∃ δ > (0 : ℝ), ∃ B : ℝ, 0 ≤ B ∧ ∀ x ∈ ⋃ S ∈ 𝒮, S, ∀ y ∈ ⋃ S ∈ 𝒮, S, ‖y - x‖ < δ →
      lfppDOn ξ φ (⋃ S ∈ 𝒮, S) x y ≤ ENNReal.ofReal (2 * B * ‖y - x‖) := by
  have hev : ∀ᶠ δ in 𝓝[>] (0 : ℝ), ∀ S ∈ 𝒮, ∀ T ∈ 𝒮, S ∩ T = ∅ →
      ∀ x ∈ S, ∀ y ∈ T, δ ≤ dist x y := by
    refine (eventually_all_finset 𝒮).2 fun S hS => (eventually_all_finset 𝒮).2 fun T hT => ?_
    obtain ⟨a, s, hs, rfl⟩ := h𝒮 S hS
    obtain ⟨b, t, ht, rfl⟩ := h𝒮 T hT
    obtain ⟨δ, hδ, hsep⟩ := exists_sep_of_isCompact (isCompact_closedSq a hs.le)
      (isCompact_closedSq b ht.le)
    filter_upwards [Ioo_mem_nhdsGT hδ] with δ' hδ' he x hx y hy
    exact hδ'.2.le.trans (hsep he x hx y hy)
  obtain ⟨δ, hδS, hδ0⟩ := (hev.and self_mem_nhdsWithin).exists
  have hevB : ∀ᶠ B in atTop, 0 ≤ B ∧ ∀ S ∈ 𝒮, ∀ x ∈ S, ∀ y ∈ S,
      lfppDOn ξ φ S x y ≤ ENNReal.ofReal (B * ‖y - x‖) := by
    refine (eventually_ge_atTop 0).and ((eventually_all_finset 𝒮).2 fun S hS => ?_)
    obtain ⟨a, s, hs, rfl⟩ := h𝒮 S hS
    obtain ⟨B0, -, hB0⟩ := exists_lfppDOn_le_mul_norm (ξ := ξ) hφ (convex_closedSq a s)
      (closedSq_subset_closedBall a hs.le)
    filter_upwards [eventually_ge_atTop B0] with B hB x hx y hy
    exact (hB0 x hx y hy).trans (ENNReal.ofReal_le_ofReal
      (mul_le_mul_of_nonneg_right hB (norm_nonneg _)))
  obtain ⟨B, hB0, hB⟩ := hevB.exists
  refine ⟨δ, hδ0, B, hB0, fun x hx y hy hxy => ?_⟩
  obtain ⟨S, hS, hxS⟩ := mem_iUnion₂.1 hx
  obtain ⟨T, hT, hyT⟩ := mem_iUnion₂.1 hy
  have hST : (S ∩ T).Nonempty := by
    by_contra hc
    have := hδS S hS T hT (not_nonempty_iff_eq_empty.1 hc) x hxS y hyT
    rw [dist_eq_norm, norm_sub_rev] at this
    linarith
  obtain ⟨a, s, hs, rfl⟩ := h𝒮 S hS
  obtain ⟨b, t, ht, rfl⟩ := h𝒮 T hT
  obtain ⟨u, ⟨huS, huT⟩, hu1, hu2⟩ := exists_mem_inter_closedSq_near hxS hyT hST
  calc lfppDOn ξ φ (⋃ S ∈ 𝒮, S) x y
      ≤ lfppDOn ξ φ (⋃ S ∈ 𝒮, S) x u + lfppDOn ξ φ (⋃ S ∈ 𝒮, S) u y := lfppDOn_triangle _ _ _
    _ ≤ lfppDOn ξ φ (closedSq a s) x u + lfppDOn ξ φ (closedSq b t) u y :=
        add_le_add (lfppDOn_anti_set (subset_biUnion_of_mem (u := fun S : Set ℂ => S) hS) _ _)
          (lfppDOn_anti_set (subset_biUnion_of_mem (u := fun S : Set ℂ => S) hT) _ _)
    _ ≤ ENNReal.ofReal (B * ‖u - x‖) + ENNReal.ofReal (B * ‖y - u‖) :=
        add_le_add (hB _ hS x hxS u huS) (hB _ hT u huT y hyT)
    _ ≤ ENNReal.ofReal (B * ‖y - x‖) + ENNReal.ofReal (B * ‖y - x‖) :=
        add_le_add (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left hu1 hB0))
          (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left hu2 hB0))
    _ = ENNReal.ofReal (2 * B * ‖y - x‖) := by
        rw [← ENNReal.ofReal_add (by positivity) (by positivity)]; ring_nf

end LQGMetric.DFGPS
