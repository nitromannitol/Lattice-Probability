/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.CONF.S3L214P2 at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.CONF.S3L214P1
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S4.JordanJ1bFinal
import LatticeProb.Bonanno.LQGMetric.Topo.ArcDisconnect

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# CONF Lemma 2.15 for filled metric balls (decision D120 §2.1, packet J1)

Gwynne–Miller, *Confluence of geodesics in LQG* (arXiv:1905.00381), Lemma 2.15,
`confluence-final.tex` C:898–924, for `K = 𝓑^•_s(z;D)`. The proof is CONF's (C:918–924): invert
`ℂ ∖ K` by `ι(x) = 1/(x − z)`, apply Lemma 2.14 to `U = Ω(K) = ι(ℂ ∖ K) ∪ {0}`
(`area(U) ≤ π/r₁²`), and pull the disconnecting sets back by `ι⁻¹` (`|(ι⁻¹)'| ≤ 4 r₂²` on
`{|w| ≥ 1/(2r₂)}`). `∂K` is a Jordan curve and `Ω(K)` has the Carathéodory map `GM.jo_disc_map`
(DEC-120 S7 (c): prime ends of `∂K` are its points, C:835), so the connected sets `Iᵢ ⊆ ∂K`
correspond to connected subsets `Jᵢ = φ⁻¹(ι(Iᵢ))` of the circle, to which `t39p_L214_conn`
(S3L214P1, located L2.14) applies.

* `t39p_inv_disconnects`: the pull-back step (C:922–924).
* **`confL215_filledBall`**: DEC-120 §2.1.
-/

namespace LQGMetric
namespace CONF

open Set Metric Filter Complex MeasureTheory
open LQGMetric.Blueprint
open scoped Topology Real ENNReal

/-- **Pull-back by the inversion** (C:922–924): a set `X` near `∂Ω(K)` (within `δ ≤ 1/(4r₂)` of
`ℂ ∖ Ω(K)`) of diameter `≤ δ` disconnecting `ι(I)` from `0` in `Ω(K)` gives a bounded set
`Y = ι⁻¹(X)` of diameter `≤ 4 r₂² δ` disconnecting `I` from `∞` in `ℂ ∖ K`. -/
theorem t39p_inv_disconnects {D : ContMetric} {z : ℂ} {s r₁ r₂ δ : ℝ} (hs : 0 < s)
    (hr₁ : 0 < r₁) (hK1 : ball z r₁ ⊆ filledBall D z s) (hK2 : filledBall D z s ⊆ ball z r₂)
    (hδ0 : 0 ≤ δ) (hδ : δ ≤ 1 / (4 * r₂)) {I X : Set ℂ} (hI : I ⊆ frontier (filledBall D z s))
    (hX : Metric.ediam X ≤ ENNReal.ofReal δ)
    (hXd : ∀ x ∈ X, infDist x (GM.jordanOmega D z s)ᶜ ≤ δ)
    (hsep : DisconnectsIn (GM.jordanOmega D z s) X {0} ((fun x => (x - z)⁻¹) '' I)) :
    ∃ Y : Set ℂ, Bornology.IsBounded Y ∧ Metric.diam Y ≤ 4 * r₂ ^ 2 * δ ∧
      DisconnectsFromInfty (filledBall D z s) Y I := by
  set K := filledBall D z s with hKdef
  set U := GM.jordanOmega D z s with hU
  have hzK : z ∈ K := hK1 (mem_ball_self hr₁)
  have hr₂ : 0 < r₂ := by have := hK2 hzK; rw [mem_ball, dist_self] at this; exact this
  -- `ℂ ∖ U ⊆ {|w| > 1/r₂}`, nonempty
  have hUc : ∀ w ∉ U, 1 / r₂ < ‖w‖ := by
    intro w hw
    simp only [hU, GM.jordanOmega, mem_union, mem_ofPred_eq, mem_singleton_iff, not_or,
      not_not] at hw
    obtain ⟨hwK, hw0⟩ := hw
    have := hK2 hwK
    rw [mem_ball, dist_eq_norm, add_sub_cancel_left, norm_inv] at this
    rw [div_lt_iff₀ hr₂]
    have hw' : 0 < ‖w‖ := norm_pos_iff.2 hw0
    calc 1 = ‖w‖ * ‖w‖⁻¹ := (mul_inv_cancel₀ hw'.ne').symm
      _ < ‖w‖ * r₂ := by gcongr
  have hUcne : (Uᶜ).Nonempty := by
    refine ⟨((2 / r₁ : ℝ) : ℂ), ?_⟩
    simp only [hU, GM.jordanOmega, mem_compl_iff, mem_union, mem_ofPred_eq, mem_singleton_iff,
      not_or, not_not]
    refine ⟨hK1 ?_, by exact_mod_cast (by positivity : (2 / r₁ : ℝ) ≠ 0)⟩
    rw [mem_ball, dist_eq_norm, add_sub_cancel_left, ← ofReal_inv, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos (by positivity), inv_div]
    linarith
  -- points of `X` have `|x| ≥ 1/(2r₂)`
  have hXn : ∀ x ∈ X, 1 / (2 * r₂) ≤ ‖x‖ := by
    intro x hx
    by_contra hlt
    push Not at hlt
    have h1 : 1 / (2 * r₂) ≤ infDist x Uᶜ := by
      rw [le_infDist hUcne]
      intro w hw
      have := hUc w hw
      have h2 : ‖w‖ ≤ dist x w + ‖x‖ := by
        rw [dist_eq_norm]; have := norm_sub_le w x
        rw [norm_sub_rev w x] at this; linarith [norm_sub_norm_le w x, norm_sub_rev x w]
      have h3 : 1 / r₂ = 1 / (2 * r₂) + 1 / (2 * r₂) := by field_simp; ring
      linarith
    have h4 := hXd x hx
    have h5 : 1 / (4 * r₂) < 1 / (2 * r₂) := by
      rw [div_lt_div_iff₀ (by positivity) (by positivity)]; linarith
    linarith
  have hXdist : ∀ x ∈ X, ∀ x' ∈ X, dist x x' ≤ δ := by
    intro x hx x' hx'
    have := (Metric.edist_le_ediam_of_mem hx hx').trans hX
    rwa [edist_dist, ENNReal.ofReal_le_ofReal_iff hδ0] at this
  set Y := (fun w : ℂ => z + w⁻¹) '' X with hY
  refine ⟨Y, ?_, ?_, ?_⟩
  · refine (isBounded_closedBall (x := z) (r := 2 * r₂)).subset ?_
    rintro _ ⟨x, hx, rfl⟩
    have hx0 : 0 < ‖x‖ := lt_of_lt_of_le (by positivity) (hXn x hx)
    rw [mem_closedBall, dist_eq_norm, add_sub_cancel_left, norm_inv]
    have := hXn x hx
    rw [div_le_iff₀ (by positivity)] at this
    rw [inv_le_iff_one_le_mul₀ hx0]; linarith
  · refine Metric.diam_le_of_forall_dist_le (by positivity) ?_
    rintro _ ⟨x, hx, rfl⟩ _ ⟨x', hx', rfl⟩
    have hx0 : x ≠ 0 := norm_pos_iff.1 (lt_of_lt_of_le (by positivity) (hXn x hx))
    have hx0' : x' ≠ 0 := norm_pos_iff.1 (lt_of_lt_of_le (by positivity) (hXn x' hx'))
    have e := GM.jo_inv_sub_norm (z := 0) hx0 hx0'
    simp only [sub_zero] at e
    rw [dist_eq_norm, add_sub_add_left_eq_sub]
    have h1 := hXn x hx
    have h2 := hXn x' hx'
    have hm : 1 / (2 * r₂) * (1 / (2 * r₂)) ≤ ‖x‖ * ‖x'‖ :=
      mul_le_mul h1 h2 (by positivity) (norm_nonneg _)
    have hd := hXdist x hx x' hx'
    rw [dist_eq_norm] at hd
    have ha := norm_nonneg (x⁻¹ - x'⁻¹)
    have h4 : ‖x⁻¹ - x'⁻¹‖ * (1 / (2 * r₂) * (1 / (2 * r₂))) ≤ δ := by
      nlinarith
    have h5 : 1 / (2 * r₂) * (1 / (2 * r₂)) = 1 / (4 * r₂ ^ 2) := by field_simp; ring
    rw [h5, ← div_eq_mul_one_div, div_le_iff₀ (by positivity)] at h4
    linarith
  · refine ⟨‖z‖ + 2 * r₂, fun y x γ hy hx hγK => ?_⟩
    have hxz : x ≠ z := fun e => GM.jo_not_mem_frontier_self hs (e ▸ hI hx)
    have hγz : ∀ t, γ t ≠ z := by
      intro t ht
      have : γ t ∈ range γ ∩ K := ⟨mem_range_self t, ht ▸ hzK⟩
      exact hxz ((mem_singleton_iff.1 (hγK this)).symm.trans ht)
    -- `ι ∘ γ`
    let γ' : Path ((y - z)⁻¹) ((x - z)⁻¹) :=
      ⟨⟨fun t => (γ t - z)⁻¹, (γ.continuous.sub continuous_const).inv₀
        fun t => sub_ne_zero.2 (hγz t)⟩, by simp, by simp⟩
    have hγ' : range γ' ⊆ U ∪ (fun x => (x - z)⁻¹) '' I := by
      rintro _ ⟨t, rfl⟩
      by_cases htx : γ t = x
      · right; exact ⟨x, hx, by simp [γ', htx]⟩
      · left; left
        show z + ((γ t - z)⁻¹)⁻¹ ∉ K
        rw [GM.jo_inv_left (hγz t)]
        exact fun hK => htx (mem_singleton_iff.1 (hγK ⟨mem_range_self t, hK⟩))
    -- the segment from `0` to `ι y` inside `B_{1/(2r₂)}(0) ⊆ U`
    have hball : ball (0 : ℂ) (1 / (2 * r₂)) ⊆ U := by
      intro w hw
      by_cases hw0 : w = 0
      · right; exact hw0
      left
      show z + w⁻¹ ∉ K
      intro hK
      have h1 := hK2 hK
      rw [mem_ball, dist_eq_norm, add_sub_cancel_left, norm_inv] at h1
      rw [mem_ball_zero_iff] at hw
      have hw' : 0 < ‖w‖ := norm_pos_iff.2 hw0
      have : 1 < ‖w‖ * r₂ * 1 := by
        calc (1 : ℝ) = ‖w‖ * ‖w‖⁻¹ := (mul_inv_cancel₀ hw'.ne').symm
          _ < ‖w‖ * r₂ := by gcongr
          _ = _ := by ring
      rw [lt_div_iff₀ (by positivity)] at hw
      nlinarith
    have hyz : 2 * r₂ < ‖y - z‖ := by
      have := norm_sub_norm_le y z; linarith
    have hιy : (y - z)⁻¹ ∈ ball (0 : ℂ) (1 / (2 * r₂)) := by
      rw [mem_ball_zero_iff, norm_inv]
      exact (inv_lt_comm₀ (by linarith) (by positivity)).2 (by rw [one_div, inv_inv]; exact hyz) |>.trans_le' le_rfl
    have hJ : JoinedIn (ball (0 : ℂ) (1 / (2 * r₂))) 0 ((y - z)⁻¹) :=
      ((convex_ball _ _).isPathConnected ⟨_, hιy⟩).joinedIn _ (mem_ball_self (by positivity)) _ hιy
    set σ := hJ.somePath
    have hrange : range (σ.trans γ') ⊆ U ∪ (fun x => (x - z)⁻¹) '' I := by
      rw [Path.trans_range]
      refine union_subset ?_ hγ'
      rintro _ ⟨t, rfl⟩
      exact Or.inl (hball (hJ.somePath_mem t))
    obtain ⟨p, hpr, hpX⟩ := hsep 0 _ (σ.trans γ') rfl ⟨x, hx, rfl⟩ hrange
    rw [Path.trans_range] at hpr
    rcases hpr with ⟨t, rfl⟩ | ⟨t, rfl⟩
    · have h1 := hXn _ hpX
      have h2 := mem_ball_zero_iff.1 (hJ.somePath_mem t)
      exact absurd h1 (not_le.2 h2)
    · refine ⟨γ t, mem_range_self t, ⟨(γ t - z)⁻¹, hpX, ?_⟩⟩
      exact GM.jo_inv_left (hγz t)

open Classical in
/-- **CONF Lemma 2.15 for filled metric balls** (C:898–924), Euclidean form: `K = 𝓑^•_s(z;D)`,
`B_{r₁}(z) ⊆ K ⊆ B_{r₂}(z)`; of `n` pairwise disjoint nonempty connected subsets `Iᵢ ⊆ ∂K`, at
least `(1 − A r₂⁴/(r₁² C²)) n − N₀` are disconnected from `∞` in `ℂ ∖ K` by a bounded set of
diameter `≤ C n^{-1/2}` (`C n^{-1/2} ≤ r₂`; the CONF use has `C n^{-1/2} ≍ ε_k 𝕣 ≤ 𝕣 < 3𝕣`). -/
theorem confL215_filledBall : ∃ A N₀ : ℝ, 0 < A ∧ 1 ≤ N₀ ∧
    ∀ {D : ContMetric} {z : ℂ} {s r₁ r₂ : ℝ}, 0 < s → D.IsLength →
      Bornology.IsBounded (ballM D z s) → 0 < r₁ → ball z r₁ ⊆ filledBall D z s →
      filledBall D z s ⊆ ball z r₂ →
      ∀ {ι : Type} (S : Finset ι) (I : ι → Set ℂ),
        (∀ i ∈ S, I i ⊆ frontier (filledBall D z s)) → (∀ i ∈ S, (I i).Nonempty) →
        (∀ i ∈ S, IsPreconnected (I i)) → (S : Set ι).PairwiseDisjoint I →
        ∀ C : ℝ, 0 < C → C * (S.card : ℝ) ^ (-(1 / 2 : ℝ)) ≤ r₂ →
        (1 - A * r₂ ^ 4 / (r₁ ^ 2 * C ^ 2)) * S.card - N₀ ≤
          ((S.filter fun i => ∃ Y : Set ℂ, Bornology.IsBounded Y ∧
            Metric.diam Y ≤ C * (S.card : ℝ) ^ (-(1 / 2 : ℝ)) ∧
            DisconnectsFromInfty (filledBall D z s) Y (I i)).card : ℝ) := by
  obtain ⟨A₀, N₀', hA₀, hN₀', hL214⟩ := t39p_L214_conn
  refine ⟨16 * π * A₀, max N₀' 1, by positivity, le_max_right _ _, ?_⟩
  intro D z s r₁ r₂ hs hL hbd hr₁ hK1 hK2 ι S I hIf hIn hIc hId C hC hCr
  set K := filledBall D z s with hKdef
  set n : ℝ := (S.card : ℝ) with hn
  have hzK : z ∈ K := hK1 (mem_ball_self hr₁)
  have hr₂ : 0 < r₂ := by have := hK2 hzK; rw [mem_ball, dist_self] at this; exact this
  set a : ℝ := 16 * π * A₀ * r₂ ^ 4 / (r₁ ^ 2 * C ^ 2) with ha
  have ha0 : 0 ≤ a := by positivity
  have hn0 : 0 ≤ n := Nat.cast_nonneg _
  have hNmax := le_max_right N₀' 1
  rcases le_or_gt S.card 1 with h1 | h2
  · have : n ≤ 1 := by rw [hn]; exact_mod_cast h1
    have : (1 - a) * n - max N₀' 1 ≤ 0 := by nlinarith
    exact this.trans (Nat.cast_nonneg _)
  have hnpos : 0 < n := by rw [hn]; exact_mod_cast (by omega : 0 < S.card)
  obtain ⟨φ, hφc, hφi, hφd, hφ0, hφB, hφS⟩ := GM.jo_disc_map hs hL hbd (GM.gm_j1b D z s hs hL hbd)
  set ιm : ℂ → ℂ := fun x => (x - z)⁻¹ with hιm
  have hιinj : Function.Injective ιm := fun u v h => by
    simpa [hιm] using h
  set J : ι → Set ℂ := fun i => sphere 0 1 ∩ φ ⁻¹' (ιm '' I i) with hJ
  have hJimg : ∀ i ∈ S, φ '' J i = ιm '' I i := by
    intro i hi
    apply subset_antisymm
    · rintro _ ⟨b, hb, rfl⟩; exact hb.2
    · intro w hw
      have : w ∈ φ '' sphere 0 1 := hφS ▸ image_mono (hIf i hi) hw
      obtain ⟨b, hb, rfl⟩ := this
      exact ⟨b, ⟨hb, hw⟩, rfl⟩
  have hJS : ∀ i ∈ S, J i ⊆ sphere 0 1 := fun i _ => inter_subset_left
  have hJn : ∀ i ∈ S, (J i).Nonempty := fun i hi => by
    have := (hIn i hi).image ιm
    rw [← hJimg i hi] at this
    exact this.of_image
  have hJd : (S : Set ι).PairwiseDisjoint J := by
    intro i hi j hj hij
    have := ((disjoint_image_iff hιinj).2 (hId hi hj hij)).preimage φ
    exact this.mono inter_subset_right inter_subset_right
  have hJc : ∀ i ∈ S, IsPreconnected (J i) := by
    intro i hi
    have hzI : z ∉ I i := fun h => GM.jo_not_mem_frontier_self hs (hIf i hi h)
    have hpc : IsPreconnected (ιm '' I i) := (hIc i hi).image _ (GM.jo_continuousOn_iota _ hzI)
    let e : sphere (0 : ℂ) 1 → ℂ := fun b => φ b
    have he : Continuous e := (hφc.mono sphere_subset_closedBall).domRestrict
    have heinj : Function.Injective e := fun u v h =>
      Subtype.ext (hφi (sphere_subset_closedBall u.2) (sphere_subset_closedBall v.2) h)
    have hemb := he.isClosedEmbedding heinj
    set T : Set (sphere (0 : ℂ) 1) := e ⁻¹' (ιm '' I i) with hT
    have heT : e '' T = ιm '' I i := by
      refine image_preimage_eq_of_subset ?_
      rw [← hJimg i hi]
      rintro _ ⟨b, hb, rfl⟩
      exact ⟨⟨b, hb.1⟩, rfl⟩
    have hTc : IsPreconnected T := hemb.isInducing.isPreconnected_image.1 (heT ▸ hpc)
    have hJT : J i = Subtype.val '' T := by
      ext b
      constructor
      · rintro ⟨hb1, hb2⟩; exact ⟨⟨b, hb1⟩, hb2, rfl⟩
      · rintro ⟨b', hb', rfl⟩; exact ⟨b'.2, hb'⟩
    rw [hJT]
    exact hTc.image _ continuous_subtype_val.continuousOn
  have hfree : ∀ i ∈ S, ∃ p ∈ sphere (0 : ℂ) 1, p ∉ J i := by
    intro i hi
    obtain ⟨j, hj, hji⟩ := Finset.exists_mem_ne h2 i
    obtain ⟨p, hp⟩ := hJn j hj
    exact ⟨p, hJS j hj hp, fun hpi => Set.disjoint_left.1 (hJd hj hi hji) hp hpi⟩
  set CU : ℝ := C / (4 * r₂ ^ 2) with hCU
  have hCU0 : 0 < CU := by positivity
  set q : ℝ := n ^ (-(1 / 2 : ℝ)) with hq
  have hq0 : 0 < q := Real.rpow_pos_of_pos hnpos _
  have hm := hL214 S φ J CU hφd hφc hφi hφ0 hJS hJn hJc hJd hfree hCU0
  rw [hφB] at hm
  -- `area(Ω(K)) ≤ π / r₁²`
  have hUsub : GM.jordanOmega D z s ⊆ closedBall 0 (1 / r₁) := by
    intro w hw
    rw [mem_closedBall_zero_iff]
    rcases hw with hw | hw
    · have hw0 : w ≠ 0 := by
        rintro rfl
        exact hw (by rw [inv_zero, add_zero]; exact hzK)
      have : z + w⁻¹ ∉ ball z r₁ := fun h => hw (hK1 h)
      rw [mem_ball, dist_eq_norm, add_sub_cancel_left, norm_inv, not_lt] at this
      have hw' : 0 < ‖w‖ := norm_pos_iff.2 hw0
      rw [le_div_iff₀ hr₁]
      calc ‖w‖ * r₁ ≤ ‖w‖ * ‖w‖⁻¹ := by gcongr
        _ = 1 := mul_inv_cancel₀ hw'.ne'
    · rw [mem_singleton_iff.1 hw, norm_zero]; positivity
  set V : ℝ := (volume (GM.jordanOmega D z s)).toReal with hV
  have hV0 : 0 ≤ V := ENNReal.toReal_nonneg
  have hVle : V ≤ π / r₁ ^ 2 := by
    have h1 := ENNReal.toReal_mono measure_closedBall_lt_top.ne (measure_mono (μ := volume) hUsub)
    rw [Complex.volume_closedBall] at h1
    refine h1.trans (le_of_eq ?_)
    simp only [ENNReal.toReal_mul, ENNReal.toReal_pow, ENNReal.coe_toReal, NNReal.coe_real_pi,
      ENNReal.toReal_ofReal (by positivity : (0 : ℝ) ≤ 1 / r₁)]
    field_simp
  -- good arcs of L2.14 give good sets for L2.15
  have hδ : CU * q ≤ 1 / (4 * r₂) := by
    rw [hCU, div_mul_eq_mul_div, div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith
  have hsub : (S.filter fun i => ∃ X : Set ℂ,
      Metric.ediam X ≤ ENNReal.ofReal (CU * q) ∧
      (∀ x ∈ X, infDist x (GM.jordanOmega D z s)ᶜ ≤ CU * q) ∧
      DisconnectsIn (GM.jordanOmega D z s) X {0} (φ '' J i)) ⊆
      (S.filter fun i => ∃ Y : Set ℂ, Bornology.IsBounded Y ∧ Metric.diam Y ≤ C * q ∧
        DisconnectsFromInfty K Y (I i)) := by
    intro i hi
    obtain ⟨hiS, X, h1, h2, h3⟩ := Finset.mem_filter.1 hi
    rw [hJimg i hiS] at h3
    obtain ⟨Y, hYb, hYd, hYs⟩ := t39p_inv_disconnects hs hr₁ hK1 hK2 (by positivity) hδ
      (hIf i hiS) h1 h2 h3
    refine Finset.mem_filter.2 ⟨hiS, Y, hYb, hYd.trans (le_of_eq ?_), hYs⟩
    rw [hCU]; field_simp
  have hcard := Finset.card_le_card hsub
  have hcard' : ((S.filter fun i => ∃ X : Set ℂ,
      Metric.ediam X ≤ ENNReal.ofReal (CU * q) ∧
      (∀ x ∈ X, infDist x (GM.jordanOmega D z s)ᶜ ≤ CU * q) ∧
      DisconnectsIn (GM.jordanOmega D z s) X {0} (φ '' J i)).card : ℝ) ≤
      ((S.filter fun i => ∃ Y : Set ℂ, Bornology.IsBounded Y ∧ Metric.diam Y ≤ C * q ∧
        DisconnectsFromInfty K Y (I i)).card : ℝ) := by exact_mod_cast hcard
  have hAV : A₀ / CU ^ 2 * V ≤ a := by
    have e : A₀ / CU ^ 2 = 16 * A₀ * r₂ ^ 4 / C ^ 2 := by rw [hCU]; field_simp; ring
    rw [e, ha]
    calc 16 * A₀ * r₂ ^ 4 / C ^ 2 * V ≤ 16 * A₀ * r₂ ^ 4 / C ^ 2 * (π / r₁ ^ 2) := by gcongr
      _ = 16 * π * A₀ * r₂ ^ 4 / (r₁ ^ 2 * C ^ 2) := by field_simp
  have hfin : (1 - a) * n - max N₀' 1 ≤ (1 - A₀ / CU ^ 2 * V) * n - N₀' := by
    nlinarith [mul_le_mul_of_nonneg_right hAV hn0, le_max_left N₀' 1]
  exact hfin.trans (hm.trans hcard')

end CONF
end LQGMetric
