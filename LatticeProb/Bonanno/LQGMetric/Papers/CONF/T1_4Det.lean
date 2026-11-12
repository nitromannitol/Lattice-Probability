/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.CONF.T1_4Det at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S4.P412bStep1
import LatticeProb.Bonanno.LQGMetric.Papers.CONF.L2_4S2

/-!
# CONF Theorem 1.4: the deterministic part

Source: CONF = Gwynne–Miller, *Confluence of geodesics in Liouville quantum gravity for
γ ∈ (0,2)*, arXiv:1905.00381, `confluence-final.tex`, proof of Theorem 1.4 (`thm-finite-geo0`)
assuming Theorem 3.1, l. 1046–1062.

* `t14_exists_rat_radius`, `t14_tauR_btwn`: CONF l. 1056–1058, "`𝕣 ↦ τ_𝕣` is continuous and
  surjective … for any given times `0 < t < s` we can find a rational `𝕣 > 0` … such that
  `t < τ_𝕣 < … < s`". We prove only what is used: for `0 < t < s` there is a rational `𝕣 > 0`
  with `t < τ_𝕣 < s` (a farthest point `w` of `𝓑^•_{t₁}` from `z` lies on `∂𝓑^•_{t₁}`, so
  `D(z, w) = t₁`, and points just beyond `w` on the ray from `z` lie in `𝓑_{t₂}`).
* `t14_core`: CONF l. 1050–1062. If `X = X_{τ,τ'}` (leftmost geodesics in the sense of CONF
  Lemma 2.4 as in decision D44, `hitSetLM`, the set counted by Theorem 3.9) is finite and
  `t < τ < τ' < s`, then every leftmost geodesic `Q` to `∂𝓑^•_s` (Blueprint reading) passes
  through a point `x ∈ X` at time `τ`, and agrees on `[0, τ]` with every geodesic from `z` to `x`
  (l. 1051–1054: approximate `Q` by the geodesics `P_q` to rational points from Lemma 2.4; their
  restrictions to `[0, τ']` are the unique, hence leftmost, geodesics to their endpoints, so
  `P_q(τ) ∈ X`; finiteness of `X` forces `P_q(τ) = Q(τ)`; Lemma 2.3 (uniqueness of `P_q`)).
  CONF applies the approximation to the leftmost geodesic to `∂𝓑^•_{τ'}` through `x`; we apply
  it directly to `Q` (which then needs no restriction step), the same argument.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology
open LQGMetric.Blueprint

namespace LQGMetric.CONF

section Det
variable {D : ContMetric} {z : ℂ}

/-- CONF l. 1056–1058 (S-tau-cont), deterministic form: for `0 < t₁ < t₂` there is a rational
radius `R > 0` with `𝓑^•_{t₁} ⊆ B_R(z)` and `𝓑^•_{t₂} ⊄ B_R(z)` -/
theorem t14_exists_rat_radius (hbd : ∀ u : ℝ, Bornology.IsBounded (ballM D z u)) {t₁ t₂ : ℝ}
    (h1 : 0 < t₁) (h12 : t₁ < t₂) :
    ∃ R : ℚ, 0 < (R : ℝ) ∧ filledBall D z t₁ ⊆ Metric.ball z R ∧
      ¬ filledBall D z t₂ ⊆ Metric.ball z R := by
  have hK : IsCompact (filledBall D z t₁) := GM.jb_isCompact_filledBall (hbd t₁)
  have hzK : z ∈ filledBall D z t₁ :=
    Or.inl (subset_closure (show D.1 (z, z) < t₁ by rw [D.2.self_eq_zero]; exact h1))
  obtain ⟨w, hwK, hwmax⟩ := hK.exists_isMaxOn ⟨z, hzK⟩
    (continuous_id.sub continuous_const).norm.continuousOn
  set v : ℂ := if w = z then 1 else w - z with hvdef
  have hv : ∀ δ : ℝ, 0 < δ → ‖w - z‖ < ‖w + δ * v - z‖ := by
    intro δ hδ
    by_cases hw : w = z
    · have : w + δ * v - z = (δ : ℂ) := by simp [hvdef, hw]
      rw [this, hw, sub_self, norm_zero, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hδ]
      exact hδ
    · have e : w + δ * v - z = ((1 + δ : ℝ) : ℂ) * (w - z) := by
        simp only [hvdef, hw, if_false]; push_cast; ring
      have hwz : 0 < ‖w - z‖ := norm_pos_iff.2 (sub_ne_zero.2 hw)
      rw [e, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by linarith)]
      nlinarith
  have hout : ∀ δ : ℝ, 0 < δ → w + δ * v ∉ filledBall D z t₁ := fun δ hδ hmem =>
    (hv δ hδ).not_ge (hwmax hmem)
  have hcont : Continuous fun δ : ℝ => w + (δ : ℂ) * v := by fun_prop
  have hlim : Tendsto (fun δ : ℝ => w + (δ : ℂ) * v) (𝓝[>] 0) (𝓝 w) := by
    have := (hcont.tendsto 0).mono_left (nhdsWithin_le_nhds (s := Ioi (0 : ℝ)))
    simpa using this
  have hfr : w ∈ frontier (filledBall D z t₁) := by
    rw [frontier_eq_closure_inter_closure]
    exact ⟨subset_closure hwK, mem_closure_of_tendsto hlim
      (eventually_nhdsWithin_of_forall fun δ hδ => hout δ hδ)⟩
  have hDw : D.1 (z, w) = t₁ := GM.jp_frontier_subset_sphere (hbd t₁) hfr
  have hc2 : Tendsto (fun δ : ℝ => D.1 (z, w + (δ : ℂ) * v)) (𝓝[>] 0) (𝓝 t₁) := by
    rw [← hDw]
    exact ((DD.cl_continuous_distFrom D z).tendsto w).comp hlim
  obtain ⟨δ, hδ1, hδ0⟩ := ((hc2.eventually (gt_mem_nhds h12)).and self_mem_nhdsWithin).exists
  obtain ⟨R, hR1, hR2⟩ := exists_rat_btwn (hv δ hδ0)
  refine ⟨R, lt_of_le_of_lt (norm_nonneg _) hR1, fun x hx => ?_, fun hsub => ?_⟩
  · rw [Metric.mem_ball, dist_eq_norm]; exact lt_of_le_of_lt (hwmax hx) hR1
  · have hm : w + δ * v ∈ filledBall D z t₂ := Or.inl (subset_closure hδ1)
    have := hsub hm
    rw [Metric.mem_ball, dist_eq_norm] at this
    linarith

/-- CONF l. 1056–1058: for `0 < t < s` there is a rational `𝕣 > 0` with `t < τ_𝕣 < s` -/
theorem t14_tauR_btwn {Ω : Type} {D : DistC → ContMetric} {h : Ω → DistC} {z : ℂ} {ω : Ω}
    (hbd : ∀ u : ℝ, Bornology.IsBounded (ballM (D (h ω)) z u)) {t s : ℝ} (ht : 0 < t)
    (hts : t < s) :
    ∃ R : ℚ, 0 < (R : ℝ) ∧ t < tauR D h z R ω ∧ tauR D h z R ω < s := by
  obtain ⟨R, hR, h1, h2⟩ := t14_exists_rat_radius hbd (t₁ := t + (s - t) / 3)
    (t₂ := t + 2 * (s - t) / 3) (by linarith) (by linarith)
  refine ⟨R, hR, lt_of_lt_of_le (show t < t + (s - t) / 3 by linarith) ?_, lt_of_le_of_lt ?_
    (show t + 2 * (s - t) / 3 < s by linarith)⟩
  · refine le_csInf (GM.gm_tauR_set_nonempty _ z R) ?_
    rintro s' ⟨-, hs'⟩
    by_contra hlt
    exact hs' ((GM.gm_filledBall_mono _ z (not_le.1 hlt).le).trans h1)
  · exact csInf_le ⟨0, fun _ hx => hx.1.le⟩ ⟨by linarith, h2⟩

/-- **CONF Theorem 1.4, deterministic core** (CONF l. 1050–1062) -/
theorem t14_core
    (hbc : ∀ A : Set ℂ, IsClosed A → (∃ M : ℝ, ∀ u ∈ A, ∀ v ∈ A, D.1 (u, v) ≤ M) → IsCompact A)
    (hq : ∀ q : ℚ × ℚ, UniqueGeod D z (ratPt q)) {t τ τ' s : ℝ}
    (happrox : ∀ y Q, IsLeftmostGeod D z s y Q →
      ∃ (q : ℕ → ℚ × ℚ) (Qn : ℕ → ℝ → ℂ),
        (∀ n, ratPt (q n) ∉ filledBall D z s) ∧
        (∀ n, IsGeodesicL D (Qn n) (D.1 (z, ratPt (q n))) z (ratPt (q n))) ∧
        Tendsto (fun n => supDistOn (Qn n) Q s) atTop (𝓝 0))
    (ht : 0 < t) (htτ : t < τ) (hττ' : τ < τ') (hτ's : τ' < s)
    (hX : (hitSetLM D z τ τ').Finite) :
    (∃ F : Set (ℝ → ℂ), F.Finite ∧
        (∀ Q ∈ F, ∃ x ∈ frontier (filledBall D z t), IsGeodesicL D Q t z x) ∧
        ∀ y Q, IsLeftmostGeod D z s y Q → ∃ Q' ∈ F, EqOn Q Q' (Icc 0 t)) ∧
      (hitSet D z t s).Finite := by
  have hbd : ∀ u : ℝ, Bornology.IsBounded (ballM D z u) := isBounded_ballM_of_bc hbc z
  have hτ0 : 0 < τ := ht.trans htτ
  set X := hitSetLM D z τ τ' with hXdef
  -- the level of a hit point
  have hlev : ∀ x ∈ X, ∃ G, IsGeodesicL D G τ z x := by
    rintro x ⟨hx, y, P, hl, u, hu, hPu⟩
    have hus : u = τ := (DD.cl_geodL_dist hl.2.1 hu).symm.trans
      (hPu ▸ GM.jp_frontier_subset_sphere (hbd τ) hx)
    subst hus
    exact ⟨P, hPu ▸ geodL_restr hl.2.1 ⟨hτ0.le, hττ'.le⟩⟩
  -- CONF l. 1051–1054
  have key : ∀ y Q, IsLeftmostGeod D z s y Q → Q τ ∈ X ∧
      ∀ G, IsGeodesicL D G τ z (Q τ) → EqOn Q G (Icc 0 τ) := by
    intro y Q hQ
    obtain ⟨q, Qn, hqn, hQn, hconv⟩ := happrox y Q hQ
    have hLn : ∀ n, s ≤ D.1 (z, ratPt (q n)) := fun n => by
      by_contra hlt
      exact hqn n (Or.inl (subset_closure (show D.1 (z, ratPt (q n)) < s from not_le.1 hlt)))
    have hnot : ∀ n {u : ℝ}, u ≤ s → ratPt (q n) ∉ filledBall D z u := fun n u hu hm =>
      hqn n (GM.gm_filledBall_mono D z hu hm)
    have hmem : ∀ n, Qn n τ ∈ X := by
      intro n
      have hfr' : Qn n τ' ∈ frontier (filledBall D z τ') :=
        DD.cl_geod_mem_frontier (hQn n) (hτ0.trans hττ') (lt_of_lt_of_le hτ's (hLn n))
          (hnot n hτ's.le)
      have hgeo' : IsGeodesicL D (Qn n) τ' z (Qn n τ') :=
        geodL_restr (hQn n) ⟨(hτ0.trans hττ').le, hτ's.le.trans (hLn n)⟩
      refine ⟨DD.cl_geod_mem_frontier (hQn n) hτ0
          (lt_of_lt_of_le (hττ'.trans hτ's) (hLn n)) (hnot n (hττ'.trans hτ's).le),
        Qn n τ', Qn n, DD.isLeftmost_of_unique hfr' hgeo' fun R hR => ?_, τ,
        ⟨hτ0.le, hττ'.le⟩, rfl⟩
      exact ((conf_L2_3_det (hq (q n)) (hQn n) hR
        ⟨(hτ0.trans hττ').le, hτ's.le.trans (hLn n)⟩ ⟨(hτ0.trans hττ').le, le_rfl⟩
        hR.2.2.1.symm).2).symm
    have hlim : Tendsto (fun n => Qn n τ) atTop (𝓝 (Q τ)) :=
      tendsto_of_supDistOn hconv ⟨hτ0.le, (hττ'.trans hτ's).le⟩
    have hQX : Q τ ∈ X := hX.isClosed.mem_of_tendsto hlim (Eventually.of_forall hmem)
    have hev : ∀ᶠ n in atTop, Qn n τ ∈ (X \ {Q τ})ᶜ :=
      hlim.eventually ((hX.sdiff).isClosed.isOpen_compl.mem_nhds fun h => h.2 rfl)
    obtain ⟨n, hn⟩ := hev.exists
    have hnx : Qn n τ = Q τ := by
      by_contra hne
      exact hn ⟨hmem n, hne⟩
    have hIcc : τ ∈ Icc 0 (D.1 (z, ratPt (q n))) := ⟨hτ0.le, (hττ'.trans hτ's).le.trans (hLn n)⟩
    have hEq : ∀ G, IsGeodesicL D G τ z (Q τ) → EqOn (Qn n) G (Icc 0 τ) := fun G hG =>
      (conf_L2_3_det (hq (q n)) (hQn n) hG hIcc ⟨hτ0.le, le_rfl⟩ (hnx.trans hG.2.2.1.symm)).2
    have hQg : IsGeodesicL D Q τ z (Q τ) := geodL_restr hQ.2.1 ⟨hτ0.le, (hττ'.trans hτ's).le⟩
    exact ⟨hQX, fun G hG => (hEq Q hQg).symm.trans (hEq G hG)⟩
  classical
  set Gx : ℂ → ℝ → ℂ := fun x => if hx : ∃ G, IsGeodesicL D G τ z x then hx.choose else fun _ => z
  have hGx : ∀ x ∈ X, IsGeodesicL D (Gx x) τ z x := fun x hx => by
    simp only [Gx, dif_pos (hlev x hx)]
    exact (hlev x hx).choose_spec
  have hF : ∀ y Q, IsLeftmostGeod D z s y Q → ∃ Q' ∈ Gx '' X, EqOn Q Q' (Icc 0 t) := by
    intro y Q hQ
    obtain ⟨hQX, hQe⟩ := key y Q hQ
    exact ⟨Gx (Q τ), mem_image_of_mem _ hQX,
      (hQe _ (hGx _ hQX)).mono (Icc_subset_Icc_right htτ.le)⟩
  refine ⟨⟨Gx '' X, hX.image _, ?_, hF⟩, ?_⟩
  · rintro _ ⟨x, hx, rfl⟩
    have hxd : D.1 (z, x) = τ := GM.jp_frontier_subset_sphere (hbd τ) hx.1
    exact ⟨Gx x t, DD.cl_geod_mem_frontier (hGx x hx) ht htτ
        (DD.cl_not_mem_filledBall_of_frontier hxd hx.1 htτ),
      geodL_restr (hGx x hx) ⟨ht.le, htτ.le⟩⟩
  · refine ((hX.image Gx).image fun Q => Q t).subset ?_
    rintro x ⟨hx, y, Q, hQ, u, hu, hQu⟩
    have hut : u = t := (DD.cl_geodL_dist hQ.2.1 hu).symm.trans
      (hQu ▸ GM.jp_frontier_subset_sphere (hbd t) hx)
    subst hut
    obtain ⟨Q', hQ'F, hQQ'⟩ := hF y Q hQ
    exact ⟨Q', hQ'F, by rw [← hQu]; exact (hQQ' ⟨ht.le, le_rfl⟩).symm⟩

end Det

end LQGMetric.CONF
