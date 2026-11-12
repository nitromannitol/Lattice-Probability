/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.GM.S4.L46MeasB3 at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S4.L46MeasDet
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S3.GoodAnnulusMeas

/-!
# GM Lemma 4.6 (b), deterministic part: `Stab_{k,r}(z)` is local (task P2-E3b)

Source: GM = Gwynne–Miller, arXiv:1905.00383v3, `literature/src/1905.00383/uniqueness-final.tex`,
proof of Lemma 4.6, l. 1705–1708: "`(𝓑^•_{t_k}, h|_{𝓑^•_{t_k}})` and hence also `𝓘_k` is
determined by `h|_{ℂ∖B_r(z)}` on the event `{(z,r) ∈ 𝒵_k}`. By Axiom II (locality), it then
follows that `Stab_{k,r}(z)` is determined by `h|_{ℂ∖B_r(z)}`."

Deterministic content: for two length metrics whose internal metrics agree on an open
`U ⊇ ℂ ∖ B_ρ(z)` (`ρ ≤ r`, `ρ ≤ λ₄ε𝕣`), on `(z,r) ∈ 𝒵_k`:
* the metric balls `𝓑_u(𝕫)`, `u ≤ t_k`, agree and `𝓑^•_{t_k} ⊆ U` (`gm_agree_of_candEvD`, the
  argument of `gm_candEvD_of_internal_eq`);
* geodesics from `𝕫` of length `≤ t_k` are geodesics of both metrics (`gm_geodL_transfer`: their
  lengths are lengths of paths in `U`, GM l. 1348 `lenFun_internal`), hence leftmost geodesics,
  `Conf_k` and the arcs `arcOf` agree;
* the `D(·,·;ℂ∖cl B_r(z))`-geodesics agree (`gm_avoidGeod_transfer`: paths in `ℂ ∖ B_r(z) ⊆ U`);
* so `stabCond` (GM (4.11)) transfers (`gm_stab_of_internal_eq`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Filter Topology Set Metric
open scoped ENNReal
open LQGMetric.Blueprint

namespace LQGMetric.GM

/-- lengths of paths in `U` agree when the internal metrics on `U` agree (GM l. 1348) -/
theorem gm_len_eq_of_internal_eq {d₁ d₂ : ContMetric} {U : Set ℂ}
    (heq : ∀ x ∈ U, ∀ y ∈ U, d₁.internal U x y = d₂.internal U x y) {P : ℝ → ℂ} {a b : ℝ}
    (hP : ContinuousOn P (Icc a b)) (hPU : MapsTo P (Icc a b) U) : d₂.len P a b = d₁.len P a b := by
  rw [← lenFun_internal d₂ hP hPU, ← lenFun_internal d₁ hP hPU]
  unfold lenFun
  refine iSup_congr fun p => Finset.sum_congr rfl fun i _ => ?_
  exact (heq _ (hPU (p.2.2.2 _)) _ (hPU (p.2.2.2 _))).symm

/-- agreement of two metrics up to level `T` around `𝕫`, inside `U` -/
structure GMAgree (d₁ d₂ : ContMetric) (U : Set ℂ) (𝕫 : ℂ) (T : ℝ) : Prop where
  int : ∀ x ∈ U, ∀ y ∈ U, d₁.internal U x y = d₂.internal U x y
  ball : ∀ u ≤ T, ballM d₁ 𝕫 u = ballM d₂ 𝕫 u
  sub : filledBall d₁ 𝕫 T ⊆ U
  pos : 0 < T

theorem GMAgree.fb {d₁ d₂ : ContMetric} {U : Set ℂ} {𝕫 : ℂ} {T : ℝ} (H : GMAgree d₁ d₂ U 𝕫 T)
    {u : ℝ} (hu : u ≤ T) : filledBall d₂ 𝕫 u = filledBall d₁ 𝕫 u :=
  gm_filledBall_congr (H.ball u hu).symm

theorem GMAgree.symm {d₁ d₂ : ContMetric} {U : Set ℂ} {𝕫 : ℂ} {T : ℝ} (H : GMAgree d₁ d₂ U 𝕫 T) :
    GMAgree d₂ d₁ U 𝕫 T :=
  ⟨fun x hx y hy => (H.int x hx y hy).symm, fun u hu => (H.ball u hu).symm,
    (H.fb le_rfl) ▸ H.sub, H.pos⟩

/-- geodesics from `𝕫` of length `≤ T` are geodesics of both metrics -/
theorem gm_geodL_transfer {d₁ d₂ : ContMetric} {U : Set ℂ} {𝕫 : ℂ} {T : ℝ}
    (H : GMAgree d₁ d₂ U 𝕫 T) {P : ℝ → ℂ} {L : ℝ} {y : ℂ} (hP : IsGeodesicL d₁ P L 𝕫 y)
    (hL : L ≤ T) : IsGeodesicL d₂ P L 𝕫 y := by
  have hc := gm_geodL_continuousOn hP
  have hd1 : ∀ u ∈ Icc 0 L, d₁.1 (𝕫, P u) = u := fun u hu => gm_geodL_dist hP hu
  have hmapsK : MapsTo P (Icc 0 L) (closure (ballM d₁ 𝕫 T)) := by
    intro u hu
    rcases lt_or_eq_of_le (hu.2.trans hL) with hlt | heq'
    · exact subset_closure (show d₁.1 (𝕫, P u) < T by rw [hd1 u hu]; exact hlt)
    · have huL : u = L := le_antisymm hu.2 (heq' ▸ hL)
      have hL0 : 0 < L := huL ▸ heq' ▸ H.pos
      have hcw : ContinuousWithinAt P (Ico 0 L) L :=
        (hc L ⟨hL0.le, le_rfl⟩).mono Ico_subset_Icc_self
      have hmem : L ∈ closure (Ico 0 L) := by
        rw [closure_Ico hL0.ne]; exact ⟨hL0.le, le_rfl⟩
      rw [huL]
      refine closure_mono ?_ (hcw.mem_closure_image hmem)
      rintro _ ⟨v, hv, rfl⟩
      show d₁.1 (𝕫, P v) < T
      rw [hd1 v ⟨hv.1, hv.2.le⟩]
      linarith [hv.2]
  have hmaps : MapsTo P (Icc 0 L) U := fun u hu => H.sub (Or.inl (hmapsK hu))
  have hgc := MetricGeometry.isGeodesicCurve_of_edist_eq (X := d₁.Space) (P := d₁.pt ∘ P) hP.1
    (fun s hs t ht => by
      simp only [Function.comp_apply, edist_dist]
      show ENNReal.ofReal (d₁.1 (P s, P t)) = ENNReal.ofReal (dist s t)
      rw [hP.2.2.2 s hs t ht, Real.dist_eq, abs_sub_comm])
  have hup : ∀ a ∈ Icc 0 L, ∀ b ∈ Icc 0 L, a ≤ b → d₂.1 (P a, P b) ≤ b - a := by
    intro a ha b hb hab
    have hsub : Icc a b ⊆ Icc 0 L := Icc_subset_Icc ha.1 hb.2
    have e := gm_len_eq_of_internal_eq H.int (hc.mono hsub) (hmaps.mono_left hsub)
    have h1 := MetricGeometry.edist_le_curveLength (d₂.pt ∘ P) hab
    have h2 : MetricGeometry.curveLength (d₂.pt ∘ P) a b = ENNReal.ofReal (b - a) := by
      rw [show MetricGeometry.curveLength (d₂.pt ∘ P) a b = d₂.len P a b from rfl, e]
      exact MetricGeometry.curveLength_of_hasUnitSpeedOn hgc.2 ha hb
    rw [h2, edist_dist] at h1
    exact (ENNReal.ofReal_le_ofReal_iff (by linarith)).1 h1
  have hlow : ∀ b ∈ Icc 0 L, b ≤ d₂.1 (𝕫, P b) := by
    intro b hb
    by_contra hlt
    push_neg at hlt
    have hb2 : P b ∈ ballM d₂ 𝕫 b := hlt
    rw [← H.ball b (hb.2.trans hL)] at hb2
    have : d₁.1 (𝕫, P b) < b := hb2
    rw [hd1 b hb] at this
    exact lt_irrefl _ this
  refine ⟨hP.1, hP.2.1, hP.2.2.1, fun s hs t ht => ?_⟩
  have key : ∀ s ∈ Icc 0 L, ∀ t ∈ Icc 0 L, s ≤ t → d₂.1 (P s, P t) = |t - s| := by
    intro s hs t ht hst
    rw [abs_of_nonneg (sub_nonneg.2 hst)]
    refine le_antisymm (hup s hs t ht hst) ?_
    have htri := d₂.2.triangle 𝕫 (P s) (P t)
    have h0 := hup 0 ⟨le_rfl, hP.1⟩ s hs hs.1
    rw [hP.2.1] at h0
    linarith [hlow t ht]
  rcases le_total s t with hst | hts
  · exact key s hs t ht hst
  · rw [d₂.2.symm (P s) (P t), abs_sub_comm]
    exact key t ht s hs hts

theorem gm_sideGeod_transfer {d₁ d₂ : ContMetric} {U : Set ℂ} {𝕫 : ℂ} {T : ℝ}
    (H : GMAgree d₁ d₂ U 𝕫 T) {s : ℝ} (hs : s ≤ T) {b : Bool} {y : ℂ} {P : ℝ → ℂ}
    (h : IsSideGeod b d₁ 𝕫 s y P) : IsSideGeod b d₂ 𝕫 s y P := by
  obtain ⟨hy, hP, φ, hφ, t₀, ht₀, t, Pn, h1, h2, h3, h4⟩ := h
  refine ⟨by rw [H.fb hs]; exact hy, gm_geodL_transfer H hP hs, φ, by rw [H.fb hs]; exact hφ,
    t₀, ht₀, t, Pn, h1, h2, fun n => gm_geodL_transfer H (h3 n) hs, h4⟩

theorem gm_hitSet_transfer {d₁ d₂ : ContMetric} {U : Set ℂ} {𝕫 : ℂ} {T : ℝ}
    (H : GMAgree d₁ d₂ U 𝕫 T) {a b : ℝ} (ha : a ≤ T) (hb : b ≤ T) {x : ℂ}
    (hx : x ∈ hitSet d₁ 𝕫 a b) : x ∈ hitSet d₂ 𝕫 a b := by
  obtain ⟨hxf, y, P, hP, u, hu, hPu⟩ := hx
  exact ⟨by rw [H.fb ha]; exact hxf, y, P, gm_sideGeod_transfer H hb hP, u, hu, hPu⟩

theorem gm_arcOf_transfer {d₁ d₂ : ContMetric} {U : Set ℂ} {𝕫 : ℂ} {T : ℝ}
    (H : GMAgree d₁ d₂ U 𝕫 T) {t : ℝ} (ht : t ≤ T) {x y : ℂ} (hy : y ∈ arcOf d₁ 𝕫 t x) :
    y ∈ arcOf d₂ 𝕫 t x := by
  obtain ⟨hyf, Q, hQ, u, hu, hQu⟩ := hy
  exact ⟨by rw [H.fb ht]; exact hyf, Q, gm_sideGeod_transfer H ht hQ, u, hu, hQu⟩

/-- `D(·,·;ℂ∖cl B_r(z))`-geodesics only see the internal metric of `U ⊇ ℂ ∖ B_r(z)` -/
theorem gm_avoidGeod_transfer {d₁ d₂ : ContMetric} {U : Set ℂ}
    (heq : ∀ x ∈ U, ∀ y ∈ U, d₁.internal U x y = d₂.internal U x y) {𝕫 z : ℂ} {r : ℝ}
    (hUr : (ball z r)ᶜ ⊆ U) {x : ℂ} {Q : ℝ → ℂ} {T : ℝ} (h : IsAvoidGeod d₁ 𝕫 z r x Q T) :
    IsAvoidGeod d₂ 𝕫 z r x Q T := by
  obtain ⟨hT, hQc, hQ0, hQT, hx, hout, hmin⟩ := h
  refine ⟨hT, hQc, hQ0, hQT, hx, hout, fun Q' a b hab hQ'c hQ'a hQ'b hQ'U => ?_⟩
  have hQU : MapsTo Q (Icc 0 T) (ball z r)ᶜ := by
    intro u hu
    rcases eq_or_lt_of_le hu.2 with h | h
    · rw [h, hQT]
      intro hb
      rw [mem_sphere] at hx
      rw [mem_ball] at hb
      linarith
    · exact fun hb => hout u ⟨hu.1, h⟩ (ball_subset_closedBall hb)
  rw [gm_len_eq_of_internal_eq heq hQc (hQU.mono_right hUr),
    gm_len_eq_of_internal_eq heq hQ'c (hQ'U.mono_right hUr)]
  exact hmin Q' a b hab hQ'c hQ'a hQ'b hQ'U

/-- on `(z,r) ∈ 𝒵_k`, the two metrics agree up to level `t_k` (the argument of
`gm_candEvD_of_internal_eq`) -/
theorem gm_agree_of_candEvD {d₁ d₂ : ContMetric} (h₁ : d₁.IsLength) (h₂ : d₂.IsLength)
    {𝕫 : ℂ} {R c lam1 lam4 ε ν 𝕣 : ℝ} {Rads : Set ℝ} {z : ℂ} {r ρ : ℝ} (hc : 1 < c)
    (ha : 0 < lam4 * ε * 𝕣) (hρ : ρ ≤ lam4 * ε * 𝕣) {U : Set ℂ} (hU : IsOpen U)
    (hUρ : (Metric.ball z ρ)ᶜ ⊆ U)
    (heq : ∀ x ∈ U, ∀ y ∈ U, d₁.internal U x y = d₂.internal U x y)
    (H : candEvD d₁ 𝕫 R c lam1 lam4 ε ν 𝕣 Rads z r) :
    GMAgree d₁ d₂ U 𝕫 (tauD d₁ 𝕫 R * c) ∧ tauD d₂ 𝕫 R = tauD d₁ 𝕫 R := by
  obtain ⟨-, hzK, -, hdist⟩ := H
  set τ₁ := tauD d₁ 𝕫 R with hτ₁
  set K₁ := filledBall d₁ 𝕫 (τ₁ * c) with hK₁
  have hτpos : 0 < τ₁ := by
    by_contra hneg
    have hK : K₁ = ∅ := gm_filledBall_nonpos d₁ 𝕫
      (mul_nonpos_of_nonpos_of_nonneg (not_lt.1 hneg) (by linarith))
    have h0 := hdist.1
    rw [hK, frontier_empty, infDist_empty] at h0
    linarith
  have hT : 0 < τ₁ * c := mul_pos hτpos (by linarith)
  have hτT : τ₁ < τ₁ * c := by nlinarith
  have hKU : K₁ ⊆ U := by
    intro x hx
    refine hUρ fun hxb => ?_
    have h1 := gm_infDist_frontier_le_dist hzK hx
    rw [mem_ball, dist_comm] at hxb
    linarith [hdist.1]
  have hball : ∀ s ≤ τ₁ * c, ballM d₂ 𝕫 s = ballM d₁ 𝕫 s := by
    intro s hs
    rcases le_or_gt s 0 with hs0 | hs0
    · rw [gm_ballM_nonpos d₂ 𝕫 hs0, gm_ballM_nonpos d₁ 𝕫 hs0]
    · refine gm_ballM_eq_of_internal_eq h₁ h₂ hU heq hs0 ?_
      exact subset_closure.trans (subset_union_left.trans
        ((gm_filledBall_mono d₁ 𝕫 hs).trans hKU))
  have hfb : ∀ s ≤ τ₁ * c, filledBall d₂ 𝕫 s = filledBall d₁ 𝕫 s := fun s hs =>
    gm_filledBall_congr (hball s hs)
  have hne : {s | 0 < s ∧ ¬ filledBall d₁ 𝕫 s ⊆ Metric.ball 𝕫 R}.Nonempty := by
    by_contra hemp
    rw [not_nonempty_iff_eq_empty] at hemp
    have : τ₁ = 0 := by rw [hτ₁, tauD, hemp, Real.sInf_empty]
    linarith
  have hτ : tauD d₂ 𝕫 R = τ₁ := by
    refine gm_sInf_eq_of_agree (fun s hs => hs.1) (fun s hs => hs.1) ?_ hne hτT
    intro s hs
    simp only [mem_ofPred_eq, hfb s hs]
  exact ⟨⟨heq, fun u hu => (hball u hu).symm, hKU, hT⟩, hτ⟩

end LQGMetric.GM
