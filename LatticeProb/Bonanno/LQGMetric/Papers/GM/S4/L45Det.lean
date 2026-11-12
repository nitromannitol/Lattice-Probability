/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.GM.S4.L45Det at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Meas.LocalEventRandom2
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S4.L46MeasDet
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S4.SetupArc
import LatticeProb.Bonanno.LQGMetric.Metric.Midpoint
import LatticeProb.Bonanno.LQGMetric.Metric.Internal

/-!
# GM Lemma 4.5: deterministic locality of `𝓑^•_{t_k}`, its geodesics and arcs (task P2-E2R)

GM = Gwynne–Miller, arXiv:1905.00383, `uniqueness-final.tex`, l. 1654: "by Axiom II (locality),
`𝓘_k` is determined by `𝓑^•_{t_k}` and `h|_{𝓑^•_{t_k}}`", and l. 1665–1668 (`P|_{[0,s_k]}` is
determined by `(𝓑^•_{t_k}, h|)`). The deterministic content: if two length metrics `d₁, d₂` have
the same internal metric on an open `U ⊇ 𝓑^•_{t_k}(d₁)`, then

* `gm_tk_congr`: `τ_R`, and the balls `𝓑_s(𝕫)` for `s ≤ t_k = τ_R c`, agree (from the proof of
  `gm_candEvD_of_internal_eq`, P2-E3a);
* `gm_dist_congr`: `d₂(𝕫, w) = d₁(𝕫, w)` on `cl 𝓑_{t_k}`;
* `gm_isGeodesicL_congr`: geodesics from `𝕫` of length `≤ t_k` agree (lower bound by the
  triangle inequality at `𝕫`, upper bound through the internal metric of `U`,
  `internal_le_of_isGeod01`);
* `gm_isSideGeod_congr`, `gm_arcOf_congr`, `gm_confPts_congr`: leftmost geodesics, the arcs
  `arcOf` and `Conf_k` agree.

These are the saturation hypotheses of `LocalEvent.aeEventIn_localSigma_of_saturated` for the
objects of GM Lemma 4.5. Own elementary arguments (GM give none; DEVIATIONS entry proposed in
handoff/P2-E2R.md).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Filter Topology Set Metric
open scoped ENNReal
open LQGMetric.Blueprint

namespace LQGMetric.GM

/-- a `D`-geodesic contained in `V` bounds the internal metric (copy of P2-M2L's
`internal_le_of_isGeod01`, `Papers/GM/S5/Tubes55Det.lean`, whose module clashes with the S3
imports here) -/
theorem gm_internal_le_of_isGeod01' {D : ContMetric} {u v : ℂ} {η : C(unitInterval, ℂ)}
    {V : Set ℂ} (hη : IsGeod01 D u v η) (hV : range η ⊆ V) :
    D.internal V u v ≤ ENNReal.ofReal (D.1 (u, v)) := by
  set P : ℝ → D.Space := fun t => D.pt (η (Set.projIcc 0 1 zero_le_one t)) with hPdef
  have hd : ∀ s ∈ Icc (0 : ℝ) 1, ∀ t ∈ Icc (0 : ℝ) 1, dist (P s) (P t) ≤ D.1 (u, v) * dist s t := by
    intro s hs t ht
    have e1 : dist (P s) (P t) = D.1 (η (Set.projIcc 0 1 zero_le_one s),
      η (Set.projIcc 0 1 zero_le_one t)) := rfl
    rw [e1, hη.2.2, Set.projIcc_of_mem _ hs, Set.projIcc_of_mem _ ht, Real.dist_eq, abs_sub_comm,
      mul_comm]
  have hnn : 0 ≤ D.1 (u, v) := by
    have : dist (D.pt u) (D.pt v) = D.1 (u, v) := rfl
    rw [← this]; exact dist_nonneg
  obtain ⟨hc, hlen⟩ := MetricGeometry.curveLength_le_of_dist_le_mul hnn hd
  have h0 : P 0 = D.pt u := by
    simp only [hPdef, Set.projIcc_left]
    rw [← hη.1]; rfl
  have h1 : P 1 = D.pt v := by
    simp only [hPdef, Set.projIcc_right]
    rw [← hη.2.1]; rfl
  have hmaps : MapsTo P (Icc 0 1) (D.pt '' V) := fun t _ =>
    ⟨_, hV ⟨Set.projIcc 0 1 zero_le_one t, rfl⟩, rfl⟩
  have := MetricGeometry.internalEDist_le_curveLength zero_le_one hc hmaps
  rw [h0, h1] at this
  exact this.trans hlen

/-- **`t_k` and the balls up to `t_k` are local**: with `K = 𝓑^•_{τ_R c}(𝕫; d₁) ⊆ U` and equal
internal metrics on `U`, `τ_R(d₂) = τ_R(d₁)` and `𝓑_s(𝕫; d₂) = 𝓑_s(𝕫; d₁)` for `s ≤ τ_R c`. -/
theorem gm_tk_congr {d₁ d₂ : ContMetric} (h₁ : d₁.IsLength) (h₂ : d₂.IsLength) {𝕫 : ℂ}
    {R c : ℝ} (hc : 1 < c) {U : Set ℂ} (hU : IsOpen U) (heq : d₁.internal U = d₂.internal U)
    (hτpos : 0 < tauD d₁ 𝕫 R) (hKU : filledBall d₁ 𝕫 (tauD d₁ 𝕫 R * c) ⊆ U) :
    tauD d₂ 𝕫 R = tauD d₁ 𝕫 R ∧ ∀ s ≤ tauD d₁ 𝕫 R * c, ballM d₂ 𝕫 s = ballM d₁ 𝕫 s := by
  set τ₁ := tauD d₁ 𝕫 R with hτ₁
  have hτT : τ₁ < τ₁ * c := by nlinarith
  have hball : ∀ s ≤ τ₁ * c, ballM d₂ 𝕫 s = ballM d₁ 𝕫 s := by
    intro s hs
    rcases le_or_gt s 0 with hs0 | hs0
    · rw [gm_ballM_nonpos d₂ 𝕫 hs0, gm_ballM_nonpos d₁ 𝕫 hs0]
    · refine gm_ballM_eq_of_internal_eq h₁ h₂ hU (fun x _ y _ => by rw [heq]) hs0 ?_
      exact subset_closure.trans (subset_union_left.trans
        ((gm_filledBall_mono d₁ 𝕫 hs).trans hKU))
  have hfb : ∀ s ≤ τ₁ * c, filledBall d₂ 𝕫 s = filledBall d₁ 𝕫 s := fun s hs =>
    gm_filledBall_congr (hball s hs)
  have hne : {s | 0 < s ∧ ¬ filledBall d₁ 𝕫 s ⊆ Metric.ball 𝕫 R}.Nonempty := by
    by_contra hemp
    rw [not_nonempty_iff_eq_empty] at hemp
    have : τ₁ = 0 := by rw [hτ₁, tauD, hemp, Real.sInf_empty]
    linarith
  refine ⟨?_, hball⟩
  refine gm_sInf_eq_of_agree (fun s hs => hs.1) (fun s hs => hs.1) ?_ hne hτT
  intro s hs
  simp only [mem_ofPred_eq, hfb s hs]

lemma gm_dist_le_of_mem_closure (d : ContMetric) (𝕫 : ℂ) {T : ℝ} {w : ℂ}
    (hw : w ∈ closure (ballM d 𝕫 T)) : d.1 (𝕫, w) ≤ T :=
  closure_lt_subset_le (gm_continuous_distFrom d 𝕫) continuous_const hw

lemma gm_dist_le_of_ball_eq {d₁ d₂ : ContMetric} {𝕫 : ℂ} {T : ℝ}
    (hball : ∀ s ≤ T, ballM d₂ 𝕫 s = ballM d₁ 𝕫 s) {w : ℂ}
    (hw₁ : w ∈ closure (ballM d₁ 𝕫 T)) : d₂.1 (𝕫, w) ≤ d₁.1 (𝕫, w) := by
  rcases (gm_dist_le_of_mem_closure d₁ 𝕫 hw₁).lt_or_eq with hlt | heq
  · refine le_of_forall_gt fun s hs => ?_
    by_cases hsT : s ≤ T
    · have : w ∈ ballM d₁ 𝕫 s := hs
      rw [← hball s hsT] at this
      exact this
    · have : w ∈ ballM d₁ 𝕫 T := hlt
      rw [← hball T le_rfl] at this
      exact (show d₂.1 (𝕫, w) < T from this).trans (not_le.1 hsT)
  · rw [heq]
    rw [← hball T le_rfl] at hw₁
    exact gm_dist_le_of_mem_closure d₂ 𝕫 hw₁

/-- distances from `𝕫` agree on `cl 𝓑_T` when the balls up to `T` agree -/
theorem gm_dist_congr {d₁ d₂ : ContMetric} {𝕫 : ℂ} {T : ℝ}
    (hball : ∀ s ≤ T, ballM d₂ 𝕫 s = ballM d₁ 𝕫 s) {w : ℂ}
    (hw₁ : w ∈ closure (ballM d₁ 𝕫 T)) : d₂.1 (𝕫, w) = d₁.1 (𝕫, w) := by
  have hball' : ∀ s ≤ T, ballM d₁ 𝕫 s = ballM d₂ 𝕫 s := fun s hs => (hball s hs).symm
  have hw₂ : w ∈ closure (ballM d₂ 𝕫 T) := by rwa [hball T le_rfl]
  exact le_antisymm (gm_dist_le_of_ball_eq hball hw₁) (gm_dist_le_of_ball_eq hball' hw₂)

/-- **geodesics from `𝕫` of length `≤ T` are local** -/
theorem gm_isGeodesicL_of_congr {d₁ d₂ : ContMetric} {𝕫 : ℂ} {T : ℝ} (hT : 0 < T)
    (hball : ∀ s ≤ T, ballM d₂ 𝕫 s = ballM d₁ 𝕫 s) {U : Set ℂ}
    (hKU : closure (ballM d₁ 𝕫 T) ⊆ U) (heq : d₁.internal U = d₂.internal U)
    {P : ℝ → ℂ} {L : ℝ} {y : ℂ} (hP : IsGeodesicL d₁ P L 𝕫 y) (hLT : L ≤ T) :
    IsGeodesicL d₂ P L 𝕫 y := by
  -- the geodesic lies in `cl 𝓑_T(d₁)`
  have hmem : ∀ v ∈ Icc 0 L, P v ∈ closure (ballM d₁ 𝕫 T) := by
    intro v hv
    rcases hv.1.lt_or_eq with hv0 | hv0
    · exact gm_closure_ballM_mono d₁ 𝕫 (hv.2.trans hLT) (gm_geod_mem_closure_ballM hP hv0 hv.2)
    · rw [← hv0, hP.2.1]
      exact subset_closure (show d₁.1 (𝕫, 𝕫) < T by rw [d₁.2.self_eq_zero]; exact hT)
  have hd : ∀ v ∈ Icc 0 L, d₂.1 (𝕫, P v) = v := fun v hv => by
    rw [gm_dist_congr hball (hmem v hv), gm_geodL_dist hP hv]
  -- the key estimate for `s ≤ u`
  have key : ∀ s ∈ Icc 0 L, ∀ u ∈ Icc 0 L, s ≤ u → d₂.1 (P s, P u) = u - s := by
    intro s hs u hu hsu
    apply le_antisymm
    · -- upper bound through the internal metric of `U`
      set Q : ℝ → ℂ := fun v => P (s + v)
      have hQ : IsGeodesicL d₁ Q (u - s) (P s) (P u) := by
        refine ⟨by linarith, by simp [Q], by simp [Q], fun a ha b hb => ?_⟩
        simp only [Q]
        rw [hP.2.2.2 (s + a) ⟨by linarith [ha.1, hs.1], by linarith [ha.2, hu.2]⟩ (s + b)
          ⟨by linarith [hb.1, hs.1], by linarith [hb.2, hu.2]⟩]
        congr 1
        ring
      obtain ⟨η, hη, hηQ⟩ := gm_exists_geod01 hQ
      have hrange : range η ⊆ U := by
        rintro _ ⟨x, rfl⟩
        rw [hηQ x]
        refine hKU (hmem _ ⟨?_, ?_⟩)
        · have := mul_nonneg (sub_nonneg.2 hsu) x.2.1
          linarith [hs.1]
        · have := mul_le_of_le_one_right (sub_nonneg.2 hsu) x.2.2
          linarith [hu.2]
      have h1 := gm_internal_le_of_isGeod01' hη hrange
      have h2 : ENNReal.ofReal (d₂.1 (P s, P u)) ≤ d₂.internal U (P s) (P u) := by
        rw [← ContMetric.edist_pt]
        exact MetricGeometry.edist_le_internalEDist _ _ _
      rw [← heq] at h2
      have h3 := h2.trans h1
      rw [hP.2.2.2 s hs u hu, abs_of_nonneg (sub_nonneg.2 hsu)] at h3
      exact (ENNReal.ofReal_le_ofReal_iff (sub_nonneg.2 hsu)).1 h3
    · -- lower bound by the triangle inequality at `𝕫`
      have := d₂.2.triangle 𝕫 (P s) (P u)
      rw [hd u hu, hd s hs] at this
      linarith
  refine ⟨hP.1, hP.2.1, hP.2.2.1, fun s hs u hu => ?_⟩
  rcases le_total s u with hsu | hus
  · rw [key s hs u hu hsu, abs_of_nonneg (sub_nonneg.2 hsu)]
  · rw [d₂.2.symm, key u hu s hs hus, abs_sub_comm, abs_of_nonneg (sub_nonneg.2 hus)]

/-- the symmetric locality data: equal balls up to `T`, `cl 𝓑_T ⊆ U`, equal internal metrics -/
structure GMLocData (d₁ d₂ : ContMetric) (𝕫 : ℂ) (T : ℝ) (U : Set ℂ) : Prop where
  pos : 0 < T
  ball : ∀ s ≤ T, ballM d₂ 𝕫 s = ballM d₁ 𝕫 s
  sub : filledBall d₁ 𝕫 T ⊆ U
  int : d₁.internal U = d₂.internal U

theorem GMLocData.symm {d₁ d₂ : ContMetric} {𝕫 : ℂ} {T : ℝ} {U : Set ℂ}
    (H : GMLocData d₁ d₂ 𝕫 T U) : GMLocData d₂ d₁ 𝕫 T U :=
  ⟨H.pos, fun s hs => (H.ball s hs).symm,
    by rw [gm_filledBall_congr (H.ball T le_rfl)]; exact H.sub, H.int.symm⟩

theorem GMLocData.filledBall_eq {d₁ d₂ : ContMetric} {𝕫 : ℂ} {T : ℝ} {U : Set ℂ}
    (H : GMLocData d₁ d₂ 𝕫 T U) {s : ℝ} (hs : s ≤ T) : filledBall d₂ 𝕫 s = filledBall d₁ 𝕫 s :=
  gm_filledBall_congr (H.ball s hs)

theorem GMLocData.geod {d₁ d₂ : ContMetric} {𝕫 : ℂ} {T : ℝ} {U : Set ℂ}
    (H : GMLocData d₁ d₂ 𝕫 T U) {P : ℝ → ℂ} {L : ℝ} {y : ℂ} (hP : IsGeodesicL d₁ P L 𝕫 y)
    (hLT : L ≤ T) : IsGeodesicL d₂ P L 𝕫 y :=
  gm_isGeodesicL_of_congr H.pos H.ball (fun _ hx => H.sub (Or.inl hx)) H.int hP hLT

/-- **leftmost (side) geodesics to `∂𝓑^•_s`, `s ≤ T`, are local** -/
theorem GMLocData.sideGeod {d₁ d₂ : ContMetric} {𝕫 : ℂ} {T : ℝ} {U : Set ℂ}
    (H : GMLocData d₁ d₂ 𝕫 T U) {left : Bool} {s : ℝ} (hs : s ≤ T) {y : ℂ} {P : ℝ → ℂ}
    (hP : IsSideGeod left d₁ 𝕫 s y P) : IsSideGeod left d₂ 𝕫 s y P := by
  obtain ⟨hy, hPg, φ, hφ, t₀, hφt₀, t, Pn, ht, hside, hPn, hsup⟩ := hP
  refine ⟨by rw [H.filledBall_eq hs]; exact hy, H.geod hPg hs, φ,
    by rw [H.filledBall_eq hs]; exact hφ, t₀, hφt₀, t, Pn, ht, hside,
    fun n => H.geod (hPn n) hs, hsup⟩

/-- **the arcs `arcOf` of `∂𝓑^•_t`, `t ≤ T`, are local** (GM l. 1654) -/
theorem GMLocData.arcOf_eq {d₁ d₂ : ContMetric} {𝕫 : ℂ} {T : ℝ} {U : Set ℂ}
    (H : GMLocData d₁ d₂ 𝕫 T U) {t : ℝ} (ht : t ≤ T) (x : ℂ) :
    arcOf d₂ 𝕫 t x = arcOf d₁ 𝕫 t x := by
  ext y
  simp only [arcOf, mem_ofPred_eq, H.filledBall_eq ht]
  constructor
  · rintro ⟨hy, Q, hQ, hx⟩
    exact ⟨hy, Q, H.symm.sideGeod ht hQ, hx⟩
  · rintro ⟨hy, Q, hQ, hx⟩
    exact ⟨hy, Q, H.sideGeod ht hQ, hx⟩

/-- **`Conf_k` is local** -/
theorem GMLocData.confPts_eq {d₁ d₂ : ContMetric} {𝕫 : ℂ} {T : ℝ} {U : Set ℂ}
    (H : GMLocData d₁ d₂ 𝕫 T U) {s t : ℝ} (hs : s ≤ T) (ht : t ≤ T) :
    confPts d₂ 𝕫 s t = confPts d₁ 𝕫 s t := by
  ext x
  simp only [confPts, hitSet, mem_ofPred_eq, H.filledBall_eq hs]
  constructor
  · rintro ⟨hx, y, Q, hQ, hu⟩
    exact ⟨hx, y, Q, H.symm.sideGeod ht hQ, hu⟩
  · rintro ⟨hx, y, Q, hQ, hu⟩
    exact ⟨hx, y, Q, H.sideGeod ht hQ, hu⟩

/-- **the locality data at `t_k`** from equal internal metrics on `U ⊇ 𝓑^•_{t_k}` -/
theorem gm_locData_tk {d₁ d₂ : ContMetric} (h₁ : d₁.IsLength) (h₂ : d₂.IsLength) {𝕫 : ℂ}
    {R c : ℝ} (hc : 1 < c) {U : Set ℂ} (hU : IsOpen U) (heq : d₁.internal U = d₂.internal U)
    (hτpos : 0 < tauD d₁ 𝕫 R) (hKU : filledBall d₁ 𝕫 (tauD d₁ 𝕫 R * c) ⊆ U) :
    tauD d₂ 𝕫 R = tauD d₁ 𝕫 R ∧ GMLocData d₁ d₂ 𝕫 (tauD d₁ 𝕫 R * c) U := by
  obtain ⟨hτ, hball⟩ := gm_tk_congr h₁ h₂ hc hU heq hτpos hKU
  exact ⟨hτ, ⟨mul_pos hτpos (by linarith), hball, hKU, heq⟩⟩

end LQGMetric.GM
