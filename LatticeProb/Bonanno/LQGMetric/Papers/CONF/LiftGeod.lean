/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.CONF.LiftGeod at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.CONF.Lift

/-!
# CONF §2 small nodes: S-geod-level, S-right-antisymm, S-left-restr, S-unique-left

Decision D-D1 (`decisions/DEC-D.md` (a), "Theorems the CONF §2 package proves"). Source:
Gwynne–Miller, *Confluence of geodesics in LQG*, arXiv:1905.00381 (CONF),
`literature/src/1905.00381/confluence-final.tex`.

* **S-geod-level** (`geodLevel_frontier`, `geodLevel_mapsTo`, `geodLevel_ne`): a geodesic from
  `z` to `y ∈ ∂𝓑^•_s` crosses `∂𝓑^•_t` at time `t` and stays in `𝓑^•_s ∖ int 𝓑^•_t` after it
  (DEC-D (a) finding 3). The two auxiliary lemmas `cl_not_mem_filledBall_of_frontier`,
  `cl_geod_mem_frontier` are copies of `gm_not_mem_filledBall_of_frontier`,
  `gm_geod_mem_frontier` (`Papers/GM/S4/Setup.lean`, task WP-M2g, own elementary proof), copied
  so that this package does not import an unbuilt module of another task.
* **S-right-antisymm** (`right_antisymm`) and reflexivity (`weaklyRightOf_of_eqOn`).
* **S-unique-left** (`isLeftmost_of_unique`): GM l. 1673 "unique (hence also leftmost)".
* **S-left-restr** (`isLeftmost_restr`): CONF l. 554, "the concatenation of `P^-_{P^-_x(t)}` and
  `P^-_x|_{[t,s]}` is a `D_h`-geodesic which lies (weakly) to the left of `P^-_x`" — CONF's
  argument: concatenate, compare at level `s`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set

namespace LQGMetric.CONF.DD

open LQGMetric.Blueprint

section Det
variable {D : ContMetric} {z x y w : ℂ} {P Q : ℝ → ℂ} {L s t : ℝ}

theorem cl_geodL_continuousOn (hP : IsGeodesicL D P L z y) : ContinuousOn P (Icc 0 L) := by
  intro a ha
  rw [Metric.continuousWithinAt_iff]
  intro ε hε
  obtain ⟨δ, hδ, hδε⟩ := D.2.euclidean_of_small (P a) ε hε
  refine ⟨δ, hδ, fun {b} hb hab => ?_⟩
  rw [dist_comm, dist_eq_norm]
  apply hδε
  rw [hP.2.2.2 a ha b hb]
  rwa [Real.dist_eq] at hab

theorem cl_geodL_dist (hP : IsGeodesicL D P L z y) {u : ℝ} (hu : u ∈ Icc 0 L) :
    D.1 (z, P u) = u := by
  have := hP.2.2.2 0 ⟨le_rfl, hP.1⟩ u hu
  rw [hP.2.1, sub_zero, abs_of_nonneg hu.1] at this
  exact this

theorem cl_continuous_distFrom (D : ContMetric) (z : ℂ) : Continuous fun w => D.1 (z, w) :=
  (map_continuous D.1).comp (Continuous.prodMk_right z)

theorem cl_closure_ballM_subset (D : ContMetric) (z : ℂ) (s : ℝ) :
    closure (ballM D z s) ⊆ {w | D.1 (z, w) ≤ s} :=
  closure_minimal (fun w (hw : D.1 (z, w) < s) => show D.1 (z, w) ≤ s from hw.le)
    (isClosed_le (cl_continuous_distFrom D z) continuous_const)

theorem cl_closure_ballM_mono (D : ContMetric) (z : ℂ) {s t : ℝ} (hst : s ≤ t) :
    closure (ballM D z s) ⊆ closure (ballM D z t) :=
  closure_mono (fun _ hw => lt_of_lt_of_le hw hst)

/-- copy of `gm_not_mem_filledBall_of_frontier` (`Papers/GM/S4/Setup.lean`) -/
theorem cl_not_mem_filledBall_of_frontier (hyd : D.1 (z, y) = t)
    (hy : y ∈ frontier (filledBall D z t)) (hst : s < t) : y ∉ filledBall D z s := by
  have hyc : y ∉ closure (ballM D z s) := fun h' => by
    have := cl_closure_ballM_subset D z s h'
    simp only [mem_setOf_eq, hyd] at this
    linarith
  have hopen : IsOpen (connectedComponentIn (closure (ballM D z s))ᶜ y) :=
    isClosed_closure.isOpen_compl.connectedComponentIn
  have hyy : y ∈ connectedComponentIn (closure (ballM D z s))ᶜ y := mem_connectedComponentIn hyc
  have hcl : y ∈ closure (filledBall D z t)ᶜ := by
    rw [← frontier_compl] at hy
    exact frontier_subset_closure hy
  obtain ⟨p, hp1, hp2⟩ := mem_closure_iff.mp hcl _ hopen hyy
  have hpt : p ∉ closure (ballM D z t) ∧
      ¬ Bornology.IsBounded (connectedComponentIn (closure (ballM D z t))ᶜ p) := by
    simp only [filledBall, mem_compl_iff, mem_union, mem_setOf_eq, not_or, not_and] at hp2
    exact ⟨hp2.1, hp2.2 hp2.1⟩
  have heq := connectedComponentIn_eq hp1
  rintro (h' | ⟨_, hb⟩)
  · exact hyc h'
  · apply hpt.2
    refine hb.subset ?_
    rw [heq]
    exact connectedComponentIn_mono p (compl_subset_compl.mpr (cl_closure_ballM_mono D z hst.le))

/-- a geodesic at time `u ∈ (0, L]` lies in `cl 𝓑_u` -/
theorem cl_geod_mem_closure (hP : IsGeodesicL D P L z y) {u : ℝ} (hu : 0 < u) (huL : u ≤ L) :
    P u ∈ closure (ballM D z u) := by
  have hc := cl_geodL_continuousOn hP
  have hcw : ContinuousWithinAt P (Ico 0 u) u :=
    (hc u ⟨hu.le, huL⟩).mono (fun r hr => ⟨hr.1, hr.2.le.trans huL⟩)
  have hmem : u ∈ closure (Ico 0 u) := by rw [closure_Ico hu.ne]; exact ⟨hu.le, le_rfl⟩
  refine closure_mono ?_ (hcw.mem_closure_image hmem)
  rintro _ ⟨r, hr, rfl⟩
  show D.1 (z, P r) < u
  rw [cl_geodL_dist hP ⟨hr.1, hr.2.le.trans huL⟩]
  exact hr.2

/-- copy of `gm_geod_mem_frontier` (`Papers/GM/S4/Setup.lean`) -/
theorem cl_geod_mem_frontier (hP : IsGeodesicL D P L z y) (hs : 0 < s) (hsL : s < L)
    (hy : y ∉ filledBall D z s) : P s ∈ frontier (filledBall D z s) := by
  have hc := cl_geodL_continuousOn hP
  have hsI : s ∈ Icc 0 L := ⟨hs.le, hsL.le⟩
  have h1 : P s ∈ closure (ballM D z s) := cl_geod_mem_closure hP hs hsL.le
  have hyc : y ∉ closure (ballM D z s) := fun h' => hy (Or.inl h')
  have hyb : ¬ Bornology.IsBounded (connectedComponentIn (closure (ballM D z s))ᶜ y) :=
    fun hb => hy (Or.inr ⟨hyc, hb⟩)
  have hsub : P '' Ioc s L ⊆ (closure (ballM D z s))ᶜ := by
    rintro _ ⟨u, hu, rfl⟩ h'
    have := cl_closure_ballM_subset D z s h'
    simp only [mem_setOf_eq] at this
    rw [cl_geodL_dist hP ⟨hs.le.trans hu.1.le, hu.2⟩] at this
    linarith [hu.1]
  have hconn : IsPreconnected (P '' Ioc s L) :=
    isPreconnected_Ioc.image P (hc.mono (fun u hu => ⟨hs.le.trans hu.1.le, hu.2⟩))
  have hyL : y ∈ P '' Ioc s L := ⟨L, ⟨hsL, le_rfl⟩, hP.2.2.1⟩
  have hcc := hconn.subset_connectedComponentIn hyL hsub
  have h2 : P '' Ioc s L ⊆ (filledBall D z s)ᶜ := by
    intro x hx
    rintro (h' | ⟨_, hb⟩)
    · exact hsub hx h'
    · apply hyb
      rwa [connectedComponentIn_eq (hcc hx)]
  have h3 : P s ∈ closure (filledBall D z s)ᶜ := by
    have hcw : ContinuousWithinAt P (Ioc s L) s :=
      (hc s hsI).mono (fun u hu => ⟨hs.le.trans hu.1.le, hu.2⟩)
    have hmem : s ∈ closure (Ioc s L) := by rw [closure_Ioc hsL.ne]; exact ⟨le_rfl, hsL.le⟩
    exact closure_mono h2 (hcw.mem_closure_image hmem)
  rw [closure_compl] at h3
  exact ⟨subset_closure (Or.inl h1), h3⟩

/-! ## S-geod-level -/

/-- **S-geod-level** (i): `P t ∈ ∂𝓑^•_t` for `0 < t ≤ s` -/
theorem geodLevel_frontier (hP : IsGeodesicL D P s z y) (hy : y ∈ frontier (filledBall D z s))
    (ht : 0 < t) (hts : t ≤ s) : P t ∈ frontier (filledBall D z t) := by
  rcases hts.lt_or_eq with hlt | rfl
  · exact cl_geod_mem_frontier hP ht hlt
      (cl_not_mem_filledBall_of_frontier (cl_geodL_dist hP ⟨hP.1, le_rfl⟩ ▸ hP.2.2.1 ▸ rfl) hy hlt)
  · rwa [hP.2.2.1]

/-- **S-geod-level** (iii): `P u ≠ z` for `u ∈ (0, s]` -/
theorem geodLevel_ne (hP : IsGeodesicL D P s z y) {u : ℝ} (hu : 0 < u) (hus : u ≤ s) :
    P u ≠ z := by
  intro h
  have := cl_geodL_dist hP ⟨hu.le, hus⟩
  rw [h, D.2.self_eq_zero] at this
  linarith

/-- **S-geod-level** (ii): `P '' [t, s] ⊆ 𝓑^•_s ∖ int 𝓑^•_t` for `0 < t ≤ s` -/
theorem geodLevel_mapsTo (hP : IsGeodesicL D P s z y) (hy : y ∈ frontier (filledBall D z s))
    (ht : 0 < t) (hts : t ≤ s) :
    MapsTo P (Icc t s) (filledBall D z s \ interior (filledBall D z t)) := by
  intro u hu
  have hu0 : 0 < u := ht.trans_le hu.1
  refine ⟨Or.inl (cl_closure_ballM_mono D z hu.2 (cl_geod_mem_closure hP hu0 hu.2)), ?_⟩
  rcases hu.1.lt_or_eq with hlt | rfl
  · have hfr := geodLevel_frontier hP hy hu0 hu.2
    exact fun h => cl_not_mem_filledBall_of_frontier (cl_geodL_dist hP ⟨hu0.le, hu.2⟩) hfr hlt
      (interior_subset h)
  · exact (geodLevel_frontier hP hy ht hts).2

/-! ## Lifts of geodesics -/

/-- angle lifts of two geodesics to `y` on `[t, s]` with equal endpoint angle, and their
positions on a positive Jordan lift of `∂𝓑^•_t` -/
theorem exists_lifts_pos (hP : IsGeodesicL D P s z y) (hQ : IsGeodesicL D Q s z y)
    (hy : y ∈ frontier (filledBall D z s)) (ht : t ∈ Ioo 0 s) {φ : ℝ → ℂ} {θ : ℝ → ℝ}
    (hφ : IsPosJordanLift (frontier (filledBall D z t)) z φ θ) :
    ∃ α β : ℝ → ℝ, IsAngleLift z P t s α ∧ IsAngleLift z Q t s β ∧ α s = β s ∧
      ∃ u v : ℝ, φ u = P t ∧ θ u = α t ∧ φ v = Q t ∧ θ v = β t := by
  have hts : t ≤ s := ht.2.le
  have hne : ∀ {R : ℝ → ℂ}, IsGeodesicL D R s z y → ∀ u ∈ Icc t s, R u ≠ z :=
    fun hR u hu => geodLevel_ne hR (ht.1.trans_le hu.1) hu.2
  have hsub : Icc t s ⊆ Icc 0 s := Icc_subset_Icc_left ht.1.le
  obtain ⟨α, hα⟩ := exists_angleLift hts ((cl_geodL_continuousOn hP).mono hsub) (hne hP)
  obtain ⟨β₀, hβ₀⟩ := exists_angleLift hts ((cl_geodL_continuousOn hQ).mono hsub) (hne hQ)
  have hsI : s ∈ Icc t s := ⟨hts, le_rfl⟩
  have hyz : y - z ≠ 0 := sub_ne_zero.2 (hP.2.2.1 ▸ hne hP s hsI)
  have hPs := hα.2 s hsI
  have hQs := hβ₀.2 s hsI
  rw [hP.2.2.1] at hPs
  rw [hQ.2.2.1] at hQs
  obtain ⟨n, hn⟩ := isAngle_sub hyz hPs hQs
  have hβ := hβ₀.add_int n
  have htI : t ∈ Icc t s := ⟨le_rfl, hts⟩
  obtain ⟨u, hu1, hu2⟩ := hφ.exists_pos (geodLevel_frontier hP hy ht.1 hts)
    (hne hP t htI) (hα.2 t htI)
  obtain ⟨v, hv1, hv2⟩ := hφ.exists_pos (geodLevel_frontier hQ hy ht.1 hts)
    (hne hQ t htI) (hβ.2 t htI)
  exact ⟨α, _, hα, hβ, by show α s = β₀ s + n * (2 * Real.pi); linarith, u, v, hu1, hu2, hv1, hv2⟩

/-- **S-right-antisymm** (D-D1; given S-PosLift at the levels `t ∈ (0, s)`) -/
theorem right_antisymm (hP : IsGeodesicL D P s z y) (hQ : IsGeodesicL D Q s z y)
    (hy : y ∈ frontier (filledBall D z s))
    (hpos : ∀ t ∈ Ioo 0 s, ∃ φ θ, IsPosJordanLift (frontier (filledBall D z t)) z φ θ)
    (h₁ : WeaklyRightOf D z s Q P) (h₂ : WeaklyRightOf D z s P Q) : EqOn P Q (Icc 0 s) := by
  intro t ht
  rcases ht.1.lt_or_eq with h0 | rfl
  · rcases ht.2.lt_or_eq with hs | rfl
    · obtain ⟨φ, θ, hφ⟩ := hpos t ⟨h0, hs⟩
      obtain ⟨α, β, hα, hβ, hαβ, u, v, hu1, hu2, hv1, hv2⟩ :=
        exists_lifts_pos hP hQ hy ⟨h0, hs⟩ hφ
      have huv := h₁ t ⟨h0, hs⟩ φ θ hφ α β hα hβ hαβ u v hu1 hu2 hv1 hv2
      have hvu := h₂ t ⟨h0, hs⟩ φ θ hφ β α hβ hα hαβ.symm v u hv1 hv2 hu1 hu2
      rw [← hu1, ← hv1, le_antisymm huv hvu]
    · rw [hP.2.2.1, hQ.2.2.1]
  · rw [hP.2.1, hQ.2.1]

/-- reflexivity of `WeaklyRightOf` (up to equality on `[0, s]`) -/
theorem weaklyRightOf_of_eqOn (hP : IsGeodesicL D P s z y) (hQP : EqOn Q P (Icc 0 s)) :
    WeaklyRightOf D z s Q P := by
  intro t ht φ θ hφ α β hα hβ hαβ u v hu1 hu2 hv1 hv2
  have hsub : Icc t s ⊆ Icc 0 s := Icc_subset_Icc_left ht.1.le
  have hβP : IsAngleLift z P t s β :=
    ⟨hβ.1, fun r hr => by rw [← hQP (hsub hr)]; exact hβ.2 r hr⟩
  have hne : ∀ r ∈ Icc t s, P r ≠ z := fun r hr => geodLevel_ne hP (ht.1.trans_le hr.1) hr.2
  have heq := angleLift_eqOn hα hβP hne ⟨ht.2.le, le_rfl⟩ hαβ ⟨le_rfl, ht.2.le⟩
  have : v = u := hφ.pos_unique (by rw [hv1, hu1, hQP (hsub ⟨le_rfl, ht.2.le⟩)])
    (by rw [hv2, hu2, heq])
  exact this.le

/-- **S-unique-left** (D-D1; GM l. 1673 "unique (hence also leftmost)") -/
theorem isLeftmost_of_unique (hy : y ∈ frontier (filledBall D z s))
    (hP : IsGeodesicL D P s z y) (huniq : ∀ Q, IsGeodesicL D Q s z y → EqOn Q P (Icc 0 s)) :
    IsLeftmostGeod D z s y P :=
  ⟨hy, hP, fun Q hQ => by
    show WeaklyRightOf D z s Q P
    exact weaklyRightOf_of_eqOn hP (huniq Q hQ)⟩

/-! ## S-left-restr -/

/-- concatenation of a geodesic `Q` to `P t` with `P|[t, s]` is a geodesic (CONF l. 526, 554) -/
theorem concat_geod (hQ : IsGeodesicL D Q t z w) (hP : IsGeodesicL D P s z x) (ht : 0 ≤ t)
    (hts : t ≤ s) (hw : P t = w) :
    IsGeodesicL D (fun r => if r ≤ t then Q r else P r) s z x := by
  have key : ∀ a ∈ Icc 0 t, ∀ b ∈ Icc t s, D.1 (Q a, P b) = b - a := by
    intro a ha b hb
    apply le_antisymm
    · have h1 := D.2.triangle (Q a) (Q t) (P b)
      rw [hQ.2.2.2 a ha t ⟨ht, le_rfl⟩, hQ.2.2.1, ← hw, hP.2.2.2 t ⟨ht, hts⟩ b ⟨ht.trans hb.1, hb.2⟩,
        abs_of_nonneg (by linarith [ha.2]), abs_of_nonneg (by linarith [hb.1])] at h1
      linarith
    · have h1 := D.2.triangle z (Q a) (P b)
      rw [cl_geodL_dist hP ⟨ht.trans hb.1, hb.2⟩, cl_geodL_dist hQ ha] at h1
      linarith
  refine ⟨ht.trans hts, by simp [ht, hQ.2.1], ?_, fun a ha b hb => ?_⟩
  · by_cases h : s ≤ t
    · have : s = t := le_antisymm h hts
      simp only [h, if_true]; rw [this, hQ.2.2.1, ← hw, ← this, hP.2.2.1]
    · simp only [h, if_false, hP.2.2.1]
  · by_cases hat : a ≤ t <;> by_cases hbt : b ≤ t <;> simp only [hat, hbt, if_true, if_false]
    · exact hQ.2.2.2 a ⟨ha.1, hat⟩ b ⟨hb.1, hbt⟩
    · rw [key a ⟨ha.1, hat⟩ b ⟨(not_le.1 hbt).le, hb.2⟩, abs_of_nonneg (by linarith)]
    · rw [D.2.symm, key b ⟨hb.1, hbt⟩ a ⟨(not_le.1 hat).le, ha.2⟩, abs_of_nonpos (by linarith)]
      ring
    · exact hP.2.2.2 a ha b hb

/-- gluing angle lifts -/
theorem IsAngleLift.glue {z : ℂ} {P Q : ℝ → ℂ} {a b c : ℝ} {α β : ℝ → ℝ} (hab : a ≤ b)
    (hbc : b ≤ c) (hα : IsAngleLift z P a b α) (hβ : IsAngleLift z Q b c β) (hαβ : α b = β b) :
    IsAngleLift z (fun r => if r ≤ b then P r else Q r) a c
      (fun r => if r ≤ b then α r else β r) := by
  refine ⟨continuousOn_glue hab hbc hα.1 hβ.1 hαβ, fun r hr => ?_⟩
  by_cases h : r ≤ b
  · simp only [h, if_true]; exact hα.2 r ⟨hr.1, h⟩
  · simp only [h, if_false]; exact hβ.2 r ⟨(not_le.1 h).le, hr.2⟩

/-- **S-left-restr** (CONF l. 554) -/
theorem isLeftmost_restr (hl : IsLeftmostGeod D z s x P) (ht : 0 < t) (hts : t < s) :
    IsLeftmostGeod D z t (P t) P := by
  obtain ⟨hx, hP, hleft⟩ := hl
  refine ⟨geodLevel_frontier hP hx ht hts.le, ⟨ht.le, hP.2.1, rfl, fun a ha b hb =>
    hP.2.2.2 a ⟨ha.1, ha.2.trans hts.le⟩ b ⟨hb.1, hb.2.trans hts.le⟩⟩, fun Q hQ => ?_⟩
  show WeaklyRightOf D z t Q P
  intro t' ht' φ θ hφ α β hα hβ hαβ u v hu1 hu2 hv1 hv2
  have hPt : P t ≠ z := geodLevel_ne hP ht hts.le
  obtain ⟨γ, hγ⟩ := exists_angleLift hts.le ((cl_geodL_continuousOn hP).mono
    (Icc_subset_Icc_left ht.le)) (fun r hr => geodLevel_ne hP (ht.trans_le hr.1) hr.2)
  have htI : t ∈ Icc t' t := ⟨ht'.2.le, le_rfl⟩
  obtain ⟨n, hn⟩ := isAngle_sub (sub_ne_zero.2 hPt) (hα.2 t htI) (hγ.2 t ⟨le_rfl, hts.le⟩)
  have hγ' := hγ.add_int n
  have hα' := hα.glue ht'.2.le hts.le hγ' (by show α t = γ t + n * (2 * Real.pi); linarith)
  have hβ' := hβ.glue ht'.2.le hts.le hγ'
    (by show β t = γ t + n * (2 * Real.pi); linarith)
  simp only [ite_self] at hα'
  have hQ' := concat_geod hQ hP ht.le hts.le rfl
  have hW : WeaklyRightOf D z s (fun r => if r ≤ t then Q r else P r) P := by
    have := hleft _ hQ'; simpa using this
  have h't : t' ≤ t := ht'.2.le
  exact hW t' ⟨ht'.1, ht'.2.trans hts⟩ φ θ hφ _ _ hα' hβ'
    (by simp only [not_le.2 hts, if_false]) u v hu1 (by simp only [h't, if_true]; exact hu2)
    (by simp only [h't, if_true]; exact hv1) (by simp only [h't, if_true]; exact hv2)

end Det

end LQGMetric.CONF.DD
