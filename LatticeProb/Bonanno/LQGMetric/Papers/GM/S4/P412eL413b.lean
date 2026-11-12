/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.GM.S4.P412eL413b at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S4.P412eL413
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S4.JordanBasic
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S4.P412eAccess

/-!
# GM Lemma 4.13′: the set `X = X₀ ∪ P((s,t])` (l. 2075–2081)

Source: GM = `literature/src/1905.00383/uniqueness-final.tex`, proof of Lemma 4.13
(`lem-geo-disconnect`), l. 2075–2081, with `𝓑^•_s = filledBall`, `d^U = dU` (closures, D86 (2)).

* `p412e_geod_eucl_pair`: Euclidean diameter of `P([s,t])` (l. 2079), pairwise form.
* `p412e_geod_after`, `p412e_geod_before`: `P((s,L]) ∩ 𝓑^•_s = ∅`, `P([0,s)) ⊆ 𝓑^•_s`.
* `p412e_L413_build` (l. 2077–2080): `X := X₀ ∪ P((s,t]) ⊆ ℂ ∖ 𝓑^•_s` is connected, has
  Euclidean diameter `≤ d + (d/𝕣)^{χ/χ'}𝕣` and its closure contains `P(s)` and `v`.
* `p412e_L413_X` (l. 2075–2081): from `d^{ℂ∖𝓑^•_s}(P(u₀), v) < ε𝕣` (`v ∈ ∂𝓑^•_s`): a connected
  `X ⊆ ℂ ∖ 𝓑^•_s` of diameter `≤ 2ε^{χ/χ'}𝕣` with `P(s), v ∈ cl X`. With the strict inequality
  GM's auxiliary `δ` is not needed (`ε + ε^{χ/χ'} ≤ 2ε^{χ/χ'}` for `ε ≤ 1`). GM's "possibly
  shrinking `X₀`" (single prime end) and the separation (l. 2081–2082) are not part of this file.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter Topology Metric
open LQGMetric.MetricGeometry LQGMetric.Blueprint
open scoped ENNReal

namespace LQGMetric.GM

/-- GM l. 2079, pairwise form -/
theorem p412e_geod_eucl_pair {Ω : Type} {D : DistC → ContMetric} {h : Ω → DistC} {R : RegPar}
    {𝕣 a : ℝ} (h𝕣 : 0 < 𝕣) (ha : 0 < a) (hχ' : 0 < R.χ') {ω : Ω} (hω : ω ∈ regC3 D h R 𝕣 a)
    (hs : 0 < scaleFac R.ξ R.c (h ω) 𝕣 0) {P : ℝ → ℂ} {L : ℝ} {𝕫 y : ℂ}
    (hP : IsGeodesicL (D (h ω)) P L 𝕫 y) (hPc : ContinuousOn P (Icc 0 L)) {s t : ℝ}
    (hs0 : 0 ≤ s) (htL : t ≤ L) (hreg : ∀ u ∈ Icc s t, P u ∈ regRegion R 𝕣)
    (hsmall : (t - s) / scaleFac R.ξ R.c (h ω) 𝕣 0 < a ^ R.χ') :
    ∀ u ∈ Icc s t, ∀ u' ∈ Icc s t,
      ‖P u - P u'‖ ≤ ((t - s) / scaleFac R.ξ R.c (h ω) 𝕣 0) ^ (1 / R.χ') * 𝕣 := by
  have key : ∀ u ∈ Icc s t, ∀ u' ∈ Icc s t, u' ≤ u →
      ‖P u - P u'‖ ≤ ((t - s) / scaleFac R.ξ R.c (h ω) 𝕣 0) ^ (1 / R.χ') * 𝕣 := by
    intro u hu u' hu' hle
    have hmono : (u - u') / scaleFac R.ξ R.c (h ω) 𝕣 0 ≤ (t - s) / scaleFac R.ξ R.c (h ω) 𝕣 0 :=
      div_le_div_of_nonneg_right (by linarith [hu.2, hu'.1]) hs.le
    have H := p412e_geod_eucl h𝕣 ha hχ' hω hs hP hPc (hs0.trans hu'.1) hle (hu.2.trans htL)
      (fun v hv => hreg v ⟨hu'.1.trans hv.1, hv.2.trans hu.2⟩) (hmono.trans_lt hsmall) u
      ⟨hle, le_rfl⟩
    refine H.trans (mul_le_mul_of_nonneg_right ?_ h𝕣.le)
    exact Real.rpow_le_rpow (div_nonneg (by linarith) hs.le) hmono (by positivity)
  intro u hu u' hu'
  rcases le_total u' u with h | h
  · exact key u hu u' hu' h
  · rw [norm_sub_rev]; exact key u' hu' u hu h

section Det
variable {D : ContMetric} {P : ℝ → ℂ} {L : ℝ} {𝕫 y : ℂ} {s : ℝ}

/-- a geodesic from `𝕫` to `y ∉ 𝓑^•_s` stays outside `𝓑^•_s` after time `s` -/
theorem p412e_geod_after (hP : IsGeodesicL D P L 𝕫 y) (hs : 0 < s) (hsL : s < L)
    (hy : y ∉ filledBall D 𝕫 s) : ∀ u ∈ Ioc s L, P u ∉ filledBall D 𝕫 s := by
  have hc := gm_geodL_continuousOn hP
  have hyc : y ∉ closure (ballM D 𝕫 s) := fun h' => hy (Or.inl h')
  have hyb : ¬ Bornology.IsBounded (connectedComponentIn (closure (ballM D 𝕫 s))ᶜ y) :=
    fun hb => hy (Or.inr ⟨hyc, hb⟩)
  have hsub : P '' Ioc s L ⊆ (closure (ballM D 𝕫 s))ᶜ := by
    rintro _ ⟨u, hu, rfl⟩ h'
    have := gm_closure_ballM_subset D 𝕫 s h'
    simp only [mem_setOf_eq] at this
    rw [gm_geodL_dist hP ⟨hs.le.trans hu.1.le, hu.2⟩] at this
    linarith [hu.1]
  have hconn : IsPreconnected (P '' Ioc s L) :=
    isPreconnected_Ioc.image P (hc.mono (fun u hu => ⟨hs.le.trans hu.1.le, hu.2⟩))
  have hyL : y ∈ P '' Ioc s L := ⟨L, ⟨hsL, le_rfl⟩, hP.2.2.1⟩
  have hcc := hconn.subset_connectedComponentIn hyL hsub
  intro u hu
  have hx : P u ∈ P '' Ioc s L := ⟨u, hu, rfl⟩
  rintro (h' | ⟨_, hb⟩)
  · exact hsub hx h'
  · apply hyb
    rwa [connectedComponentIn_eq (hcc hx)]

/-- a geodesic from `𝕫` is in `𝓑^•_s` before time `s` -/
theorem p412e_geod_before (hP : IsGeodesicL D P L 𝕫 y) {u : ℝ} (hu : u ∈ Icc 0 L) (hus : u < s) :
    P u ∈ filledBall D 𝕫 s := by
  refine Or.inl (subset_closure ?_)
  show D.1 (𝕫, P u) < s
  rw [gm_geodL_dist hP hu]; exact hus

end Det

/-- **GM L4.13′, construction of `X`** (l. 2077–2080) -/
theorem p412e_L413_build {Ω : Type} {D : DistC → ContMetric} {h : Ω → DistC} {R : RegPar}
    {𝕣 a : ℝ} (h𝕣 : 0 < 𝕣) (ha : 0 < a) (hχ : 0 < R.χ) (hχ' : 0 < R.χ') (hc : 0 < R.c 𝕣)
    {ω : Ω} (hω : ω ∈ regC3 D h R 𝕣 a) {P : ℝ → ℂ} {L : ℝ} {𝕫 y : ℂ}
    (hP : IsGeodesicL (D (h ω)) P L 𝕫 y) {s : ℝ} (hs : 0 < s) (hsL : s < L)
    (hbd : Bornology.IsBounded (ballM (D (h ω)) 𝕫 s)) (hy : y ∉ filledBall (D (h ω)) 𝕫 s)
    {X₀ : Set ℂ} (hX₀K : X₀ ⊆ (filledBall (D (h ω)) 𝕫 s)ᶜ) (hX₀c : IsConnected X₀)
    {t : ℝ} (htL : t ∈ Icc 0 L) (htX : P t ∈ X₀) {v : ℂ}
    (hv : v ∈ frontier (filledBall (D (h ω)) 𝕫 s)) (hvX : v ∈ closure X₀) {d : ℝ}
    (hXd : ∀ w ∈ X₀, ∀ w' ∈ X₀, ‖w - w'‖ ≤ d) (hda : d ≤ a * 𝕣)
    (hsmall : (d / 𝕣) ^ R.χ < a ^ R.χ') (hXreg : X₀ ⊆ regRegion R 𝕣)
    (hreg : ∀ u ∈ Icc s L, u ≤ s + scaleFac R.ξ R.c (h ω) 𝕣 0 * (d / 𝕣) ^ R.χ →
      P u ∈ regRegion R 𝕣) :
    ∃ X ⊆ (filledBall (D (h ω)) 𝕫 s)ᶜ, IsConnected X ∧
      (∀ w ∈ X, ∀ w' ∈ X, ‖w - w'‖ ≤ d + (d / 𝕣) ^ (R.χ / R.χ') * 𝕣) ∧
      P s ∈ closure X ∧ v ∈ closure X ∧
      closure X ∩ filledBall (D (h ω)) 𝕫 s ⊆ (closure X₀ ∩ filledBall (D (h ω)) 𝕫 s) ∪ {P s} := by
  set K := filledBall (D (h ω)) 𝕫 s with hKdef
  have hS : 0 < scaleFac R.ξ R.c (h ω) 𝕣 0 := by unfold scaleFac; positivity
  set S := scaleFac R.ξ R.c (h ω) 𝕣 0
  have hKc : IsClosed K := jb_isClosed_filledBall hbd
  have hPc := gm_geodL_continuousOn hP
  have hd0 : 0 ≤ d := by have := hXd _ htX _ htX; rwa [sub_self, norm_zero] at this
  -- `t > s`
  have hst : s < t := by
    by_contra hle; push_neg at hle
    rcases eq_or_lt_of_le hle with heq | hlt
    · exact hX₀K (heq ▸ htX) (hKc.frontier_subset (gm_geod_mem_frontier hP hs hsL hy))
    · exact hX₀K htX (p412e_geod_before hP htL hlt)
  -- the time bound (l. 2078)
  have hvd : (D (h ω)).1 (𝕫, v) ≤ s := gm_closure_ballM_subset _ _ _ (jb_frontier_subset_closure hbd hv)
  have htime : t - s ≤ S * (d / 𝕣) ^ R.χ :=
    p412e_time_le hP htL hvd hvX htX fun w hw w' hw' =>
      p412e_dist_le_of_regC3 h𝕣 hχ hω hS (hXreg hw) (hXreg hw') (hXd w hw w' hw') hda
  have hq' : (t - s) / S ≤ (d / 𝕣) ^ R.χ := by rw [div_le_iff₀ hS]; linarith
  have hregst : ∀ u ∈ Icc s t, P u ∈ regRegion R 𝕣 := fun u hu =>
    hreg u ⟨hu.1, hu.2.trans htL.2⟩ (by linarith [hu.2])
  have Hp := p412e_geod_eucl_pair h𝕣 ha hχ' hω hS hP hPc hs.le htL.2 hregst
    (hq'.trans_lt hsmall)
  have hδ : ((t - s) / S) ^ (1 / R.χ') * 𝕣 ≤ (d / 𝕣) ^ (R.χ / R.χ') * 𝕣 := by
    refine mul_le_mul_of_nonneg_right ?_ h𝕣.le
    calc ((t - s) / S) ^ (1 / R.χ') ≤ ((d / 𝕣) ^ R.χ) ^ (1 / R.χ') :=
          Real.rpow_le_rpow (div_nonneg (by linarith) hS.le) hq' (by positivity)
      _ = (d / 𝕣) ^ (R.χ / R.χ') := by
          rw [← Real.rpow_mul (div_nonneg hd0 h𝕣.le)]; congr 1; ring
  set δ' := (d / 𝕣) ^ (R.χ / R.χ') * 𝕣
  have hδ0 : 0 ≤ δ' := by positivity
  have hPP : ∀ u ∈ Icc s t, ∀ u' ∈ Icc s t, ‖P u - P u'‖ ≤ δ' := fun u hu u' hu' =>
    (Hp u hu u' hu').trans hδ
  refine ⟨X₀ ∪ P '' Ioc s t, union_subset hX₀K ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rintro _ ⟨u, hu, rfl⟩
    exact p412e_geod_after hP hs hsL hy u ⟨hu.1, hu.2.trans htL.2⟩
  · refine ⟨hX₀c.nonempty.mono subset_union_left, hX₀c.isPreconnected.union (P t) htX
      ⟨t, ⟨hst, le_rfl⟩, rfl⟩ ?_⟩
    exact isPreconnected_Ioc.image P (hPc.mono fun u hu => ⟨hs.le.trans hu.1.le, hu.2.trans htL.2⟩)
  · have htI : t ∈ Icc s t := ⟨hst.le, le_rfl⟩
    rintro w (hw | ⟨u, hu, rfl⟩) w' (hw' | ⟨u', hu', rfl⟩)
    · linarith [hXd w hw w' hw']
    · calc ‖w - P u'‖ ≤ ‖w - P t‖ + ‖P t - P u'‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
        _ ≤ d + δ' := add_le_add (hXd w hw _ htX) (hPP t htI u' ⟨hu'.1.le, hu'.2⟩)
    · calc ‖P u - w'‖ ≤ ‖P u - P t‖ + ‖P t - w'‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
        _ ≤ δ' + d := add_le_add (hPP u ⟨hu.1.le, hu.2⟩ t htI) (hXd _ htX w' hw')
        _ = d + δ' := add_comm _ _
    · linarith [hPP u ⟨hu.1.le, hu.2⟩ u' ⟨hu'.1.le, hu'.2⟩]
  · have hcw : ContinuousWithinAt P (Ioc s t) s :=
      (hPc s ⟨hs.le, hsL.le⟩).mono fun u hu => ⟨hs.le.trans hu.1.le, hu.2.trans htL.2⟩
    have hmem : s ∈ closure (Ioc s t) := by rw [closure_Ioc hst.ne]; exact ⟨le_rfl, hst.le⟩
    exact closure_mono subset_union_right (hcw.mem_closure_image hmem)
  · exact closure_mono subset_union_left hvX
  · rintro w ⟨hw, hwK⟩
    rw [closure_union] at hw
    rcases hw with hw | hw
    · exact Or.inl ⟨hw, hwK⟩
    · have hcl : closure (P '' Ioc s t) ⊆ P '' Icc s t :=
        closure_minimal (image_mono Ioc_subset_Icc_self)
          (isCompact_Icc.image_of_continuousOn (hPc.mono fun u hu =>
            ⟨hs.le.trans hu.1, hu.2.trans htL.2⟩)).isClosed
      obtain ⟨u, hu, rfl⟩ := hcl hw
      rcases eq_or_lt_of_le hu.1 with h' | h'
      · right; rw [h']; rfl
      · exact absurd hwK (p412e_geod_after hP hs hsL hy u ⟨h', hu.2.trans htL.2⟩)

/-- **GM L4.13′, the set `X`** (l. 2075–2081): from `d^{ℂ∖𝓑^•_s}(P(u₀), v) < ε𝕣` with
`P(u₀) ∉ 𝓑^•_s`, `v ∈ ∂𝓑^•_s`, a connected `X ⊆ ℂ ∖ 𝓑^•_s` of Euclidean diameter
`≤ 2ε^{χ/χ'}𝕣` whose closure contains `P(s)` and `v` -/
theorem p412e_L413_X {Ω : Type} {D : DistC → ContMetric} {h : Ω → DistC} {R : RegPar}
    {𝕣 a : ℝ} (h𝕣 : 0 < 𝕣) (ha : 0 < a) (hχ : 0 < R.χ) (hχχ : R.χ ≤ R.χ') (hc : 0 < R.c 𝕣)
    {ω : Ω} (hω : ω ∈ regC3 D h R 𝕣 a) {P : ℝ → ℂ} {L : ℝ} {𝕫 y : ℂ}
    (hP : IsGeodesicL (D (h ω)) P L 𝕫 y) {s : ℝ} (hs : 0 < s) (hsL : s < L)
    (hbd : Bornology.IsBounded (ballM (D (h ω)) 𝕫 s)) (hy : y ∉ filledBall (D (h ω)) 𝕫 s)
    {u₀ : ℝ} (hu₀ : u₀ ∈ Icc 0 L) (hu₀K : P u₀ ∉ filledBall (D (h ω)) 𝕫 s) {v : ℂ}
    (hv : v ∈ frontier (filledBall (D (h ω)) 𝕫 s))
    (hLC : LocConnAt (filledBall (D (h ω)) 𝕫 s) v) {ε : ℝ} (hε0 : 0 < ε) (hε1 : ε ≤ 1)
    (hεa : ε ≤ a) (hsmall : ε ^ R.χ < a ^ R.χ')
    (hdU : dU (filledBall (D (h ω)) 𝕫 s)ᶜ (P u₀) v < ENNReal.ofReal (ε * 𝕣))
    (hKreg : cthickening (ε * 𝕣) (filledBall (D (h ω)) 𝕫 s) ⊆ regRegion R 𝕣)
    (hreg : ∀ u ∈ Icc s L, u ≤ s + scaleFac R.ξ R.c (h ω) 𝕣 0 * ε ^ R.χ →
      P u ∈ regRegion R 𝕣) :
    ∃ X ⊆ (filledBall (D (h ω)) 𝕫 s)ᶜ, IsConnected X ∧
      Metric.ediam X ≤ ENNReal.ofReal (2 * ε ^ (R.χ / R.χ') * 𝕣) ∧
      P s ∈ closure X ∧ v ∈ closure X ∧
      closure X ∩ filledBall (D (h ω)) 𝕫 s ⊆ {P s, v} := by
  set K := filledBall (D (h ω)) 𝕫 s with hKdef
  have hχ' : 0 < R.χ' := hχ.trans_le hχχ
  have hKc : IsClosed K := jb_isClosed_filledBall hbd
  simp only [dU, iInf_lt_iff] at hdU
  obtain ⟨X₀, hX₀K, hX₀c, hPX, hvX, hdiam⟩ := hdU
  set X₁ := insert (P u₀) X₀
  have hX₁cl : X₁ ⊆ closure X₀ := insert_subset hPX subset_closure
  have hX₁c : IsConnected X₁ :=
    ⟨⟨_, mem_insert _ _⟩, hX₀c.isPreconnected.subset_closure (subset_insert _ _) hX₁cl⟩
  have hdiam₁ : Metric.ediam X₁ < ENNReal.ofReal (ε * 𝕣) :=
    lt_of_le_of_lt ((Metric.ediam_mono hX₁cl).trans_eq (Metric.ediam_closure X₀)) hdiam
  have hvX₁ : v ∈ closure X₁ := closure_mono (subset_insert _ _) hvX
  have hεr : 0 < ε * 𝕣 := mul_pos hε0 h𝕣
  -- a real bound `d₁ < ε𝕣` for the diameter of `X₁`, then shrink (GM l. 2075–2076)
  have hne : Metric.ediam X₁ ≠ ∞ := (hdiam₁.trans ENNReal.ofReal_lt_top).ne
  set d₁ := (Metric.ediam X₁).toReal
  have hd₁ : d₁ < ε * 𝕣 := ENNReal.toReal_lt_of_lt_ofReal hdiam₁
  have hpair₁ : ∀ w ∈ X₁, ∀ w' ∈ X₁, dist w w' ≤ d₁ := fun w hw w' hw' => by
    rw [dist_edist]; exact ENNReal.toReal_mono hne (Metric.edist_le_ediam_of_mem hw hw')
  have hη : 0 < (ε * 𝕣 - d₁) / 2 := by linarith
  obtain ⟨X₂, hX₂K, hX₂c, hPX₂, hvX₂, hclX₂, hX₂th⟩ := p412e_shrink hKc
    (insert_subset hu₀K hX₀K) hX₁c.isPreconnected (mem_insert _ _) hvX₁ hLC hη
  have hpair : ∀ w ∈ X₂, ∀ w' ∈ X₂, ‖w - w'‖ ≤ ε * 𝕣 := by
    intro w hw w' hw'
    obtain ⟨x, hx, hwx⟩ := mem_thickening_iff.1 (hX₂th hw)
    obtain ⟨x', hx', hwx'⟩ := mem_thickening_iff.1 (hX₂th hw')
    rw [← dist_eq_norm]
    calc dist w w' ≤ dist w x + dist x x' + dist x' w' := dist_triangle4 _ _ _ _
      _ ≤ (ε * 𝕣 - d₁) / 2 + d₁ + (ε * 𝕣 - d₁) / 2 := by
          exact add_le_add (add_le_add hwx.le (hpair₁ x hx x' hx'))
            (by rw [dist_comm]; exact hwx'.le)
      _ = ε * 𝕣 := by ring
  have hpairv : ∀ w ∈ X₂, ‖w - v‖ ≤ ε * 𝕣 := by
    intro w hw
    have : closure X₂ ⊆ {z | ‖w - z‖ ≤ ε * 𝕣} :=
      closure_minimal (fun z hz => hpair w hw z hz)
        (isClosed_le (by fun_prop) continuous_const)
    exact this hvX₂
  have hd : ε * 𝕣 / 𝕣 = ε := by field_simp
  obtain ⟨X, hXK, hXc, hXd, hPs, hvXc, hclX⟩ := p412e_L413_build h𝕣 ha hχ hχ' hc hω hP hs hsL hbd
    hy hX₂K hX₂c hu₀ hPX₂ hv hvX₂ hpair
    (mul_le_mul_of_nonneg_right hεa h𝕣.le) (by rwa [hd])
    (fun w hw => hKreg (mem_cthickening_of_dist_le w v _ K (hKc.frontier_subset hv)
      (by rw [dist_eq_norm]; exact hpairv w hw)))
    (by rw [hd]; exact hreg)
  refine ⟨X, hXK, hXc, ?_, hPs, hvXc, fun w hw => ?_⟩
  swap
  · rcases hclX hw with h' | h'
    · exact Or.inr (hclX₂ h')
    · exact Or.inl h'
  have hεκ : ε ≤ ε ^ (R.χ / R.χ') := by
    have := Real.rpow_le_rpow_of_exponent_ge hε0 hε1 (div_le_one_of_le₀ hχχ hχ'.le)
    rwa [Real.rpow_one] at this
  refine Metric.ediam_le_of_forall_dist_le fun w hw w' hw' => ?_
  rw [dist_eq_norm]
  refine (hXd w hw w' hw').trans ?_
  rw [hd]; nlinarith

end LQGMetric.GM
