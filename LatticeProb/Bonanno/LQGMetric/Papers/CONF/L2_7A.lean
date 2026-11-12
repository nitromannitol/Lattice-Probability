/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.CONF.L2_7A at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.CONF.L2_4S2

/-!
# CONF Lemma 2.7: leftmost geodesics map arcs to arcs

Source: CONF = Gwynne–Miller, *Confluence of geodesics in Liouville quantum gravity for
`γ ∈ (0,2)`*, arXiv:1905.00381, `confluence-final.tex`, Lemma 2.7 (`lem-geo-arc`, l. 617–622)
and its proof (l. 623–645).

CONF's proof: disjointness "since each `y` gives rise to a unique leftmost geodesic" (l. 624);
connectedness by lifting to the universal cover of the annulus `𝓑^•_{s'} ∖ 𝓑^•_s`
(l. 627–630), using that lifts of geodesics cannot cross the lifts `P̂_q` of the geodesics to
rational points (Lemma 2.3, l. 632–635), so that for `y₁ < y < y₂` the lifted leftmost geodesic to
`y` hits level `s` between the hitting points of those to `y₁`, `y₂` (l. 637–643).

Here the lift is the log-cover lift of DEC-D (`DD.IsPosJordanLift`). The ordering step
(l. 640–643, "`P̂_y` cannot cross `P̂_{q₁}` or `P̂_{q₂}`") is `step_order` (TOPO-ORD + CONF
Lemma 2.3 through a geodesic to a rational point between the two endpoints, exactly CONF's
`q₁, q₂`), applied with angle lifts normalized at the endpoint. With this normalization the
position at level `s` is a monotone function of the endpoint position (`pos_mono`) and commutes
with the deck shift `+2π` (`pos_shift`), which replaces CONF's use of the winding bound
Lemma 2.6 (l. 628–629: there the bound only serves to place all lifted endpoints in one
fundamental interval `[a,b]`).

* `arc_lift`: the lift of a connected subset `I` of a Jordan curve is a translate-family of one
  interval (CONF l. 636, "By possibly re-choosing `π` … each `Î` is an interval"; own elementary
  proof: two closed half-arcs).
* `levelPos`, `pos_exists`, `pos_mono`, `pos_shift`, `pos_mem`;
* `geoArc_det` (deterministic Lemma 2.7), `confLem2_7 (h38 : DFGPSLem3_8) : CONFLem2_7`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Filter Topology Set Metric
open LQGMetric.Blueprint

namespace LQGMetric.CONF

/-- reduction of a real number into `[c, c + 2π)` modulo `2π` -/
theorem exists_red (c p : ℝ) : ∃ k : ℤ, p + k * (2 * Real.pi) ∈ Ico c (c + 2 * Real.pi) := by
  have h2 : (0 : ℝ) < 2 * Real.pi := by positivity
  refine ⟨-⌊(p - c) / (2 * Real.pi)⌋, ?_⟩
  have h1 := Int.floor_le ((p - c) / (2 * Real.pi))
  have h3 := Int.lt_floor_add_one ((p - c) / (2 * Real.pi))
  rw [le_div_iff₀ h2] at h1
  rw [div_lt_iff₀ h2] at h3
  push_cast
  constructor <;> nlinarith

/-- **CONF l. 636** (own elementary proof): the lift of a connected subset `I` of a Jordan curve
`Γ = range φ` is the union of the `2πℤ`-translates of one interval `J` -/
theorem arc_lift {Γ : Set ℂ} {z : ℂ} {φ : ℝ → ℂ} {θ : ℝ → ℝ} (hφ : DD.IsPosJordanLift Γ z φ θ)
    {I : Set ℂ} (hIΓ : I ⊆ Γ) (hI : IsPreconnected I) :
    ∃ J : Set ℝ, J.OrdConnected ∧ (∀ p ∈ J, φ p ∈ I) ∧
      ∀ p, φ p ∈ I → ∃ k : ℤ, p + k * (2 * Real.pi) ∈ J := by
  have h2 : (0 : ℝ) < 2 * Real.pi := by positivity
  by_cases hall : ∀ p, φ p ∈ I
  · exact ⟨univ, ordConnected_univ, fun p _ => hall p, fun p _ => ⟨0, trivial⟩⟩
  push Not at hall
  obtain ⟨c, hc⟩ := hall
  refine ⟨{p | p ∈ Ioo c (c + 2 * Real.pi) ∧ φ p ∈ I}, ⟨fun a ha e he b hb => ?_⟩,
    fun p hp => hp.2, fun p hp => ?_⟩
  · refine ⟨⟨ha.1.1.trans_le hb.1, hb.2.trans_lt he.1.2⟩, ?_⟩
    by_contra hbI
    have hcl : ∀ x y : ℝ, IsClosed (φ '' Icc x y) := fun x y =>
      (isCompact_Icc.image hφ.1).isClosed
    obtain ⟨x, hxI, ⟨p₁, hp₁, rfl⟩, ⟨p₂, hp₂, hp₂e⟩⟩ := isPreconnected_closed_iff.1 hI _ _
      (hcl c b) (hcl b (c + 2 * Real.pi)) (fun x hx => by
        have hxΓ := hIΓ hx
        rw [← hφ.2.2.2.1] at hxΓ
        obtain ⟨p, rfl⟩ := hxΓ
        obtain ⟨k, hk⟩ := exists_red c p
        rw [← hφ.phi_add_int p k]
        rcases le_total (p + k * (2 * Real.pi)) b with hpb | hpb
        · exact Or.inl ⟨_, ⟨hk.1, hpb⟩, rfl⟩
        · exact Or.inr ⟨_, ⟨hpb, hk.2.le⟩, rfl⟩)
      ⟨φ a, ha.2, a, ⟨ha.1.1.le, hb.1⟩, rfl⟩ ⟨φ e, he.2, e, ⟨hb.2, he.1.2.le⟩, rfl⟩
    obtain ⟨n, hn⟩ := hφ.phi_eq_imp hp₂e
    have hn1 : 0 ≤ (n : ℝ) * (2 * Real.pi) := by linarith [hp₁.2, hp₂.1]
    have hn2 : (n : ℝ) * (2 * Real.pi) ≤ 2 * Real.pi := by linarith [hp₁.1, hp₂.2]
    have hn1' : (0 : ℝ) ≤ n := by nlinarith
    have hn2' : (n : ℝ) ≤ 1 := by nlinarith
    have hn1'' : 0 ≤ n := by exact_mod_cast hn1'
    have hn2'' : n ≤ 1 := by exact_mod_cast hn2'
    rcases (show n = 0 ∨ n = 1 by omega) with rfl | rfl
    · have : p₁ = b := by simp at hn; linarith [hp₁.2, hp₂.1]
      exact hbI (this ▸ hxI)
    · have : p₁ = c := by push_cast at hn; linarith [hp₁.1, hp₂.2]
      exact hc (this ▸ hxI)
  · obtain ⟨k, hk⟩ := exists_red c p
    refine ⟨k, ⟨lt_of_le_of_ne hk.1 fun h => hc ?_, hk.2⟩, by rwa [hφ.phi_add_int]⟩
    rw [h, hφ.phi_add_int]; exact hp

section Det
variable {D : ContMetric} {z : ℂ} {s t : ℝ}

/-- `p` is the position at level `t` (on the lift `(φ₁, θ₁)` of `∂𝓑^•_t`) of a leftmost geodesic
to `φ w ∈ ∂𝓑^•_s`, its angle lift normalized by `α s = θ w` (CONF's lift `P̂`, l. 630) -/
def levelPos (D : ContMetric) (z : ℂ) (s t : ℝ) (φ φ₁ : ℝ → ℂ) (θ θ₁ : ℝ → ℝ) (w p : ℝ) : Prop :=
  ∃ (Q : ℝ → ℂ) (α : ℝ → ℝ), IsLeftmostGeod D z s (φ w) Q ∧ DD.IsAngleLift z Q t s α ∧
    α s = θ w ∧ φ₁ p = Q t ∧ θ₁ p = α t

variable {φ φ₁ : ℝ → ℂ} {θ θ₁ : ℝ → ℝ}

theorem pos_exists (hL : D.IsLength)
    (hbc : ∀ A : Set ℂ, IsClosed A → (∃ M : ℝ, ∀ u ∈ A, ∀ v ∈ A, D.1 (u, v) ≤ M) → IsCompact A)
    (hgeo : ∀ a b : ℂ, ∃ η, IsGeod01 D a b η)
    (hφ : DD.IsPosJordanLift (frontier (filledBall D z s)) z φ θ)
    (hφ₁ : DD.IsPosJordanLift (frontier (filledBall D z t)) z φ₁ θ₁) (ht0 : 0 < t)
    (hts : t < s) (w : ℝ) : ∃ p, levelPos D z s t φ φ₁ θ θ₁ w p := by
  have hy : φ w ∈ frontier (filledBall D z s) := hφ.2.2.2.1 ▸ mem_range_self w
  obtain ⟨Q, hQ⟩ := exists_sideGeod' hL hbc hgeo (ht0.trans hts) hy true
  obtain ⟨α, p, hα, hαs, h1, h2⟩ := exists_normLift hφ hφ₁ ht0 hts hQ.2.1
  exact ⟨p, Q, α, hQ, hα, hαs, h1, h2⟩

/-- **CONF l. 637–643**: the level-`t` position is monotone in the endpoint position -/
theorem pos_mono
    (hbc : ∀ A : Set ℂ, IsClosed A → (∃ M : ℝ, ∀ u ∈ A, ∀ v ∈ A, D.1 (u, v) ≤ M) → IsCompact A)
    (hgeo : ∀ a b : ℂ, ∃ η, IsGeod01 D a b η) (hq : ∀ q : ℚ × ℚ, UniqueGeod D z (ratPt q))
    (hφ : DD.IsPosJordanLift (frontier (filledBall D z s)) z φ θ)
    (hφ₁ : DD.IsPosJordanLift (frontier (filledBall D z t)) z φ₁ θ₁) (ht0 : 0 < t)
    (hts : t < s) {w₀ w₁ p₀ p₁ : ℝ} (h₀ : levelPos D z s t φ φ₁ θ θ₁ w₀ p₀)
    (h₁ : levelPos D z s t φ φ₁ θ θ₁ w₁ p₁) (hw : w₀ < w₁) : p₀ ≤ p₁ := by
  obtain ⟨Q₀, α₀, hQ₀, hα₀, hα₀s, h01, h02⟩ := h₀
  obtain ⟨Q₁, α₁, hQ₁, hα₁, hα₁s, h11, h12⟩ := h₁
  exact step_order hbc hgeo hq hφ hφ₁ ht0 hts hQ₀.2.1 hQ₁.2.1 hα₀ hα₁ hα₀s hα₁s h01 h02 h11 h12 hw

/-- deck shift: `levelPos (w + 2πn) (p + 2πn)` -/
theorem pos_shift (hφ : DD.IsPosJordanLift (frontier (filledBall D z s)) z φ θ)
    (hφ₁ : DD.IsPosJordanLift (frontier (filledBall D z t)) z φ₁ θ₁) {w p : ℝ}
    (h : levelPos D z s t φ φ₁ θ θ₁ w p) (n : ℤ) :
    levelPos D z s t φ φ₁ θ θ₁ (w + n * (2 * Real.pi)) (p + n * (2 * Real.pi)) := by
  obtain ⟨Q, α, hQ, hα, hαs, h1, h2⟩ := h
  refine ⟨Q, _, by rwa [hφ.phi_add_int], hα.add_int n, ?_, by rw [hφ₁.phi_add_int, h1], ?_⟩
  · simp only [hφ.theta_add_int, hαs]
  · simp only [hφ₁.theta_add_int, h2]

/-- the set `I′` of CONF l. 619 -/
def arcPre (D : ContMetric) (z : ℂ) (s : ℝ) (I : Set ℂ) : Set ℂ :=
  {y | y ∈ frontier (filledBall D z s) ∧ ∃ Q, IsLeftmostGeod D z s y Q ∧ ∃ u ∈ Icc 0 s, Q u ∈ I}

/-- a geodesic to `∂𝓑^•_s` meets `∂𝓑^•_t` only at time `t` -/
theorem geod_hit_eq
    (hbc : ∀ A : Set ℂ, IsClosed A → (∃ M : ℝ, ∀ u ∈ A, ∀ v ∈ A, D.1 (u, v) ≤ M) → IsCompact A)
    {Q : ℝ → ℂ} {y : ℂ} (hQ : IsGeodesicL D Q s z y) {u : ℝ} (hu : u ∈ Icc 0 s)
    (hQu : Q u ∈ frontier (filledBall D z t)) : u = t := by
  have h1 := DD.cl_geodL_dist hQ hu
  have h2 := GM.jp_frontier_subset_sphere (isBounded_ballM_of_bc hbc z t) hQu
  simp only [mem_ofPred_eq] at h2
  linarith

/-- membership in `I′` is read off the level-`t` position (uses uniqueness, CONF l. 624) -/
theorem pos_mem
    (hbc : ∀ A : Set ℂ, IsClosed A → (∃ M : ℝ, ∀ u ∈ A, ∀ v ∈ A, D.1 (u, v) ≤ M) → IsCompact A)
    (huniq : ∀ y Q Q', IsLeftmostGeod D z s y Q → IsLeftmostGeod D z s y Q' → EqOn Q Q' (Icc 0 s))
    (hφ : DD.IsPosJordanLift (frontier (filledBall D z s)) z φ θ) (ht0 : 0 < t) (hts : t < s)
    {I : Set ℂ} (hI : I ⊆ frontier (filledBall D z t)) {w p : ℝ}
    (h : levelPos D z s t φ φ₁ θ θ₁ w p) : φ w ∈ arcPre D z s I ↔ φ₁ p ∈ I := by
  obtain ⟨Q, α, hQ, -, -, h1, -⟩ := h
  rw [h1]
  constructor
  · rintro ⟨-, Q', hQ', u, hu, hQu⟩
    have hut := geod_hit_eq hbc hQ'.2.1 hu (hI hQu)
    subst hut
    rwa [huniq _ _ _ hQ hQ' hu]
  · intro hQt
    exact ⟨hφ.2.2.2.1 ▸ mem_range_self w, Q, hQ, t, ⟨ht0.le, hts.le⟩, hQt⟩

/-- positions are unique (uniqueness of the leftmost geodesic, CONF Lemma 2.4) -/
theorem pos_uniq
    (huniq : ∀ y Q Q', IsLeftmostGeod D z s y Q → IsLeftmostGeod D z s y Q' → EqOn Q Q' (Icc 0 s))
    (hφ₁ : DD.IsPosJordanLift (frontier (filledBall D z t)) z φ₁ θ₁) (ht0 : 0 < t) (hts : t < s)
    {w p p' : ℝ} (h : levelPos D z s t φ φ₁ θ θ₁ w p) (h' : levelPos D z s t φ φ₁ θ θ₁ w p') :
    p = p' := by
  obtain ⟨Q, α, hQ, hα, hαs, h1, h2⟩ := h
  obtain ⟨Q', α', hQ', hα', hα's, h1', h2'⟩ := h'
  have heq := huniq _ _ _ hQ hQ'
  have hsub : Icc t s ⊆ Icc 0 s := Icc_subset_Icc_left ht0.le
  have hα'Q : DD.IsAngleLift z Q t s α' :=
    ⟨hα'.1, fun u hu => by rw [heq (hsub hu)]; exact hα'.2 u hu⟩
  have hne : ∀ u ∈ Icc t s, Q u ≠ z := fun u hu =>
    DD.geodLevel_ne hQ.2.1 (ht0.trans_le hu.1) hu.2
  have hE := DD.angleLift_eqOn hα hα'Q hne ⟨hts.le, le_rfl⟩ (hαs.trans hα's.symm)
  refine hφ₁.pos_unique ?_ ?_
  · rw [h1, h1', heq (hsub ⟨le_rfl, hts.le⟩)]
  · rw [h2, h2', hE ⟨le_rfl, hts.le⟩]

/-- **CONF Lemma 2.7, connectedness** (deterministic; l. 626–645) -/
theorem arcPre_connected (hL : D.IsLength)
    (hbc : ∀ A : Set ℂ, IsClosed A → (∃ M : ℝ, ∀ u ∈ A, ∀ v ∈ A, D.1 (u, v) ≤ M) → IsCompact A)
    (hgeo : ∀ a b : ℂ, ∃ η, IsGeod01 D a b η) (hq : ∀ q : ℚ × ℚ, UniqueGeod D z (ratPt q))
    (ht0 : 0 < t) (hts : t < s) {I : Set ℂ} (hI : IsBdyArc D z t I) :
    arcPre D z s I = ∅ ∨ IsBdyArc D z s (arcPre D z s I) := by
  have hs : 0 < s := ht0.trans hts
  have huniq : ∀ y Q Q', IsLeftmostGeod D z s y Q → IsLeftmostGeod D z s y Q' →
      EqOn Q Q' (Icc 0 s) := fun y Q Q' hQ hQ' =>
    confSideUniq D z hL hbc hgeo hq s hs y hQ.1 true Q Q' hQ hQ'
  obtain ⟨φ, θ, hφ⟩ := DD.posLift_filledBall hs hL (isBounded_ballM_of_bc hbc z s)
    (GM.gm_j1b D z s hs hL (isBounded_ballM_of_bc hbc z s))
  obtain ⟨φ₁, θ₁, hφ₁⟩ := DD.posLift_filledBall ht0 hL (isBounded_ballM_of_bc hbc z t)
    (GM.gm_j1b D z t ht0 hL (isBounded_ballM_of_bc hbc z t))
  obtain ⟨J, hJ, hJI, hIJ⟩ := arc_lift hφ₁ hI.1 hI.2.isPreconnected
  have hmono : ∀ {w₀ w₁ p₀ p₁ : ℝ}, levelPos D z s t φ φ₁ θ θ₁ w₀ p₀ →
      levelPos D z s t φ φ₁ θ θ₁ w₁ p₁ → w₀ ≤ w₁ → p₀ ≤ p₁ := by
    intro w₀ w₁ p₀ p₁ h₀ h₁ hw
    rcases hw.lt_or_eq with hw | rfl
    · exact pos_mono hbc hgeo hq hφ hφ₁ ht0 hts h₀ h₁ hw
    · exact (pos_uniq huniq hφ₁ ht0 hts h₀ h₁).le
  set K : Set ℝ := {w | ∃ p, levelPos D z s t φ φ₁ θ θ₁ w p ∧ p ∈ J} with hK
  have hKo : K.OrdConnected := by
    refine ⟨fun a ha e he w hw => ?_⟩
    obtain ⟨pa, hpa, hpaJ⟩ := ha
    obtain ⟨pe, hpe, hpeJ⟩ := he
    obtain ⟨p, hp⟩ := pos_exists hL hbc hgeo hφ hφ₁ ht0 hts w
    exact ⟨p, hp, hJ.out hpaJ hpeJ ⟨hmono hpa hp hw.1, hmono hp hpe hw.2⟩⟩
  have himg : arcPre D z s I = φ '' K := by
    ext y
    constructor
    · intro hy
      have hyr := hy.1
      rw [← hφ.2.2.2.1] at hyr
      obtain ⟨w, rfl⟩ := hyr
      obtain ⟨p, hp⟩ := pos_exists hL hbc hgeo hφ hφ₁ ht0 hts w
      obtain ⟨k, hk⟩ := hIJ p ((pos_mem hbc huniq hφ ht0 hts hI.1 hp).1 hy)
      exact ⟨w + k * (2 * Real.pi), ⟨_, pos_shift hφ hφ₁ hp k, hk⟩, hφ.phi_add_int w k⟩
    · rintro ⟨w, ⟨p, hp, hpJ⟩, rfl⟩
      exact (pos_mem hbc huniq hφ ht0 hts hI.1 hp).2 (hJI p hpJ)
  rcases (arcPre D z s I).eq_empty_or_nonempty with he | hne
  · exact Or.inl he
  · refine Or.inr ⟨fun y hy => hy.1, hne, ?_⟩
    rw [himg]
    exact hKo.isPreconnected.image φ hφ.1.continuousOn

/-- **CONF Lemma 2.7, disjointness** (l. 624: "each `y` gives rise to a unique leftmost
geodesic") -/
theorem arcPre_disjoint
    (hbc : ∀ A : Set ℂ, IsClosed A → (∃ M : ℝ, ∀ u ∈ A, ∀ v ∈ A, D.1 (u, v) ≤ M) → IsCompact A)
    (huniq : ∀ y Q Q', IsLeftmostGeod D z s y Q → IsLeftmostGeod D z s y Q' → EqOn Q Q' (Icc 0 s))
    {I I' : Set ℂ} (hI : I ⊆ frontier (filledBall D z t)) (hI' : I' ⊆ frontier (filledBall D z t))
    (hd : Disjoint I I') : Disjoint (arcPre D z s I) (arcPre D z s I') := by
  rw [Set.disjoint_left]
  rintro y ⟨-, Q, hQ, u, hu, hQu⟩ ⟨-, Q', hQ', u', hu', hQu'⟩
  have h1 := geod_hit_eq hbc hQ.2.1 hu (hI hQu)
  have h2 := geod_hit_eq hbc hQ'.2.1 hu' (hI' hQu')
  subst h1; subst h2
  rw [huniq _ _ _ hQ hQ' hu] at hQu
  exact Set.disjoint_left.1 hd hQu hQu'

end Det

/-- **CONF Lemma 2.7** (`lem-geo-arc`, l. 617–645), from DFGPS Lemma 3.8 -/
theorem confLem2_7 (h38 : DFGPSLem3_8) : CONFLem2_7 := by
  intro γ hγ hγ2 D c hD Ω _ P _ h hh z₀
  filter_upwards [GM.gm_S1_1_bcpt h38 hγ hγ2 hD P h hh, GM.gm_S1_1 h38 hγ hγ2 hD P h hh,
    hD.length P h (GM.Tight.isGFFPlusCont_of_wp hh), confLem2_2 h38 γ hγ hγ2 D c hD P h hh z₀]
    with ω hc hg hL hq s s' hs hss' 𝓘 _ h𝓘 hdisj
  have huniq : ∀ y Q Q', IsLeftmostGeod (D (h ω)) z₀ s' y Q →
      IsLeftmostGeod (D (h ω)) z₀ s' y Q' → EqOn Q Q' (Icc 0 s') := fun y Q Q' hQ hQ' =>
    confSideUniq (D (h ω)) z₀ hL hc hg hq s' (hs.trans hss') y hQ.1 true Q Q' hQ hQ'
  refine ⟨fun I hI => arcPre_connected hL hc hg hq hs hss' (h𝓘 I hI), ?_⟩
  intro I hI I' hI' hne
  exact arcPre_disjoint hc huniq (h𝓘 I hI).1 (h𝓘 I' hI').1 (hdisj hI hI' hne)

end LQGMetric.CONF
