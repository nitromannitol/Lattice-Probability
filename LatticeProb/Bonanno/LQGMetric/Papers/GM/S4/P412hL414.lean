/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.GM.S4.P412hL414 at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S4.P412hDef

/-!
# GM L4.14 with canonical choices (D98 §2, packet P-L414B)

Source: GM = `literature/src/1905.00383/uniqueness-final.tex`, Lemma 4.14 (`lem-dc-set`,
l. 2097–2102), proof l. 2457–2520 as repaired in DEC-86 (1) (`p412d_GML4_14`); L4.15 Step 3 (∗),
l. 2162–2165; decision D98 §2.

* `p412h_T_cover`, `p412h_rho` — the net `T` and the radius `ρ` of `P412hDef` have the properties
  used in the proof of `p412d_GML4_14`;
* **`p412h_L414B`** — the proof of `p412d_GML4_14` with the four choices made canonical: either
  `𝒞^ε_y = ∅`, or the output of `GML4_14'` holds with centre `c = gd(K, y) = p412hGd K y ε`;
* **`p412h_goodZ`** — (DV-D98b) every `x ∈ B̄_{8ε}(gd(K, y))` satisfies GM's (∗) for `y`
  (`p412eGoodZ K y x ε`, radius `r = 8ε`), as in the proof of `p412e_goodZ_exists`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Metric Topology Bornology
open LQGMetric.Topo.Crosscut

namespace LQGMetric.GM

/-- `T` is an `ε/8`-net of `cthickening (3ε) K` -/
theorem p412h_T_cover {K : Set ℂ} (hK : IsCompact K) {ε : ℝ} (hε : 0 < ε) {x : ℂ}
    (hx : x ∈ cthickening (3 * ε) K) : ∃ m ∈ p412hT K ε, dist x (p412hG ε m) ≤ ε / 8 := by
  set m : ℤ × ℤ := (round (8 / ε * x.re), round (8 / ε * x.im)) with hm
  have hre : (x - p412hG ε m).re = ε / 8 * (8 / ε * x.re - round (8 / ε * x.re)) := by
    simp only [p412hG, hm, Complex.sub_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      Complex.add_re, Complex.add_im, Complex.intCast_re, Complex.intCast_im, Complex.I_re,
      Complex.I_im, Complex.mul_im]
    field_simp; ring
  have him : (x - p412hG ε m).im = ε / 8 * (8 / ε * x.im - round (8 / ε * x.im)) := by
    simp only [p412hG, hm, Complex.sub_im, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      Complex.add_re, Complex.add_im, Complex.intCast_re, Complex.intCast_im, Complex.I_re,
      Complex.I_im, Complex.mul_im]
    field_simp; ring
  have hd : dist x (p412hG ε m) ≤ ε / 8 := by
    rw [dist_eq_norm]
    refine (Complex.norm_le_abs_re_add_abs_im _).trans ?_
    rw [hre, him, abs_mul, abs_mul, abs_of_pos (by positivity : 0 < ε / 8)]
    have h1 := abs_sub_round (8 / ε * x.re)
    have h2 := abs_sub_round (8 / ε * x.im)
    nlinarith
  refine ⟨m, ?_, hd⟩
  rw [hK.cthickening_eq_biUnion_closedBall (by positivity)] at hx
  obtain ⟨k, hk, hxk⟩ := mem_iUnion₂.1 hx
  refine ⟨k, ?_, hk⟩
  rw [mem_closedBall]
  linarith [dist_triangle k x (p412hG ε m), mem_closedBall.1 hxk, dist_comm k x]

theorem p412h_rho_ex {K : Set ℂ} (hK : IsBounded K) (y : ℂ) {ε : ℝ} (hε : 0 < ε) :
    ∃ j, p412hRhoOK K y ε j := by
  obtain ⟨j, -, hj⟩ := Set.infinite_univ.exists_notMem_finite
    ((p412h_T_finite hK hε).biUnion fun m _ =>
      (show ({j : ℕ | p412hRad ε j = dist y (p412hG ε m)}).Subsingleton from
        fun a ha b hb => p412h_rad_inj hε (ha.trans hb.symm)).finite)
  refine ⟨j, fun m hm h => hj (mem_biUnion hm h.symm)⟩

theorem p412h_rho_eq {K : Set ℂ} (hK : IsBounded K) (y : ℂ) {ε : ℝ} (hε : 0 < ε) :
    ∃ j, p412hRhoOK K y ε j ∧ p412hRho K y ε = p412hRad ε j := by
  classical
  have hex := p412h_rho_ex hK y hε
  rw [p412hRho, dite_eq_left_of_eq_true (eq_true hex)]
  exact ⟨_, Nat.find_spec hex, rfl⟩

/-- the radius `ρ ∈ (3ε/2, 2ε]` avoids `y` on every circle of the net -/
theorem p412h_rho {K : Set ℂ} (hK : IsBounded K) (y : ℂ) {ε : ℝ} (hε : 0 < ε) :
    3 / 2 * ε < p412hRho K y ε ∧ p412hRho K y ε ≤ 2 * ε ∧
      ∀ m ∈ p412hT K ε, y ∉ sphere (p412hG ε m) (p412hRho K y ε) := by
  obtain ⟨j, hj, he⟩ := p412h_rho_eq hK y hε
  rw [he]
  exact ⟨(p412h_rad_mem hε j).1, (p412h_rad_mem hε j).2, fun m hm h => hj m hm (mem_sphere.1 h)⟩

theorem p412h_gd_eq {K : Set ℂ} {y : ℂ} {ε : ℝ} (hM : ∃ i, p412hMx K y ε i) :
    ∃ i, p412hMx K y ε i ∧ p412hGd K y ε = p412hC ε i := by
  classical
  rw [p412hGd, dite_eq_left_of_eq_true (eq_true hM)]
  exact ⟨_, Nat.find_spec hM, rfl⟩

/-- **GM Lemma 4.14′ with canonical choices** (D98 §2, P-L414B): the proof of `p412d_GML4_14`
with the net `T`, the radius `ρ`, the arcs (rational angles) and the maximal arc (least index)
chosen canonically; the output centre is `gd(K, y) = p412hGd K y ε`. -/
theorem p412h_L414B {K : Set ℂ} (hK : IsCompact K) (hKc : IsConnected K) (hKo : IsPreconnected Kᶜ)
    (hLC : ∀ q ∈ frontier K, LocConnAt K q) {y : ℂ} (hy : y ∈ frontier K) {ε : ℝ} (hε : 0 < ε) :
    dcSetC K y ε = ∅ ∨
      ∃ r : ℝ, 0 < r ∧ r ≤ 8 * ε ∧ (closedBall (p412hGd K y ε) r ∩ K).Nonempty ∧
        ∃ y₀ ∈ sphere (p412hGd K y ε) r, y₀ ∉ K ∧ ∃ v,
          v ∉ connectedComponentIn (sphere (p412hGd K y ε) r \ K) y₀ ∪ K ∧
          Bornology.IsBounded (connectedComponentIn
            (connectedComponentIn (sphere (p412hGd K y ε) r \ K) y₀ ∪ K)ᶜ v) ∧
          dcSetC K y ε ⊆ closure (connectedComponentIn
            (connectedComponentIn (sphere (p412hGd K y ε) r \ K) y₀ ∪ K)ᶜ v) := by
  have hKcl := hK.isClosed
  have hyK : y ∈ K := hKcl.frontier_subset hy
  have hKne : K.Nonempty := ⟨y, hyK⟩
  set ρ := p412hRho K y ε with hρdef
  obtain ⟨hρI1, hρI2, hyS⟩ := p412h_rho hK.isBounded y hε
  have hρ : 0 < ρ := by linarith
  set T := p412hT K ε
  have hTf : T.Finite := p412h_T_finite hK.isBounded hε
  set F : Set (ℂ × ℂ) := {p | (∃ m ∈ T, p.1 = p412hG ε m) ∧ p412hArc K y ρ p.1 p.2} with hFdef
  set bs : ℂ × ℂ → Set ℂ := fun p => p412hBs K ρ p.1 p.2 with hbs
  set G := bs '' F
  have hyS' : ∀ p ∈ F, y ∉ sphere p.1 ρ := by
    rintro p ⟨⟨m, hm, he⟩, -⟩; rw [he]; exact hyS m hm
  have hGf : G.Finite := by
    have hsub : G ⊆ ⋃ m ∈ T, bs '' {p | p ∈ F ∧ p.1 = p412hG ε m} := by
      rintro _ ⟨p, hp, rfl⟩
      obtain ⟨m, hm, he⟩ := hp.1
      exact mem_biUnion hm ⟨p, ⟨hp, he⟩, rfl⟩
    refine (hTf.biUnion fun c _ => Set.Subsingleton.finite ?_).subset hsub
    rintro _ ⟨⟨c₁, y₁⟩, ⟨hp, hpc⟩, rfl⟩ _ ⟨⟨c₂, y₂⟩, ⟨hq, hqc⟩, rfl⟩
    simp only at hpc hqc
    subst hpc; subst hqc
    simp only [bs, p412hBs]
    rw [p412d_unique hK hKc hKo hρ hp.2.1 hp.2.2.1 hq.2.1 hq.2.2.1 hp.2.2.2.1 hq.2.2.2.1
      (hyS' _ hp) (hLC y hy) hp.2.2.2.2 hq.2.2.2.2]
  -- the indexed (rational-angle) arcs represent every arc of the family
  have hOKF : ∀ i, p412hOK K y ε i → (p412hC ε i, p412hY ε ρ i) ∈ F :=
    fun i hi => ⟨⟨_, hi.1, rfl⟩, hi.2⟩
  have hrep : ∀ p ∈ F, ∃ i, p412hOK K y ε i ∧ bs (p412hC ε i, p412hY ε ρ i) = bs p := by
    rintro ⟨c, y₀⟩ ⟨⟨m, hm, hc⟩, hA⟩
    simp only at hc hA
    subst hc
    obtain ⟨θ, hθ⟩ := p412h_rat_pt hKcl hKne hρ hA.1 hA.2.1
    obtain ⟨i, hi⟩ := p412h_Ix_surj m θ
    have hCi : p412hC ε i = p412hG ε m := by rw [p412hC, hi]
    have hYi : p412hY ε ρ i = p412hPt (p412hG ε m) ρ θ := by rw [p412hY, hCi, hi]
    have he : connectedComponentIn (sphere (p412hG ε m) ρ \ K) (p412hY ε ρ i) =
        connectedComponentIn (sphere (p412hG ε m) ρ \ K) y₀ := by
      rw [hYi]; exact (connectedComponentIn_eq hθ).symm
    have hYK : p412hY ε ρ i ∈ sphere (p412hG ε m) ρ \ K := by
      rw [hYi]; exact connectedComponentIn_subset _ _ hθ
    refine ⟨i, ⟨by rw [hi]; exact hm, ?_⟩, ?_⟩
    · rw [hCi]
      exact ⟨hYK.1, hYK.2, he ▸ hA.2.2.1, he ▸ hA.2.2.2⟩
    · simp only [bs, p412hBs, hCi, he]
  -- Step 1: every point of `𝒞^ε_y` is in the closure of some `U(α_B)`
  have hcov : ∀ x ∈ dcSetC K y ε, ∃ p ∈ F, x ∈ closure (bs p) := by
    rintro x ⟨-, X, hXK, hXc, hXd, v, hv, hb, hxV, hyV⟩
    obtain ⟨x₀, hx₀⟩ := hXc.nonempty
    have hXx₀ : ∀ z ∈ X, dist z x₀ ≤ ε := fun z hz => by
      have h := edist_le_of_ediam_le hz hx₀ hXd
      rw [edist_dist] at h
      exact (ENNReal.ofReal_le_ofReal_iff hε.le).1 h
    by_cases hx₀S : x₀ ∈ cthickening (3 * ε) K
    · obtain ⟨m, hmT, hc⟩ := p412h_T_cover hK hε hx₀S
      have hXB : X ⊆ ball (p412hG ε m) ρ := fun z hz => by
        rw [mem_ball]
        linarith [dist_triangle z x₀ (p412hG ε m), hXx₀ z hz]
      obtain ⟨y₀, hy₀, hy₀K, hαN, hVB, -⟩ := p412d_dagger hK hKc hKo hXK hρ hXB hv hb
      exact ⟨(p412hG ε m, y₀), ⟨⟨m, hmT, rfl⟩, hy₀, hy₀K, hαN, closure_mono hVB hyV⟩,
        closure_mono hVB hxV⟩
    · exfalso
      refine p412d_far hK hKc hKo hXK (c := x₀) (r := 2 * ε) (by positivity) (fun z hz => ?_)
        (fun k hk => ?_) hv hb hyV hyK
      · rw [mem_ball]; linarith [hXx₀ z hz]
      · by_contra hle
        exact hx₀S (mem_cthickening_of_dist_le x₀ k _ K hk (by rw [dist_comm]; linarith))
  -- maximal elements of `G` are represented by maximal indices
  have hmaxI : ∀ i, p412hOK K y ε i → Maximal (· ∈ G) (bs (p412hC ε i, p412hY ε ρ i)) →
      p412hMx K y ε i := fun i hi hS =>
    ⟨hi, fun j hj hij => (hS.2 (mem_image_of_mem bs (hOKF j hj)) (show bs (p412hC ε i, p412hY ε ρ i) ⊆
      bs (p412hC ε j, p412hY ε ρ j) from hij) : bs (p412hC ε j, p412hY ε ρ j) ⊆ bs (p412hC ε i, p412hY ε ρ i))⟩
  have hImax : ∀ i, p412hMx K y ε i → Maximal (· ∈ G) (bs (p412hC ε i, p412hY ε ρ i)) := by
    intro i hi
    refine ⟨mem_image_of_mem bs (hOKF i hi.1), ?_⟩
    rintro _ ⟨p, hp, rfl⟩ hle
    obtain ⟨j, hj, hje⟩ := hrep p hp
    have hle' : bs (p412hC ε i, p412hY ε ρ i) ⊆ bs p := hle
    rw [← hje] at hle' ⊢
    exact hi.2 j hj hle'
  by_cases hM : ∃ i, p412hMx K y ε i
  swap
  · left
    refine eq_empty_of_forall_notMem fun x hx => hM ?_
    obtain ⟨p, hp, -⟩ := hcov x hx
    obtain ⟨S, -, hS⟩ := hGf.exists_le_maximal (mem_image_of_mem bs hp)
    obtain ⟨p', hp', rfl⟩ := hS.1
    obtain ⟨j, hj, hje⟩ := hrep p' hp'
    exact ⟨j, hmaxI j hj (hje ▸ hS)⟩
  right
  obtain ⟨i₁, hi₁, hgd⟩ := p412h_gd_eq hM
  rw [hgd]
  have hS₁ := hImax i₁ hi₁
  have hp₁ := hOKF i₁ hi₁.1
  set c₁ := p412hC ε i₁ with hc₁
  set y₁ := p412hY ε ρ i₁ with hy₁
  set ρ' : ℝ := if dist y c₁ = 8 * ε then 7 * ε else 8 * ε with hρ'def
  have hρ'1 : 6 * ε < ρ' ∧ ρ' ≤ 8 * ε := by
    rw [hρ'def]; split_ifs <;> constructor <;> linarith
  have hρ'0 : 0 < ρ' := by linarith [hρ'1.1]
  have hyS'' : y ∉ sphere c₁ ρ' := by
    rw [mem_sphere, hρ'def]; split_ifs with h
    · intro h'; rw [h] at h'; linarith
    · exact h
  -- every maximal `U(α*)` lies in `U(β)` for an arc `β ⊆ cl N(B̃)` of `∂B̃ ∖ K`
  have hkey : ∀ S, Maximal (· ∈ G) S → ∃ z₀ ∈ sphere c₁ ρ', z₀ ∉ K ∧
      connectedComponentIn (sphere c₁ ρ' \ K) z₀ ⊆ closure (dgW (closedBall c₁ ρ' ∪ K)) ∧
      S ⊆ dgB (connectedComponentIn (sphere c₁ ρ' \ K) z₀ ∪ K) := by
    intro S hS
    obtain ⟨⟨c₂, y₂⟩, hp₂, rfl⟩ := hS.1
    have hmeet : (closure (connectedComponentIn (sphere c₂ ρ \ K) y₂) ∩
        closure (connectedComponentIn (sphere c₁ ρ \ K) y₁)).Nonempty := by
      rw [← not_disjoint_iff_nonempty_inter]
      intro hdis
      exact p412d_max_meet hK hKc hKo hρ hρ hp₂.2.1 hp₂.2.2.1 hp₁.2.1 hp₁.2.2.1 hdis
        (hyS' _ hp₂) (hLC y hy) hp₂.2.2.2.2 hp₁.2.2.2.2
        (fun h => hS.2 (mem_image_of_mem bs hp₁) h) (fun h => hS₁.2 (mem_image_of_mem bs hp₂) h)
    obtain ⟨q, hq₂, hq₁⟩ := hmeet
    have hq₂' := mem_sphere.1 ((isClosed_sphere.closure_subset_iff.2
      (cc_subset_sphere K c₂ y₂ ρ)) hq₂)
    have hq₁' := mem_sphere.1 ((isClosed_sphere.closure_subset_iff.2
      (cc_subset_sphere K c₁ y₁ ρ)) hq₁)
    have hXB : connectedComponentIn (sphere c₂ ρ \ K) y₂ ⊆ ball c₁ ρ' := fun z hz => by
      have hz' := mem_sphere.1 (cc_subset_sphere K c₂ y₂ ρ hz)
      rw [mem_ball]
      linarith [dist_triangle z c₂ c₁, dist_triangle_left c₂ c₁ q, hρ'1.1]
    have hXK : connectedComponentIn (sphere c₂ ρ \ K) y₂ ⊆ Kᶜ := fun z hz =>
      ((connectedComponentIn_subset _ _) hz).2
    obtain ⟨v, hv⟩ := closure_nonempty_iff.1 ⟨y, hp₂.2.2.2.2⟩
    obtain ⟨z₀, hz₀, hz₀K, hβN, hVB, -⟩ :=
      p412d_dagger hK hKc hKo hXK hρ'0 hXB hv.1 hv.2
    refine ⟨z₀, hz₀, hz₀K, hβN, ?_⟩
    simp only [bs, p412hBs]
    rw [p412d_dgB_eq_cc hK hKc hKo hρ hp₂.2.1 hp₂.2.2.1 hv]
    exact hVB
  obtain ⟨z₁, hz₁, hz₁K, hβ₁N, hS₁β⟩ := hkey _ hS₁
  have hyβ₁ : y ∈ closure (dgB (connectedComponentIn (sphere c₁ ρ' \ K) z₁ ∪ K)) :=
    closure_mono hS₁β hp₁.2.2.2.2
  -- the closed ball `B̃` meets `K`
  obtain ⟨k, hkc, hk⟩ := hi₁.1.1
  obtain ⟨u, w, -, -, hαB, -⟩ := p412d_arc hK hKc hKo hρ'0 hz₁ hz₁K
  obtain ⟨v, hv⟩ := closure_nonempty_iff.1 ⟨z₁, hαB (mem_connectedComponentIn ⟨hz₁, hz₁K⟩)⟩
  refine ⟨ρ', hρ'0, hρ'1.2, ⟨k, ?_, hk⟩, z₁, hz₁, hz₁K, v, hv.1, hv.2, ?_⟩
  · rw [mem_closedBall, dist_comm]
    have := mem_closedBall.1 hkc
    rw [dist_comm] at this
    simp only [c₁, p412hC]
    linarith [hρ'1.1]
  rw [← p412d_dgB_eq_cc hK hKc hKo hρ'0 hz₁ hz₁K hv]
  intro x hx
  obtain ⟨p, hp, hxp⟩ := hcov x hx
  obtain ⟨S, hpS, hS⟩ := hGf.exists_le_maximal (mem_image_of_mem bs hp)
  obtain ⟨z₂, hz₂, hz₂K, hβ₂N, hSβ⟩ := hkey S hS
  have hyβ₂ := closure_mono (hpS.trans hSβ) hp.2.2.2.2
  rw [p412d_unique hK hKc hKo hρ'0 hz₂ hz₂K hz₁ hz₁K hβ₂N hβ₁N hyS'' (hLC y hy) hyβ₂ hyβ₁]
    at hSβ
  exact closure_mono (hpS.trans hSβ) hxp

/-- **(∗) at every point of `B̄_{8ε}(gd(K, y))`** (D98 §2, DV-D98b): as in `p412e_goodZ_exists`,
with radius `r = 8ε`, since `cl(arc) ⊆ B̄_{ρ'}(gd) ⊆ B̄_{16ε}(x)`. -/
theorem p412h_goodZ {K : Set ℂ} (hK : IsCompact K) (hKc : IsConnected K)
    (hKo : IsPreconnected Kᶜ) (hLC : ∀ q ∈ frontier K, LocConnAt K q) {y : ℂ}
    (hy : y ∈ frontier K) {ε : ℝ} (hε : 0 < ε) {x : ℂ}
    (hx : x ∈ closedBall (p412hGd K y ε) (8 * ε)) : p412eGoodZ K y x ε := by
  have hKcl := hK.isClosed
  refine ⟨8 * ε, by positivity, le_rfl, fun F hF hFb hFc hKF X v P a b hX hXc hXd hv hb hyV hPa
    hPaK hab hP hPK hPb => ?_⟩
  rcases p412h_L414B hK hKc hKo hLC hy hε with hC | ⟨r, hr, hr8, ⟨k, hkB, hkK⟩, y₀, hy₀, hy₀K, u,
    hu, hub, hdc⟩
  · exfalso
    have := p412c_cc_subset_dcSetC hX hXc hXd hv hb hyV (mem_connectedComponentIn hv)
    rw [hC] at this; exact this
  set c := p412hGd K y ε
  set Y := connectedComponentIn (sphere c r \ K) y₀
  have hYB : closure Y ⊆ closedBall x (2 * (8 * ε)) := by
    refine closure_minimal (fun p hp => ?_) isClosed_closedBall
    have hp' : p ∈ sphere c r := (connectedComponentIn_subset _ _ hp).1
    rw [mem_closedBall] at hx ⊢
    rw [mem_sphere] at hp'
    linarith [dist_triangle p c x, dist_comm c x]
  have hYF : Y ∪ K ⊆ F := by
    refine union_subset (fun p hp => hKF ?_) fun p hp => hKF (self_subset_cthickening _ hp)
    have hp' : p ∈ sphere c r := (connectedComponentIn_subset _ _ hp).1
    refine mem_cthickening_of_dist_le p k _ K hkK ?_
    rw [mem_sphere] at hp'
    rw [mem_closedBall] at hkB
    linarith [dist_triangle p c k, dist_comm c k]
  have hUF := p412b_closure_cc_subset hYF hF hFb hFc hub
  have hVU : closure (connectedComponentIn (X ∪ K)ᶜ v) ⊆
      closure (connectedComponentIn (Y ∪ K)ᶜ u) := by
    have := closure_mono ((p412c_cc_subset_dcSetC hX hXc hXd hv hb hyV).trans hdc)
    rwa [closure_closure] at this
  have hPb' : P b ∉ connectedComponentIn (Y ∪ K)ᶜ u := fun h => hPb (hUF (subset_closure h))
  obtain ⟨s, hs, hsY⟩ := p412c_exit hab (hLC _ hPaK) (hVU hPa) hP hPK hPb'
  exact ⟨s, hs, hYB hsY⟩

end LQGMetric.GM
