/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.GM.S4.P412fEnd at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S4.P412eArcs
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S4.JordanJ1bFinal
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S4.Setup

/-!
# GM L4.15: the endpoints `𝒴_k` of the arcs of `Conf_k` and `#𝒴_k ≤ 2 #Conf_k`

Source: GM = `literature/src/1905.00383/uniqueness-final.tex`, l. 2106 ("let `𝒴_k` be the set
of endpoints of the arcs in `𝓘_k`") and l. 2155 ("`#𝒴_k = #𝓘_k`"), used for the union bound
(4.40′) over at most `ε^{-ω}` endpoints (l. 2177).

"Endpoint of `I`" is read as a point of `cl I ∩ cl(∂𝓑^•_t ∖ I)` (as in `p412e_endpoint`,
DV-L413-sep). `p412f_endpts_two`: a preconnected `I ⊆ ∂𝓑^•_t` has at most two endpoints
(own elementary proof via the Jordan parametrization `Ψ ∘ e^{2πi·}` of `gm_filledBall_conformal'`:
the parameters of `I` in a period starting at a point outside `I` form an interval `T`, and
the endpoints are the images of `inf T`, `sup T`). Hence `#𝒴_k ≤ 2 #Conf_k`
(`p412f_endSet_encard`); GM's equality `#𝒴_k = #𝓘_k` is not needed, the factor 2 is absorbed
in the union bound (proposed DEVIATIONS entry DV-Yk).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Metric
open LQGMetric.Blueprint

namespace LQGMetric.GM

/-- the endpoints `cl I ∩ cl(J ∖ I)` of `I ⊆ J` -/
def p412fEndpts (J I : Set ℂ) : Set ℂ := closure I ∩ closure (J \ I)

/-- **the endpoints of a connected subset of a parametrized Jordan curve**: two points -/
theorem p412f_endpts_param {φ : ℝ → ℂ} {t₀ t₁ : ℝ} (h01 : t₀ ≤ t₁)
    (hφc : ContinuousOn φ (Icc t₀ t₁))
    (hφi : InjOn φ (Ico t₀ t₁)) (hper : φ t₁ = φ t₀) {I : Set ℂ} (hI : IsPreconnected I)
    (hIJ : I ⊆ φ '' Icc t₀ t₁) (hp : φ t₀ ∉ I) :
    ∃ a b : ℂ, p412fEndpts (φ '' Icc t₀ t₁) I ⊆ {a, b} := by
  set J := φ '' Icc t₀ t₁
  set T := {t ∈ Ioo t₀ t₁ | φ t ∈ I} with hTdef
  have hcl : ∀ {u v : ℝ}, t₀ ≤ u → v ≤ t₁ → IsClosed (φ '' Icc u v) := fun hu hv =>
    ((isCompact_Icc).image_of_continuousOn
      (hφc.mono (Icc_subset_Icc hu hv))).isClosed
  -- every point of `I` is `φ r` with `r ∈ T`
  have hIT : ∀ w ∈ I, ∃ r ∈ T, φ r = w := by
    intro w hw
    obtain ⟨r, hr, rfl⟩ := hIJ hw
    refine ⟨r, ⟨⟨lt_of_le_of_ne hr.1 ?_, lt_of_le_of_ne hr.2 ?_⟩, hw⟩, rfl⟩
    · rintro rfl; exact hp hw
    · rintro rfl; exact hp (hper ▸ hw)
  -- injectivity up to the period
  have hinj : ∀ r ∈ Ioo t₀ t₁, ∀ r' ∈ Icc t₀ t₁, φ r = φ r' → r = r' := by
    intro r hr r' hr' he
    rcases eq_or_lt_of_le hr'.2 with h | h
    · exfalso; subst h
      have := hφi ⟨hr.1.le, hr.2⟩ ⟨le_rfl, h01.lt_of_ne (by rintro rfl; exact (hr.1.trans hr.2).false)⟩
        (he.trans hper)
      linarith [hr.1]
    · exact hφi ⟨hr.1.le, hr.2⟩ ⟨hr'.1, h⟩ he
  by_cases hT : T = ∅
  · refine ⟨0, 0, fun w hw => ?_⟩
    have hI0 : I = ∅ := eq_empty_iff_forall_notMem.2 fun w hw => by
      obtain ⟨r, hr, -⟩ := hIT w hw; rw [hT] at hr; exact hr
    have := hw.1; rw [hI0, closure_empty] at this; exact this.elim
  obtain ⟨x₀, hx₀⟩ := nonempty_iff_ne_empty.2 hT
  -- `T` is order-connected
  have hord : ∀ x ∈ T, ∀ y ∈ T, ∀ s, x < s → s < y → s ∈ T := by
    intro x hx y hy s hxs hsy
    have hs : s ∈ Ioo t₀ t₁ := ⟨hx.1.1.trans hxs, hsy.trans hy.1.2⟩
    by_contra hsT
    have hsI : φ s ∉ I := fun h => hsT ⟨hs, h⟩
    set U := (φ '' Icc s t₁)ᶜ
    set V := (φ '' Icc t₀ s)ᶜ
    have hU : IsOpen U := (hcl hs.1.le le_rfl).isOpen_compl
    have hV : IsOpen V := (hcl le_rfl hs.2.le).isOpen_compl
    have hIUV : I ⊆ U ∪ V := by
      intro w hw
      obtain ⟨r, hr, rfl⟩ := hIT w hw
      rcases lt_trichotomy r s with hrs | hrs | hrs
      · left; rintro ⟨r', hr', he⟩
        have := hinj r hr.1 r' ⟨hs.1.le.trans hr'.1, hr'.2⟩ he.symm; linarith [hr'.1]
      · exact absurd (hrs ▸ hr.2) hsI
      · right; rintro ⟨r', hr', he⟩
        have := hinj r hr.1 r' ⟨hr'.1, hr'.2.trans hs.2.le⟩ he.symm; linarith [hr'.2]
    obtain ⟨w, hwI, hwU, hwV⟩ := hI U V hU hV hIUV ⟨φ x, hx.2, hIUV hx.2 |>.resolve_right
      (fun h => h ⟨x, ⟨hx.1.1.le, hxs.le⟩, rfl⟩)⟩ ⟨φ y, hy.2, hIUV hy.2 |>.resolve_left
      (fun h => h ⟨y, ⟨hsy.le, hy.1.2.le⟩, rfl⟩)⟩
    obtain ⟨r, hr, rfl⟩ := hIJ hwI
    rcases le_total r s with h | h
    · exact hwV ⟨r, ⟨hr.1, h⟩, rfl⟩
    · exact hwU ⟨r, ⟨h, hr.2⟩, rfl⟩
  have hbb : BddBelow T := ⟨t₀, fun t ht => ht.1.1.le⟩
  have hba : BddAbove T := ⟨t₁, fun t ht => ht.1.2.le⟩
  set a := sInf T
  set b := sSup T
  have ha0 : t₀ ≤ a := le_csInf ⟨x₀, hx₀⟩ fun t ht => ht.1.1.le
  have hb1 : b ≤ t₁ := csSup_le ⟨x₀, hx₀⟩ fun t ht => ht.1.2.le
  have hab : a ≤ b := (csInf_le hbb hx₀).trans (le_csSup hba hx₀)
  have hTab : T ⊆ Icc a b := fun t ht => ⟨csInf_le hbb ht, le_csSup hba ht⟩
  have hIoo : Ioo a b ⊆ T := by
    intro c hc
    obtain ⟨x, hx, hxc⟩ := exists_lt_of_csInf_lt ⟨x₀, hx₀⟩ hc.1
    obtain ⟨y, hy, hcy⟩ := exists_lt_of_lt_csSup ⟨x₀, hx₀⟩ hc.2
    exact hord x hx y hy c hxc hcy
  have hclI : closure I ⊆ φ '' Icc a b := by
    refine closure_minimal (fun w hw => ?_) (hcl ha0 hb1)
    obtain ⟨r, hr, rfl⟩ := hIT w hw
    exact ⟨r, hTab hr, rfl⟩
  have hclJ : closure (J \ I) ⊆ φ '' Icc t₀ a ∪ φ '' Icc b t₁ := by
    refine closure_minimal (fun w hw => ?_) ((hcl (u := t₀) (v := a) le_rfl (hab.trans hb1)).union
      (hcl (u := b) (v := t₁) (ha0.trans hab) le_rfl))
    obtain ⟨r, hr, rfl⟩ := hw.1
    rcases le_or_gt r a with h | h
    · exact Or.inl ⟨r, ⟨hr.1, h⟩, rfl⟩
    rcases le_or_gt b r with h' | h'
    · exact Or.inr ⟨r, ⟨h', hr.2⟩, rfl⟩
    exact absurd (hIoo ⟨h, h'⟩).2 hw.2
  refine ⟨φ a, φ b, fun w hw => ?_⟩
  obtain ⟨r, hr, rfl⟩ := hclI hw.1
  -- `r ∈ {a, b}` up to the period
  rcases eq_or_lt_of_le hr.2 with hrb | hrb
  · rw [hrb]; exact Or.inr rfl
  rcases eq_or_lt_of_le hr.1 with hra | hra
  · rw [← hra]; exact Or.inl rfl
  have hrI : r ∈ Ioo t₀ t₁ := ⟨ha0.trans_lt hra, hrb.trans_le hb1⟩
  rcases hclJ hw.2 with ⟨r', hr', he⟩ | ⟨r', hr', he⟩
  · have := hinj r hrI r' ⟨hr'.1, hr'.2.trans (hab.trans hb1)⟩ he.symm; linarith [hr'.2]
  · have := hinj r hrI r' ⟨(ha0.trans hab).trans hr'.1, hr'.2⟩ he.symm; linarith [hr'.1]

/-- **a preconnected `I ⊆ ∂𝓑^•_t` has at most two endpoints** -/
theorem p412f_endpts_two {D : ContMetric} {𝕫 : ℂ} {t : ℝ} (ht : 0 < t) (hL : D.IsLength)
    (hbd : Bornology.IsBounded (ballM D 𝕫 t)) {I : Set ℂ} (hIc : IsPreconnected I)
    (hIJ : I ⊆ frontier (filledBall D 𝕫 t)) :
    ∃ a b : ℂ, p412fEndpts (frontier (filledBall D 𝕫 t)) I ⊆ {a, b} := by
  obtain ⟨Ψ, hΨc, hΨi, -, -, hΨS, -⟩ := gm_filledBall_conformal' ht hL hbd
  by_cases hfull : frontier (filledBall D 𝕫 t) ⊆ I
  · refine ⟨0, 0, fun w hw => ?_⟩
    have : frontier (filledBall D 𝕫 t) \ I = ∅ := sdiff_eq_empty.2 hfull
    have h2 := hw.2; rw [this, closure_empty] at h2; exact h2.elim
  obtain ⟨p, hpJ, hpI⟩ := not_subset.1 hfull
  have hsub : sphere (0 : ℂ) 1 ⊆ closedBall 0 1 \ {0} := fun w hw =>
    ⟨sphere_subset_closedBall hw, fun h => by
      rw [mem_singleton_iff] at h; rw [h, mem_sphere_zero_iff_norm, norm_zero] at hw
      exact zero_ne_one hw⟩
  rw [← hΨS] at hpJ
  obtain ⟨ζ, hζ, rfl⟩ := hpJ
  obtain ⟨t₀, rfl⟩ := p412eC_surj hζ
  set φ : ℝ → ℂ := Ψ ∘ p412eC with hφ
  have hJ : φ '' Icc t₀ (t₀ + 1) = frontier (filledBall D 𝕫 t) := by
    rw [hφ, image_comp, p412eC_image_Icc, hΨS]
  have hφc : ContinuousOn φ (Icc t₀ (t₀ + 1)) :=
    (hΨc.mono hsub).comp p412eC_continuous.continuousOn fun s _ => p412eC_mem s
  have hφi : InjOn φ (Ico t₀ (t₀ + 1)) := by
    intro s hs s' hs' he
    have h1 : p412eC s = p412eC s' := (hΨi.mono hsub) (p412eC_mem s) (p412eC_mem s') he
    rcases p412eC_inj ⟨hs.1, hs.2.le⟩ ⟨hs'.1, hs'.2.le⟩ h1 with h | h | h
    · exact h
    · linarith [h.2, hs'.2]
    · linarith [h.1, hs.2]
  have hper : φ (t₀ + 1) = φ t₀ := by
    have := p412eC_add_int t₀ 1; push_cast at this
    simp only [hφ, Function.comp_apply, this]
  rw [← hJ] at hIJ ⊢
  exact p412f_endpts_param (by linarith) hφc hφi hper hIc hIJ hpI

/-- GM's `𝒴_k`: the endpoints of the arcs `arcOf x`, `x ∈ Conf(s, t)` -/
def p412fEndSet (D : ContMetric) (𝕫 : ℂ) (s t : ℝ) : Set ℂ :=
  ⋃ x ∈ confPts D 𝕫 s t, p412fEndpts (frontier (filledBall D 𝕫 t)) (arcOf D 𝕫 t x)

theorem p412f_endpts_subset_endSet {D : ContMetric} {𝕫 : ℂ} {s t : ℝ} {x : ℂ}
    (hx : x ∈ confPts D 𝕫 s t) :
    closure (arcOf D 𝕫 t x) ∩ closure (frontier (filledBall D 𝕫 t) \ arcOf D 𝕫 t x) ⊆
      p412fEndSet D 𝕫 s t :=
  subset_biUnion_of_mem (u := fun x => p412fEndpts (frontier (filledBall D 𝕫 t))
    (arcOf D 𝕫 t x)) hx

/-- **`#𝒴_k ≤ 2 #Conf_k`** (GM l. 2155, with the factor 2, DV-Yk) -/
theorem p412f_endSet_encard {D : ContMetric} {𝕫 : ℂ} {s t : ℝ} (ht : 0 < t) (hL : D.IsLength)
    (hbd : Bornology.IsBounded (ballM D 𝕫 t))
    (harc : ∀ x ∈ confPts D 𝕫 s t, IsBdyArc D 𝕫 t (arcOf D 𝕫 t x)) :
    (p412fEndSet D 𝕫 s t).encard ≤ 2 * (confPts D 𝕫 s t).encard := by
  classical
  set C := confPts D 𝕫 s t
  have H : ∀ x ∈ C, ∃ ab : ℂ × ℂ,
      p412fEndpts (frontier (filledBall D 𝕫 t)) (arcOf D 𝕫 t x) ⊆ {ab.1, ab.2} := by
    intro x hx
    obtain ⟨a, b, hab⟩ := p412f_endpts_two ht hL hbd (harc x hx).2.isPreconnected (harc x hx).1
    exact ⟨(a, b), hab⟩
  choose! f hf using H
  have hsub : p412fEndSet D 𝕫 s t ⊆ (fun x => (f x).1) '' C ∪ (fun x => (f x).2) '' C := by
    intro w hw
    obtain ⟨x, hx, hwx⟩ := mem_iUnion₂.1 hw
    rcases hf x hx hwx with h | h
    · exact Or.inl ⟨x, hx, h.symm⟩
    · exact Or.inr ⟨x, hx, (mem_singleton_iff.1 h).symm⟩
  calc (p412fEndSet D 𝕫 s t).encard
      ≤ ((fun x => (f x).1) '' C ∪ (fun x => (f x).2) '' C).encard := encard_le_encard hsub
    _ ≤ ((fun x => (f x).1) '' C).encard + ((fun x => (f x).2) '' C).encard :=
        encard_union_le _ _
    _ ≤ C.encard + C.encard := add_le_add (encard_image_le _ _) (encard_image_le _ _)
    _ = 2 * C.encard := by rw [two_mul]

end LQGMetric.GM
