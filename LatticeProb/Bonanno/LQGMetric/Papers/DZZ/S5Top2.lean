/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DZZ.S5Top2 at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.S5Top1

/-!
# D117 P-GLUE (2): the ring of four crossings separates (DZZ Fig. glue)

DZZ = Ding–Zeitouni–Zhang, arXiv:1807.00422, `LBM_LGDarXiv.tex` l. 2562–2568 (proof of L5.4:
"four short crossings through four rectangles … which altogether form a contour enclosing
`L_δ`") and l. 2605 (proof of L6.1: "the union of these short crossings, the geodesic between
`L_δ` and `∂𝕍̄_u`, … contains a path between `v_{L_δ}` and `∂𝕍̄_u`").

The four rectangles are the strips of the rectangular annulus between the inner rectangle
`[x₁, x₂] × [y₁, y₂]` and the outer rectangle `[x₀, x₃] × [y₀, y₃]`:
bottom `[x₀, x₃] × [y₀, y₁]`, top `[x₀, x₃] × [y₂, y₃]` (crossed left–right), left
`[x₀, x₁] × [y₀, y₃]`, right `[x₂, x₃] × [y₀, y₃]` (crossed bottom–top). We prove what DZZ use:

* `dzz_ring_sep`: a path-connected set joining a point of the inner rectangle to a point outside
  the open outer rectangle meets one of the four crossings;
* `dzz_ring_isPathConnected`: the union of the four crossings is path-connected (consecutive
  crossings meet in the corner squares);
* `dzz_ring_glue`: hence the union of the ring with two such sets is path-connected (the gluing
  of the two legs in DZZ l. 2563–2566).

Both facts reduce to the rectangle crossing lemma (`Sector.lr_tb_meet`, S5Top1). The reduction
(first passage from the inner to the outer rectangle through a strip, extracted with
`RectCross.exists_sub_crossing`) is an own elementary argument: DZZ only say "form a contour
enclosing `L_δ`" (DV-D117-GLUE, proposed).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace LQGMetric
namespace DZZ

open Set

/-- The normalised "annulus coordinate": `≤ 0` on the inner rectangle, `≥ 1` off the open outer
rectangle, `≤ 1` exactly on the outer rectangle. -/
noncomputable def ringPhi (x₀ x₁ x₂ x₃ y₀ y₁ y₂ y₃ : ℝ) (z : ℂ) : ℝ :=
  max (max ((z.re - x₂) / (x₃ - x₂)) ((x₁ - z.re) / (x₁ - x₀)))
    (max ((z.im - y₂) / (y₃ - y₂)) ((y₁ - z.im) / (y₁ - y₀)))

theorem continuous_ringPhi (x₀ x₁ x₂ x₃ y₀ y₁ y₂ y₃ : ℝ) :
    Continuous (ringPhi x₀ x₁ x₂ x₃ y₀ y₁ y₂ y₃) := by
  unfold ringPhi; fun_prop

/-- The image of a parameter interval under a continuous map is a compact continuum. -/
theorem img_Icc_props {f : ℝ → ℂ} (hf : Continuous f) {s t : ℝ} (hst : s ≤ t) :
    IsCompact (f '' Icc s t) ∧ IsPreconnected (f '' Icc s t) ∧ f s ∈ f '' Icc s t ∧
      f t ∈ f '' Icc s t :=
  ⟨isCompact_Icc.image hf, isPreconnected_Icc.image _ hf.continuousOn,
    ⟨s, left_mem_Icc.2 hst, rfl⟩, ⟨t, right_mem_Icc.2 hst, rfl⟩⟩

variable {x₀ x₁ x₂ x₃ y₀ y₁ y₂ y₃ : ℝ}

/-- A compact left–right crossing continuum meets a path-connected bottom–top crossing. -/
theorem meet_LR {X0 X1 Y0 Y1 : ℝ} (hX : X0 ≤ X1) (hY : Y0 ≤ Y1) {M S : Set ℂ} (hM : IsCompact M)
    (hMp : IsPreconnected M) (hMR : M ⊆ Icc X0 X1 ×ℂ Icc Y0 Y1) (hM0 : ∃ z ∈ M, z.re = X0)
    (hM1 : ∃ z ∈ M, z.re = X1) (hS : IsPathConnected S) (hSR : S ⊆ Icc X0 X1 ×ℂ Icc Y0 Y1)
    (hS0 : (S ∩ Icc X0 X1 ×ℂ {Y0}).Nonempty) (hS1 : (S ∩ Icc X0 X1 ×ℂ {Y1}).Nonempty) :
    ∃ z ∈ M, z ∈ S := by
  obtain ⟨a, haS, ha⟩ := hS0
  obtain ⟨b, hbS, hb⟩ := hS1
  obtain ⟨L, hLc, hLp, hLS, haL, hbL⟩ := exists_compact_conn_of_pathConn hS haS hbS
  rw [Complex.mem_reProdIm] at ha hb
  have hR : Icc X0 X1 ×ℂ Icc Y0 Y1 = RectCross.rect X0 X1 Y0 Y1 := Sector.rect_eq.symm
  obtain ⟨z, hzM, hzL⟩ := Sector.lr_tb_meet hX hY hM hMp (hMR.trans hR.le) hM0 hM1 hLc hLp
    ((hLS.trans hSR).trans hR.le) ⟨b, hbL, hb.2⟩ ⟨a, haL, ha.2⟩
  exact ⟨z, hzM, hLS hzL⟩

/-- A compact bottom–top crossing continuum meets a path-connected left–right crossing. -/
theorem meet_BT {X0 X1 Y0 Y1 : ℝ} (hX : X0 ≤ X1) (hY : Y0 ≤ Y1) {M S : Set ℂ} (hM : IsCompact M)
    (hMp : IsPreconnected M) (hMR : M ⊆ Icc X0 X1 ×ℂ Icc Y0 Y1) (hM0 : ∃ z ∈ M, z.im = Y0)
    (hM1 : ∃ z ∈ M, z.im = Y1) (hS : IsPathConnected S) (hSR : S ⊆ Icc X0 X1 ×ℂ Icc Y0 Y1)
    (hS0 : (S ∩ {X0} ×ℂ Icc Y0 Y1).Nonempty) (hS1 : (S ∩ {X1} ×ℂ Icc Y0 Y1).Nonempty) :
    ∃ z ∈ M, z ∈ S := by
  obtain ⟨a, haS, ha⟩ := hS0
  obtain ⟨b, hbS, hb⟩ := hS1
  obtain ⟨L, hLc, hLp, hLS, haL, hbL⟩ := exists_compact_conn_of_pathConn hS haS hbS
  rw [Complex.mem_reProdIm] at ha hb
  have hR : Icc X0 X1 ×ℂ Icc Y0 Y1 = RectCross.rect X0 X1 Y0 Y1 := Sector.rect_eq.symm
  obtain ⟨z, hzL, hzM⟩ := Sector.lr_tb_meet hX hY hLc hLp ((hLS.trans hSR).trans hR.le)
    ⟨a, haL, ha.1⟩ ⟨b, hbL, hb.1⟩ hM hMp (hMR.trans hR.le) hM1 hM0
  exact ⟨z, hzM, hLS hzL⟩

/-- **The ring separates** (DZZ Fig. glue, l. 2566 and 2605). -/
theorem dzz_ring_sep (hx01 : x₀ < x₁) (hx23 : x₂ < x₃) (hy01 : y₀ < y₁) (hy23 : y₂ < y₃)
    {Sb St Sl Sr T : Set ℂ}
    (hSb : IsPathConnected Sb) (hSbR : Sb ⊆ Icc x₀ x₃ ×ℂ Icc y₀ y₁)
    (hSb0 : (Sb ∩ {x₀} ×ℂ Icc y₀ y₁).Nonempty) (hSb1 : (Sb ∩ {x₃} ×ℂ Icc y₀ y₁).Nonempty)
    (hSt : IsPathConnected St) (hStR : St ⊆ Icc x₀ x₃ ×ℂ Icc y₂ y₃)
    (hSt0 : (St ∩ {x₀} ×ℂ Icc y₂ y₃).Nonempty) (hSt1 : (St ∩ {x₃} ×ℂ Icc y₂ y₃).Nonempty)
    (hSl : IsPathConnected Sl) (hSlR : Sl ⊆ Icc x₀ x₁ ×ℂ Icc y₀ y₃)
    (hSl0 : (Sl ∩ Icc x₀ x₁ ×ℂ {y₀}).Nonempty) (hSl1 : (Sl ∩ Icc x₀ x₁ ×ℂ {y₃}).Nonempty)
    (hSr : IsPathConnected Sr) (hSrR : Sr ⊆ Icc x₂ x₃ ×ℂ Icc y₀ y₃)
    (hSr0 : (Sr ∩ Icc x₂ x₃ ×ℂ {y₀}).Nonempty) (hSr1 : (Sr ∩ Icc x₂ x₃ ×ℂ {y₃}).Nonempty)
    (hT : IsPathConnected T) {p q : ℂ} (hpT : p ∈ T) (hqT : q ∈ T)
    (hp : p ∈ Icc x₁ x₂ ×ℂ Icc y₁ y₂) (hq : q ∉ Ioo x₀ x₃ ×ℂ Ioo y₀ y₃) :
    (T ∩ (Sb ∪ St ∪ Sl ∪ Sr)).Nonempty := by
  have hj := hT.joinedIn p hpT q hqT
  set f : ℝ → ℂ := fun u => hj.somePath.extend u with hfdef
  have hfc : Continuous f := hj.somePath.continuous_extend
  have hfT : ∀ u, f u ∈ T := fun u => by
    exact hj.somePath_mem (projIcc 0 1 zero_le_one u)
  have hf0 : f 0 = p := by simp [hfdef]
  have hf1 : f 1 = q := by simp [hfdef]
  set φ := ringPhi x₀ x₁ x₂ x₃ y₀ y₁ y₂ y₃ with hφ
  have hd1 : 0 < x₃ - x₂ := sub_pos.2 hx23
  have hd2 : 0 < x₁ - x₀ := sub_pos.2 hx01
  have hd3 : 0 < y₃ - y₂ := sub_pos.2 hy23
  have hd4 : 0 < y₁ - y₀ := sub_pos.2 hy01
  rw [Complex.mem_reProdIm] at hp
  have hφp : φ (f 0) ≤ 0 := by
    rw [hf0, hφ, ringPhi]
    refine max_le (max_le ?_ ?_) (max_le ?_ ?_) <;> rw [div_le_iff₀ (by assumption)] <;>
      linarith [hp.1.1, hp.1.2, hp.2.1, hp.2.2]
  have hφq : 1 ≤ φ (f 1) := by
    rw [hf1, hφ, ringPhi]
    rw [Complex.mem_reProdIm, not_and_or, mem_Ioo, mem_Ioo, not_and_or, not_and_or,
      not_lt, not_lt, not_lt, not_lt] at hq
    rcases hq with (h | h) | (h | h)
    · exact le_max_of_le_left (le_max_of_le_right (by rw [le_div_iff₀ hd2]; linarith))
    · exact le_max_of_le_left (le_max_of_le_left (by rw [le_div_iff₀ hd1]; linarith))
    · exact le_max_of_le_right (le_max_of_le_right (by rw [le_div_iff₀ hd4]; linarith))
    · exact le_max_of_le_right (le_max_of_le_left (by rw [le_div_iff₀ hd3]; linarith))
  obtain ⟨s, t, -, hst, -, hφs, hφt, hφI⟩ := RectCross.exists_sub_crossing (f := fun u => φ (f u))
    zero_le_one ((continuous_ringPhi _ _ _ _ _ _ _ _).comp hfc).continuousOn zero_le_one hφp hφq
  -- on `[s, t]` the path stays in the outer rectangle
  have hout : ∀ u ∈ Icc s t, (f u).re ∈ Icc x₀ x₃ ∧ (f u).im ∈ Icc y₀ y₃ := by
    intro u hu
    have h := (hφI u hu).2
    simp only [hφ, ringPhi, max_le_iff] at h
    obtain ⟨⟨h1, h2⟩, h3, h4⟩ := h
    rw [div_le_iff₀ hd1] at h1; rw [div_le_iff₀ hd2] at h2
    rw [div_le_iff₀ hd3] at h3; rw [div_le_iff₀ hd4] at h4
    exact ⟨⟨by linarith, by linarith⟩, by linarith, by linarith⟩
  have hs0 : (f s).re ∈ Icc x₁ x₂ ∧ (f s).im ∈ Icc y₁ y₂ := by
    have h := hφs.le
    simp only [hφ, ringPhi, max_le_iff] at h
    obtain ⟨⟨h1, h2⟩, h3, h4⟩ := h
    rw [div_le_iff₀ hd1] at h1; rw [div_le_iff₀ hd2] at h2
    rw [div_le_iff₀ hd3] at h3; rw [div_le_iff₀ hd4] at h4
    exact ⟨⟨by linarith, by linarith⟩, by linarith, by linarith⟩
  have hfre : Continuous fun u => (f u).re := Complex.continuous_re.comp hfc
  have hfim : Continuous fun u => (f u).im := Complex.continuous_im.comp hfc
  -- which side is hit at time `t`
  have hle := (hφI t (right_mem_Icc.2 hst)).2
  simp only [hφ, ringPhi, max_le_iff] at hle
  have hside : (f t).re = x₃ ∨ (f t).re = x₀ ∨ (f t).im = y₃ ∨ (f t).im = y₀ := by
    have h4 : ((f t).re - x₂) / (x₃ - x₂) = 1 ∨ (x₁ - (f t).re) / (x₁ - x₀) = 1 ∨
        ((f t).im - y₂) / (y₃ - y₂) = 1 ∨ (y₁ - (f t).im) / (y₁ - y₀) = 1 := by
      by_contra hno
      simp only [not_or] at hno
      have : φ (f t) < 1 := by
        simp only [hφ, ringPhi, max_lt_iff]
        exact ⟨⟨lt_of_le_of_ne hle.1.1 hno.1, lt_of_le_of_ne hle.1.2 hno.2.1⟩,
          lt_of_le_of_ne hle.2.1 hno.2.2.1, lt_of_le_of_ne hle.2.2 hno.2.2.2⟩
      linarith
    rcases h4 with h | h | h | h <;> rw [div_eq_one_iff_eq (by positivity)] at h
    · exact Or.inl (by linarith)
    · exact Or.inr (Or.inl (by linarith))
    · exact Or.inr (Or.inr (Or.inl (by linarith)))
    · exact Or.inr (Or.inr (Or.inr (by linarith)))
  have hsub : ∀ {s' t' : ℝ}, s ≤ s' → t' ≤ t → ∀ u ∈ Icc s' t', u ∈ Icc s t :=
    fun h1 h2 u hu => ⟨h1.trans hu.1, hu.2.trans h2⟩
  have hy03 : y₀ ≤ y₃ := by linarith [hs0.2.1, hs0.2.2]
  have hx03 : x₀ ≤ x₃ := by linarith [hs0.1.1, hs0.1.2]
  rcases hside with h | h | h | h
  · -- right strip, crossed left–right by `f`, bottom–top by `Sr`
    obtain ⟨s', t', h1, h2, h3, hs', ht', hI⟩ := RectCross.exists_sub_crossing (f := fun u => (f u).re)
      hst hfre.continuousOn hx23.le hs0.1.2 h.ge
    obtain ⟨hMc, hMp, hMs, hMt⟩ := img_Icc_props hfc h2
    obtain ⟨z, hzM, hzS⟩ := meet_LR hx23.le hy03 hMc hMp
      (by rintro _ ⟨u, hu, rfl⟩; exact Complex.mem_reProdIm.2 ⟨hI u hu, (hout u (hsub h1 h3 u hu)).2⟩)
      ⟨_, hMs, hs'⟩ ⟨_, hMt, ht'⟩ hSr hSrR hSr0 hSr1
    obtain ⟨u, -, rfl⟩ := hzM
    exact ⟨f u, hfT u, Or.inr hzS⟩
  · -- left strip
    obtain ⟨s', t', h1, h2, h3, hs', ht', hI⟩ := RectCross.exists_sub_crossing' (f := fun u => (f u).re)
      hst hfre.continuousOn hx01.le hs0.1.1 h.le
    obtain ⟨hMc, hMp, hMs, hMt⟩ := img_Icc_props hfc h2
    obtain ⟨z, hzM, hzS⟩ := meet_LR hx01.le hy03 hMc hMp
      (by rintro _ ⟨u, hu, rfl⟩; exact Complex.mem_reProdIm.2 ⟨hI u hu, (hout u (hsub h1 h3 u hu)).2⟩)
      ⟨_, hMt, ht'⟩ ⟨_, hMs, hs'⟩ hSl hSlR hSl0 hSl1
    obtain ⟨u, -, rfl⟩ := hzM
    exact ⟨f u, hfT u, Or.inl (Or.inr hzS)⟩
  · -- top strip
    obtain ⟨s', t', h1, h2, h3, hs', ht', hI⟩ := RectCross.exists_sub_crossing (f := fun u => (f u).im)
      hst hfim.continuousOn hy23.le hs0.2.2 h.ge
    obtain ⟨hMc, hMp, hMs, hMt⟩ := img_Icc_props hfc h2
    obtain ⟨z, hzM, hzS⟩ := meet_BT hx03 hy23.le hMc hMp
      (by rintro _ ⟨u, hu, rfl⟩; exact Complex.mem_reProdIm.2 ⟨(hout u (hsub h1 h3 u hu)).1, hI u hu⟩)
      ⟨_, hMs, hs'⟩ ⟨_, hMt, ht'⟩ hSt hStR hSt0 hSt1
    obtain ⟨u, -, rfl⟩ := hzM
    exact ⟨f u, hfT u, Or.inl (Or.inl (Or.inr hzS))⟩
  · -- bottom strip
    obtain ⟨s', t', h1, h2, h3, hs', ht', hI⟩ := RectCross.exists_sub_crossing' (f := fun u => (f u).im)
      hst hfim.continuousOn hy01.le hs0.2.1 h.le
    obtain ⟨hMc, hMp, hMs, hMt⟩ := img_Icc_props hfc h2
    obtain ⟨z, hzM, hzS⟩ := meet_BT hx03 hy01.le hMc hMp
      (by rintro _ ⟨u, hu, rfl⟩; exact Complex.mem_reProdIm.2 ⟨(hout u (hsub h1 h3 u hu)).1, hI u hu⟩)
      ⟨_, hMt, ht'⟩ ⟨_, hMs, hs'⟩ hSb hSbR hSb0 hSb1
    obtain ⟨u, -, rfl⟩ := hzM
    exact ⟨f u, hfT u, Or.inl (Or.inl (Or.inl hzS))⟩

end DZZ
end LQGMetric
