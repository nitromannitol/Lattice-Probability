/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DZZ.S5Top3 at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.S5Top2

/-!
# D117 P-GLUE (3): the ring of four crossings is path-connected; gluing of the legs

DZZ = Ding–Zeitouni–Zhang, arXiv:1807.00422, `LBM_LGDarXiv.tex` l. 2562–2566 (the four short
crossings "altogether form a contour enclosing `L_δ`", glued with the geodesics from `u` and
from `v` to `L_δ`) and l. 2605 (L6.1: the union of the crossings and of two geodesics "contains a
path between `v_{L_δ}` and `∂𝕍̄_u`").

* `dzz_ring_isPathConnected`: consecutive crossings meet in the corner squares (rectangle
  crossing lemma, `Sector.lr_tb_meet`, on sub-crossings of the corner squares), so the union of
  the four crossings is path-connected;
* `dzz_ring_glue`: two path-connected sets, each joining the inner rectangle to the complement of
  the open outer rectangle, together with the ring form a path-connected set (`dzz_ring_sep`).

Own elementary argument from the crossing lemma (DV-D117-GLUE, proposed).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace LQGMetric
namespace DZZ

open Set

/-- A left–right crossing of `[X0, X3] × I` contains a compact continuum crossing
`[z, w] × I` left–right, for `X0 ≤ z ≤ w ≤ X3`. -/
theorem sub_LR {X0 X3 z w : ℝ} {I : Set ℝ} {S : Set ℂ} (hS : IsPathConnected S)
    (hSR : S ⊆ Icc X0 X3 ×ℂ I) {a b : ℂ} (ha : a ∈ S) (hb : b ∈ S) (har : a.re = X0)
    (hbr : b.re = X3) (hz : X0 ≤ z) (hzw : z ≤ w) (hw : w ≤ X3) :
    ∃ M : Set ℂ, IsCompact M ∧ IsPreconnected M ∧ M ⊆ S ∧ M ⊆ Icc z w ×ℂ I ∧
      (∃ m ∈ M, m.re = z) ∧ ∃ m ∈ M, m.re = w := by
  have hj := hS.joinedIn a ha b hb
  set f : ℝ → ℂ := fun u => hj.somePath.extend u with hfdef
  have hfc : Continuous f := hj.somePath.continuous_extend
  have hfS : ∀ u, f u ∈ S := fun u => hj.somePath_mem (projIcc 0 1 zero_le_one u)
  have hf0 : (f 0).re = X0 := by simp [hfdef, har]
  have hf1 : (f 1).re = X3 := by simp [hfdef, hbr]
  obtain ⟨s, t, -, hst, -, hs, ht, hI⟩ := RectCross.exists_sub_crossing (f := fun u => (f u).re)
    zero_le_one (Complex.continuous_re.comp hfc).continuousOn hzw (hf0.le.trans hz)
    (hw.trans hf1.ge)
  obtain ⟨hMc, hMp, hMs, hMt⟩ := img_Icc_props hfc hst
  refine ⟨f '' Icc s t, hMc, hMp, ?_, ?_, ⟨_, hMs, hs⟩, ⟨_, hMt, ht⟩⟩
  · rintro _ ⟨u, -, rfl⟩; exact hfS u
  · rintro _ ⟨u, hu, rfl⟩
    exact Complex.mem_reProdIm.2 ⟨hI u hu, (Complex.mem_reProdIm.1 (hSR (hfS u))).2⟩

/-- The bottom–top version of `sub_LR`. -/
theorem sub_BT {Y0 Y3 z w : ℝ} {I : Set ℝ} {S : Set ℂ} (hS : IsPathConnected S)
    (hSR : S ⊆ I ×ℂ Icc Y0 Y3) {a b : ℂ} (ha : a ∈ S) (hb : b ∈ S) (har : a.im = Y0)
    (hbr : b.im = Y3) (hz : Y0 ≤ z) (hzw : z ≤ w) (hw : w ≤ Y3) :
    ∃ M : Set ℂ, IsCompact M ∧ IsPreconnected M ∧ M ⊆ S ∧ M ⊆ I ×ℂ Icc z w ∧
      (∃ m ∈ M, m.im = z) ∧ ∃ m ∈ M, m.im = w := by
  have hj := hS.joinedIn a ha b hb
  set f : ℝ → ℂ := fun u => hj.somePath.extend u with hfdef
  have hfc : Continuous f := hj.somePath.continuous_extend
  have hfS : ∀ u, f u ∈ S := fun u => hj.somePath_mem (projIcc 0 1 zero_le_one u)
  have hf0 : (f 0).im = Y0 := by simp [hfdef, har]
  have hf1 : (f 1).im = Y3 := by simp [hfdef, hbr]
  obtain ⟨s, t, -, hst, -, hs, ht, hI⟩ := RectCross.exists_sub_crossing (f := fun u => (f u).im)
    zero_le_one (Complex.continuous_im.comp hfc).continuousOn hzw (hf0.le.trans hz)
    (hw.trans hf1.ge)
  obtain ⟨hMc, hMp, hMs, hMt⟩ := img_Icc_props hfc hst
  refine ⟨f '' Icc s t, hMc, hMp, ?_, ?_, ⟨_, hMs, hs⟩, ⟨_, hMt, ht⟩⟩
  · rintro _ ⟨u, -, rfl⟩; exact hfS u
  · rintro _ ⟨u, hu, rfl⟩
    exact Complex.mem_reProdIm.2 ⟨(Complex.mem_reProdIm.1 (hSR (hfS u))).1, hI u hu⟩

/-- Corner meeting: a left–right crossing of a horizontal strip and a bottom–top crossing of a
vertical strip meet in the corner square `[z, w] × [z', w']`. -/
theorem corner_meet {X0 X3 Y0 Y3 z w z' w' : ℝ} {I J : Set ℝ} {S S' : Set ℂ}
    (hS : IsPathConnected S) (hSR : S ⊆ Icc X0 X3 ×ℂ I) (hSI : I ⊆ Icc z' w')
    (hS0 : (S ∩ {X0} ×ℂ I).Nonempty) (hS1 : (S ∩ {X3} ×ℂ I).Nonempty)
    (hS' : IsPathConnected S') (hS'R : S' ⊆ J ×ℂ Icc Y0 Y3) (hJ : J ⊆ Icc z w)
    (hS'0 : (S' ∩ J ×ℂ {Y0}).Nonempty) (hS'1 : (S' ∩ J ×ℂ {Y3}).Nonempty)
    (hz : X0 ≤ z) (hzw : z ≤ w) (hw : w ≤ X3) (hz' : Y0 ≤ z') (hzw' : z' ≤ w') (hw' : w' ≤ Y3) :
    (S ∩ S').Nonempty := by
  obtain ⟨a, haS, ha⟩ := hS0
  obtain ⟨b, hbS, hb⟩ := hS1
  obtain ⟨a', haS', ha'⟩ := hS'0
  obtain ⟨b', hbS', hb'⟩ := hS'1
  rw [Complex.mem_reProdIm] at ha hb ha' hb'
  obtain ⟨M, hMc, hMp, hMS, hMR, hM0, hM1⟩ := sub_LR hS hSR haS hbS ha.1 hb.1 hz hzw hw
  obtain ⟨M', hM'c, hM'p, hM'S, hM'R, hM'0, hM'1⟩ :=
    sub_BT hS' hS'R haS' hbS' ha'.2 hb'.2 hz' hzw' hw'
  have hR : ∀ {a b c d : ℝ}, Icc a b ×ℂ Icc c d = RectCross.rect a b c d := Sector.rect_eq.symm
  obtain ⟨m, hmM, hmM'⟩ := Sector.lr_tb_meet hzw hzw' hMc hMp
    (hR.le.trans' (hMR.trans fun m hm => by
      rw [Complex.mem_reProdIm] at hm ⊢; exact ⟨hm.1, hSI hm.2⟩)) hM0 hM1 hM'c hM'p
    (hR.le.trans' (hM'R.trans fun m hm => by
      rw [Complex.mem_reProdIm] at hm ⊢; exact ⟨hJ hm.1, hm.2⟩)) hM'1 hM'0
  exact ⟨m, hMS hmM, hM'S hmM'⟩

variable {x₀ x₁ x₂ x₃ y₀ y₁ y₂ y₃ : ℝ}

/-- **The ring of four crossings is path-connected** (DZZ Fig. glue, "a contour"). -/
theorem dzz_ring_isPathConnected (hx01 : x₀ ≤ x₁) (hx12 : x₁ ≤ x₂) (hx23 : x₂ ≤ x₃)
    (hy01 : y₀ ≤ y₁) (hy12 : y₁ ≤ y₂) (hy23 : y₂ ≤ y₃) {Sb St Sl Sr : Set ℂ}
    (hSb : IsPathConnected Sb) (hSbR : Sb ⊆ Icc x₀ x₃ ×ℂ Icc y₀ y₁)
    (hSb0 : (Sb ∩ {x₀} ×ℂ Icc y₀ y₁).Nonempty) (hSb1 : (Sb ∩ {x₃} ×ℂ Icc y₀ y₁).Nonempty)
    (hSt : IsPathConnected St) (hStR : St ⊆ Icc x₀ x₃ ×ℂ Icc y₂ y₃)
    (hSt0 : (St ∩ {x₀} ×ℂ Icc y₂ y₃).Nonempty) (hSt1 : (St ∩ {x₃} ×ℂ Icc y₂ y₃).Nonempty)
    (hSl : IsPathConnected Sl) (hSlR : Sl ⊆ Icc x₀ x₁ ×ℂ Icc y₀ y₃)
    (hSl0 : (Sl ∩ Icc x₀ x₁ ×ℂ {y₀}).Nonempty) (hSl1 : (Sl ∩ Icc x₀ x₁ ×ℂ {y₃}).Nonempty)
    (hSr : IsPathConnected Sr) (hSrR : Sr ⊆ Icc x₂ x₃ ×ℂ Icc y₀ y₃)
    (hSr0 : (Sr ∩ Icc x₂ x₃ ×ℂ {y₀}).Nonempty) (hSr1 : (Sr ∩ Icc x₂ x₃ ×ℂ {y₃}).Nonempty) :
    IsPathConnected (Sb ∪ St ∪ Sl ∪ Sr) := by
  -- bottom-left, top-left and top-right corners
  have hbl : (Sb ∩ Sl).Nonempty := corner_meet hSb hSbR subset_rfl hSb0 hSb1 hSl hSlR subset_rfl
    hSl0 hSl1 le_rfl hx01 (hx12.trans hx23) le_rfl hy01 (hy12.trans hy23)
  have htl : (St ∩ Sl).Nonempty := corner_meet hSt hStR subset_rfl hSt0 hSt1 hSl hSlR subset_rfl
    hSl0 hSl1 le_rfl hx01 (hx12.trans hx23) (hy01.trans hy12) hy23 le_rfl
  have htr : (St ∩ Sr).Nonempty := corner_meet hSt hStR subset_rfl hSt0 hSt1 hSr hSrR subset_rfl
    hSr0 hSr1 (hx01.trans hx12) hx23 le_rfl (hy01.trans hy12) hy23 le_rfl
  have h1 : IsPathConnected (Sb ∪ Sl) := hSb.union hSl hbl
  have h2 : IsPathConnected (Sb ∪ Sl ∪ St) :=
    h1.union hSt (htl.mono fun z hz => ⟨Or.inr hz.2, hz.1⟩)
  have h3 : IsPathConnected (Sb ∪ Sl ∪ St ∪ Sr) :=
    h2.union hSr (htr.mono fun z hz => ⟨Or.inr hz.1, hz.2⟩)
  have he : Sb ∪ St ∪ Sl ∪ Sr = Sb ∪ Sl ∪ St ∪ Sr := by rw [union_right_comm Sb St Sl]
  rw [he]; exact h3

end DZZ
end LQGMetric
