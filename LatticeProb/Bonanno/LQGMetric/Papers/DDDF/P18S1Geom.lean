/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DDDF.P18S1Geom at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DDDF.P16Indep
import LatticeProb.Bonanno.LQGMetric.LFPP.DistOn
import LatticeProb.Bonanno.LQGMetric.Topo.RectMeet
import LatticeProb.Bonanno.LQGMetric.Perc.Basic

/-!
# DDDF Prop 18, Step 1: circuits of `3 × 1` crossings around a site (task P2-DDDF18S1)

DDDF (arXiv:1904.08021, `tightness.tex` l. 902–905 and Figure `surroundingrectangles`): to a
unit square `P = [i,i+1] × [j,j+1]` one associates the four `3 × 1` rectangles of the
eight-square annulus around `P` (`siteRect`), crossed in the long direction. Here:
* `dOn_pt_le`: two points of a path are joined in `U` at cost at most the path's length;
* `hv_meet`: a long crossing of a horizontal rectangle `H` and one of a vertical rectangle `V`
  meet when `V`'s abscissas lie in `H`'s and `H`'s ordinates in `V`'s (sub-crossings of the
  common rectangle, `RectCross.exists_sub_crossing`, then `rect_crossings_meet`);
* the four crossings around a site form a circuit (DDDF: "Any geodesic which intersects `P`
  has to cross the green circuit"), and the circuits of `4`-adjacent sites meet.
Own elementary arguments for these planar facts (DDDF use them via the figure).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false
set_option linter.unnecessarySeqFocus false

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace LQGMetric
namespace DDDF

open LFPP

variable {ξ : ℝ} {f : ℂ → ℝ}

/-- two points of an admissible path in `U` are at `U`-distance at most the path's length -/
lemma dOn_pt_le {U : Set ℂ} {γ : ℝ → ℂ} {z w : ℂ} (hγ : IsPiecewiseC1Path γ z w)
    (hU : ∀ t ∈ Icc (0 : ℝ) 1, γ t ∈ U) {s t : ℝ} (hs : s ∈ Icc (0 : ℝ) 1)
    (ht : t ∈ Icc (0 : ℝ) 1) : lfppDOn ξ f U (γ s) (γ t) ≤ lfppLen ξ f γ := by
  have key : ∀ s t : ℝ, s ∈ Icc (0 : ℝ) 1 → t ∈ Icc (0 : ℝ) 1 → s < t →
      lfppDOn ξ f U (γ s) (γ t) ≤ lfppLen ξ f γ := by
    intro s t hs ht h
    have hsub := isPiecewiseC1Path_subPath hγ hs.1 h ht.2
    calc lfppDOn ξ f U (γ s) (γ t) ≤ lfppLen ξ f (subPath γ s t) :=
          lfppDOn_le hsub fun u hu => hU _ ⟨by nlinarith [hu.1, hu.2, hs.1],
            by nlinarith [hu.1, hu.2, ht.2]⟩
      _ = ∫⁻ x in Icc s t, lenDens ξ f γ x := lfppLen_subPath γ h
      _ ≤ ∫⁻ x in Icc 0 1, lenDens ξ f γ x := lintegral_mono_set (Icc_subset_Icc hs.1 ht.2)
      _ = lfppLen ξ f γ := (lfppLen_eq _ _ _).symm
  rcases lt_trichotomy s t with h | rfl | h
  · exact key s t hs ht h
  · calc lfppDOn ξ f U (γ s) (γ s) ≤ lfppLen ξ f (fun _ => γ s) :=
          lfppDOn_le (isPiecewiseC1Path_const _) fun _ _ => hU s hs
      _ = 0 := lfppLen_const _
      _ ≤ _ := bot_le
  · rw [lfppDOn_comm]; exact key t s ht hs h

lemma mem_toSet_iff {R : MarkedRect} {z : ℂ} :
    z ∈ R.toSet ↔ z.re ∈ Icc R.x0 (R.x0 + R.w) ∧ z.im ∈ Icc R.y0 (R.y0 + R.h) := by
  simp [MarkedRect.toSet, Complex.mem_reProdIm]

/-- **A horizontal and a vertical long crossing meet** when `V`'s abscissas lie in `H`'s and
`H`'s ordinates in `V`'s. -/
lemma hv_meet {H V : MarkedRect} (hH : H.horiz = true) (hV : V.horiz = false)
    (hw : 0 ≤ V.w) (hh : 0 ≤ H.h) (h1 : H.x0 ≤ V.x0) (h2 : V.x0 + V.w ≤ H.x0 + H.w)
    (h3 : V.y0 ≤ H.y0) (h4 : H.y0 + H.h ≤ V.y0 + V.h) {γ δ : ℝ → ℂ}
    (hγ : AdmPath H.toSet H.side₁ H.side₂ γ) (hδ : AdmPath V.toSet V.side₁ V.side₂ δ) :
    ∃ s ∈ Icc (0 : ℝ) 1, ∃ t ∈ Icc (0 : ℝ) 1, γ s = δ t := by
  obtain ⟨z, hz, w, hw', hγp, hγU⟩ := hγ
  obtain ⟨z', hz', w', hw'', hδp, hδU⟩ := hδ
  simp only [MarkedRect.side₁, MarkedRect.side₂, hH, hV, ite_true, Bool.false_eq_true,
    ite_false, Complex.mem_reProdIm, mem_singleton_iff] at hz hw' hz' hw''
  have hγ0 : (γ 0).re = H.x0 := by rw [hγp.source]; exact hz.1
  have hγ1 : (γ 1).re = H.x0 + H.w := by rw [hγp.target]; exact hw'.1
  have hδ0 : (δ 0).im = V.y0 := by rw [hδp.source]; exact hz'.2
  have hδ1 : (δ 1).im = V.y0 + V.h := by rw [hδp.target]; exact hw''.2
  have hγc := hγp.continuousOn
  have hδc := hδp.continuousOn
  obtain ⟨s₁, t₁, hs₁, hst₁, ht₁, e1, e2, hr⟩ := RectCross.exists_sub_crossing zero_le_one
    (Complex.continuous_re.comp_continuousOn hγc) (by linarith : V.x0 ≤ V.x0 + V.w)
    (by simp only [Function.comp]; linarith) (by simp only [Function.comp]; linarith)
  obtain ⟨s₂, t₂, hs₂, hst₂, ht₂, e3, e4, hi⟩ := RectCross.exists_sub_crossing zero_le_one
    (Complex.continuous_im.comp_continuousOn hδc) (by linarith : H.y0 ≤ H.y0 + H.h)
    (by simp only [Function.comp]; linarith) (by simp only [Function.comp]; linarith)
  have hp1 : ∀ u ∈ Icc (0 : ℝ) 1, s₁ + u * (t₁ - s₁) ∈ Icc s₁ t₁ := fun u hu =>
    ⟨by nlinarith [hu.1], by nlinarith [hu.2]⟩
  have hp2 : ∀ u ∈ Icc (0 : ℝ) 1, t₂ + u * (s₂ - t₂) ∈ Icc s₂ t₂ := fun u hu =>
    ⟨by nlinarith [hu.2], by nlinarith [hu.1]⟩
  have hI1 : Icc s₁ t₁ ⊆ Icc (0 : ℝ) 1 := Icc_subset_Icc hs₁ ht₁
  have hI2 : Icc s₂ t₂ ⊆ Icc (0 : ℝ) 1 := Icc_subset_Icc hs₂ ht₂
  obtain ⟨s, hs, t, ht, hst⟩ := RectMeet.rect_crossings_meet V.x0 (V.x0 + V.w) H.y0 (H.y0 + H.h)
    (fun u => γ (s₁ + u * (t₁ - s₁))) (fun u => δ (t₂ + u * (s₂ - t₂)))
    (hγc.comp (by fun_prop) fun u hu => hI1 (hp1 u hu))
    (hδc.comp (by fun_prop) fun u hu => hI2 (hp2 u hu))
    (fun u hu => ⟨hr _ (hp1 u hu), (mem_toSet_iff.1 (hγU _ (hI1 (hp1 u hu)))).2⟩)
    (fun u hu => ⟨(mem_toSet_iff.1 (hδU _ (hI2 (hp2 u hu)))).1, hi _ (hp2 u hu)⟩)
    (by simpa using e1) (by simpa using e2) (by simpa using e4) (by simpa using e3)
  exact ⟨_, hI1 (hp1 s hs), _, hI2 (hp2 t ht), hst⟩

/-! ### The four `3 × 1` rectangles around a site -/

/-- bottom rectangle `[i-1,i+2] × [j-1,j]` around the site `z = (i,j)`, crossed left–right -/
def sB (z : ℤ × ℤ) : MarkedRect := ⟨(z.1 : ℝ) - 1, (z.2 : ℝ) - 1, 3, 1, true⟩
/-- top rectangle `[i-1,i+2] × [j+1,j+2]`, crossed left–right -/
def sT (z : ℤ × ℤ) : MarkedRect := ⟨(z.1 : ℝ) - 1, (z.2 : ℝ) + 1, 3, 1, true⟩
/-- left rectangle `[i-1,i] × [j-1,j+2]`, crossed bottom–top -/
def sL (z : ℤ × ℤ) : MarkedRect := ⟨(z.1 : ℝ) - 1, (z.2 : ℝ) - 1, 1, 3, false⟩
/-- right rectangle `[i+1,i+2] × [j-1,j+2]`, crossed bottom–top -/
def sR (z : ℤ × ℤ) : MarkedRect := ⟨(z.1 : ℝ) + 1, (z.2 : ℝ) - 1, 1, 3, false⟩

/-- four long crossings around the site `z`, of total length `≤ c` -/
structure SiteCirc (ξ : ℝ) (f : ℂ → ℝ) (z : ℤ × ℤ) (c : ℝ≥0∞) where
  B : ℝ → ℂ
  T : ℝ → ℂ
  L : ℝ → ℂ
  R : ℝ → ℂ
  hB : AdmPath (sB z).toSet (sB z).side₁ (sB z).side₂ B
  hT : AdmPath (sT z).toSet (sT z).side₁ (sT z).side₂ T
  hL : AdmPath (sL z).toSet (sL z).side₁ (sL z).side₂ L
  hR : AdmPath (sR z).toSet (sR z).side₁ (sR z).side₂ R
  hc : lfppLen ξ f B + lfppLen ξ f T + lfppLen ξ f L + lfppLen ξ f R ≤ c

namespace SiteCirc

variable {z z' : ℤ × ℤ} {c c' : ℝ≥0∞}

/-- `a` lies on one of the four crossings -/
def On (C : SiteCirc ξ f z c) (a : ℂ) : Prop :=
  (∃ s ∈ Icc (0 : ℝ) 1, C.B s = a) ∨ (∃ s ∈ Icc (0 : ℝ) 1, C.T s = a) ∨
    (∃ s ∈ Icc (0 : ℝ) 1, C.L s = a) ∨ (∃ s ∈ Icc (0 : ℝ) 1, C.R s = a)

/-- the four rectangles of `z` lie in `U` -/
def Sub (U : Set ℂ) (z : ℤ × ℤ) : Prop :=
  (sB z).toSet ⊆ U ∧ (sT z).toSet ⊆ U ∧ (sL z).toSet ⊆ U ∧ (sR z).toSet ⊆ U

lemma adm_pt_le {U : Set ℂ} {R : MarkedRect} (hRU : R.toSet ⊆ U) {γ : ℝ → ℂ}
    (hγ : AdmPath R.toSet R.side₁ R.side₂ γ) {s t : ℝ} (hs : s ∈ Icc (0 : ℝ) 1)
    (ht : t ∈ Icc (0 : ℝ) 1) : lfppDOn ξ f U (γ s) (γ t) ≤ lfppLen ξ f γ := by
  obtain ⟨_, _, _, _, hp, hm⟩ := hγ
  exact dOn_pt_le hp (fun u hu => hRU (hm u hu)) hs ht

/-- **The circuit around a site is connected**: a hub `m` at `U`-distance `≤ c` from every point
of the four crossings. -/
lemma hub (C : SiteCirc ξ f z c) {U : Set ℂ} (hU : Sub U z) :
    ∃ m : ℂ, ∀ a, C.On a → lfppDOn ξ f U a m ≤ c := by
  obtain ⟨hUB, hUT, hUL, hUR⟩ := hU
  have hz1 : ((z.1 : ℝ) - 1) + 1 = (z.1 : ℝ) := by ring
  obtain ⟨sBL, hsBL, tBL, htBL, eBL⟩ := hv_meet (H := sB z) (V := sL z) rfl rfl
    (by simp [sL] <;> linarith) (by simp [sB] <;> linarith) (by simp [sB, sL] <;> linarith) (by simp [sB, sL] <;> linarith)
    (by simp [sB, sL] <;> linarith) (by simp [sB, sL] <;> linarith) C.hB C.hL
  obtain ⟨sTL, hsTL, tTL, htTL, eTL⟩ := hv_meet (H := sT z) (V := sL z) rfl rfl
    (by simp [sL] <;> linarith) (by simp [sT] <;> linarith) (by simp [sT, sL] <;> linarith) (by simp [sT, sL] <;> linarith)
    (by simp [sT, sL] <;> linarith) (by simp [sT, sL] <;> linarith) C.hT C.hL
  obtain ⟨sBR, hsBR, tBR, htBR, eBR⟩ := hv_meet (H := sB z) (V := sR z) rfl rfl
    (by simp [sR] <;> linarith) (by simp [sB] <;> linarith) (by simp [sB, sR] <;> linarith) (by simp [sB, sR] <;> linarith)
    (by simp [sB, sR] <;> linarith) (by simp [sB, sR] <;> linarith) C.hB C.hR
  have hc := C.hc
  set lB := lfppLen ξ f C.B
  set lT := lfppLen ξ f C.T
  set lL := lfppLen ξ f C.L
  set lR := lfppLen ξ f C.R
  refine ⟨C.B sBL, fun a ha => ?_⟩
  rcases ha with ⟨s, hs, rfl⟩ | ⟨s, hs, rfl⟩ | ⟨s, hs, rfl⟩ | ⟨s, hs, rfl⟩
  · refine (adm_pt_le hUB C.hB hs hsBL).trans (le_trans ?_ hc)
    exact le_self_add.trans (le_self_add.trans le_self_add)
  · have h1 : lfppDOn ξ f U (C.T s) (C.L tTL) ≤ lT := by
      rw [← eTL]; exact adm_pt_le hUT C.hT hs hsTL
    have h2 : lfppDOn ξ f U (C.L tTL) (C.B sBL) ≤ lL := by
      rw [eBL]; exact adm_pt_le hUL C.hL htTL htBL
    refine (lfppDOn_triangle _ (C.L tTL) _).trans (le_trans ?_ hc)
    calc _ ≤ lT + lL := add_le_add h1 h2
      _ ≤ lB + lT + lL := by rw [add_assoc]; exact le_add_self
      _ ≤ _ := le_self_add
  · rw [eBL]
    refine (adm_pt_le hUL C.hL hs htBL).trans (le_trans ?_ hc)
    exact le_add_self.trans le_self_add
  · have h1 : lfppDOn ξ f U (C.R s) (C.B sBR) ≤ lR := by
      rw [eBR]; exact adm_pt_le hUR C.hR hs htBR
    have h2 : lfppDOn ξ f U (C.B sBR) (C.B sBL) ≤ lB := adm_pt_le hUB C.hB hsBR hsBL
    refine (lfppDOn_triangle _ (C.B sBR) _).trans (le_trans ?_ hc)
    calc _ ≤ lR + lB := add_le_add h1 h2
      _ = lB + lR := add_comm _ _
      _ ≤ _ := add_le_add (le_self_add.trans le_self_add) le_rfl

/-- **Circuits of `4`-adjacent sites meet.** -/
lemma meet (C : SiteCirc ξ f z c) (C' : SiteCirc ξ f z' c') (h : PercAdj4 z z') :
    ∃ q, C.On q ∧ C'.On q := by
  have key : ∀ {y y' : ℤ × ℤ} {d d' : ℝ≥0∞} (D : SiteCirc ξ f y d) (D' : SiteCirc ξ f y' d'),
      y'.1 = y.1 + 1 → y'.2 = y.2 → ∃ q, D.On q ∧ D'.On q := by
    intro y y' d d' D D' e1 e2
    obtain ⟨s, hs, t, ht, e⟩ := hv_meet (H := sT y) (V := sL y') rfl rfl
      (by simp [sL] <;> linarith) (by simp [sT] <;> linarith) (by simp [sT, sL, e1] <;> linarith) (by simp [sT, sL, e1] <;> linarith)
      (by simp [sT, sL, e2] <;> linarith) (by simp [sT, sL, e2] <;> linarith) D.hT D'.hL
    exact ⟨D.T s, Or.inr (Or.inl ⟨s, hs, rfl⟩), Or.inr (Or.inr (Or.inl ⟨t, ht, e.symm⟩))⟩
  have key2 : ∀ {y y' : ℤ × ℤ} {d d' : ℝ≥0∞} (D : SiteCirc ξ f y d) (D' : SiteCirc ξ f y' d'),
      y'.1 = y.1 → y'.2 = y.2 + 1 → ∃ q, D.On q ∧ D'.On q := by
    intro y y' d d' D D' e1 e2
    obtain ⟨s, hs, t, ht, e⟩ := hv_meet (H := sB y') (V := sR y) rfl rfl
      (by simp [sR] <;> linarith) (by simp [sB] <;> linarith) (by simp [sB, sR, e1] <;> linarith) (by simp [sB, sR, e1] <;> linarith)
      (by simp [sB, sR, e2] <;> linarith) (by simp [sB, sR, e2] <;> linarith) D'.hB D.hR
    exact ⟨D.R t, Or.inr (Or.inr (Or.inr ⟨t, ht, rfl⟩)), Or.inl ⟨s, hs, e⟩⟩
  rcases h with ⟨e1, e2 | e2⟩ | ⟨e1, e2 | e2⟩
  · obtain ⟨q, h1, h2⟩ := key2 C' C e1 e2; exact ⟨q, h2, h1⟩
  · exact key2 C C' e1.symm e2
  · obtain ⟨q, h1, h2⟩ := key C' C e2 e1; exact ⟨q, h2, h1⟩
  · exact key C C' e2 e1.symm

end SiteCirc

end DDDF
end LQGMetric
