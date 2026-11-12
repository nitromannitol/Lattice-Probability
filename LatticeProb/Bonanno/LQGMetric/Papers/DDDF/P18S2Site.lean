/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DDDF.P18S2Site at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DDDF.P18S1Chain
import LatticeProb.Bonanno.LQGMetric.Papers.DDDF.P18Blocks
import LatticeProb.Bonanno.LQGMetric.Papers.DDDF.C8

/-!
# DDDF Prop 18, Step 1: one site of the percolation (task P2-DDDF18P)

DDDF (arXiv:1904.08021, `tightness.tex` l. 902–905): a site `P` is open when each of the four
`3 × 1` rectangles around it is crossed (in the long direction) at length `≤ ℓ̄^{(n)}_{3,1}(ψ, p)`
(deviation note (c) of handoff P2-DDDF16: DDDF bound each crossing, not the sum). Here:
* the four site rectangles `sB z`, `sT z` (translates of `R_{3,1}`) and `sL z`, `sR z` (images of
  `R_{3,1}` under `x ↦ i x + c`) are rigid images of `R_{3,1}` (`rectLen_sB_eq`, …), so their
  `ψ`-crossing lengths have the law of `L^{(n)}_{3,1}(ψ)` (`prob_site_gt`, via
  `map_psiMN_motion`);
* `prob_gt_ellBarQ`: `P(L > ℓ̄(p)) ≤ p`;
* `prob_siteBad_le`: `P(site bad) ≤ 4p` (union bound);
* `siteCirc_of_good`: an open site carries a `SiteCirc` of total length `≤ 4ℓ + δ`;
* `rectLen_le_of_percGoodLR`: a left–right chain of open sites gives
  `L_{3k,k} ≤ (6k² + 2) · 4ℓ` (gluing `splice_rectLen`, then `δ → 0`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace LQGMetric
namespace DDDF

open WhiteNoise LFPP

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {ξ : ℝ}

/-! ### The site rectangles as rigid images of `R_{3,1}` -/

/-- the motion `x ↦ u x + c` -/
def s2Mot (u : Circle) (c : ℂ) : ℂ → ℂ := fun x => (u : ℂ) * x + c

/-- `rectLen` of a rigid image of `R_{3,1}` -/
def s2ImLen (ξ : ℝ) (g : ℂ → ℝ) (u : Circle) (c : ℂ) : ℝ≥0∞ :=
  crossLenIn ξ g (s2Mot u c '' (rectAB 3 1).toSet) (s2Mot u c '' (rectAB 3 1).side₁)
    (s2Mot u c '' (rectAB 3 1).side₂)

theorem rectLen_sB_eq (g : ℂ → ℝ) (z : ℤ × ℤ) :
    rectLen ξ g (sB z) = s2ImLen ξ g 1 (((z.1 : ℝ) - 1 : ℝ) + ((z.2 : ℝ) - 1 : ℝ) * Complex.I) := by
  unfold rectLen s2ImLen s2Mot
  congr 1 <;> ext w <;> rw [mem_image_motion] <;>
    simp only [Circle.coe_one, inv_one, one_mul, MarkedRect.toSet, MarkedRect.side₁,
      MarkedRect.side₂, sB, rectAB, ↓reduceIte, Complex.mem_reProdIm, mem_Icc,
      mem_singleton_iff, Complex.sub_re, Complex.sub_im, Complex.add_re, Complex.add_im,
      Complex.ofReal_re, Complex.ofReal_im, Complex.mul_re, Complex.mul_im, Complex.I_re,
      Complex.I_im, mul_zero, mul_one, sub_zero, zero_add, add_zero] <;>
    constructor <;> intro h <;> refine ⟨?_, ?_⟩ <;> (try constructor) <;> linarith [h.1, h.2]

theorem rectLen_sT_eq (g : ℂ → ℝ) (z : ℤ × ℤ) :
    rectLen ξ g (sT z) = s2ImLen ξ g 1 (((z.1 : ℝ) - 1 : ℝ) + ((z.2 : ℝ) + 1 : ℝ) * Complex.I) := by
  unfold rectLen s2ImLen s2Mot
  congr 1 <;> ext w <;> rw [mem_image_motion] <;>
    simp only [Circle.coe_one, inv_one, one_mul, MarkedRect.toSet, MarkedRect.side₁,
      MarkedRect.side₂, sT, rectAB, ↓reduceIte, Complex.mem_reProdIm, mem_Icc,
      mem_singleton_iff, Complex.sub_re, Complex.sub_im, Complex.add_re, Complex.add_im,
      Complex.ofReal_re, Complex.ofReal_im, Complex.mul_re, Complex.mul_im, Complex.I_re,
      Complex.I_im, mul_zero, mul_one, sub_zero, zero_add, add_zero] <;>
    constructor <;> intro h <;> refine ⟨?_, ?_⟩ <;> (try constructor) <;> linarith [h.1, h.2]

theorem rectLen_sL_eq (g : ℂ → ℝ) (z : ℤ × ℤ) :
    rectLen ξ g (sL z) = s2ImLen ξ g circI (((z.1 : ℝ) : ℝ) + ((z.2 : ℝ) - 1 : ℝ) * Complex.I) := by
  unfold rectLen s2ImLen s2Mot
  congr 1 <;> ext w <;> rw [mem_image_motion] <;>
    simp only [coe_circI, Complex.inv_I, MarkedRect.toSet, MarkedRect.side₁,
      MarkedRect.side₂, sL, rectAB, ↓reduceIte, Bool.false_eq_true, Complex.mem_reProdIm,
      mem_Icc, mem_singleton_iff, Complex.sub_re, Complex.sub_im, Complex.add_re,
      Complex.add_im, Complex.ofReal_re, Complex.ofReal_im, Complex.mul_re, Complex.mul_im,
      Complex.I_re, Complex.I_im, Complex.neg_re, Complex.neg_im, mul_zero, mul_one, zero_mul,
      sub_zero, zero_add, add_zero, zero_sub, neg_mul, one_mul, neg_neg] <;>
    constructor <;> intro h <;> refine ⟨?_, ?_⟩ <;> (try constructor) <;>
      linarith [h.1, h.2]

theorem rectLen_sR_eq (g : ℂ → ℝ) (z : ℤ × ℤ) :
    rectLen ξ g (sR z) = s2ImLen ξ g circI (((z.1 : ℝ) + 2 : ℝ) + ((z.2 : ℝ) - 1 : ℝ) * Complex.I) := by
  unfold rectLen s2ImLen s2Mot
  congr 1 <;> ext w <;> rw [mem_image_motion] <;>
    simp only [coe_circI, Complex.inv_I, MarkedRect.toSet, MarkedRect.side₁,
      MarkedRect.side₂, sR, rectAB, ↓reduceIte, Bool.false_eq_true, Complex.mem_reProdIm,
      mem_Icc, mem_singleton_iff, Complex.sub_re, Complex.sub_im, Complex.add_re,
      Complex.add_im, Complex.ofReal_re, Complex.ofReal_im, Complex.mul_re, Complex.mul_im,
      Complex.I_re, Complex.I_im, Complex.neg_re, Complex.neg_im, mul_zero, mul_one, zero_mul,
      sub_zero, zero_add, add_zero, zero_sub, neg_mul, one_mul, neg_neg] <;>
    constructor <;> intro h <;> refine ⟨?_, ?_⟩ <;> (try constructor) <;>
      linarith [h.1, h.2]

/-! ### Laws -/

/-- **Law of crossing lengths of `ψ_{0,n}` invariant under rigid motions** (`ψ` version of
`measure_crossLenIn_phiMN_motion`). -/
theorem prob_imLen_psi {W : WNSpace → Ω → ℝ} (hW : IsWhiteNoise P W) (Q : PsiParams) (n : ℕ)
    (u : Circle) (c : ℂ) {S : Set ℝ≥0∞} (hS : MeasurableSet S) :
    P {ω | s2ImLen ξ (fun x => psiMN Q W P 0 n x ω) u c ∈ S} =
      P {ω | rectLen ξ (fun x => psiMN Q W P 0 n x ω) (rectAB 3 1) ∈ S} := by
  have hψ := isPsiVersion_psiMN (Q := Q) hW (Nat.zero_le n)
  have e : ∀ g : ℂ → ℝ, s2ImLen ξ g u c = crossLenIn ξ (fun x => g ((u : ℂ) * x + c))
      (rectAB 3 1).toSet (rectAB 3 1).side₁ (rectAB 3 1).side₂ := fun g =>
    crossLenIn_image_motion ξ g _ _ _ u c
  simp_rw [e]
  exact measure_crossLenIn_eq (MarkedRect.isCompact_toSet _)
    (Y := fun x ω => psiMN Q W P 0 n ((u : ℂ) * x + c) ω) (Y₂ := psiMN Q W P 0 n)
    (fun ω => (hψ.cont ω).comp ((continuous_const.mul continuous_id).add continuous_const))
    (fun x => hψ.meas _) hψ.cont hψ.meas (map_psiMN_motion hW Q n u c) hS

/-- `P(ℓ < L(R)) = P(ℓ < L_{3,1})` for `R` a rigid image of `R_{3,1}` -/
theorem prob_imLen_gt {W : WNSpace → Ω → ℝ} (hW : IsWhiteNoise P W) (Q : PsiParams) (n : ℕ)
    (u : Circle) (c : ℂ) (ℓ : ℝ) :
    P {ω | ℓ < (s2ImLen ξ (fun x => psiMN Q W P 0 n x ω) u c).toReal} =
      P {ω | ℓ < lenObs ξ (psiMN Q W P 0 n) (rectAB 3 1) ω} :=
  prob_imLen_psi hW Q n u c (S := {v | ℓ < v.toReal})
    (measurableSet_lt measurable_const ENNReal.measurable_toReal)

/-- `P(L(R) > ℓ̄(p)) ≤ p` -/
theorem prob_gt_ellBarQ [IsProbabilityMeasure P] {Y : ℂ → Ω → ℝ}
    (hYc : ∀ ω, Continuous fun x => Y x ω) (hYm : ∀ x, Measurable (Y x)) (R : MarkedRect)
    {p : ℝ≥0∞} (hp0 : 0 < p) (hp1 : p < 1) :
    P {ω | ellBarQ ξ P Y R p < lenObs ξ Y R ω} ≤ p := by
  have h := prob_le_ellQ (ξ := ξ) (P := P) hYc hYm R (p := 1 - p) (tsub_pos_of_lt hp1)
    (ENNReal.sub_lt_self ENNReal.one_ne_top one_ne_zero hp0.ne')
  have hm : MeasurableSet {ω | lenObs ξ Y R ω ≤ ellQ ξ P Y R (1 - p)} :=
    measurableSet_le (measurable_lenObs hYc hYm R) measurable_const
  have e : {ω | ellBarQ ξ P Y R p < lenObs ξ Y R ω} =
      {ω | lenObs ξ Y R ω ≤ ellQ ξ P Y R (1 - p)}ᶜ := by
    ext ω; simp [ellBarQ]
  rw [e, prob_compl_eq_one_sub hm]
  calc 1 - P {ω | lenObs ξ Y R ω ≤ ellQ ξ P Y R (1 - p)} ≤ 1 - (1 - p) := tsub_le_tsub_left h 1
    _ = p := ENNReal.sub_sub_cancel ENNReal.one_ne_top hp1.le

/-- the site `z` is bad: one of its four rectangles has a `ψ`-crossing longer than `ℓ` -/
def siteBad (Y : ℂ → Ω → ℝ) (ℓ : ℝ) (z : ℤ × ℤ) : Set Ω :=
  {ω | ℓ < lenObs ξ Y (sB z) ω} ∪ {ω | ℓ < lenObs ξ Y (sT z) ω} ∪
    {ω | ℓ < lenObs ξ Y (sL z) ω} ∪ {ω | ℓ < lenObs ξ Y (sR z) ω}

/-- **`P(site bad) ≤ 4 P(L_{3,1} > ℓ)`** (DDDF l. 903) -/
theorem prob_siteBad_le {W : WNSpace → Ω → ℝ} (hW : IsWhiteNoise P W) (Q : PsiParams) (n : ℕ)
    (ℓ : ℝ) (z : ℤ × ℤ) :
    P (siteBad (ξ := ξ) (psiMN Q W P 0 n) ℓ z) ≤
      4 * P {ω | ℓ < lenObs ξ (psiMN Q W P 0 n) (rectAB 3 1) ω} := by
  have e1 : ∀ R : MarkedRect, ∀ u c, (∀ g, rectLen ξ g R = s2ImLen ξ g u c) →
      P {ω | ℓ < lenObs ξ (psiMN Q W P 0 n) R ω} =
        P {ω | ℓ < lenObs ξ (psiMN Q W P 0 n) (rectAB 3 1) ω} := by
    intro R u c hR
    rw [← prob_imLen_gt hW Q n u c ℓ]
    simp only [lenObs, hR]
  let E : MarkedRect → Set Ω := fun R => {ω | ℓ < lenObs ξ (psiMN Q W P 0 n) R ω}
  show P (E (sB z) ∪ E (sT z) ∪ E (sL z) ∪ E (sR z)) ≤ _
  calc P (E (sB z) ∪ E (sT z) ∪ E (sL z) ∪ E (sR z)) ≤
      P (E (sB z)) + P (E (sT z)) + P (E (sL z)) + P (E (sR z)) := by
        refine (measure_union_le _ _).trans ?_
        gcongr
        refine (measure_union_le _ _).trans ?_
        gcongr
        exact measure_union_le _ _
    _ = _ := by
      simp only [E]
      rw [e1 _ _ _ (fun g => rectLen_sB_eq g z), e1 _ _ _ (fun g => rectLen_sT_eq g z),
        e1 _ _ _ (fun g => rectLen_sL_eq g z), e1 _ _ _ (fun g => rectLen_sR_eq g z)]
      ring

/-! ### Open sites carry circuits; gluing -/

/-- a crossing of length `< t` exists when `rectLen < t` -/
lemma exists_admPath_lt {g : ℂ → ℝ} {R : MarkedRect} {t : ℝ≥0∞} (h : rectLen ξ g R < t) :
    ∃ γ, AdmPath R.toSet R.side₁ R.side₂ γ ∧ lfppLen ξ g γ < t := by
  rw [rectLen, crossLenIn_eq_biInf] at h
  obtain ⟨γ, hγ⟩ := iInf_lt_iff.1 h
  obtain ⟨hA, hγ'⟩ := iInf_lt_iff.1 hγ
  exact ⟨γ, hA, hγ'⟩

/-- **an open site carries a circuit** of total length `< 4(ℓ + δ)` -/
theorem siteCirc_of_good {g : ℂ → ℝ} {z : ℤ × ℤ} {ℓ δ : ℝ≥0∞} (hδ : 0 < δ) (hℓ : ℓ ≠ ⊤)
    (hB : rectLen ξ g (sB z) ≤ ℓ) (hT : rectLen ξ g (sT z) ≤ ℓ)
    (hL : rectLen ξ g (sL z) ≤ ℓ) (hR : rectLen ξ g (sR z) ≤ ℓ) :
    Nonempty (SiteCirc ξ g z (4 * (ℓ + δ))) := by
  have hlt : ℓ < ℓ + δ := ENNReal.lt_add_right hℓ hδ.ne'
  obtain ⟨B, hB1, hB2⟩ := exists_admPath_lt (hB.trans_lt hlt)
  obtain ⟨T, hT1, hT2⟩ := exists_admPath_lt (hT.trans_lt hlt)
  obtain ⟨L, hL1, hL2⟩ := exists_admPath_lt (hL.trans_lt hlt)
  obtain ⟨R, hR1, hR2⟩ := exists_admPath_lt (hR.trans_lt hlt)
  refine ⟨⟨B, T, L, R, hB1, hT1, hL1, hR1, ?_⟩⟩
  calc lfppLen ξ g B + lfppLen ξ g T + lfppLen ξ g L + lfppLen ξ g R ≤
      (ℓ + δ) + (ℓ + δ) + (ℓ + δ) + (ℓ + δ) := by gcongr
    _ = 4 * (ℓ + δ) := by ring

/-- **gluing** (DDDF l. 902–905): a left–right chain of open sites (each of the four crossings
`≤ ℓ`) gives `L_{3k,k} ≤ (6k² + 2) · 4ℓ`. -/
theorem rectLen_le_of_percGoodLR {g : ℂ → ℝ} {k : ℕ} {ℓ : ℝ≥0∞} (hℓ : ℓ ≠ ⊤)
    {good : ℤ × ℤ → Prop}
    (hgood : ∀ x, good x → percInGrid (3 * k - 2) (k - 2) x →
      rectLen ξ g (sB (sh x)) ≤ ℓ ∧ rectLen ξ g (sT (sh x)) ≤ ℓ ∧
        rectLen ξ g (sL (sh x)) ≤ ℓ ∧ rectLen ξ g (sR (sh x)) ≤ ℓ)
    (hLR : PercGoodLR (3 * k - 2) (k - 2) good) :
    rectLen ξ g (rectAB (3 * k) k) ≤ (2 * ((3 * k * k : ℕ) : ℝ≥0∞) + 2) * (4 * ℓ) := by
  set M : ℝ≥0∞ := 2 * ((3 * k * k : ℕ) : ℝ≥0∞) + 2
  have hM0 : M ≠ 0 := by simp [M]
  have hMt : M ≠ ⊤ := by simp [M, ENNReal.mul_eq_top]
  refine ENNReal.le_of_forall_pos_le_add fun ε hε _ => ?_
  set δ : ℝ≥0∞ := (ε : ℝ≥0∞) / (4 * M)
  have hδ : 0 < δ := ENNReal.div_pos (by exact_mod_cast hε.ne') (by simp [ENNReal.mul_eq_top, hMt])
  have h := splice_rectLen (ξ := ξ) (f := g) (k := k) (c := 4 * (ℓ + δ)) (good := good)
    (fun x hx hg => by
      obtain ⟨h1, h2, h3, h4⟩ := hgood x hx hg
      exact siteCirc_of_good hδ hℓ h1 h2 h3 h4) hLR
  refine h.trans (le_of_eq ?_)
  have e : M * (4 * δ) = ε := by
    simp only [δ]
    rw [← mul_assoc, mul_comm M 4, ENNReal.mul_div_cancel (by simp [hM0]) (by simp [hMt,
      ENNReal.mul_eq_top])]
  rw [mul_add, mul_add, e]

end DDDF
end LQGMetric
