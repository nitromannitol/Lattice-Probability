/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DDDF.P18Strip at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DDDF.P18Geom
import LatticeProb.Bonanno.LQGMetric.Topo.RectCross

/-!
# DDDF Prop 18, Step 3: the geometric lower bound (task P2-DDDF16c)

DDDF (arXiv:1904.08021, `tightness.tex` l. 915–918): "For each dyadic block of size `2^{-k}`
visited by `π_n(φ)`, one of the four rectangles of size `2^{-k}(1,3)` around `P` has to be
crossed by `π_n(φ)`. Therefore, since `π_n(φ)` has to visit at least `2^k` dyadic blocks ...
`L^{(n)}_{1,1}(φ) ≥ 2^k e^{ξ inf φ_{0,k}} min_P min_i L^{(k,n)}(R_i^S(P), φ)`."

We make the counting explicit with vertical strips (own elementary argument for the
combinatorics, same rectangles as DDDF): a left–right crossing of `[0,1]²` crosses each strip
`[jδ, (j+1)δ] × ℝ` (`δ = 2^{-k}`); inside the strip, starting in the block of row `i`, it either
stays in rows `i−1..i+1` (a left–right crossing of the `1 × 3` block rectangle `p18V`) or
crosses a `3 × 1` block rectangle `p18H` vertically (`p18_strip`). The strips with even `j` give
`⌊2^k/2⌋` sub-arcs on disjoint time intervals (`p18_geom`); the factor `1/2` against DDDF's
`2^k` is absorbed in `e^{-C√k}`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace LQGMetric
namespace DDDF

open LFPP

variable {ξ : ℝ}

/-- the `δ × 3δ` block rectangle `[a, a+δ] × [y, y+3δ]`, crossed left–right -/
def p18V (a y δ : ℝ) : MarkedRect := ⟨a, y, δ, 3 * δ, true⟩

/-- the `3δ × δ` block rectangle `[a−δ, a+2δ] × [y, y+δ]`, crossed bottom–top -/
def p18H (a y δ : ℝ) : MarkedRect := ⟨a - δ, y, 3 * δ, δ, false⟩

/-- **One strip** (DDDF l. 915–916): a sub-arc crossing the strip `[a, a+δ] × ℝ` contains a
crossing of one of the block rectangles around its starting block. -/
theorem p18_strip {g : ℂ → ℝ} {P : ℝ → ℂ} {z w : ℂ} (hP : IsPiecewiseC1Path P z w)
    {δ a α β : ℝ} (hδ : 0 < δ) (hα : 0 ≤ α) (hαβ : α ≤ β) (hβ : β ≤ 1)
    (hre : ∀ u ∈ Icc α β, (P u).re ∈ Icc a (a + δ)) (hreα : (P α).re = a)
    (hreβ : (P β).re = a + δ) (him : 0 ≤ (P α).im) {m : ℝ≥0∞}
    (hm : ∀ i : ℤ, 0 ≤ i → (i : ℝ) * δ ≤ (P α).im →
      m ≤ rectLen ξ g (p18V a ((i - 1) * δ) δ) ∧ m ≤ rectLen ξ g (p18H a ((i + 1) * δ) δ) ∧
        m ≤ rectLen ξ g (p18H a ((i - 1) * δ) δ)) :
    ∃ s t, α ≤ s ∧ s ≤ t ∧ t ≤ β ∧ m ≤ ∫⁻ x in Ioo s t, lenDens ξ g P x := by
  have hPc : ContinuousOn P (Icc α β) := hP.continuousOn.mono (Icc_subset_Icc hα hβ)
  have hIm : ContinuousOn (fun u => (P u).im) (Icc α β) :=
    Complex.continuous_im.comp_continuousOn hPc
  set i : ℤ := ⌊(P α).im / δ⌋ with hi
  have hi1 : (i : ℝ) * δ ≤ (P α).im := by
    have := Int.floor_le ((P α).im / δ); rwa [le_div_iff₀ hδ] at this
  have hi2 : (P α).im < ((i : ℝ) + 1) * δ := by
    have := Int.lt_floor_add_one ((P α).im / δ); rwa [div_lt_iff₀ hδ] at this
  have hi0 : 0 ≤ i := Int.floor_nonneg.2 (div_nonneg him hδ.le)
  obtain ⟨hV, hHu, hHd⟩ := hm i hi0 hi1
  by_cases hup : ∃ u ∈ Icc α β, ((i : ℝ) + 2) * δ < (P u).im
  · obtain ⟨u, hu, hu2⟩ := hup
    obtain ⟨s, t, h1, h2, h3, h4, h5, h6⟩ := RectCross.exists_sub_crossing
      (f := fun u => (P u).im) (z := ((i : ℝ) + 1) * δ) (w := ((i : ℝ) + 2) * δ) hu.1
      (hIm.mono (Icc_subset_Icc le_rfl hu.2)) (by nlinarith) hi2.le hu2.le
    refine ⟨s, t, h1, h2, h3.trans hu.2, hHu.trans
      (crossLenIn_le_setLIntegral_Ioo hP (hα.trans h1) h2 (h3.trans (hu.2.trans hβ)) ?_ ?_ ?_)⟩
    · intro v hv
      have hvre := hre v ⟨h1.trans hv.1, hv.2.trans (h3.trans hu.2)⟩
      have hvim := h6 v hv
      simp only [MarkedRect.toSet, p18H, Complex.mem_reProdIm, mem_Icc] at hvre hvim ⊢
      exact ⟨⟨by linarith [hvre.1], by linarith [hvre.2]⟩, by linarith [hvim.1],
        by linarith [hvim.2]⟩
    · have hsre := hre s ⟨h1, h3.trans' h2 |>.trans hu.2⟩
      simp only [MarkedRect.side₁, p18H, Bool.false_eq_true, ↓reduceIte, Complex.mem_reProdIm,
        mem_Icc, mem_singleton_iff] at hsre ⊢
      exact ⟨⟨by linarith [hsre.1], by linarith [hsre.2]⟩, h4⟩
    · have htre := hre t ⟨h1.trans h2, h3.trans hu.2⟩
      simp only [MarkedRect.side₂, p18H, Bool.false_eq_true, ↓reduceIte, Complex.mem_reProdIm,
        mem_Icc, mem_singleton_iff] at htre ⊢
      exact ⟨⟨by linarith [htre.1], by linarith [htre.2]⟩, by rw [h5]; ring⟩
  push Not at hup
  by_cases hdn : ∃ u ∈ Icc α β, (P u).im < ((i : ℝ) - 1) * δ
  · obtain ⟨u, hu, hu2⟩ := hdn
    obtain ⟨s, t, h1, h2, h3, h4, h5, h6⟩ := RectCross.exists_sub_crossing'
      (f := fun u => (P u).im) (z := ((i : ℝ) - 1) * δ) (w := (i : ℝ) * δ) hu.1
      (hIm.mono (Icc_subset_Icc le_rfl hu.2)) (by nlinarith) hi1 hu2.le
    refine ⟨s, t, h1, h2, h3.trans hu.2, hHd.trans
      (crossLenIn_le_setLIntegral_Ioo_rev hP (hα.trans h1) h2 (h3.trans (hu.2.trans hβ)) ?_ ?_
        ?_)⟩
    · intro v hv
      have hvre := hre v ⟨h1.trans hv.1, hv.2.trans (h3.trans hu.2)⟩
      have hvim := h6 v hv
      simp only [MarkedRect.toSet, p18H, Complex.mem_reProdIm, mem_Icc] at hvre hvim ⊢
      exact ⟨⟨by linarith [hvre.1], by linarith [hvre.2]⟩, by linarith [hvim.1],
        by linarith [hvim.2]⟩
    · have htre := hre t ⟨h1.trans h2, h3.trans hu.2⟩
      simp only [MarkedRect.side₁, p18H, Bool.false_eq_true, ↓reduceIte, Complex.mem_reProdIm,
        mem_Icc, mem_singleton_iff] at htre ⊢
      exact ⟨⟨by linarith [htre.1], by linarith [htre.2]⟩, h5⟩
    · have hsre := hre s ⟨h1, h2.trans (h3.trans hu.2)⟩
      simp only [MarkedRect.side₂, p18H, Bool.false_eq_true, ↓reduceIte, Complex.mem_reProdIm,
        mem_Icc, mem_singleton_iff] at hsre ⊢
      exact ⟨⟨by linarith [hsre.1], by linarith [hsre.2]⟩, by rw [h4]; ring⟩
  push Not at hdn
  have hαβ' : α ∈ Icc α β := ⟨le_rfl, hαβ⟩
  have hβ' : β ∈ Icc α β := ⟨hαβ, le_rfl⟩
  refine ⟨α, β, le_rfl, hαβ, le_rfl, hV.trans
    (crossLenIn_le_setLIntegral_Ioo hP hα hαβ hβ ?_ ?_ ?_)⟩
  · intro v hv
    have hvre := hre v hv
    have h1 := hup v hv
    have h2 := hdn v hv
    simp only [MarkedRect.toSet, p18V, Complex.mem_reProdIm, mem_Icc] at hvre ⊢
    exact ⟨⟨hvre.1, hvre.2⟩, h2, by linarith⟩
  · simp only [MarkedRect.side₁, p18V, ↓reduceIte, Complex.mem_reProdIm, mem_Icc,
      mem_singleton_iff]
    exact ⟨hreα, by nlinarith, by nlinarith⟩
  · have h1 := hup β hβ'
    have h2 := hdn β hβ'
    simp only [MarkedRect.side₂, p18V, ↓reduceIte, Complex.mem_reProdIm, mem_Icc,
      mem_singleton_iff]
    exact ⟨hreβ, h2, by linarith⟩

/-- **DDDF Prop 18, Step 3, geometric part** (l. 915–918): with `δ = 2^{-k}`, if `m` bounds the
crossing lengths (field `g`) of all block rectangles `p18V (jδ) ((i−1)δ) δ`,
`p18H (jδ) ((i±1)δ) δ` with `j < 2^k`, `0 ≤ i ≤ 2^k`, then `⌊2^k/2⌋ · m ≤ L_{1,1}(g)`. -/
theorem p18_geom {g : ℂ → ℝ} (k : ℕ) {m : ℝ≥0∞}
    (hm : ∀ (j : ℕ) (i : ℤ), j < 2 ^ k → 0 ≤ i → (i : ℝ) ≤ 2 ^ k →
      m ≤ rectLen ξ g (p18V (j * (2 : ℝ)⁻¹ ^ k) ((i - 1) * (2 : ℝ)⁻¹ ^ k) ((2 : ℝ)⁻¹ ^ k)) ∧
      m ≤ rectLen ξ g (p18H (j * (2 : ℝ)⁻¹ ^ k) ((i + 1) * (2 : ℝ)⁻¹ ^ k) ((2 : ℝ)⁻¹ ^ k)) ∧
      m ≤ rectLen ξ g (p18H (j * (2 : ℝ)⁻¹ ^ k) ((i - 1) * (2 : ℝ)⁻¹ ^ k) ((2 : ℝ)⁻¹ ^ k))) :
    ((2 ^ k / 2 : ℕ) : ℝ≥0∞) * m ≤ rectLen ξ g (rectAB 1 1) := by
  set δ : ℝ := (2 : ℝ)⁻¹ ^ k with hδdef
  have hδ : 0 < δ := by positivity
  have hNδ : (2 : ℝ) ^ k * δ = 1 := by rw [hδdef, inv_pow, mul_inv_cancel₀ (by positivity)]
  set N : ℕ := 2 ^ k / 2 with hN
  have hN2 : 2 * N ≤ 2 ^ k := Nat.mul_div_le (2 ^ k) 2
  refine le_crossLenIn fun P hP => ?_
  obtain ⟨z, hz, w, hw, hPp, hU⟩ := hP
  have hz' : (P 0).re = 0 := by
    rw [hPp.source]
    simp only [rectAB, MarkedRect.side₁, ↓reduceIte, Complex.mem_reProdIm,
      mem_singleton_iff] at hz
    exact hz.1
  have hw' : (P 1).re = 1 := by
    rw [hPp.target]
    simp only [rectAB, MarkedRect.side₂, ↓reduceIte, Complex.mem_reProdIm,
      mem_singleton_iff, zero_add] at hw
    exact hw.1
  have hUim : ∀ u ∈ Icc (0 : ℝ) 1, (P u).im ∈ Icc (0 : ℝ) 1 := by
    intro u hu
    have h := hU u hu
    simp only [MarkedRect.toSet, rectAB, Complex.mem_reProdIm, zero_add] at h
    exact h.2
  have hRe : ContinuousOn (fun u => (P u).re) (Icc 0 1) :=
    Complex.continuous_re.comp_continuousOn hPp.continuousOn
  have hstrip : ∀ l ∈ Finset.range N, ∃ s t : ℝ, 0 ≤ s ∧ s ≤ t ∧ t ≤ 1 ∧
      (∀ u ∈ Icc s t, (P u).re ∈ Icc (2 * l * δ) (2 * l * δ + δ)) ∧
      m ≤ ∫⁻ x in Ioo s t, lenDens ξ g P x := by
    intro l hl
    have hl' : 2 * l + 1 ≤ 2 ^ k := by have := Finset.mem_range.1 hl; omega
    have hl'' : 2 * (l : ℝ) + 1 ≤ 2 ^ k := by exact_mod_cast hl'
    obtain ⟨α, β, h1, h2, h3, h4, h5, h6⟩ := RectCross.exists_sub_crossing
      (f := fun u => (P u).re) (z := 2 * l * δ) (w := 2 * l * δ + δ) zero_le_one hRe
      (by linarith) (by rw [hz']; positivity) (by rw [hw']; nlinarith)
    have hαmem : α ∈ Icc (0 : ℝ) 1 := ⟨h1, h2.trans h3⟩
    have him := hUim α hαmem
    have hm' : ∀ i : ℤ, 0 ≤ i → (i : ℝ) * δ ≤ (P α).im →
        m ≤ rectLen ξ g (p18V (2 * l * δ) ((i - 1) * δ) δ) ∧
        m ≤ rectLen ξ g (p18H (2 * l * δ) ((i + 1) * δ) δ) ∧
        m ≤ rectLen ξ g (p18H (2 * l * δ) ((i - 1) * δ) δ) := by
      intro i hi0 hiδ
      have hle : (i : ℝ) * δ ≤ 2 ^ k * δ := by rw [hNδ]; exact hiδ.trans him.2
      have h := hm (2 * l) i (by omega) hi0 (le_of_mul_le_mul_right hle hδ)
      push_cast at h
      exact h
    obtain ⟨s, t, g1, g2, g3, g4⟩ := p18_strip (ξ := ξ) (g := g) hPp hδ h1 h2 h3 h6 h4 h5
      him.1 hm'
    exact ⟨s, t, h1.trans g1, g2, g3.trans h3,
      fun u hu => h6 u ⟨g1.trans hu.1, hu.2.trans g3⟩, g4⟩
  choose! s t hs0 hst ht1 hre hint using hstrip
  have hdisj : ((Finset.range N : Finset ℕ) : Set ℕ).PairwiseDisjoint
      fun l => Ioo (s l) (t l) := by
    intro l hl l' hl' hne
    rw [Function.onFun, Set.disjoint_left]
    intro x hx hx'
    have e1 := hre l (Finset.mem_coe.1 hl) x ⟨hx.1.le, hx.2.le⟩
    have e2 := hre l' (Finset.mem_coe.1 hl') x ⟨hx'.1.le, hx'.2.le⟩
    rcases lt_or_gt_of_ne hne with h | h
    · have : (l : ℝ) + 1 ≤ l' := by exact_mod_cast h
      nlinarith [e1.2, e2.1]
    · have : (l' : ℝ) + 1 ≤ l := by exact_mod_cast h
      nlinarith [e1.1, e2.2]
  calc ((N : ℕ) : ℝ≥0∞) * m = ∑ _l ∈ Finset.range N, m := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    _ ≤ ∑ l ∈ Finset.range N, ∫⁻ x in Ioo (s l) (t l), lenDens ξ g P x :=
        Finset.sum_le_sum hint
    _ ≤ lfppLen ξ g P := sum_setLIntegral_le_lfppLen P _ s t hs0 ht1 hdisj

end DDDF
end LQGMetric
