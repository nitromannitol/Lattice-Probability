/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DDDF.RSWUnif at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DDDF.RSWHigh

/-!
# DDDF Proposition 7 (`Prop:RSWphi`): RSW estimates uniform over `[A, B]`

Task P2-DDDFRSW2. DDDF arXiv:1904.08021, `tightness.tex` l. 653–662: for `[A,B] ⊂ (0,∞)` there is
one `C` that works for all `(a,b), (a',b') ∈ [A,B]²` with `a/b < 1 < a'/b'`. DDDF state Prop 14
(l. 783–790) for fixed shapes and call Prop 7 "a rephrasing" of it (l. 783); the uniformity in
the shapes is not argued there. Own step (D-DDDF-21, proposed): monotonicity of crossing lengths
in the shape, `L_{A,B} ≤ L_{a,b}` and `L_{a',b'} ≤ L_{B,A}` (a left–right crossing of the wider
or lower rectangle contains one of the narrower or higher one, `rectLen_rectAB_mono`), reduces to
the single pair of shapes `(A,B)`, `(B,A)` of `rsw_low` / `rsw_high`. (DF's Lemma 4.8 route with
the factor `j(b/a)` is not uniform as `a/b → 1`.) The reduction does not need `a/b < 1 < a'/b'`,
so the statements below hold for all `(a,b), (a',b') ∈ [A,B]²`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

namespace LQGMetric
namespace DDDF

open WhiteNoise

/-- **Monotonicity in the shape** (own step, D-DDDF-21): for `0 ≤ x ≤ X`, `0 ≤ y ≤ y'`, the
left–right crossing length of `[0,x] × [0,y']` is at most that of `[0,X] × [0,y]` (cut a crossing
of the latter at its first hitting of `Re = x`). -/
theorem rectLen_rectAB_mono {ξ : ℝ} {f : ℂ → ℝ} {x X y y' : ℝ} (hx : 0 ≤ x) (hxX : x ≤ X)
    (hyy : y ≤ y') : rectLen ξ f (rectAB x y') ≤ rectLen ξ f (rectAB X y) := by
  refine le_crossLenIn fun P hP => ?_
  obtain ⟨z, hz, w, hw, hPc, hPU⟩ := hP
  have hU : ∀ u ∈ Icc (0 : ℝ) 1, (P u).re ∈ Icc 0 X ∧ (P u).im ∈ Icc 0 y := fun u hu => by
    have := hPU u hu
    simpa [rectAB, MarkedRect.toSet, Complex.mem_reProdIm] using this
  have hz' : z.re = 0 ∧ z.im ∈ Icc 0 y := by
    simpa [rectAB, MarkedRect.side₁, Complex.mem_reProdIm] using hz
  have hw' : w.re = X := by
    simp only [rectAB, MarkedRect.side₂, ite_true, Complex.mem_reProdIm, zero_add,
      mem_singleton_iff] at hw
    exact hw.1
  have hcont : ContinuousOn (fun u => (P u).re) (Icc 0 1) :=
    Complex.continuous_re.comp_continuousOn hPc.continuousOn
  set Sx := Icc (0 : ℝ) 1 ∩ (fun u => (P u).re) ⁻¹' Ici x with hSx
  have hScl : IsClosed Sx := hcont.preimage_isClosed_of_isClosed isClosed_Icc isClosed_Ici
  have hSc : IsCompact Sx := isCompact_Icc.of_isClosed_subset hScl inter_subset_left
  have h1S : (1 : ℝ) ∈ Sx := ⟨⟨zero_le_one, le_rfl⟩, by
    show x ≤ (P 1).re
    rw [hPc.target, hw']; exact hxX⟩
  obtain ⟨t, htS, htmin⟩ := hSc.exists_isLeast ⟨1, h1S⟩
  have ht1 : t ∈ Icc (0 : ℝ) 1 := htS.1
  have hxt : x ≤ (P t).re := htS.2
  have hlt : ∀ u ∈ Ico 0 t, (P u).re < x := fun u hu => by
    by_contra h
    push Not at h
    have := htmin ⟨⟨hu.1, hu.2.le.trans ht1.2⟩, h⟩
    linarith [hu.2]
  have hte : (P t).re = x := by
    refine le_antisymm ?_ hxt
    rcases eq_or_lt_of_le ht1.1 with h0 | h0
    · rw [← h0, hPc.source, hz'.1]; exact hx
    · have hT : IsClosed (Icc (0 : ℝ) 1 ∩ (fun u => (P u).re) ⁻¹' Iic x) :=
        hcont.preimage_isClosed_of_isClosed isClosed_Icc isClosed_Iic
      have hsub : Ico 0 t ⊆ Icc (0 : ℝ) 1 ∩ (fun u => (P u).re) ⁻¹' Iic x := fun u hu =>
        ⟨⟨hu.1, hu.2.le.trans ht1.2⟩, (hlt u hu).le⟩
      have h2 := hT.closure_subset_iff.2 hsub
      rw [closure_Ico h0.ne] at h2
      exact (h2 ⟨h0.le, le_rfl⟩).2
  refine crossLenIn_le_of_sub hPc (s := 0) (t := t) ⟨le_rfl, zero_le_one⟩ ht1 ?_ ?_ ?_
  · intro u hu
    rw [uIcc_of_le ht1.1] at hu
    have h1 := hU u ⟨hu.1, hu.2.trans ht1.2⟩
    have h2 : (P u).re ≤ x := by
      rcases eq_or_lt_of_le hu.2 with h | h
      · rw [h]; exact hte.le
      · exact (hlt u ⟨hu.1, h⟩).le
    simp only [rectAB, MarkedRect.toSet, Complex.mem_reProdIm, zero_add]
    exact ⟨⟨h1.1.1, h2⟩, h1.2.1, h1.2.2.trans hyy⟩
  · rw [hPc.source]
    simp only [rectAB, MarkedRect.side₁, ite_true, Complex.mem_reProdIm, zero_add,
      mem_singleton_iff]
    exact ⟨hz'.1, hz'.2.1, hz'.2.2.trans hyy⟩
  · have h1 := hU t ht1
    simp only [rectAB, MarkedRect.side₂, ite_true, Complex.mem_reProdIm, zero_add,
      mem_singleton_iff]
    exact ⟨hte, h1.2.1, h1.2.2.trans hyy⟩

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {W : WNSpace → Ω → ℝ} {ξ : ℝ}

omit [MeasurableSpace Ω] in
theorem lenObs_rectAB_mono {Y : ℂ → Ω → ℝ} (hYc : ∀ ω, Continuous fun x => Y x ω)
    {x X y y' : ℝ} (hx : 0 ≤ x) (hxX : x ≤ X) (hy : 0 ≤ y) (hyy : y ≤ y') (ω : Ω) :
    lenObs ξ Y (rectAB x y') ω ≤ lenObs ξ Y (rectAB X y) ω :=
  ENNReal.toReal_mono (rectLen_ne_top _ (hx.trans hxX) hy (hYc ω))
    (rectLen_rectAB_mono hx hxX hyy)

/-- **DDDF Proposition 7, small quantiles, uniform over `[A, B]`** (l. 653–662 in probability
form; from `rsw_low` for the shapes `(A,B)`, `(B,A)` and `lenObs_rectAB_mono`). -/
theorem rsw_low_unif (hW : IsWhiteNoise P W) (h10 : Prop10 ξ P W) {A B : ℝ} (hA : 0 < A)
    (hAB : A < B) :
    ∃ C : ℝ, 0 < C ∧ ∀ a b a' b' : ℝ, a ∈ Icc A B → b ∈ Icc A B → a' ∈ Icc A B → b' ∈ Icc A B →
      ∀ (n : ℕ) (l ε : ℝ), 0 < ε → ε < 1 / 2 →
      ENNReal.ofReal ε ≤ P {ω | lenObs ξ (phiMN W P 0 n) (rectAB a b) ω ≤ l} →
      ENNReal.ofReal (ε / C) ≤ P {ω | lenObs ξ (phiMN W P 0 n) (rectAB a' b') ω ≤
        C * l * Real.exp (C * Real.sqrt |Real.log (ε / C)|)} := by
  obtain ⟨C, hC0, hC⟩ := rsw_low (ξ := ξ) hW h10 hA hAB (hA.trans hAB) hA
  refine ⟨C, hC0, fun a b a' b' ha hb ha' hb' n l ε hε hε2 hP => ?_⟩
  have hc := (isPhiVersion_phiMN hW (Nat.zero_le n)).cont
  refine (hC n l ε hε hε2 (hP.trans (measure_mono fun ω hω => ?_))).trans
    (measure_mono fun ω hω => ?_)
  · exact (lenObs_rectAB_mono hc hA.le ha.1 (hA.le.trans hb.1) hb.2 ω).trans hω
  · exact (lenObs_rectAB_mono hc (hA.le.trans ha'.1) ha'.2 hA.le hb'.1 ω).trans hω

/-- **DDDF Proposition 7, high quantiles, uniform over `[A, B]`** (l. 653–662 in probability
form, reading D-DDDF-8; from `rsw_high` for the shapes `(A,B)`, `(B,A)`). -/
theorem rsw_high_unif (hW : IsWhiteNoise P W) (hξ : 0 ≤ ξ) (h10 : Prop10 ξ P W) {A B : ℝ}
    (hA : 0 < A) (hAB : A < B) :
    ∃ C : ℝ, 0 < C ∧ (∀ a b a' b' : ℝ, a ∈ Icc A B → b ∈ Icc A B → a' ∈ Icc A B → b' ∈ Icc A B →
      ∀ (n : ℕ) (l ε : ℝ), 0 < ε → ε < 1 / 2 →
      ENNReal.ofReal (1 - ε) ≤ P {ω | lenObs ξ (phiMN W P 0 n) (rectAB a b) ω ≤ l} →
      ENNReal.ofReal (1 - 3 * ε ^ (1 / C)) ≤ P {ω | lenObs ξ (phiMN W P 0 n) (rectAB a' b') ω ≤
        C * l * Real.exp (C * Real.sqrt |Real.log (ε / C)|)}) ∧ 1 ≤ C := by
  obtain ⟨C, hC0, hC, hC1⟩ := rsw_high (ξ := ξ) hW hξ h10 hA hAB (hA.trans hAB) hA
  refine ⟨C, hC0, fun a b a' b' ha hb ha' hb' n l ε hε hε2 hP => ?_, hC1⟩
  have hc := (isPhiVersion_phiMN hW (Nat.zero_le n)).cont
  refine (hC n l ε hε hε2 (hP.trans (measure_mono fun ω hω => ?_))).trans
    (measure_mono fun ω hω => ?_)
  · exact (lenObs_rectAB_mono hc hA.le ha.1 (hA.le.trans hb.1) hb.2 ω).trans hω
  · exact (lenObs_rectAB_mono hc (hA.le.trans ha'.1) ha'.2 hA.le hb'.1 ω).trans hω

end DDDF
end LQGMetric
