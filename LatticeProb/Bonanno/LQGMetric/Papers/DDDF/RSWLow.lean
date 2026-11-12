/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DDDF.RSWLow at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DDDF.RSWMaps
import Mathlib.Analysis.Complex.ExponentialBounds

/-!
# DDDF Proposition 14 (= Prop 7), Step 1: comparison of small quantiles

Task P2-DDDFRSW. DDDF `tightness.tex` l. 783–797 (Step 1), after DF arXiv:1809.02607, proof of
Thm 3.1 (DF:624–650): if `P(L_{a,b}^{(n)} ≤ l) ≥ ε` then, by Lemma 11 iterated and the union
bound, one of the finitely many crossings `(K_τ, A_τ, B_τ)` of `rsw_geom` has
`P(L_τ ≤ l) ≥ ε/N` (`N` = number of crossings, DDDF's `j^p m²`); Prop 10 (1) gives
`P(L'_τ ≤ l'_τ) ≥ ε/(4N)`, and `L^{(n)}_{a',b'} ≤ L'_τ` (Lemma 12′ (2)). The constants are
absorbed as in DDDF l. 795: `l'_τ ≤ C l e^{C√|log(ε/C)|}` (`p10Len_le`).

`rsw_low`: ∃ `C > 0`, ∀ `n`, `l`, `ε ∈ (0, 1/2)`:
`P(L^{(n)}_{a,b} ≤ l) ≥ ε ⇒ P(L^{(n)}_{a',b'} ≤ C l e^{C√|log(ε/C)|}) ≥ ε/C`
(DDDF l. 788, item 1), for `0 < a < b`, `a', b' > 0`, given `Prop10 ξ P W`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

namespace LQGMetric
namespace DDDF

open WhiteNoise

/-- `|log(ε/c)| ≤ (1 + 2|log c|) |log(ε/C)|` for `ε < 1/2`, `C ≥ 1` (own elementary step, D-DDDF-20) -/
theorem abs_log_div_le {ε c C : ℝ} (hε : 0 < ε) (hε2 : ε < 1 / 2) (hc : 0 < c) (hC : 1 ≤ C) :
    |Real.log (ε / c)| ≤ (1 + 2 * |Real.log c|) * |Real.log (ε / C)| := by
  have hlogε : Real.log ε < -Real.log 2 := by
    rw [← Real.log_inv]; exact Real.log_lt_log hε (by norm_num; linarith)
  have hl2 := Real.log_two_gt_d9
  have hlogC : 0 ≤ Real.log C := Real.log_nonneg hC
  rw [Real.log_div hε.ne' hc.ne', Real.log_div hε.ne' (by linarith : C ≠ 0),
    abs_of_neg (by linarith : Real.log ε - Real.log C < 0)]
  have h1 : |Real.log ε - Real.log c| ≤ -Real.log ε + |Real.log c| := by
    refine (abs_sub _ _).trans ?_
    rw [abs_of_neg (by linarith : Real.log ε < 0)]
  have h3 : |Real.log c| ≤ 2 * |Real.log c| * (-(Real.log ε - Real.log C)) := by
    nlinarith [abs_nonneg (Real.log c)]
  nlinarith [abs_nonneg (Real.log c)]

/-- the constant bookkeeping of DDDF l. 795 -/
theorem p10Len_le {Cτ S l ε₁ ε c C : ℝ} (hCτ : 0 < Cτ) (hl : 0 < l)
    (hc : 0 < c) (he : ε₁ / (2 * Cτ) = ε / c)
    (hC1 : 1 ≤ C) (hCS : Cτ * S ≤ C) (hCk : Cτ * Real.sqrt (1 + 2 * |Real.log c|) ≤ C)
    (hε : 0 < ε) (hε2 : ε < 1 / 2) :
    p10Len Cτ l ε₁ S ≤ C * l * Real.exp (C * Real.sqrt |Real.log (ε / C)|) := by
  unfold p10Len
  rw [he]
  have hk := abs_log_div_le hε hε2 hc hC1
  have hsq : Real.sqrt |Real.log (ε / c)| ≤
      Real.sqrt (1 + 2 * |Real.log c|) * Real.sqrt |Real.log (ε / C)| := by
    rw [← Real.sqrt_mul (by positivity)]; exact Real.sqrt_le_sqrt hk
  have hexp : Real.exp (Cτ * Real.sqrt |Real.log (ε / c)|) ≤
      Real.exp (C * Real.sqrt |Real.log (ε / C)|) := by
    refine Real.exp_le_exp.2 ?_
    calc Cτ * Real.sqrt |Real.log (ε / c)|
        ≤ Cτ * (Real.sqrt (1 + 2 * |Real.log c|) * Real.sqrt |Real.log (ε / C)|) :=
          mul_le_mul_of_nonneg_left hsq hCτ.le
      _ = (Cτ * Real.sqrt (1 + 2 * |Real.log c|)) * Real.sqrt |Real.log (ε / C)| := by ring
      _ ≤ C * Real.sqrt |Real.log (ε / C)| :=
          mul_le_mul_of_nonneg_right hCk (Real.sqrt_nonneg _)
  have hl1 : Cτ * l * S ≤ C * l := by nlinarith
  exact mul_le_mul hl1 hexp (Real.exp_pos _).le (by positivity)

theorem derivSup_nonneg (F : ℂ → ℂ) (K : Set ℂ) : 0 ≤ derivSup F K :=
  Real.sSup_nonneg fun _ ⟨_, _, hx⟩ => hx ▸ norm_nonneg _

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {W : WNSpace → Ω → ℝ} {ξ : ℝ}

/-- **DDDF Proposition 14 (= Prop 7), item 1** (small quantiles; l. 788, Step 1 l. 792–797). -/
theorem rsw_low (hW : IsWhiteNoise P W) (h10 : Prop10 ξ P W) {a b a' b' : ℝ} (ha : 0 < a)
    (hab : a < b) (ha' : 0 < a') (hb' : 0 < b') :
    ∃ C : ℝ, 0 < C ∧ ∀ (n : ℕ) (l ε : ℝ), 0 < ε → ε < 1 / 2 →
      ENNReal.ofReal ε ≤ P {ω | lenObs ξ (phiMN W P 0 n) (rectAB a b) ω ≤ l} →
      ENNReal.ofReal (ε / C) ≤ P {ω | lenObs ξ (phiMN W P 0 n) (rectAB a' b') ω ≤
        C * l * Real.exp (C * Real.sqrt |Real.log (ε / C)|)} := by
  have := hW.isProbabilityMeasure
  obtain ⟨κ, _, K, A, B, U, F, hgeo, hlow, hup⟩ := rsw_geom ha hab ha' hb'
  have hC := fun τ => h10 (K τ) (A τ) (B τ) (U τ) (F τ) (hgeo τ).1 (hgeo τ).2.1
    (hgeo τ).2.2.1 (hgeo τ).2.2.2.1 (hgeo τ).2.2.2.2.1 (hgeo τ).2.2.2.2.2
  choose Cτ hCτ0 hCτ using hC
  set N : ℝ := (Fintype.card κ : ℝ) with hNdef
  set S : κ → ℝ := fun τ => derivSup (F τ) (K τ) with hSdef
  set T : κ → ℝ := fun τ => Cτ τ * S τ + Cτ τ * Real.sqrt (1 + 2 * |Real.log (2 * Cτ τ * N)|)
    with hTdef
  have hT0 : ∀ τ, 0 ≤ T τ := fun τ => by
    have := derivSup_nonneg (F τ) (K τ)
    have := hCτ0 τ
    positivity
  have hTle : ∀ τ, T τ ≤ ∑ τ', T τ' := fun τ =>
    Finset.single_le_sum (fun i _ => hT0 i) (Finset.mem_univ τ)
  have hN0 : 0 ≤ N := Nat.cast_nonneg _
  set C : ℝ := ∑ τ, T τ + 4 * N + 1 with hCdef
  have hsum0 : 0 ≤ ∑ τ, T τ := Finset.sum_nonneg fun i _ => hT0 i
  have hC1 : 1 ≤ C := by linarith
  refine ⟨C, by linarith, fun n l ε hε hε2 hP => ?_⟩
  have hφ := isPhiVersion_phiMN hW (Nat.zero_le n)
  have hR : ∀ {x y : ℝ}, 0 < x → 0 < y → 0 < (rectAB x y).crossWidth := fun hx _ => by
    simpa [MarkedRect.crossWidth, rectAB] using hx
  obtain ⟨ω₀, hω₀⟩ : {ω | lenObs ξ (phiMN W P 0 n) (rectAB a b) ω ≤ l}.Nonempty :=
    nonempty_of_measure_ne_zero (lt_of_lt_of_le (ENNReal.ofReal_pos.2 hε) hP).ne'
  have hb : 0 < b := ha.trans hab
  have hl : 0 < l :=
    (lenObs_pos hφ.cont (rectAB a b) ha.le hb.le (hR ha hb) ω₀).trans_le hω₀
  have hκ : Nonempty κ := by
    by_contra hne
    rw [not_nonempty_iff] at hne
    have h := hlow ξ (fun x => phiMN W P 0 n x ω₀)
    rw [iInf_of_empty, top_le_iff] at h
    exact rectLen_ne_top _ ha.le hb.le (hφ.cont ω₀) h
  have hN1 : 1 ≤ N := by
    rw [hNdef]; exact_mod_cast Fintype.card_pos
  -- the union bound over the crossings `τ` (DDDF l. 794)
  have hsub : {ω | lenObs ξ (phiMN W P 0 n) (rectAB a b) ω ≤ l} ⊆
      ⋃ τ, {ω | crossLenIn ξ (fun x => phiMN W P 0 n x ω) (K τ) (A τ) (B τ) ≤
        ENNReal.ofReal l} := by
    intro ω hω
    obtain ⟨τ, hτ⟩ := Finite.exists_min
      (fun τ => crossLenIn ξ (fun x => phiMN W P 0 n x ω) (K τ) (A τ) (B τ))
    refine mem_iUnion.2 ⟨τ, ?_⟩
    calc _ ≤ ⨅ τ', crossLenIn ξ (fun x => phiMN W P 0 n x ω) (K τ') (A τ') (B τ') :=
          le_iInf hτ
      _ ≤ rectLen ξ (fun x => phiMN W P 0 n x ω) (rectAB a b) := hlow ξ _
      _ = ENNReal.ofReal (lenObs ξ (phiMN W P 0 n) (rectAB a b) ω) :=
          (ofReal_lenObs hφ.cont _ ha.le hb.le ω).symm
      _ ≤ ENNReal.ofReal l := ENNReal.ofReal_le_ofReal hω
  obtain ⟨τ, hτ⟩ : ∃ τ, ENNReal.ofReal (ε / N) ≤
      P {ω | crossLenIn ξ (fun x => phiMN W P 0 n x ω) (K τ) (A τ) (B τ) ≤
        ENNReal.ofReal l} := by
    by_contra hcon
    push Not at hcon
    have h1 := (hP.trans (measure_mono hsub)).trans (measure_iUnion_fintype_le P _)
    have h2 := ENNReal.sum_lt_sum_of_nonempty Finset.univ_nonempty fun τ (_ : τ ∈ Finset.univ) =>
      hcon τ
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, ← ENNReal.ofReal_natCast,
      ← ENNReal.ofReal_mul (Nat.cast_nonneg _), ← hNdef,
      mul_div_cancel₀ _ (by linarith : N ≠ 0)] at h2
    exact lt_irrefl _ (h1.trans_lt h2)
  have hε₁ : 0 < ε / N := div_pos hε (by linarith)
  have hε₁2 : ε / N < 1 / 2 := lt_of_le_of_lt (div_le_self hε.le hN1) hε2
  have h3 := (hCτ τ n l (ε / N) hl hε₁ hε₁2).1 hτ
  refine le_trans ?_ (h3.trans (measure_mono fun ω hω => ?_))
  · refine ENNReal.ofReal_le_ofReal ?_
    rw [div_div]
    exact div_le_div_of_nonneg_left hε.le (by positivity) (by linarith)
  · simp only [mem_ofPred_eq] at hω ⊢
    have h4 := (hup ξ (fun x => phiMN W P 0 n x ω) τ).trans hω
    rw [← ofReal_lenObs hφ.cont _ ha'.le hb'.le ω] at h4
    have h5 := (ENNReal.ofReal_le_ofReal_iff (by
      unfold p10Len; have := derivSup_nonneg (F τ) (K τ); have := hCτ0 τ
      positivity)).1 h4
    refine h5.trans (p10Len_le (hCτ0 τ) hl
      (c := 2 * Cτ τ * N) (by have := hCτ0 τ; positivity) (by field_simp) hC1 ?_ ?_ hε hε2)
    · have := hTle τ
      have : 0 ≤ Cτ τ * Real.sqrt (1 + 2 * |Real.log (2 * Cτ τ * N)|) :=
        mul_nonneg (hCτ0 τ).le (Real.sqrt_nonneg _)
      simp only [hTdef] at *
      linarith
    · have := hTle τ
      have : 0 ≤ Cτ τ * S τ := mul_nonneg (hCτ0 τ).le (derivSup_nonneg _ _)
      simp only [hTdef] at *
      linarith

end DDDF
end LQGMetric
