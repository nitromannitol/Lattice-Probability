/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DDDF.RSWHigh at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DDDF.RSWLow
import LatticeProb.Bonanno.LQGMetric.Papers.DDDF.L13Cross

/-!
# DDDF Proposition 14 (= Prop 7), Step 2: comparison of high quantiles

Task P2-DDDFRSW2. DDDF arXiv:1904.08021, `tightness.tex` l. 788–790 (item 2) and l. 799–806
(Step 2), after DF arXiv:1809.02607, proof of Thm 3.1 (DF:650–678): if
`P(L_{a,b}^{(n)} ≤ l) ≥ 1 − ε`, then on this event one of the finitely many crossings
`(K_τ, A_τ, B_τ)` of `rsw_geom` (Lemma 11 iterated + Lemma 12′) has length `≤ l`; by the
square-root trick (Lemma 13 for these crossings, `lemma13_cross_sqrt`) some `τ` has
`P(L_τ ≤ l) ≥ 1 − ε^{1/N}` (`N` = number of crossings, DDDF's `j^p m²`); Prop 10 (2) with
`ε₁ = ε^{1/N}` gives `P(L'_τ ≤ l'_τ) ≥ 1 − 3ε₁ ≥ 1 − 3ε^{1/C}`, and `L^{(n)}_{a',b'} ≤ L'_τ`.
Two bookkeeping points DDDF leave implicit: Prop 10 (2) needs `ε₁ < 1/2`; when `ε₁ ≥ 1/3` the
conclusion is trivial (`1 − 3ε^{1/C} ≤ 0`). Crossings `τ` with no admissible path
(`crossLenIn ξ 0 K_τ A_τ B_τ = ∞`) never have finite length and are dropped before the square-root
trick (Lemma 13 needs finite lengths).

`rsw_high`: ∃ `C > 0`, ∀ `n`, `l`, `ε ∈ (0, 1/2)`:
`P(L^{(n)}_{a,b} ≤ l) ≥ 1 − ε ⇒ P(L^{(n)}_{a',b'} ≤ C l e^{C√|log(ε/C)|}) ≥ 1 − 3ε^{1/C}`
(DDDF l. 789, item 2; the constant also satisfies `C ≥ 1`), for `0 < a < b`, `a', b' > 0`, `ξ ≥ 0`, given `Prop10 ξ P W`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

namespace LQGMetric
namespace DDDF

open WhiteNoise

/-- a crossing with finite length for a continuous field has an admissible path -/
theorem crossLenIn_zero_ne_top_of_cont {ξ : ℝ} {K A B : Set ℂ} (hK : IsCompact K) {f : ℂ → ℝ}
    (hf : Continuous f) (h : crossLenIn ξ f K A B ≠ ⊤) : crossLenIn ξ 0 K A B ≠ ⊤ := by
  obtain ⟨M, hM⟩ := (hK.image_of_continuousOn (continuous_abs.comp hf).continuousOn).isBounded
    |>.bddAbove
  exact crossLenIn_zero_ne_top (fun x hx => hM ⟨x, hx, rfl⟩) h

theorem abs_log_div_mono {ε ε₁ C : ℝ} (hε : 0 < ε) (hεε : ε ≤ ε₁) (hε₁ : ε₁ < 1) (hC : 1 ≤ C) :
    |Real.log (ε₁ / C)| ≤ |Real.log (ε / C)| := by
  have hC0 : 0 < C := by linarith
  have h1 : ε₁ / C < 1 := (div_lt_one hC0).2 (by linarith)
  have h0 : 0 < ε / C := div_pos hε hC0
  rw [abs_of_neg (Real.log_neg (h0.trans_le (div_le_div_of_nonneg_right hεε hC0.le)) h1),
    abs_of_neg (Real.log_neg h0 ((div_le_div_of_nonneg_right hεε hC0.le).trans_lt h1))]
  exact neg_le_neg (Real.log_le_log h0 (div_le_div_of_nonneg_right hεε hC0.le))

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {W : WNSpace → Ω → ℝ} {ξ : ℝ}

/-- **DDDF Proposition 14 (= Prop 7), item 2** (high quantiles; l. 789, Step 2 l. 799–806). -/
theorem rsw_high (hW : IsWhiteNoise P W) (hξ : 0 ≤ ξ) (h10 : Prop10 ξ P W) {a b a' b' : ℝ}
    (ha : 0 < a) (hab : a < b) (ha' : 0 < a') (hb' : 0 < b') :
    ∃ C : ℝ, 0 < C ∧ (∀ (n : ℕ) (l ε : ℝ), 0 < ε → ε < 1 / 2 →
      ENNReal.ofReal (1 - ε) ≤ P {ω | lenObs ξ (phiMN W P 0 n) (rectAB a b) ω ≤ l} →
      ENNReal.ofReal (1 - 3 * ε ^ (1 / C)) ≤ P {ω | lenObs ξ (phiMN W P 0 n) (rectAB a' b') ω ≤
        C * l * Real.exp (C * Real.sqrt |Real.log (ε / C)|)}) ∧ 1 ≤ C := by
  classical
  have := hW.isProbabilityMeasure
  obtain ⟨κ, _, K, A, B, U, F, hgeo, hlow, hup⟩ := rsw_geom ha hab ha' hb'
  have hC := fun τ => h10 (K τ) (A τ) (B τ) (U τ) (F τ) (hgeo τ).1 (hgeo τ).2.1
    (hgeo τ).2.2.1 (hgeo τ).2.2.2.1 (hgeo τ).2.2.2.2.1 (hgeo τ).2.2.2.2.2
  choose Cτ hCτ0 hCτ using hC
  set N : ℝ := (Fintype.card κ : ℝ) with hNdef
  set S : κ → ℝ := fun τ => derivSup (F τ) (K τ) with hSdef
  set T : κ → ℝ := fun τ => Cτ τ * S τ + Cτ τ * Real.sqrt (1 + 2 * |Real.log (2 * Cτ τ)|)
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
  have hC0 : 0 < C := by linarith
  refine ⟨C, hC0, fun n l ε hε hε2 hP => ?_, hC1⟩
  have hφ := isPhiVersion_phiMN hW (Nat.zero_le n)
  set Y := phiMN W P 0 n with hYdef
  have hR : ∀ {x y : ℝ}, 0 < x → 0 < y → 0 < (rectAB x y).crossWidth := fun hx _ => by
    simpa [MarkedRect.crossWidth, rectAB] using hx
  obtain ⟨ω₀, hω₀⟩ : {ω | lenObs ξ Y (rectAB a b) ω ≤ l}.Nonempty :=
    nonempty_of_measure_ne_zero (lt_of_lt_of_le (ENNReal.ofReal_pos.2 (by linarith)) hP).ne'
  have hb : 0 < b := ha.trans hab
  have hl : 0 < l :=
    (lenObs_pos hφ.cont (rectAB a b) ha.le hb.le (hR ha hb) ω₀).trans_le hω₀
  have hκ : Nonempty κ := by
    by_contra hne
    rw [not_nonempty_iff] at hne
    have h := hlow ξ (fun x => Y x ω₀)
    rw [iInf_of_empty, top_le_iff] at h
    exact rectLen_ne_top _ ha.le hb.le (hφ.cont ω₀) h
  -- the crossings with an admissible path
  set κ' := {τ : κ // crossLenIn ξ 0 (K τ) (A τ) (B τ) ≠ ⊤}
  have hfin' : ∀ τ : κ', ∀ ω, crossLenIn ξ (fun x => Y x ω) (K τ.1) (A τ.1) (B τ.1) ≠ ⊤ :=
    fun τ ω => crossLenIn_ne_top_of_cont (hgeo τ.1).1 τ.2 (hφ.cont ω)
  -- on `{L_{a,b} ≤ l}` some crossing has length `≤ l` (DDDF l. 801–803)
  have hsub : ∀ ω, lenObs ξ Y (rectAB a b) ω ≤ l → ∃ τ : κ',
      (crossLenIn ξ (fun x => Y x ω) (K τ.1) (A τ.1) (B τ.1)).toReal ≤ l := by
    intro ω hω
    obtain ⟨τ, hτ⟩ := Finite.exists_min
      (fun τ => crossLenIn ξ (fun x => Y x ω) (K τ) (A τ) (B τ))
    have h1 : crossLenIn ξ (fun x => Y x ω) (K τ) (A τ) (B τ) ≤ ENNReal.ofReal l :=
      calc _ ≤ ⨅ τ', crossLenIn ξ (fun x => Y x ω) (K τ') (A τ') (B τ') := le_iInf hτ
        _ ≤ rectLen ξ (fun x => Y x ω) (rectAB a b) := hlow ξ _
        _ = ENNReal.ofReal (lenObs ξ Y (rectAB a b) ω) :=
            (ofReal_lenObs hφ.cont _ ha.le hb.le ω).symm
        _ ≤ ENNReal.ofReal l := ENNReal.ofReal_le_ofReal hω
    have hne := ne_top_of_le_ne_top ENNReal.ofReal_ne_top h1
    exact ⟨⟨τ, crossLenIn_zero_ne_top_of_cont (hgeo τ).1 (hφ.cont ω) hne⟩,
      ENNReal.toReal_le_of_le_ofReal hl.le h1⟩
  have : Nonempty κ' := (hsub ω₀ hω₀).nonempty
  -- the square-root trick (DDDF l. 803)
  obtain ⟨τ, hτ⟩ := lemma13_cross_sqrt hξ hφ.cont hφ.meas
    (hasGaussianLaw_phiMN hW (Nat.zero_le n)) (cov_phiMN_nonneg hW (Nat.zero_le n))
    (fun τ : κ' => K τ.1) (fun τ => A τ.1) (fun τ => B τ.1) (fun τ => (hgeo τ.1).1)
    (fun τ => τ.2) (fun _ => l)
  set N' : ℝ := (Fintype.card κ' : ℝ) with hN'def
  have hN'1 : 1 ≤ N' := by rw [hN'def]; exact_mod_cast Fintype.card_pos
  have hN'N : N' ≤ N := by
    rw [hN'def, hNdef]; exact_mod_cast Fintype.card_subtype_le _
  set Ev := ⋃ τ : κ', {ω | (crossLenIn ξ (fun x => Y x ω) (K τ.1) (A τ.1) (B τ.1)).toReal ≤ l}
  have hEv : 1 - ε ≤ P.real Ev := by
    have h1 : ENNReal.ofReal (1 - ε) ≤ P Ev :=
      hP.trans (measure_mono fun ω hω => mem_iUnion.2 (hsub ω hω))
    rwa [← ofReal_measureReal, ENNReal.ofReal_le_ofReal_iff measureReal_nonneg] at h1
  set ε₁ := ε ^ (1 / N') with hε₁def
  have hε1 : ε < 1 := by linarith
  have hroot : (1 - P.real Ev) ^ (1 / N') ≤ ε₁ :=
    Real.rpow_le_rpow (by linarith [measureReal_le_one (μ := P) (s := Ev)]) (by linarith)
      (by positivity)
  have hτ' : 1 - ε₁ ≤
      P.real {ω | (crossLenIn ξ (fun x => Y x ω) (K τ.1) (A τ.1) (B τ.1)).toReal ≤ l} := by
    linarith
  have hεε₁ : ε ≤ ε₁ := by
    calc ε = ε ^ (1 : ℝ) := (Real.rpow_one ε).symm
      _ ≤ ε₁ := Real.rpow_le_rpow_of_exponent_ge hε hε1.le
          (by rw [div_le_one (by linarith)]; exact hN'1)
  have hε₁C : ε₁ ≤ ε ^ (1 / C) :=
    Real.rpow_le_rpow_of_exponent_ge hε hε1.le
      (one_div_le_one_div_of_le (by linarith) (by linarith))
  by_cases h3 : 1 / 3 ≤ ε₁
  · rw [ENNReal.ofReal_of_nonpos (by linarith)]; exact zero_le
  push Not at h3
  have hε₁0 : 0 < ε₁ := hε.trans_le hεε₁
  have hP₁ : ENNReal.ofReal (1 - ε₁) ≤ P {ω | crossLenIn ξ (fun x => Y x ω) (K τ.1) (A τ.1)
      (B τ.1) ≤ ENNReal.ofReal l} := by
    refine le_trans ?_ (measure_mono (s := {ω | (crossLenIn ξ (fun x => Y x ω) (K τ.1) (A τ.1)
      (B τ.1)).toReal ≤ l}) fun ω hω =>
      (ENNReal.le_ofReal_iff_toReal_le (hfin' τ ω) hl.le).2 hω)
    exact (ENNReal.ofReal_le_iff_le_toReal (measure_ne_top _ _)).2 hτ'
  have h4 := (hCτ τ.1 n l ε₁ hl hε₁0 (by linarith)).2 hP₁
  refine le_trans (ENNReal.ofReal_le_ofReal (by linarith)) (h4.trans (measure_mono fun ω hω => ?_))
  simp only [mem_ofPred_eq] at hω ⊢
  have h5 := (hup ξ (fun x => Y x ω) τ.1).trans hω
  rw [← ofReal_lenObs hφ.cont _ ha'.le hb'.le ω] at h5
  have h6 := (ENNReal.ofReal_le_ofReal_iff (by
    unfold p10Len; have := derivSup_nonneg (F τ.1) (K τ.1); have := hCτ0 τ.1
    positivity)).1 h5
  have h7 : p10Len (Cτ τ.1) l ε₁ (S τ.1) ≤
      C * l * Real.exp (C * Real.sqrt |Real.log (ε₁ / C)|) := by
    refine p10Len_le (hCτ0 τ.1) hl (c := 2 * Cτ τ.1) (by have := hCτ0 τ.1; positivity) rfl hC1
      ?_ ?_ hε₁0 (by linarith)
    · have := hTle τ.1
      have : 0 ≤ Cτ τ.1 * Real.sqrt (1 + 2 * |Real.log (2 * Cτ τ.1)|) :=
        mul_nonneg (hCτ0 τ.1).le (Real.sqrt_nonneg _)
      simp only [hTdef] at *
      linarith
    · have := hTle τ.1
      have : 0 ≤ Cτ τ.1 * S τ.1 := mul_nonneg (hCτ0 τ.1).le (derivSup_nonneg _ _)
      simp only [hTdef] at *
      linarith
  have h8 : Real.exp (C * Real.sqrt |Real.log (ε₁ / C)|) ≤
      Real.exp (C * Real.sqrt |Real.log (ε / C)|) :=
    Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt
      (abs_log_div_mono hε hεε₁ (by linarith) hC1)) hC0.le)
  calc _ ≤ _ := h6
    _ ≤ _ := h7
    _ ≤ _ := mul_le_mul_of_nonneg_left h8 (by positivity)

end DDDF
end LQGMetric
