/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DDDF.T20DDen at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DDDF.T20DField

/-!
# DDDF Theorem 20, Step 4: the denominator bound (5.67) (task P2-DDDFT20d)

DDDF = arXiv:1904.08021, `tightness.tex` l. 1131–1149 (`eq:Denum`). For every block
`P ∈ π^K` visited by the near-geodesic `γ`, `γ` has a piece inside `\hat P` crossing one of the four
short rectangles `R_i^S(P)` (`T20D.exists_short_piece`); on `\hat P`
`e^{ξψ_{0,n}} ≥ e^{ξψ_{0,K}(P)} e^{-2ξX} e^{-3ξO} e^{ξφ_{K,n}}` (`|φ − ψ| ≤ X`,
`φ_{0,n} = φ_{0,K} + φ_{K,n}`, the mean value inequality for `φ_{0,K}`), so the `ψ_{0,n}`-length of
the piece is at least `e^{ξψ_{0,K}(P)} e^{-2ξX-3ξO} min_{J'} L^{(K,n)}(R^S)`. Each point lies in at
most 16 boxes `\hat P` (DDDF: 9), so summing over `P ∈ π^K`,
`e^{-2ξX-3ξO} min L(R^S) Σ_{π^K} e^{ξψ_{0,K}(P)} ≤ 16 lfppLen(γ) ≤ 32 L_n(ψ)`.
`J'` = the four short rectangles of every block of `blkIdx K`, `|J'| ≤ 36 · 4^K`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal

namespace LQGMetric
namespace DDDF

open WhiteNoise SupTail LFPP

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {W : WNSpace → Ω → ℝ}

namespace T20D

/-- the `g`-length of the piece of `γ` crossing a short rectangle of a visited block `P` is at
least `E · m` when `E e^{ξ f} ≤ e^{ξ g}` on `\hat P ∩ [0,1]²` and `m` bounds the `f`-crossings of
the `R_i^S(P)` from below -/
lemma piece_lower {ξ : ℝ} {K : ℕ} (hK : 2 ≤ K) {γ : ℝ → ℂ}
    (hγ : AdmPath (rectAB 1 1).toSet (rectAB 1 1).side₁ (rectAB 1 1).side₂ γ) {f g : ℂ → ℝ}
    {E m : ℝ} {b : ℤ × ℤ} (hb : b ∈ T20.coarseBlocks K γ) (hE : 0 ≤ E)
    (hfg : ∀ x ∈ (rectAB 1 1).toSet, x ∈ hatBox K b → E * Real.exp (ξ * f x) ≤ Real.exp (ξ * g x))
    (hmJ : ∀ j ∈ shortJ K b, m ≤ T20B.mrectLen ξ f K j.1 j.2 1 3) :
    ∃ a c, Icc a c ⊆ Icc (0 : ℝ) 1 ∧ (∀ r ∈ Icc a c, γ r ∈ hatBox K b) ∧
      ENNReal.ofReal (E * m) ≤ ∫⁻ r in Icc a c, lenDens ξ g γ r := by
  classical
  simp only [T20.coarseBlocks, Finset.mem_filter] at hb
  obtain ⟨-, t, ht, hbt⟩ := hb
  have hγU : ∀ r ∈ Icc (0 : ℝ) 1, γ r ∈ (rectAB 1 1).toSet := by
    obtain ⟨_, _, _, _, _, hU⟩ := hγ; exact hU
  obtain ⟨a, c, ha, hac, hc, hbox, j, hj, hadm⟩ := exists_short_piece hK hγ ht hbt
  have hsub : Icc a c ⊆ Icc (0 : ℝ) 1 := Icc_subset_Icc ha hc
  refine ⟨a, c, hsub, hbox, ?_⟩
  have hcross : crossLenIn ξ f (RS K j) (RS₁ K j) (RS₂ K j) ≤ lfppLen ξ f (subPath γ a c) := by
    rcases hadm with h | h
    · exact crossLenIn_le_lfppLen h
    · exact (crossLenIn_le_lfppLen h).trans_eq (lfppLen_revPath _)
  have hm' : ENNReal.ofReal m ≤ crossLenIn ξ f (RS K j) (RS₁ K j) (RS₂ K j) :=
    (ENNReal.ofReal_le_ofReal (hmJ j hj)).trans ENNReal.ofReal_toReal_le
  calc ENNReal.ofReal (E * m) ≤ ENNReal.ofReal E * ENNReal.ofReal m := by
        rw [ENNReal.ofReal_mul hE]
    _ ≤ ENNReal.ofReal E * ∫⁻ r in Icc a c, lenDens ξ f γ r := by
        gcongr; rw [← lfppLen_subPath γ hac]; exact hm'.trans hcross
    _ ≤ ∫⁻ r in Icc a c, ENNReal.ofReal E * lenDens ξ f γ r := lintegral_const_mul_le _ _
    _ ≤ ∫⁻ r in Icc a c, lenDens ξ g γ r := by
        refine setLIntegral_mono' measurableSet_Icc fun r hr => ?_
        simp only [lenDens]
        rw [← ENNReal.ofReal_mul hE, ← mul_assoc]
        exact ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right
          (hfg _ (hγU r (hsub hr)) (hbox r hr)) (norm_nonneg _))

/-- **bounded overlap** (DDDF l. 1140: each point is in at most 9 of the `\hat P`): pieces inside
the boxes `\hat P` have total `g`-length at most `16 ∫₀¹ g` -/
lemma sum_pieces_le {K : ℕ} {γ : ℝ → ℂ} (s : Finset (ℤ × ℤ)) (g : ℝ → ℝ≥0∞)
    (A : ℤ × ℤ → ℝ≥0∞) (hA : ∀ b ∈ s, ∃ a c, Icc a c ⊆ Icc (0 : ℝ) 1 ∧
      (∀ r ∈ Icc a c, γ r ∈ hatBox K b) ∧ A b ≤ ∫⁻ r in Icc a c, g r) :
    ∑ b ∈ s, A b ≤ 16 * ∫⁻ r in Icc (0 : ℝ) 1, g r := by
  classical
  have hA' : ∀ b, ∃ a c : ℝ, b ∈ s → Icc a c ⊆ Icc (0 : ℝ) 1 ∧
      (∀ r ∈ Icc a c, γ r ∈ hatBox K b) ∧ A b ≤ ∫⁻ r in Icc a c, g r := by
    intro b
    by_cases hb : b ∈ s
    · obtain ⟨a, c, h⟩ := hA b hb; exact ⟨a, c, fun _ => h⟩
    · exact ⟨0, 0, fun h => absurd h hb⟩
  choose a c hac using hA'
  have h1 : ∀ b ∈ s, A b ≤ ∫⁻ r in Icc (0 : ℝ) 1, (Icc (a b) (c b)).indicator g r := by
    intro b hb
    obtain ⟨hsub, -, hle⟩ := hac b hb
    rw [lintegral_indicator measurableSet_Icc, Measure.restrict_restrict measurableSet_Icc,
      inter_eq_left.2 hsub]
    exact hle
  calc ∑ b ∈ s, A b ≤ ∑ b ∈ s, ∫⁻ r in Icc (0 : ℝ) 1, (Icc (a b) (c b)).indicator g r :=
        Finset.sum_le_sum h1
    _ ≤ ∫⁻ r in Icc (0 : ℝ) 1, ∑ b ∈ s, (Icc (a b) (c b)).indicator g r :=
        T20C.sum_lintegral_le s _
    _ ≤ ∫⁻ r in Icc (0 : ℝ) 1, 16 * g r := by
        refine lintegral_mono fun r => ?_
        calc ∑ b ∈ s, (Icc (a b) (c b)).indicator g r
            ≤ ∑ b ∈ s, if γ r ∈ hatBox K b then g r else 0 := by
              refine Finset.sum_le_sum fun b hb => ?_
              by_cases hr : r ∈ Icc (a b) (c b)
              · rw [indicator_of_mem hr, if_pos ((hac b hb).2.1 r hr)]
              · rw [indicator_of_notMem hr]; exact zero_le
          _ = ((s.filter fun b => γ r ∈ hatBox K b).card : ℝ≥0∞) * g r := by
              rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
          _ ≤ 16 * g r := by
              gcongr
              exact_mod_cast card_filter_hatBox_le K s (γ r)
    _ = 16 * ∫⁻ r in Icc (0 : ℝ) 1, g r := lintegral_const_mul' _ _ (by norm_num)

lemma card_blkIdx_le (K : ℕ) : ((T20.blkIdx K).card : ℝ) ≤ 9 * 4 ^ K := by
  unfold T20.blkIdx
  rw [Finset.card_product, Int.card_Icc]
  have e : ((2 : ℤ) ^ K + 1 - -1) = ((2 ^ K + 2 : ℕ) : ℤ) := by push_cast; ring
  rw [e, Int.toNat_natCast]
  push_cast
  have h1 : (1 : ℝ) ≤ 2 ^ K := one_le_pow₀ (by norm_num)
  have h4 : (4 : ℝ) ^ K = 2 ^ K * 2 ^ K := by
    rw [← mul_pow]; norm_num
  rw [h4]; nlinarith

end T20D

open T20C T20D in
/-- **DDDF (5.67)** (`eq:Denum`, `tightness.tex` l. 1131–1149), with `(1+η)`-near-geodesics. -/
theorem dddf_t20_step4_den (hW : IsWhiteNoise P W) (Q : PsiParams) {ξ : ℝ} (hξ : 0 < ξ) :
    T20Step4Den ξ Q W P := by
  classical
  refine ⟨36 + 3 * ξ, by positivity, 2, fun K hK n hKn => ?_⟩
  set J' : Finset (Circle × ℂ) := (T20.blkIdx K).biUnion (shortJ K) with hJ'def
  have hJ' : J'.Nonempty := by
    refine Finset.biUnion_nonempty.2 ⟨(0, 0), ?_, ?_⟩
    · simp [T20.blkIdx]
    · simp [shortJ]
  refine ⟨J', hJ', ?_, fun η hη hη1 γ hγ Y hY hYc => ?_⟩
  · calc (J'.card : ℝ) ≤ ∑ b ∈ T20.blkIdx K, ((shortJ K b).card : ℝ) := by
          exact_mod_cast Finset.card_biUnion_le
      _ ≤ ∑ _b ∈ T20.blkIdx K, (4 : ℝ) :=
          Finset.sum_le_sum fun b _ => by exact_mod_cast card_shortJ_le K b
      _ = 4 * (T20.blkIdx K).card := by rw [Finset.sum_const, nsmul_eq_mul]; ring
      _ ≤ 4 * (9 * 4 ^ K) := by gcongr; exact card_blkIdx_le K
      _ ≤ (36 + 3 * ξ) * 4 ^ K := by nlinarith [pow_pos (by norm_num : (0 : ℝ) < 4) K]
  have hφK := isPhiVersion_phiMN hW (Nat.zero_le K)
  have hYeq : ∀ᵐ ω ∂P, ∀ x, Y x ω = phiMN W P 0 K x ω := by
    refine T20C.ae_forall_eq_of_cont (fun ω => (hYc ω).continuous) hφK.cont fun x => ?_
    have e : phi W ((2 : ℝ)⁻¹ ^ K) ((2 : ℝ)⁻¹ ^ 0) x = phi W ((2 : ℝ) ^ K)⁻¹ 1 x := by
      rw [inv_pow, pow_zero]
    exact (hY x).trans (by rw [← e]; exact (hφK.ae_eq x).symm)
  filter_upwards [ae_XAB_shift_ne_top hW Q cBig 5 5, ae_phiMN_add hW hKn, hYeq]
    with ω hfin hadd hYω
  have hK2 : 2 ≤ K := hK
  have hq := h_le_quarter hK2
  have hp := h_pos K
  set X := Xbig Q W P ω
  set O := Obig K Y ω
  set m := minShort ξ W P K n J' hJ' ω
  have hX0 : 0 ≤ X := ENNReal.toReal_nonneg
  have hO0 : 0 ≤ O := Obig_nonneg K Y ω
  have hm0 : 0 ≤ m := Finset.le_inf' _ _ fun j _ => ENNReal.toReal_nonneg
  set E : ℤ × ℤ → ℝ := fun b => Real.exp (ξ * psiMN Q W P 0 K (T20.dyCenter K b) ω) *
    Real.exp (-(ξ * (2 * X + 3 * O)))
  have hγadm := hγ.adm n ω
  -- the pieces
  have hpiece : ∀ b ∈ T20.coarseBlocks K (γ n ω), ∃ a c, Icc a c ⊆ Icc (0 : ℝ) 1 ∧
      (∀ r ∈ Icc a c, γ n ω r ∈ hatBox K b) ∧ ENNReal.ofReal (E b * m) ≤
        ∫⁻ r in Icc a c, lenDens ξ (fun x => psiMN Q W P 0 n x ω) (γ n ω) r := by
    intro b hb
    have hbI : b ∈ T20.blkIdx K := (Finset.mem_filter.1 hb).1
    obtain ⟨c1, c2, c3, c4⟩ := center_near hK2 hbI
    have hcB : T20.dyCenter K b ∈ bigBox := by
      simp only [bigBox, Complex.mem_reProdIm, mem_Icc]
      exact ⟨⟨by nlinarith, by nlinarith⟩, by nlinarith, by nlinarith⟩
    refine piece_lower hK2 hγadm hb (by positivity) (fun x hx hxb => ?_) fun j hj =>
      Finset.inf'_le _ (Finset.mem_biUnion.2 ⟨b, hbI, hj⟩)
    have hxB : x ∈ bigBox := by
      simp only [MarkedRect.toSet, rectAB, Complex.mem_reProdIm, mem_Icc, zero_add] at hx
      simp only [bigBox, Complex.mem_reProdIm, mem_Icc]
      exact ⟨⟨by linarith [hx.1.1], by linarith [hx.1.2]⟩, by linarith [hx.2.1],
        by linarith [hx.2.2]⟩
    have h1 := abs_le.1 (abs_sub_le_Xbig Q hfin n hxB)
    have h2 := abs_le.1 (abs_sub_le_Xbig Q hfin K hcB)
    have h3 := abs_le.1 (osc_hatBox_le hK2 (hYc ω) hbI hxb)
    rw [hYω, hYω] at h3
    have h4 := hadd x
    simp only [E]
    rw [← Real.exp_add, ← Real.exp_add]
    refine Real.exp_le_exp.2 ?_
    have : psiMN Q W P 0 K (T20.dyCenter K b) ω - 2 * X - 3 * O + phiMN W P K n x ω ≤
        psiMN Q W P 0 n x ω := by
      linarith [h1.1, h1.2, h2.1, h2.2, h3.1, h3.2]
    nlinarith
  have hsum := sum_pieces_le (K := K) (γ := γ n ω) (T20.coarseBlocks K (γ n ω))
    (lenDens ξ (fun x => psiMN Q W P 0 n x ω) (γ n ω)) (fun b => ENNReal.ofReal (E b * m)) hpiece
  rw [← lfppLen_eq] at hsum
  have hψc := (isPsiVersion_psiMN (Q := Q) hW (Nat.zero_le n)).cont ω
  have hfinL : rectLen ξ (fun x => psiMN Q W P 0 n x ω) (rectAB 1 1) ≠ ⊤ :=
    rectLen_ne_top _ (by norm_num [rectAB]) (by norm_num [rectAB]) hψc
  have hbound : ∑ b ∈ T20.coarseBlocks K (γ n ω), ENNReal.ofReal (E b * m) ≤
      ENNReal.ofReal (16 * (1 + η)) * rectLen ξ (fun x => psiMN Q W P 0 n x ω) (rectAB 1 1) := by
    refine hsum.trans ?_
    rw [ENNReal.ofReal_mul (by norm_num), mul_assoc]
    gcongr
    · norm_num
    · exact hγ.near n ω
  have hreal := ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hfinL) hbound
  rw [ENNReal.toReal_sum (fun b _ => ENNReal.ofReal_ne_top), ENNReal.toReal_mul,
    ENNReal.toReal_ofReal (by positivity)] at hreal
  have hL0 : 0 ≤ lenPsi ξ Q W P n ω := ENNReal.toReal_nonneg
  have hKe : (1 : ℝ) ≤ (K : ℝ) ^ Q.ε₀ :=
    Real.one_le_rpow (by exact_mod_cast (by omega : 1 ≤ K)) Q.ε₀_pos.le
  have hfac : Real.exp (-((36 + 3 * ξ) * X)) * Real.exp (-((36 + 3 * ξ) * (K : ℝ) ^ Q.ε₀ * O)) ≤
      Real.exp (-(ξ * (2 * X + 3 * O))) := by
    rw [← Real.exp_add]
    refine Real.exp_le_exp.2 ?_
    have : 3 * ξ * O ≤ (36 + 3 * ξ) * (K : ℝ) ^ Q.ε₀ * O := by
      have : 3 * ξ ≤ (36 + 3 * ξ) * (K : ℝ) ^ Q.ε₀ := by nlinarith
      exact mul_le_mul_of_nonneg_right this hO0
    nlinarith
  calc Real.exp (-((36 + 3 * ξ) * X)) * Real.exp (-((36 + 3 * ξ) * (K : ℝ) ^ Q.ε₀ * O)) * m *
        ∑ P' ∈ T20.coarseBlocks K (γ n ω), Real.exp (ξ * psiMN Q W P 0 K (T20.dyCenter K P') ω)
      = ∑ b ∈ T20.coarseBlocks K (γ n ω), Real.exp (-((36 + 3 * ξ) * X)) *
          Real.exp (-((36 + 3 * ξ) * (K : ℝ) ^ Q.ε₀ * O)) * m *
          Real.exp (ξ * psiMN Q W P 0 K (T20.dyCenter K b) ω) := by rw [Finset.mul_sum]
    _ ≤ ∑ b ∈ T20.coarseBlocks K (γ n ω), (E b * m) := by
        refine Finset.sum_le_sum fun b _ => ?_
        simp only [E]
        have := mul_le_mul_of_nonneg_right hfac
          (mul_nonneg hm0 (Real.exp_pos (ξ * psiMN Q W P 0 K (T20.dyCenter K b) ω)).le)
        nlinarith [this]
    _ = ∑ b ∈ T20.coarseBlocks K (γ n ω), (ENNReal.ofReal (E b * m)).toReal := by
        refine Finset.sum_congr rfl fun b _ => ?_
        rw [ENNReal.toReal_ofReal (by positivity)]
    _ ≤ 16 * (1 + η) * lenPsi ξ Q W P n ω := hreal
    _ ≤ (36 + 3 * ξ) * lenPsi ξ Q W P n ω := by
        refine mul_le_mul_of_nonneg_right ?_ hL0; nlinarith

end DDDF
end LQGMetric
