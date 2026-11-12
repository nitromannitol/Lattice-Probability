/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DDDF.T20DNum at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DDDF.T20DField

/-!
# DDDF Theorem 20, Step 4: the numerator bound (5.65)+(5.66) from the circuit gluing
(task P2-DDDFT20d)

DDDF = arXiv:1904.08021, `tightness.tex` l. 1103–1123. `T20Step4Num` is reduced to the geometric
gluing statement `T20CircuitGlue` (DDDF l. 1103–1105 and the gluing of `O(K^{ε₀})` long
crossings, l. 1117–1119, with D-DDDF-22 for blocks at `∂[0,1]²`): the resampled length is at most
`(1+η) L_n(ψ) + Σ_{j ∈ R} L^{(n)}(R_j, ψ)` for at most `C(K+1)^d` long rectangles `R_j` of the
grid family `longFam K`, within distance `C K^{ε₀} 2^{-K}` of a block `P'` of `π^K`.

Proved here (DDDF l. 1106–1123):
* `T20D.incr_le_of`: `(log L^b − log L)_+ ≤ (L^b − L)_+/L` (`log x ≤ x − 1`, DDDF (5.65));
* `T20D.mrectLen_le_of`: `L^{(n)}(R, ψ) ≤ e^{2ξX} e^{ξψ_{0,K}(P')} e^{ξ C K^{ε₀} O} L^{(K,n)}(R, φ)`
  (the display after (5.65));
* `t20Step4Num_of_glue`: `T20Step4Num` from `T20CircuitGlue`.
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

/-- the long rectangle `u 2^{-K} R_{3,1} + c` -/
def RL (K : ℕ) (j : Circle × ℂ) : Set ℂ := T20B.mot K j.1 j.2 '' (rectAB 3 1).toSet

open Classical in
/-- the grid family of long rectangles: horizontal and vertical, corners in `2^{-K} ℤ²` within
`[-2,3]²` -/
def longFam (K : ℕ) : Finset (Circle × ℂ) :=
  ({1, circI} : Finset Circle) ×ˢ
    ((Finset.Icc (-2 * 2 ^ K : ℤ) (3 * 2 ^ K) ×ˢ Finset.Icc (-2 * 2 ^ K : ℤ) (3 * 2 ^ K)).image
      fun p => (⟨(p.1 : ℝ) * (2 : ℝ)⁻¹ ^ K, (p.2 : ℝ) * (2 : ℝ)⁻¹ ^ K⟩ : ℂ))

lemma longFam_nonempty (K : ℕ) : (longFam K).Nonempty := by
  classical
  refine Finset.Nonempty.product ⟨1, by simp⟩ (Finset.Nonempty.image ⟨(0, 0), ?_⟩ _)
  simp only [Finset.mem_product, Finset.mem_Icc]
  have : (0 : ℤ) < 2 ^ K := by positivity
  omega

lemma card_longFam_le (K : ℕ) : ((longFam K).card : ℝ) ≤ 72 * 4 ^ K := by
  classical
  unfold longFam
  have h1 : ({1, circI} : Finset Circle).card ≤ 2 := Finset.card_le_two
  have h2 := Finset.card_image_le (s := Finset.Icc (-2 * 2 ^ K : ℤ) (3 * 2 ^ K) ×ˢ
    Finset.Icc (-2 * 2 ^ K : ℤ) (3 * 2 ^ K))
    (f := fun p => (⟨(p.1 : ℝ) * (2 : ℝ)⁻¹ ^ K, (p.2 : ℝ) * (2 : ℝ)⁻¹ ^ K⟩ : ℂ))
  rw [Finset.card_product, Int.card_Icc] at h2
  have e : (3 * 2 ^ K + 1 - -2 * (2 : ℤ) ^ K) = ((5 * 2 ^ K + 1 : ℕ) : ℤ) := by push_cast; ring
  rw [e, Int.toNat_natCast] at h2
  rw [Finset.card_product]
  refine (Nat.cast_le.2 (Nat.mul_le_mul h1 h2)).trans ?_
  push_cast
  have h4 : (4 : ℝ) ^ K = 2 ^ K * 2 ^ K := by rw [← mul_pow]; norm_num
  have h5 : (1 : ℝ) ≤ 2 ^ K := one_le_pow₀ (by norm_num)
  rw [h4]; nlinarith

lemma le_maxLong {ξ : ℝ} {K n : ℕ} {J : Finset (Circle × ℂ)} {hJ : J.Nonempty} {ω : Ω}
    {j : Circle × ℂ} (hj : j ∈ J) :
    T20B.mrectLen ξ (fun x => phiMN W P K n x ω) K j.1 j.2 3 1 ≤ T20C.maxLong ξ W P K n J hJ ω := by
  set g : Circle × ℂ → ℝ := fun j => T20B.mrectLen ξ (fun x => phiMN W P K n x ω) K j.1 j.2 3 1
  exact Finset.le_sup' g hj

/-- the motion of a segment is a segment -/
lemma mot_seg (K : ℕ) (u : Circle) (c : ℂ) (R : MarkedRect) :
    (fun t => T20B.mot K u c (R.seg t)) = segPath (T20B.mot K u c R.p₁) (T20B.mot K u c R.p₂) := by
  funext t
  simp only [T20B.mot, MarkedRect.seg, segPath, Complex.real_smul]
  ring

/-- crossings of moved rectangles are finite for continuous fields -/
lemma crossLenIn_mot_ne_top {ξ : ℝ} (K : ℕ) (u : Circle) (c : ℂ) {a b : ℝ} (ha : 0 ≤ a)
    (hb : 0 ≤ b) {f : ℂ → ℝ} (hf : Continuous f) :
    crossLenIn ξ f (T20B.mot K u c '' (rectAB a b).toSet) (T20B.mot K u c '' (rectAB a b).side₁)
      (T20B.mot K u c '' (rectAB a b).side₂) ≠ ⊤ := by
  obtain ⟨z, hz, w, hw, hP, hU⟩ := (rectAB a b).admPath_seg ha hb
  have e1 : (rectAB a b).p₁ = z := (rectAB a b).isPiecewiseC1Path_seg.source.symm.trans hP.source
  have e2 : (rectAB a b).p₂ = w := (rectAB a b).isPiecewiseC1Path_seg.target.symm.trans hP.target
  have hadm : AdmPath (T20B.mot K u c '' (rectAB a b).toSet) (T20B.mot K u c '' (rectAB a b).side₁)
      (T20B.mot K u c '' (rectAB a b).side₂) (fun t => T20B.mot K u c ((rectAB a b).seg t)) := by
    rw [mot_seg]
    refine ⟨_, ⟨_, ?_, rfl⟩, _, ⟨_, ?_, rfl⟩, isPiecewiseC1Path_segPath _ _, fun t ht => ?_⟩
    · rw [e1]; exact hz
    · rw [e2]; exact hw
    · rw [← mot_seg]; exact ⟨_, hU t ht, rfl⟩
  obtain ⟨M, hM⟩ := ((isCompact_closedBall (T20B.mot K u c (rectAB a b).p₁)
    ‖T20B.mot K u c (rectAB a b).p₂ - T20B.mot K u c (rectAB a b).p₁‖).image_of_continuousOn
    (Real.continuous_exp.comp (continuous_const.mul hf)).continuousOn).isBounded.bddAbove
  have hseg := lfppLen_segPath_le (ξ := ξ) (φ := f) (T20B.mot K u c (rectAB a b).p₁)
    (T20B.mot K u c (rectAB a b).p₂) (B := M) fun x hx => hM ⟨x, hx, rfl⟩
  rw [← mot_seg] at hseg
  exact ne_top_of_le_ne_top ENNReal.ofReal_ne_top ((crossLenIn_le_lfppLen hadm).trans hseg)

/-- one-sided comparison of crossing lengths: `ξ f ≤ ξ g + a` on `U` gives `L(f) ≤ e^a L(g)` -/
lemma crossLenIn_le_of_le_add {ξ : ℝ} {f g : ℂ → ℝ} {U A B : Set ℂ} {a : ℝ}
    (h : ∀ x ∈ U, ξ * f x ≤ ξ * g x + a) :
    crossLenIn ξ f U A B ≤ ENNReal.ofReal (Real.exp a) * crossLenIn ξ g U A B := by
  have h0 : ENNReal.ofReal (Real.exp a) ≠ 0 := (ENNReal.ofReal_pos.2 (Real.exp_pos _)).ne'
  rw [crossLenIn_eq_biInf, crossLenIn_eq_biInf, ENNReal.mul_iInf_of_ne h0 ENNReal.ofReal_ne_top]
  refine iInf_mono fun P => ?_
  rw [ENNReal.mul_iInf_of_ne h0 ENNReal.ofReal_ne_top]
  refine iInf_mono fun hP => ?_
  obtain ⟨z, -, w, -, -, hU⟩ := hP
  unfold lfppLen
  rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  refine setLIntegral_mono' measurableSet_Icc fun t ht => ?_
  rw [← ENNReal.ofReal_mul (Real.exp_pos _).le, ← mul_assoc, ← Real.exp_add]
  refine ENNReal.ofReal_le_ofReal
    (mul_le_mul_of_nonneg_right (Real.exp_le_exp.2 ?_) (norm_nonneg _))
  linarith [h _ (hU t ht)]

/-- `L^{(n)}(R, ψ) ≤ e^a L^{(K,n)}(R, φ)` for a long rectangle `R` when `ξψ ≤ ξφ + a` on `R` -/
lemma mrectLen_le_of {ξ : ℝ} {K : ℕ} {j : Circle × ℂ} {f g : ℂ → ℝ} (hg : Continuous g) {a : ℝ}
    (h : ∀ x ∈ RL K j, ξ * f x ≤ ξ * g x + a) :
    T20B.mrectLen ξ f K j.1 j.2 3 1 ≤ Real.exp a * T20B.mrectLen ξ g K j.1 j.2 3 1 := by
  have h1 := crossLenIn_le_of_le_add (A := T20B.mot K j.1 j.2 '' (rectAB 3 1).side₁)
    (B := T20B.mot K j.1 j.2 '' (rectAB 3 1).side₂) h
  have hfin := crossLenIn_mot_ne_top (ξ := ξ) K j.1 j.2 (by norm_num : (0 : ℝ) ≤ 3)
    (by norm_num : (0 : ℝ) ≤ 1) hg
  have := ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hfin) h1
  rwa [ENNReal.toReal_mul, ENNReal.toReal_ofReal (Real.exp_pos _).le] at this

/-- **(5.65)**: `(log L^b − log L)_+ ≤ η + S/L` when `L^b ≤ (1+η) L + S` -/
lemma incr_le_of {ξ : ℝ} {f g : ℂ → ℝ} (hf : Continuous f) (hg : Continuous g) {η S : ℝ}
    (hη : 0 ≤ η) (hS : 0 ≤ S)
    (h : (rectLen ξ g (rectAB 1 1)).toReal ≤ (1 + η) * (rectLen ξ f (rectAB 1 1)).toReal + S) :
    max (L23.logLen ξ g - L23.logLen ξ f) 0 ≤ η + S / (rectLen ξ f (rectAB 1 1)).toReal := by
  have hpos : ∀ {k : ℂ → ℝ}, Continuous k → 0 < (rectLen ξ k (rectAB 1 1)).toReal := fun hk =>
    ENNReal.toReal_pos (rectLen_pos _ (by norm_num [MarkedRect.crossWidth, rectAB]) hk).ne'
      (rectLen_ne_top _ (by norm_num [rectAB]) (by norm_num [rectAB]) hk)
  have ha := hpos hg
  have hL := hpos hf
  refine max_le ?_ (by positivity)
  unfold L23.logLen
  rw [← Real.log_div ha.ne' hL.ne']
  refine (Real.log_le_sub_one_of_pos (div_pos ha hL)).trans ?_
  rw [div_sub_one hL.ne', div_le_iff₀ hL]
  rw [add_mul, div_mul_cancel₀ _ hL.ne']
  linarith

end T20D

open T20C T20D in
/-- **The circuit gluing** (DDDF l. 1103–1105 and l. 1117–1119; boundary blocks as in D-DDDF-22):
for a visited block `b` there are a block `P' ∈ π^K` at index distance `≤ C(K+1)` and at most
`C(K+1)^d` long rectangles of `longFam K`, inside `[-2,3]²` and within `C K^{ε₀} 2^{-K}` of the
centre of `P'`, whose `ψ_{0,n}`-crossings glued to the near-geodesic bound the resampled length:
`L^b_n ≤ (1+η) L_n(ψ) + Σ_j L^{(n)}(R_j, ψ)`. Open. -/
def T20CircuitGlue (ξ : ℝ) (Q : PsiParams) (W : WNSpace → Ω → ℝ) (P : Measure Ω) : Prop :=
  ∃ C₁ : ℝ, 0 < C₁ ∧ ∃ d₁ : ℕ, ∃ K₀ : ℕ, ∀ K : ℕ, K₀ ≤ K → ∀ n : ℕ, K ≤ n → ∃ s : ℝ,
    (∀ t ∈ Icc (((2 : ℝ)⁻¹ ^ n) ^ 2) (((2 : ℝ)⁻¹ ^ K) ^ 2), Q.sigma t ≤ s) ∧
    ∀ η : ℝ, 0 < η → η ≤ 1 → ∀ γ : ℕ → Ω → ℝ → ℂ, T20.IsNearGeodSel ξ Q W P η γ →
      ∀ᵐ z ∂(P.prod P), ∀ b ∈ T20B.nearIdx K, z ∈ visSet γ n K b s →
        ∃ P' ∈ T20.coarseBlocks K (γ n z.1),
          |((b.1 - P'.1 : ℤ) : ℝ)| ≤ C₁ * ((K : ℝ) + 1) ∧
          |((b.2 - P'.2 : ℤ) : ℝ)| ≤ C₁ * ((K : ℝ) + 1) ∧
          ∃ R : Finset (Circle × ℂ), R ⊆ longFam K ∧ (R.card : ℝ) ≤ C₁ * ((K : ℝ) + 1) ^ d₁ ∧
            (∀ j ∈ R, ∀ x ∈ RL K j, x ∈ bigBox ∧
              ‖x - T20.dyCenter K P'‖ ≤ C₁ * (K : ℝ) ^ Q.ε₀ * (2 : ℝ)⁻¹ ^ K) ∧
            (rectLen ξ (fun x => psiMN Q W P 0 n x z.1 - T20B.blkKn Q W P K n b x z.1 +
                T20B.blkKn Q W P K n b x z.2) (rectAB 1 1)).toReal ≤
              (1 + η) * lenPsi ξ Q W P n z.1 +
                ∑ j ∈ R, T20B.mrectLen ξ (fun x => psiMN Q W P 0 n x z.1) K j.1 j.2 3 1

open T20C T20D in
/-- **DDDF (5.65)+(5.66)** from the circuit gluing (`tightness.tex` l. 1106–1123): each glued
long crossing is compared with `φ_{K,n}` (`|φ − ψ| ≤ X`, `φ_{0,n} = φ_{0,K} + φ_{K,n}`, the
oscillation of `φ_{0,K}` over distance `C K^{ε₀} 2^{-K}`), and `log x ≤ x − 1`. -/
theorem t20Step4Num_of_glue (hW : IsWhiteNoise P W) (Q : PsiParams) {ξ : ℝ} (hξ : 0 < ξ)
    (hG : T20CircuitGlue ξ Q W P) : T20Step4Num ξ Q W P := by
  classical
  have := hW.isProbabilityMeasure
  obtain ⟨C₁, hC₁, d₁, K₀, hG⟩ := hG
  set C₃ : ℝ := 72 + C₁ + 2 * ξ + ξ * C₁ with hC₃
  have hC₃0 : 0 < C₃ := by positivity
  refine ⟨C₃, hC₃0, d₁, max K₀ 2, fun K hK n hKn => ?_⟩
  obtain ⟨s, hσ, hG'⟩ := hG K (le_of_max_le_left hK) n hKn
  have hK2 : 2 ≤ K := le_of_max_le_right hK
  refine ⟨s, hσ, longFam K, longFam_nonempty K, ?_, fun η hη hη1 γ hγ Y hY hYc => ?_⟩
  · refine (card_longFam_le K).trans ?_
    have h4 : (0 : ℝ) ≤ 4 ^ K := by positivity
    have h72 : (72 : ℝ) ≤ C₃ := by
      simp only [hC₃]; nlinarith [mul_pos hξ hC₁]
    exact mul_le_mul_of_nonneg_right h72 h4
  have hφK := isPhiVersion_phiMN hW (Nat.zero_le K)
  have hφKn := isPhiVersion_phiMN hW hKn
  have hYeq : ∀ᵐ ω ∂P, ∀ x, Y x ω = phiMN W P 0 K x ω := by
    refine T20C.ae_forall_eq_of_cont (fun ω => (hYc ω).continuous) hφK.cont fun x => ?_
    have e : phi W ((2 : ℝ)⁻¹ ^ K) ((2 : ℝ)⁻¹ ^ 0) x = phi W ((2 : ℝ) ^ K)⁻¹ 1 x := by
      rw [inv_pow, pow_zero]
    exact (hY x).trans (by rw [← e]; exact (hφK.ae_eq x).symm)
  have hω : ∀ᵐ ω ∂P, (XAB (fun n y => phiMN W P 0 n (y + cBig) ω)
      (fun n y => psiMN Q W P 0 n (y + cBig) ω) 5 5 ≠ ⊤) ∧
      (∀ x : ℂ, phiMN W P 0 n x ω = phiMN W P 0 K x ω + phiMN W P K n x ω) ∧
      ∀ x, Y x ω = phiMN W P 0 K x ω := by
    filter_upwards [ae_XAB_shift_ne_top hW Q cBig 5 5, ae_phiMN_add hW hKn, hYeq]
      with ω h1 h2 h3
    exact ⟨h1, h2, h3⟩
  have hlift := (measurePreserving_fst (μ := P) (ν := P)).quasiMeasurePreserving.ae hω
  filter_upwards [hlift, hG' η hη hη1 γ hγ] with z hz hzG b hb hvis
  obtain ⟨hfin, hadd, hYω⟩ := hz
  obtain ⟨P', hP', hd1, hd2, R, hRJ, hRc, hRgeo, hlen⟩ := hzG b hb hvis
  have hCC : C₁ * ((K : ℝ) + 1) ≤ C₃ * ((K : ℝ) + 1) :=
    mul_le_mul_of_nonneg_right (by nlinarith) (by positivity)
  refine ⟨P', hP', hd1.trans hCC, hd2.trans hCC, ?_⟩
  set X := Xbig Q W P z.1
  set O := Obig K Y z.1
  set c := T20.dyCenter K P'
  let MM := maxLong ξ W P K n (longFam K) (longFam_nonempty K) z.1
  have hX0 : 0 ≤ X := ENNReal.toReal_nonneg
  have hO0 : 0 ≤ O := Obig_nonneg K Y z.1
  have hM0 : 0 ≤ MM := maxLong_nonneg ξ K n _ _ z.1
  have hKe : 0 ≤ (K : ℝ) ^ Q.ε₀ := by positivity
  have hp := h_pos K
  have hq := h_le_quarter hK2
  have hcB : c ∈ bigBox := by
    obtain ⟨c1, c2, c3, c4⟩ := center_near hK2 (Finset.mem_filter.1 hP').1
    simp only [bigBox, Complex.mem_reProdIm, mem_Icc]
    exact ⟨⟨by nlinarith, by nlinarith⟩, by nlinarith, by nlinarith⟩
  set A : ℝ := ξ * psiMN Q W P 0 K c z.1 + 2 * ξ * X + ξ * (C₁ * (K : ℝ) ^ Q.ε₀ * O)
  have hj : ∀ j ∈ R, T20B.mrectLen ξ (fun x => psiMN Q W P 0 n x z.1) K j.1 j.2 3 1 ≤
      Real.exp A * MM := by
    intro j hjR
    have hMj : T20B.mrectLen ξ (fun x => phiMN W P K n x z.1) K j.1 j.2 3 1 ≤ MM := by
      exact le_maxLong (P := P) (W := W) (hRJ hjR)
    refine (mrectLen_le_of (K := K) (j := j) (f := fun x => psiMN Q W P 0 n x z.1)
      (g := fun x => phiMN W P K n x z.1) (a := A) (hφKn.cont z.1) fun x hx => ?_).trans
      (mul_le_mul_of_nonneg_left hMj (Real.exp_pos _).le)
    obtain ⟨hxB, hxc⟩ := hRgeo j hjR x hx
    have h1 := abs_le.1 (abs_sub_le_Xbig Q hfin n hxB)
    have h2 := abs_le.1 (abs_sub_le_Xbig Q hfin K hcB)
    have h3 := osc_bigBox_le K (hYc z.1) hxB hcB
    rw [hYω, hYω] at h3
    have h3' : (2 : ℝ) ^ K * O * ‖x - c‖ ≤ C₁ * (K : ℝ) ^ Q.ε₀ * O := by
      have e : (2 : ℝ) ^ K * (2 : ℝ)⁻¹ ^ K = 1 := by rw [inv_pow, mul_inv_cancel₀ (by positivity)]
      calc (2 : ℝ) ^ K * O * ‖x - c‖ ≤ (2 : ℝ) ^ K * O * (C₁ * (K : ℝ) ^ Q.ε₀ * (2 : ℝ)⁻¹ ^ K) :=
            mul_le_mul_of_nonneg_left hxc (by positivity)
        _ = C₁ * (K : ℝ) ^ Q.ε₀ * O * ((2 : ℝ) ^ K * (2 : ℝ)⁻¹ ^ K) := by ring
        _ = _ := by rw [e, mul_one]
    have h4 := hadd x
    have h5 := abs_le.1 (h3.trans h3')
    have : psiMN Q W P 0 n x z.1 ≤
        phiMN W P K n x z.1 + (psiMN Q W P 0 K c z.1 + 2 * X + C₁ * (K : ℝ) ^ Q.ε₀ * O) := by
      linarith [h1.1, h1.2, h2.1, h2.2, h5.1, h5.2]
    have := mul_le_mul_of_nonneg_left this hξ.le
    simp only [A]; nlinarith
  have hS0 : 0 ≤ ∑ j ∈ R, T20B.mrectLen ξ (fun x => psiMN Q W P 0 n x z.1) K j.1 j.2 3 1 :=
    Finset.sum_nonneg fun j _ => ENNReal.toReal_nonneg
  have hψc := (isPsiVersion_psiMN (Q := Q) hW (Nat.zero_le n)).cont z.1
  have hB := T20B.blkKn_spec hW Q hKn b
  have hinc := incr_le_of (ξ := ξ) hψc (((hψc.sub (hB.1 z.1)).add (hB.1 z.2))) hη.le hS0 hlen
  have hL0 : 0 ≤ lenPsi ξ Q W P n z.1 := ENNReal.toReal_nonneg
  have hsum : ∑ j ∈ R, T20B.mrectLen ξ (fun x => psiMN Q W P 0 n x z.1) K j.1 j.2 3 1 ≤
      C₃ * ((K : ℝ) + 1) ^ d₁ * Real.exp (C₃ * X) * Real.exp (C₃ * (K : ℝ) ^ Q.ε₀ * O) *
        Real.exp (ξ * psiMN Q W P 0 K c z.1) * MM := by
    have h1 := Finset.sum_le_card_nsmul R _ _ hj
    rw [nsmul_eq_mul] at h1
    have hA : Real.exp A ≤ Real.exp (C₃ * X) * Real.exp (C₃ * (K : ℝ) ^ Q.ε₀ * O) *
        Real.exp (ξ * psiMN Q W P 0 K c z.1) := by
      rw [← Real.exp_add, ← Real.exp_add]
      refine Real.exp_le_exp.2 ?_
      have a1 : 2 * ξ * X ≤ C₃ * X := mul_le_mul_of_nonneg_right (by nlinarith) hX0
      have a2 : ξ * (C₁ * (K : ℝ) ^ Q.ε₀ * O) ≤ C₃ * (K : ℝ) ^ Q.ε₀ * O := by
        have : ξ * C₁ ≤ C₃ := by nlinarith
        have := mul_le_mul_of_nonneg_right this (mul_nonneg hKe hO0)
        nlinarith
      simp only [A]; linarith
    have hEM : 0 ≤ Real.exp A * MM := mul_nonneg (Real.exp_pos _).le hM0
    have hk1 : (0 : ℝ) ≤ ((K : ℝ) + 1) ^ d₁ := by positivity
    calc _ ≤ (R.card : ℝ) * (Real.exp A * MM) := h1
      _ ≤ C₃ * ((K : ℝ) + 1) ^ d₁ * (Real.exp A * MM) := by
          refine mul_le_mul_of_nonneg_right (hRc.trans ?_) hEM
          exact mul_le_mul_of_nonneg_right (by nlinarith) hk1
      _ ≤ C₃ * ((K : ℝ) + 1) ^ d₁ * ((Real.exp (C₃ * X) * Real.exp (C₃ * (K : ℝ) ^ Q.ε₀ * O) *
            Real.exp (ξ * psiMN Q W P 0 K c z.1)) * MM) := by
          gcongr
      _ = _ := by ring
  refine hinc.trans ?_
  unfold lenPsi
  gcongr

end DDDF
end LQGMetric
