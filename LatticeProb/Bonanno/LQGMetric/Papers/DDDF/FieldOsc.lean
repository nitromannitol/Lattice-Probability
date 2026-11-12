/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DDDF.FieldOsc at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DDDF.FieldGrad
import Mathlib.Analysis.Complex.OperatorNorm
import Mathlib.Analysis.Complex.ExponentialBounds

/-!
# DDDF Prop. 3, (2.16): the oscillation tail of `φ_{0,n}` (task P2-DDDFFIELD, WP-94)

DDDF (arXiv:1904.08021, `tightness.tex` l. 329–345), (2.16): there are `C, σ² > 0` with
`P(2^{-n} ‖∇φ_{0,n}‖_{[0,1]²} ≥ x) ≤ C 4^n e^{−x²/(2σ²)}` for all `x > 0`, `n ≥ 0`, where
`φ_{0,n} = φ_{2^{-n},1}` (l. 293) and `‖f‖_A = sup_A |f|` (l. 320). DDDF cite DF
(arXiv:1809.02607) between (10.3) and (10.4), l. 1828–1840: Fernique for the gradient on a
square, scaling, union bound over the `4^n` dyadic squares of side `2^{-n}`.

`prop3_tail` is stated for **every** `C¹` modification `Y` of `φ_{2^{-n},1}` (they all have
a.s. the same gradient, `ae_fderiv_eq_of_modification`); `‖∇φ‖` is the operator norm of the
Fréchet derivative.

Route (deviation, see the report): instead of DF's scaling of `∇φ_0` scale by scale, the
Fernique step is applied directly to `2^{-n} ∂_j φ_{2^{-n},1}` on each square of side `2^{-n}`,
with the scale-correct bounds `Var(2^{-n} ∂_j φ) ≤ 4` and
`E(2^{-n}(∂_jφ(u) − ∂_jφ(v)))² ≤ C |u − v| 2^n` on such a square (`WhiteNoiseC1Var`); then the
union bound over the `2 · 4^n` pairs (square, direction). Same ingredients, no sum over scales.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped RealInnerProductSpace

namespace LQGMetric
namespace DDDF

open WhiteNoise SupTail

/-- The dyadic covering index: for `r ∈ [0,1]` there is `i < 2^n` with
`r ∈ [i 2^{-n}, (i+1) 2^{-n}]`. -/
lemma exists_dyadic_index (n : ℕ) {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r ≤ 1) :
    ∃ i : Fin (2 ^ n), ((2 : ℝ) ^ n)⁻¹ * i ≤ r ∧ r ≤ ((2 : ℝ) ^ n)⁻¹ * i + ((2 : ℝ) ^ n)⁻¹ := by
  have hN : (0 : ℝ) < 2 ^ n := by positivity
  set m := ⌊r * 2 ^ n⌋₊ with hm
  by_cases hmN : m < 2 ^ n
  · refine ⟨⟨m, hmN⟩, ?_, ?_⟩
    · simp only
      rw [inv_mul_le_iff₀ hN, mul_comm]
      exact Nat.floor_le (by positivity)
    · simp only
      have := Nat.lt_floor_add_one (r * 2 ^ n)
      rw [← hm] at this
      rw [← mul_add_one, le_inv_mul_iff₀ hN, mul_comm]
      exact this.le
  · have h1 : (2 : ℝ) ^ n ≤ m := by exact_mod_cast not_lt.1 hmN
    have h2 : (m : ℝ) ≤ r * 2 ^ n := Nat.floor_le (by positivity)
    have hr : r = 1 := le_antisymm hr1 (by nlinarith)
    have hpos : 0 < 2 ^ n := Nat.pos_of_ne_zero (by positivity)
    refine ⟨⟨2 ^ n - 1, Nat.sub_lt hpos one_pos⟩, ?_, ?_⟩ <;> simp only <;>
      rw [Nat.cast_sub (Nat.one_le_iff_ne_zero.2 hpos.ne'), Nat.cast_pow, Nat.cast_ofNat,
        Nat.cast_one, hr, mul_sub, inv_mul_cancel₀ hN.ne']
    · have : 0 ≤ ((2 : ℝ) ^ n)⁻¹ := by positivity
      linarith
    · linarith

/-- The dyadic squares of side `2^{-n}` cover `[0,1]²`. -/
lemma exists_dyadic_square (n : ℕ) {z : ℂ} (hz : z ∈ ferniqueBox 0 1) :
    ∃ i k : Fin (2 ^ n), z ∈ ferniqueBox ⟨((2 : ℝ) ^ n)⁻¹ * i, ((2 : ℝ) ^ n)⁻¹ * k⟩
      ((2 : ℝ) ^ n)⁻¹ := by
  obtain ⟨⟨h1, h2⟩, ⟨h3, h4⟩⟩ := hz
  simp only [Complex.zero_re, Complex.zero_im, zero_add] at h1 h2 h3 h4
  obtain ⟨i, hi1, hi2⟩ := exists_dyadic_index n h1 h2
  obtain ⟨k, hk1, hk2⟩ := exists_dyadic_index n h3 h4
  exact ⟨i, k, ⟨hi1, hi2⟩, ⟨hk1, hk2⟩⟩

lemma sq_norm_sub_le_of_mem_box {x₀ : ℂ} {b : ℝ} {u v : ℂ} (hu : u ∈ ferniqueBox x₀ b)
    (hv : v ∈ ferniqueBox x₀ b) : ‖u - v‖ ^ 2 ≤ 2 * b ^ 2 := by
  obtain ⟨⟨u1, u2⟩, ⟨u3, u4⟩⟩ := hu
  obtain ⟨⟨v1, v2⟩, ⟨v3, v4⟩⟩ := hv
  rw [Complex.sq_norm, Complex.normSq_apply]
  simp only [Complex.sub_re, Complex.sub_im]
  have h1 : (u.re - v.re) ^ 2 ≤ b ^ 2 := by
    exact sq_le_sq' (by linarith) (by linarith)
  have h2 : (u.im - v.im) ^ 2 ≤ b ^ 2 := by
    exact sq_le_sq' (by linarith) (by linarith)
  nlinarith

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {W : WNSpace → Ω → ℝ}

/-- The constant `κ = 1/80` normalising `2^{-n} ∂_j φ` for DZZ Lemma 2.3. -/
def oscκ : ℝ := 1 / 80

/-- **One square, one direction**: for the gradient `G` of the `C¹` version of `φ_{a,1}`
(`a = 2^{-n}`) and a square `Q` of side `a`,
`P(sup_Q |κ a G_j| ≥ y) ≤ 2 e^{C_F²/(2σ²)} e^{−y²/(4σ²)}` with `σ = 2κ`. -/
lemma tail_grad_square (hW : IsWhiteNoise P W) {a : ℝ} (ha : 0 < a) (ha1 : a ≤ 1)
    {G : ℂ → Ω → ℝ} (hG : IsGaussianProcess G P) (hGc : ∀ ω, Continuous fun x => G x ω)
    {e : ℂ} (he : ‖e‖ ≤ 1) (hGd : ∀ x, (fun ω => G x ω) =ᵐ[P] dphi W a 1 e x 0) (x₀ : ℂ)
    {y : ℝ} (hy : 0 ≤ y) :
    P.real {ω | y ≤ ⨆ z : ferniqueBox x₀ a, |(oscκ * a) • G z ω|} ≤
      2 * Real.exp (ferniqueCF ^ 2 / (2 * (2 * oscκ) ^ 2)) *
        Real.exp (-y ^ 2 / (2 * (2 * (2 * oscκ) ^ 2))) := by
  set c := oscκ * a with hc
  have hc0 : 0 < c := by rw [hc, oscκ]; positivity
  have hX : IsGaussianProcess (fun z ω => c • G z ω) P := hG.smul (fun _ => c)
  have hpi := Real.pi_pos
  refine tail_sup_abs_square (G := fun z ω => c • G z ω) hX (fun z => ?_)
    (fun ω => (hGc ω).const_smul c) ha x₀ (fun u hu v hv => ?_) (fun z => ?_) hy
  · rw [integral_smul, integral_congr_ae (hGd z), integral_dphi hW, smul_zero]
  · have e1 : ∫ ω, (c • G v ω - c • G u ω) ^ 2 ∂P =
        c ^ 2 * (Real.pi * ‖dqKernelL2 a 1 e v 0 - dqKernelL2 a 1 e u 0‖ ^ 2) := by
      rw [← integral_sq_dphi_sub hW a 1 e v u 0 0, ← integral_const_mul]
      refine integral_congr_ae ?_
      filter_upwards [hGd u, hGd v] with ω h1 h2
      simp only [smul_eq_mul]
      rw [h1, h2]; ring
    rw [e1]
    have hk := sq_norm_gradKernel_sub_le ha ha1 le_rfl he v u
    have hd2 := sq_norm_sub_le_of_mem_box hv hu
    have hd : ‖v - u‖ ≤ 3 / 2 * a := by
      have : ‖v - u‖ ^ 2 ≤ (3 / 2 * a) ^ 2 := by nlinarith
      exact (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).1 this
    have hE : Real.exp (‖v - u‖ ^ 2 / a ^ 2) ≤ 8 := by
      have h2 : ‖v - u‖ ^ 2 / a ^ 2 ≤ 2 := by
        rw [div_le_iff₀ (by positivity)]; linarith
      have := Real.exp_one_lt_d9
      calc Real.exp (‖v - u‖ ^ 2 / a ^ 2) ≤ Real.exp 2 := Real.exp_le_exp.2 h2
        _ = Real.exp 1 ^ 2 := by rw [← Real.exp_nat_mul]; norm_num
        _ ≤ 8 := by nlinarith [Real.exp_pos 1]
    rw [norm_sub_rev u v]
    set δ := ‖v - u‖
    have hδ0 : 0 ≤ δ := norm_nonneg _
    calc c ^ 2 * (Real.pi * ‖dqKernelL2 a 1 e v 0 - dqKernelL2 a 1 e u 0‖ ^ 2)
        ≤ c ^ 2 * (Real.pi * (392 / (Real.pi * a ^ 4) * Real.exp (δ ^ 2 / a ^ 2) * δ ^ 2)) := by
          gcongr
      _ ≤ c ^ 2 * (Real.pi * (392 / (Real.pi * a ^ 4) * 8 * (δ * (3 / 2 * a)))) := by
          gcongr
          · rw [sq]; exact mul_le_mul_of_nonneg_left hd hδ0
      _ = oscκ ^ 2 * 4704 * δ / a := by rw [hc]; field_simp; ring
      _ ≤ δ / a := by
          rw [oscκ, mul_div_assoc]
          have : 0 ≤ δ / a := by positivity
          nlinarith
  · rw [show (fun ω => c • G z ω) = c • G z from rfl, variance_smul, variance_congr (hGd z),
      variance_dphi hW]
    have hk := sq_norm_gradKernel_le ha ha1 he z
    calc c ^ 2 * (Real.pi * ‖dqKernelL2 a 1 e z 0‖ ^ 2)
        ≤ c ^ 2 * (Real.pi * (4 / (Real.pi * a ^ 2))) := by gcongr
      _ = (2 * oscκ) ^ 2 := by rw [hc]; field_simp; ring

/-- **DDDF Prop. 3, (2.16)** (`tightness.tex` l. 329–336; DF l. 1828–1840): there are
`C, σ² > 0` such that for every white noise, every `n ≥ 0`, every `C¹` modification `Y` of
`φ_{0,n} = φ_{2^{-n},1}` and every `x ≥ 0`,
`P(2^{-n} sup_{[0,1]²} ‖∇Y‖ ≥ x) ≤ C 4^n e^{−x²/(2σ²)}`. -/
theorem prop3_tail : ∃ C σ2 : ℝ, 0 < C ∧ 0 < σ2 ∧
    ∀ {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {W : WNSpace → Ω → ℝ}, IsWhiteNoise P W →
    ∀ (n : ℕ) (Y : ℂ → Ω → ℝ), (∀ x, (fun ω => Y x ω) =ᵐ[P] phi W ((2 : ℝ) ^ n)⁻¹ 1 x) →
    (∀ ω, ContDiff ℝ 1 fun x => Y x ω) → ∀ x : ℝ, 0 ≤ x →
    P.real {ω | x ≤ ((2 : ℝ) ^ n)⁻¹ * ⨆ z : ferniqueBox 0 1, ‖fderiv ℝ (fun x => Y x ω) z‖} ≤
      C * 4 ^ n * Real.exp (-x ^ 2 / (2 * σ2)) := by
  refine ⟨4 * Real.exp (ferniqueCF ^ 2 / (2 * (2 * oscκ) ^ 2)), 32, by positivity, by norm_num,
    ?_⟩
  intro Ω _ P W hW n Y hY hYc x hx
  have := hW.isProbabilityMeasure
  set a : ℝ := ((2 : ℝ) ^ n)⁻¹ with ha_def
  have ha : 0 < a := by positivity
  have ha1 : a ≤ 1 := inv_le_one_of_one_le₀ (one_le_pow₀ (by norm_num))
  obtain ⟨Y', G, hY', -, hY'c, hfd, hGc, -, hGd, hGg⟩ := exists_C1_modification_phi hW ha ha1
  have hfe := ae_fderiv_eq_of_modification (P := P) (Y₁ := Y) (Y₂ := Y')
    (fun ω => (hYc ω).continuous) (fun ω => (hY'c ω).continuous)
    (fun x => (hY x).trans (hY' x).symm)
  set F : Fin (2 ^ n) × Fin (2 ^ n) × Fin 2 → Set Ω := fun ikj =>
    {ω | oscκ * x / 2 ≤ ⨆ z : ferniqueBox ⟨a * ikj.1, a * ikj.2.1⟩ a,
      |(oscκ * a) • G ikj.2.2 z ω|} with hF
  set bad : Set Ω := {ω | ¬ ∀ z, fderiv ℝ (fun x => Y x ω) z = fderiv ℝ (fun x => Y' x ω) z}
  have hbad : P.real bad = 0 := by
    simp only [Measure.real, bad, ae_iff.mp hfe, ENNReal.toReal_zero]
  have hsub : {ω | x ≤ a * ⨆ z : ferniqueBox 0 1, ‖fderiv ℝ (fun x => Y x ω) z‖} ⊆
      bad ∪ ⋃ ikj, F ikj := by
    intro ω hω
    by_cases hgood : ∀ z, fderiv ℝ (fun x => Y x ω) z = fderiv ℝ (fun x => Y' x ω) z
    · right
      have hcont : Continuous fun z => ‖fderiv ℝ (fun x => Y x ω) z‖ :=
        continuous_norm.comp ((hYc ω).continuous_fderiv (by norm_num))
      obtain ⟨zs, hzs, hmax⟩ := (isCompact_ferniqueBox 0 1).exists_isMaxOn
        ⟨0, mem_ferniqueBox_self zero_le_one⟩ hcont.continuousOn
      haveI : Nonempty (ferniqueBox (0 : ℂ) 1) := ⟨⟨0, mem_ferniqueBox_self zero_le_one⟩⟩
      have hle : (⨆ z : ferniqueBox 0 1, ‖fderiv ℝ (fun x => Y x ω) z‖) ≤
          ‖fderiv ℝ (fun x => Y x ω) zs‖ := ciSup_le fun z => hmax z.2
      have hn : ‖fderiv ℝ (fun x => Y x ω) zs‖ ≤ |G 0 zs ω| + |G 1 zs ω| := by
        rw [hgood zs, hfd ω zs]
        refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
        · rw [norm_smul, Complex.reCLM_norm, mul_one, Real.norm_eq_abs]
        · rw [norm_smul, Complex.imCLM_norm, mul_one, Real.norm_eq_abs]
      have hω' : x ≤ a * |G 0 zs ω| + a * |G 1 zs ω| := by
        have := mul_le_mul_of_nonneg_left (hle.trans hn) ha.le
        simp only [Set.mem_ofPred_eq] at hω
        linarith
      obtain ⟨j, hj⟩ : ∃ j : Fin 2, x / 2 ≤ a * |G j zs ω| := by
        by_cases h0 : x / 2 ≤ a * |G 0 zs ω|
        · exact ⟨0, h0⟩
        · exact ⟨1, by linarith⟩
      obtain ⟨i, k, hik⟩ := exists_dyadic_square n hzs
      refine Set.mem_iUnion.2 ⟨(i, k, j), ?_⟩
      simp only [hF, Set.mem_ofPred_eq]
      have hbdd : BddAbove (Set.range fun z : ferniqueBox ⟨a * i, a * k⟩ a =>
          |(oscκ * a) • G j z ω|) := by
        have := (isCompact_ferniqueBox ⟨a * i, a * k⟩ a).bddAbove_image
          ((continuous_abs.comp ((hGc j ω).const_smul (oscκ * a))).continuousOn)
        rwa [Set.image_eq_range] at this
      refine le_ciSup_of_le hbdd ⟨zs, hik⟩ ?_
      simp only [smul_eq_mul, abs_mul, abs_of_pos (show 0 < oscκ * a by rw [oscκ]; positivity)]
      have : 0 < oscκ := by rw [oscκ]; norm_num
      nlinarith
    · left; exact hgood
  have hκ : 0 ≤ oscκ * x / 2 := by rw [oscκ]; positivity
  calc P.real {ω | x ≤ a * ⨆ z : ferniqueBox 0 1, ‖fderiv ℝ (fun x => Y x ω) z‖}
      ≤ P.real (bad ∪ ⋃ ikj, F ikj) := measureReal_mono hsub
    _ ≤ P.real bad + P.real (⋃ ikj, F ikj) := measureReal_union_le _ _
    _ ≤ 0 + ∑ ikj, P.real (F ikj) := by rw [hbad]; gcongr; exact measureReal_iUnion_fintype_le F
    _ ≤ 0 + ∑ _ikj : Fin (2 ^ n) × Fin (2 ^ n) × Fin 2,
          2 * Real.exp (ferniqueCF ^ 2 / (2 * (2 * oscκ) ^ 2)) *
            Real.exp (-(oscκ * x / 2) ^ 2 / (2 * (2 * (2 * oscκ) ^ 2))) := by
        gcongr with ikj
        exact tail_grad_square hW ha ha1 (hGg ikj.2.2) (hGc ikj.2.2)
          (norm_unitDir_le ikj.2.2) (hGd ikj.2.2) _ hκ
    _ = 4 * Real.exp (ferniqueCF ^ 2 / (2 * (2 * oscκ) ^ 2)) * 4 ^ n *
          Real.exp (-x ^ 2 / (2 * 32)) := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_prod, Fintype.card_prod,
          Fintype.card_fin, Fintype.card_fin, nsmul_eq_mul, zero_add]
        have e1 : -(oscκ * x / 2) ^ 2 / (2 * (2 * (2 * oscκ) ^ 2)) = -x ^ 2 / (2 * 32) := by
          rw [oscκ]; field_simp; ring
        rw [e1]
        push_cast
        rw [show (4 : ℝ) ^ n = 2 ^ n * 2 ^ n by rw [← mul_pow]; norm_num]
        ring

end DDDF
end LQGMetric
