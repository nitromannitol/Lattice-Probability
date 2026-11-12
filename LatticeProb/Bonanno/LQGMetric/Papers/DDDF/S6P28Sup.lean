/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DDDF.S6P28Sup at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DDDF.FieldOsc
import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.S2Hat
import LatticeProb.Bonanno.LQGMetric.Papers.DDDF.S6TailsDec

/-!
# DDDF (2.11) for the family `δ ∈ (0,1)` (task P2-DDDF6f)

DDDF = arXiv:1904.08021, `tightness.tex`: the sup tail (2.11) (`eq:MaxBoundTail`, l. 300–305)
is stated for `φ_{0,n}`; Prop 28 Steps 2 (l. 1441–1446, 1477–1490) for the family
`δ = 2^{-n-r}` (l. 1648) need it for `φ_δ = φ_{δ,1}`. `phiVer_sup_tail`: for
`δ ∈ [2^{-n}/2, 2^{-n}]`,
`P(sup_{[0,1]²} |φ_δ| ≥ α(n + C√n) + y) ≤ C 4^n e^{−α²n/log 4} + 4^n · 2e^{C_F²/2} e^{−(y/3)²/4}`,
from `φ_{δ,1} = φ_{2^{-n},1} + φ_{δ,2^{-n}}` (`phi_add_ae`), (2.11) for `φ_{0,n}` (`prop2_tail`)
and the fine-field bound `S6P28.fine_sup_tail`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology

namespace LQGMetric
namespace DDDF
namespace S6P28

open WhiteNoise SupTail

/-- one box, one sign: sharp Fernique tail (`DGo.box_sup_tail`) for `±φ_δ` on a square of side
`b ∈ [δ, 2δ]` -/
lemma box_tail_phiVer {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {W : WNSpace → Ω → ℝ}
    (hW : IsWhiteNoise P W) {δ b : ℝ} (hδ0 : 0 < δ) (hδ1 : δ ≤ 1) (hb : b ≤ 2 * δ)
    (hbδ : δ ≤ b) (sgn : ℝ) (hsgn : sgn ^ 2 = 1) (y₀ : ℂ) {u : ℝ} (hu : 0 ≤ u) :
    P.real {ω | ferniqueCF * Real.sqrt 6 + u ≤
        ⨆ v : ferniqueBox y₀ b, sgn * phiVer W P δ 1 v ω} ≤
      Real.exp (-u ^ 2 / (2 * Real.log (1 / δ))) := by
  have hP := hW.isProbabilityMeasure
  have hY := isPhiVersion_phiVer hW hδ0 hδ1
  have hb0 : 0 < b := by linarith
  set X : ℂ → Ω → ℝ := fun v ω => sgn * phiVer W P δ 1 v ω with hX_def
  have hXg : IsGaussianProcess X P := by
    have h1 : IsGaussianProcess (phiVer W P δ 1) P :=
      (isGaussianProcess_phi_comp hW δ 1 (fun v : ℂ => v)).congr fun v => (hY.ae_eq v).symm
    simpa [hX_def, smul_eq_mul] using h1.smul (fun _ => sgn)
  have hX0 : ∀ v, ∫ ω, X v ω ∂P = 0 := fun v => by
    simp only [hX_def]
    rw [integral_const_mul, integral_congr_ae (hY.ae_eq v), integral_phi hW, mul_zero]
  have hXc : ∀ ω, ContinuousOn (fun v => X v ω) (ferniqueBox y₀ b) := fun ω =>
    (continuous_const.mul (hY.cont ω)).continuousOn
  have hinc : ∀ u ∈ ferniqueBox y₀ b, ∀ v ∈ ferniqueBox y₀ b,
      ∫ ω, (X v ω - X u ω) ^ 2 ∂P ≤ 6 / b * ‖u - v‖ := by
    intro u hu v hv
    have hm' : AEMeasurable (fun ω => phi W δ 1 v ω - phi W δ 1 u ω) P :=
      ((measurable_phi hW δ 1 v).sub (measurable_phi hW δ 1 u)).aemeasurable
    have h0 : ∫ ω, (phi W δ 1 v ω - phi W δ 1 u ω) ∂P = 0 := by
      rw [integral_sub ((memLp_phi hW δ 1 v).integrable one_le_two)
        ((memLp_phi hW δ 1 u).integrable one_le_two), integral_phi hW, integral_phi hW, sub_zero]
    have hae : (fun ω => (X v ω - X u ω) ^ 2) =ᵐ[P]
        fun ω => (phi W δ 1 v ω - phi W δ 1 u ω) ^ 2 := by
      filter_upwards [hY.ae_eq u, hY.ae_eq v] with ω h1 h2
      simp only [hX_def]; rw [h1, h2, ← mul_sub, mul_pow, hsgn, one_mul]
    rw [integral_congr_ae hae, ← variance_of_integral_eq_zero hm' h0]
    have h1 := DZZ.dzz_variance_hat_sub_le hW hδ0 hδ1 v u
    have hd2 := sq_norm_sub_le_of_mem_box hv hu
    have hd : ‖v - u‖ ≤ 3 / 2 * b := by
      have : ‖v - u‖ ^ 2 ≤ (3 / 2 * b) ^ 2 := by nlinarith
      exact (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).1 this
    rw [norm_sub_rev v u] at h1 hd
    set r := ‖u - v‖
    have hr0 : 0 ≤ r := norm_nonneg _
    have ha2 : b ^ 2 ≤ 4 * δ ^ 2 := by nlinarith
    have key : r ^ 2 * b ≤ 6 * r * δ ^ 2 := by
      nlinarith [mul_le_mul_of_nonneg_left hd (mul_nonneg hr0 hb0.le)]
    refine h1.trans ?_
    rw [div_le_iff₀ (by positivity)]
    have : 6 / b * r * δ ^ 2 = 6 * r * δ ^ 2 / b := by ring
    rw [this, le_div_iff₀ hb0]; exact key
  have hlog : 0 ≤ Real.log (1 / δ) := Real.log_nonneg ((one_le_div hδ0).2 hδ1)
  have hvar : ∀ v ∈ ferniqueBox y₀ b, Var[X v; P] ≤ Real.sqrt (Real.log (1 / δ)) ^ 2 := by
    intro v _
    rw [Real.sq_sqrt hlog, show X v = sgn • phiVer W P δ 1 v from rfl, variance_smul,
      variance_congr (hY.ae_eq v), variance_phi hW hδ0 hδ1, hsgn, one_mul]
  have h := DGo.box_sup_tail hXg hX0 hb0 (by positivity : (0 : ℝ) < 6 / b) hXc hinc hvar hu
  rw [show 6 / b * b = 6 by field_simp, Real.sq_sqrt hlog] at h
  exact h

/-- **DDDF (2.11) for every `δ ∈ (0,1]`**: for `δ ∈ [2^{-n}/2, 2^{-n}]` and `u ≥ 0`,
`P(sup_{[0,1]²} |φ_δ| ≥ C_F √6 + u) ≤ 2 · 4^n e^{−u²/(2 log(1/δ))}` (Fernique on the `4^n`
dyadic squares of side `2^{-n}`, as in DF l. 1828–1840, with the sharp Gaussian tail). -/
theorem phiVer_sup_tail_sharp {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {W : WNSpace → Ω → ℝ} (hW : IsWhiteNoise P W) (n : ℕ) {δ : ℝ}
    (hδ1 : ((2 : ℝ) ^ n)⁻¹ ≤ 2 * δ) (hδ2 : δ ≤ ((2 : ℝ) ^ n)⁻¹) {u : ℝ} (hu : 0 ≤ u) :
    P.real {ω | ferniqueCF * Real.sqrt 6 + u ≤ ⨆ z : ferniqueBox 0 1, |phiVer W P δ 1 z ω|} ≤
      2 * 4 ^ n * Real.exp (-u ^ 2 / (2 * Real.log (1 / δ))) := by
  have hP := hW.isProbabilityMeasure
  set b : ℝ := ((2 : ℝ) ^ n)⁻¹ with hb_def
  have hb0 : 0 < b := by positivity
  have hb1 : b ≤ 1 := inv_le_one_of_one_le₀ (one_le_pow₀ (by norm_num))
  have hδ0 : 0 < δ := by linarith
  have hY := isPhiVersion_phiVer hW hδ0 (hδ2.trans hb1)
  set Y := phiVer W P δ 1
  set t : ℝ := ferniqueCF * Real.sqrt 6 + u
  set F : Fin (2 ^ n) × Fin (2 ^ n) × Fin 2 → Set Ω := fun ikj =>
    {ω | t ≤ ⨆ v : ferniqueBox ⟨b * ikj.1, b * ikj.2.1⟩ b,
      (if ikj.2.2 = 0 then (1 : ℝ) else -1) * Y v ω} with hF
  have hsub : {ω | t ≤ ⨆ z : ferniqueBox 0 1, |Y z ω|} ⊆ ⋃ ikj, F ikj := by
    intro ω hω
    have hcont : Continuous fun z => |Y z ω| := continuous_abs.comp (hY.cont ω)
    obtain ⟨zs, hzs, hmax⟩ := (isCompact_ferniqueBox 0 1).exists_isMaxOn
      ⟨0, mem_ferniqueBox_self zero_le_one⟩ hcont.continuousOn
    have : Nonempty (ferniqueBox (0 : ℂ) 1) := ⟨⟨0, mem_ferniqueBox_self zero_le_one⟩⟩
    have hle : (⨆ z : ferniqueBox 0 1, |Y z ω|) ≤ |Y zs ω| := ciSup_le fun z => hmax z.2
    simp only [Set.mem_ofPred_eq] at hω
    obtain ⟨i, k, hik⟩ := exists_dyadic_square n hzs
    have hbdd : ∀ c : ℝ, BddAbove (Set.range fun v : ferniqueBox ⟨b * i, b * k⟩ b =>
        c * Y v ω) := fun c => by
      have := (isCompact_ferniqueBox ⟨b * i, b * k⟩ b).bddAbove_image
        ((continuous_const.mul (hY.cont ω) : Continuous fun v => c * Y v ω).continuousOn)
      rwa [Set.image_eq_range] at this
    rcases le_total 0 (Y zs ω) with h0 | h0
    · refine Set.mem_iUnion.2 ⟨(i, k, 0), ?_⟩
      simp only [hF, Set.mem_ofPred_eq]
      refine le_ciSup_of_le (hbdd 1) ⟨zs, hik⟩ ?_
      simp only [↓reduceIte, one_mul]; rw [abs_of_nonneg h0] at hle; linarith
    · refine Set.mem_iUnion.2 ⟨(i, k, 1), ?_⟩
      simp only [hF, Set.mem_ofPred_eq, show (1 : Fin 2) ≠ 0 from by decide, ↓reduceIte]
      refine le_ciSup_of_le (hbdd (-1)) ⟨zs, hik⟩ ?_
      simp only [neg_one_mul]; rw [abs_of_nonpos h0] at hle; linarith
  calc P.real {ω | t ≤ ⨆ z : ferniqueBox 0 1, |Y z ω|}
      ≤ P.real (⋃ ikj, F ikj) := measureReal_mono hsub
    _ ≤ ∑ ikj, P.real (F ikj) := measureReal_iUnion_fintype_le F
    _ ≤ ∑ _ikj : Fin (2 ^ n) × Fin (2 ^ n) × Fin 2,
          Real.exp (-u ^ 2 / (2 * Real.log (1 / δ))) := by
        gcongr with ikj
        exact box_tail_phiVer hW hδ0 (hδ2.trans hb1) hδ1 hδ2 _
          (by split_ifs <;> norm_num) _ hu
    _ = 2 * 4 ^ n * Real.exp (-u ^ 2 / (2 * Real.log (1 / δ))) := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_prod, Fintype.card_prod,
          Fintype.card_fin, Fintype.card_fin, nsmul_eq_mul]
        push_cast
        rw [show (4 : ℝ) ^ n = 2 ^ n * 2 ^ n by rw [← mul_pow]; norm_num]
        ring

/-- **Uniform form of (2.11) for the family**: for `δ ∈ [2^{-n}/2, 2^{-n}]`, `δ < 1`, `m ≥ 0`,
`P(sup_{[0,1]²} |φ_δ| ≥ C_F √6 + 2(n+1) log 2 + m) ≤ e^{−2m}` (DDDF l. 1446 "using (2.11) gives
a uniform tail estimate"). -/
theorem phiVer_sup_tail_unif {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {W : WNSpace → Ω → ℝ} (hW : IsWhiteNoise P W) (n : ℕ) {δ : ℝ}
    (hδ1 : ((2 : ℝ) ^ n)⁻¹ ≤ 2 * δ) (hδ2 : δ ≤ ((2 : ℝ) ^ n)⁻¹) (hδ3 : δ < 1) {m : ℝ}
    (hm : 0 ≤ m) :
    P.real {ω | ferniqueCF * Real.sqrt 6 + (2 * (n + 1) * Real.log 2 + m) ≤
        ⨆ z : ferniqueBox 0 1, |phiVer W P δ 1 z ω|} ≤ Real.exp (-(2 * m)) := by
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  set u : ℝ := 2 * (n + 1) * Real.log 2 + m with hu_def
  have hu : 0 ≤ u := by positivity
  refine (phiVer_sup_tail_sharp hW n hδ1 hδ2 hu).trans ?_
  have hδ0 : 0 < δ := by
    have : (0 : ℝ) < ((2 : ℝ) ^ n)⁻¹ := by positivity
    linarith
  set L := Real.log (1 / δ) with hL_def
  have hL0 : 0 < L := Real.log_pos (one_lt_one_div hδ0 hδ3)
  have hL1 : L ≤ (n + 1) * Real.log 2 := by
    have h1 : 1 / δ ≤ (2 : ℝ) ^ (n + 1) := by
      rw [div_le_iff₀ hδ0, pow_succ]
      have h2 : (1 : ℝ) ≤ 2 ^ n * (2 * δ) := by
        have := mul_le_mul_of_nonneg_left hδ1 (by positivity : (0 : ℝ) ≤ 2 ^ n)
        rwa [mul_inv_cancel₀ (by positivity)] at this
      linarith
    calc L ≤ Real.log ((2 : ℝ) ^ (n + 1)) := Real.log_le_log (by positivity) h1
      _ = (n + 1) * Real.log 2 := by rw [Real.log_pow]; push_cast; ring
  have key : 2 * (n + 1) * Real.log 2 + 2 * m ≤ u ^ 2 / (2 * L) := by
    rw [le_div_iff₀ (by positivity)]
    have hA : 0 ≤ 2 * (n + 1) * Real.log 2 + 2 * m := by positivity
    calc (2 * (n + 1) * Real.log 2 + 2 * m) * (2 * L)
        ≤ (2 * (n + 1) * Real.log 2 + 2 * m) * (2 * ((n + 1) * Real.log 2)) := by gcongr
      _ ≤ u ^ 2 := by rw [hu_def]; nlinarith [sq_nonneg m]
  have e4 : Real.exp (2 * (n + 1) * Real.log 2) = 4 ^ (n + 1) := by
    rw [show 2 * ((n : ℝ) + 1) * Real.log 2 = ((n + 1 : ℕ) : ℝ) * Real.log 4 by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; push_cast; ring,
      Real.exp_nat_mul, Real.exp_log (by norm_num)]
  calc 2 * 4 ^ n * Real.exp (-u ^ 2 / (2 * L))
      ≤ 2 * 4 ^ n * Real.exp (-(2 * (n + 1) * Real.log 2 + 2 * m)) := by
        gcongr; rw [neg_div]; exact neg_le_neg key
    _ = 2 * 4 ^ n * (Real.exp (2 * (n + 1) * Real.log 2))⁻¹ * Real.exp (-(2 * m)) := by
        rw [neg_add, Real.exp_add, Real.exp_neg]; ring
    _ = Real.exp (-(2 * m)) / 2 := by rw [e4, pow_succ]; field_simp; ring
    _ ≤ Real.exp (-(2 * m)) := by linarith [Real.exp_pos (-(2 * m))]

end S6P28
end DDDF
end LQGMetric
