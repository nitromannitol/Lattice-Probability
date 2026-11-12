/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DZZ.S3Eta9C at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.S3Eta9B
import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.S3Eta8
import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.S3L16Var

/-!
# Bookkeeping for DZZ l. 1193–1195 (P2-DZZETA2)

DZZ (arXiv:1807.00422, `LBM_LGDarXiv.tex` l. 1193–1195): the variance and parameter bookkeeping
of the comparison `M^W(S̃) ≥ e^{−2αγ√L log L} δ'² s^{−2} M̃_{γ,ε²s',η}(S̃)` ("similarly to
(eq-M-tilde-B-bound)"; DZZ give no details):

* `tildeVar_le_split`: `Var h̃_{2^{-n}}(z) ≤ Var η^{δ̂}_{2^{-n}}(z) + Var η_s(c_B) + V` with
  `V = b₁ + log(s/δ̂) + 2√(1076·5)√(log s⁻¹ + 4)` (`dzz_var_compare`, `etaVar_split`,
  `etaBandVar_le`, `etaVar_sub_le`);
* `expo_asymp`: the error exponent is `≤ 2(α + A)γ√L log L` (own elementary estimate);
* `norm_sub_center_le_of_sqSB`, `isCompact_evenSq`: geometry;
* `wickGood hW γ`: the full-measure set of the version identities and of the limit step
  (`ae_ofReal_mul_etaChaos_le`) for the countably many squares `S̃`; `ae_wickGood`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology Metric
open scoped ENNReal NNReal

namespace LQGMetric
namespace DZZ

open WhiteNoise QuantumZipper GMCIdent GMCIdent3 GMCIdent4 SupTail

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {W : WNSpace → Ω → ℝ}

/-- variance bookkeeping of DZZ l. 1193–1195 -/
lemma tildeVar_le_split (hW : IsWhiteNoise P W) {b₁ : ℝ}
    (hb : ∀ (n : ℕ) (v : ℂ), |tildeVar ((1 / 2 : ℝ) ^ n) v - etaVar ((1 / 2 : ℝ) ^ n) v| ≤ b₁)
    (B : DyBox) {j n : ℕ} (hn : B.n + j ≤ n) {z : ℂ} (hz : ‖z - B.center‖ ≤ 5 * B.side) :
    tildeVar ((2 : ℝ)⁻¹ ^ n) z ≤ etaBVar ((2 : ℝ)⁻¹ ^ (B.n + j)) n z + etaVar B.side B.center +
      (b₁ + Real.log (B.side / (2 : ℝ)⁻¹ ^ (B.n + j)) +
        2 * Real.sqrt (1076 * 5) * Real.sqrt (Real.log B.side⁻¹ + 4)) := by
  set δh : ℝ := (2 : ℝ)⁻¹ ^ (B.n + j)
  have hs := DyBox.side_pos' B
  have hs1 : B.side ≤ 1 := by unfold DyBox.side; exact pow_le_one₀ (by norm_num) (by norm_num)
  have hδh0 : 0 < δh := by positivity
  have hδhs : δh ≤ B.side := by
    unfold DyBox.side; exact pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)
  have hnδ : (2 : ℝ)⁻¹ ^ n ≤ δh := pow_le_pow_of_le_one (by norm_num) (by norm_num) hn
  have h1 := (abs_le.1 (hb n z)).2
  rw [one_div] at h1
  have h2 := etaVar_split (ε := δh) (ε' := (2 : ℝ)⁻¹ ^ n) (by positivity) hnδ z
  have h3 := etaVar_split (ε := B.side) (ε' := δh) hδh0 hδhs z
  have h4 := etaBandVar_le hδh0 hδhs z
  have h5 := etaVar_sub_le hW hs hs1 z B.center
  have h6 : Real.sqrt (1076 * ‖z - B.center‖ / B.side) ≤ Real.sqrt (1076 * 5) := by
    refine Real.sqrt_le_sqrt ?_
    rw [div_le_iff₀ hs]; nlinarith
  have h7 : 0 ≤ Real.sqrt (Real.log B.side⁻¹ + 4) := Real.sqrt_nonneg _
  have h8 := mul_le_mul_of_nonneg_right h6 h7
  have e2 : etaBVar δh n z = Real.pi * ‖etaKernelL2 (Ioo (((2 : ℝ)⁻¹ ^ n) ^ 2) (δh ^ 2)) z‖ ^ 2 :=
    rfl
  have e3 : etaBandVar δh B.side z = Real.pi * ‖etaKernelL2 (Ioo (δh ^ 2) (B.side ^ 2)) z‖ ^ 2 :=
    rfl
  rw [← e2] at h2
  rw [← e3] at h3
  nlinarith

/-- the error exponent of DZZ l. 1193–1195 (own elementary estimate) -/
lemma expo_asymp {γ α b₁ Cm L K : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) (hα : 0 ≤ α) (hb : 0 ≤ b₁)
    (hCm : 1 ≤ Cm) (hL : Real.exp 1 ≤ L) (hK1 : 1 ≤ K) (hK : K ≤ 4 * Cm * L) {S : ℝ}
    (hS : S ≤ Cm * L) :
    γ * (Real.sqrt L + α * Real.sqrt L * Real.log L) + γ ^ 2 / 2 *
        (b₁ + Real.log (1024 * K ^ 2) + 2 * Real.sqrt (1076 * 5) * Real.sqrt (S + 4)) ≤
      2 * (α + (1 + (b₁ + 14 + 2 * Cm + 2 * Real.sqrt (1076 * 5) * Real.sqrt (Cm + 4)))) * γ *
        Real.sqrt L * Real.log L := by
  have hL1 : 1 ≤ L := (Real.add_one_le_exp 1).trans' (by norm_num) |>.trans hL
  have hlogL : 1 ≤ Real.log L := by
    rw [← Real.log_exp 1]; exact Real.log_le_log (Real.exp_pos 1) hL
  have hsL : 1 ≤ Real.sqrt L := by rw [← Real.sqrt_one]; exact Real.sqrt_le_sqrt hL1
  have hsLsq : Real.sqrt L ^ 2 = L := Real.sq_sqrt (by linarith)
  -- `log L ≤ 2 √L`
  have hlogle : Real.log L ≤ 2 * Real.sqrt L := by
    have h := Real.log_le_sub_one_of_pos (show 0 < Real.sqrt L by linarith)
    rw [Real.log_sqrt (by linarith)] at h
    linarith
  have hK0 : 0 < K := by linarith
  have hlogK : Real.log K ≤ Real.log 4 + Real.log Cm + Real.log L := by
    rw [← Real.log_mul (by norm_num) (by linarith), ← Real.log_mul (by positivity) (by linarith)]
    exact Real.log_le_log hK0 hK
  have hlog4 : Real.log 4 < 1.4 := by
    have := Real.log_two_lt_d9
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; push_cast; linarith
  have hlog1024 : Real.log 1024 < 7 := by
    have := Real.log_two_lt_d9
    rw [show (1024 : ℝ) = 2 ^ 10 by norm_num, Real.log_pow]; push_cast; linarith
  have hlogCm : Real.log Cm ≤ Cm := (Real.log_le_sub_one_of_pos (by linarith)).trans (by linarith)
  have hlog1 : Real.log (1024 * K ^ 2) = Real.log 1024 + 2 * Real.log K := by
    rw [Real.log_mul (by norm_num) (by positivity), Real.log_pow]; push_cast; ring
  have hlogK0 : 0 ≤ Real.log K := Real.log_nonneg hK1
  have hI1 : Real.log (1024 * K ^ 2) ≤ (14 + 2 * Cm) * Real.sqrt L := by
    rw [hlog1]; nlinarith
  have hI2 : Real.sqrt (S + 4) ≤ Real.sqrt (Cm + 4) * Real.sqrt L := by
    rw [← Real.sqrt_mul (by linarith)]
    exact Real.sqrt_le_sqrt (by nlinarith)
  set A₁ := b₁ + 14 + 2 * Cm + 2 * Real.sqrt (1076 * 5) * Real.sqrt (Cm + 4) with hA₁
  have hc0 : 0 ≤ 2 * Real.sqrt (1076 * 5) := by positivity
  have hI : b₁ + Real.log (1024 * K ^ 2) + 2 * Real.sqrt (1076 * 5) * Real.sqrt (S + 4) ≤
      A₁ * Real.sqrt L := by
    have := mul_le_mul_of_nonneg_left hI2 hc0
    have hb' : b₁ ≤ b₁ * Real.sqrt L := le_mul_of_one_le_right hb hsL
    rw [hA₁]; nlinarith
  have hI0 : 0 ≤ b₁ + Real.log (1024 * K ^ 2) + 2 * Real.sqrt (1076 * 5) * Real.sqrt (S + 4) := by
    have : 0 ≤ Real.log (1024 * K ^ 2) := by rw [hlog1]; nlinarith [Real.log_nonneg (show (1 : ℝ) ≤ 1024 by norm_num)]
    positivity
  have hA0 : 0 ≤ A₁ := by rw [hA₁]; positivity
  have hγI : γ ^ 2 / 2 * (b₁ + Real.log (1024 * K ^ 2) + 2 * Real.sqrt (1076 * 5) * Real.sqrt (S + 4)) ≤
      γ * (A₁ * Real.sqrt L) := by
    have : γ ^ 2 / 2 ≤ γ := by nlinarith
    exact (mul_le_mul_of_nonneg_right this hI0).trans (mul_le_mul_of_nonneg_left hI hγ.le)
  have hsl : Real.sqrt L ≤ Real.sqrt L * Real.log L := le_mul_of_one_le_right (by linarith) hlogL
  have hX : 0 ≤ Real.sqrt L * Real.log L := by positivity
  have e1 : γ * (A₁ * Real.sqrt L) ≤ γ * (A₁ * (Real.sqrt L * Real.log L)) :=
    mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hsl hA0) hγ.le
  have e2 : γ * Real.sqrt L ≤ γ * (Real.sqrt L * Real.log L) := mul_le_mul_of_nonneg_left hsl hγ.le
  have e3 : 0 ≤ γ * ((α + 1 + A₁) * (Real.sqrt L * Real.log L)) := by positivity
  nlinarith

lemma norm_sub_center_le_of_sqSB {B : DyBox} {a b : ℕ} (ha : a < 4096) (hb : b < 4096) {z : ℂ}
    (hz : z ∈ sqSB B a b) : ‖z - B.center‖ ≤ 5 * B.side := by
  obtain ⟨h1, h2, h3, h4⟩ := hz
  have hs := DyBox.side_pos' B
  have ha' : (a : ℝ) + 1 ≤ 4096 := by exact_mod_cast ha
  have hb' : (b : ℝ) + 1 ≤ 4096 := by exact_mod_cast hb
  have ha0 : (0 : ℝ) ≤ a := Nat.cast_nonneg a
  have hb0 : (0 : ℝ) ≤ b := Nat.cast_nonneg b
  have r1 : |(z - B.center).re| ≤ 2 * B.side := by
    rw [Complex.sub_re, abs_le]; constructor <;> nlinarith
  have r2 : |(z - B.center).im| ≤ 2 * B.side := by
    rw [Complex.sub_im, abs_le]; constructor <;> nlinarith
  linarith [Complex.norm_le_abs_re_add_abs_im (z - B.center)]

lemma isClosed_evenSq (w : ℂ) (h : ℝ) (i j : ℕ) : IsClosed (evenSq w h i j) := by
  unfold evenSq
  refine (isClosed_le continuous_const Complex.continuous_re).inter
    ((isClosed_le Complex.continuous_re continuous_const).inter
    ((isClosed_le continuous_const Complex.continuous_im).inter
    (isClosed_le Complex.continuous_im continuous_const)))

lemma isCompact_evenSq {w : ℂ} {h : ℝ} {i j : ℕ} (hS : evenSq w h i j ⊆ dzzV) :
    IsCompact (evenSq w h i j) :=
  Metric.isCompact_of_isClosed_isBounded (isClosed_evenSq w h i j)
    (isBounded_closedBall.subset (hS.trans dzzV_subset_closedBall))

/-- the full-measure set of the version identities and of the limit step for all squares `S̃` -/
def wickGood (hW : IsWhiteNoise P W) (γ : ℝ) : Set Ω :=
  {ω | (∀ (p : ℕ) (b : DyBox), etaCV hW p b.center ω = etaInf W ((2 : ℝ)⁻¹ ^ p) b.center ω) ∧
    (∀ p n : ℕ, p ≤ n → ∀ᵐ z ∂(volume : Measure ℂ),
      etaCV hW n z ω = etaVer W ((2 : ℝ)⁻¹ ^ p) n z ω + etaCV hW p z ω) ∧
    (∀ (B : DyBox) (a b k i j : ℕ),
      evenSq (sqCorner B a b) (B.side / 1024 / (2 * k)) i j ⊆ dzzV → ∀ c : ℝ,
      (∀ᶠ n in atTop, ∀ᵐ z ∂(volume.restrict (evenSq (sqCorner B a b) (B.side / 1024 / (2 * k)) i j)),
        ENNReal.ofReal c * etaDens W γ (B.side / 1024 / (2 * k) ^ 2) n z ω ≤ wickDensC hW γ n z ω) →
      ENNReal.ofReal c * etaChaos W γ (B.side / 1024 / (2 * k) ^ 2)
          (evenSq (sqCorner B a b) (B.side / 1024 / (2 * k)) i j) ω ≤
        wickQArea γ W ω (evenSq (sqCorner B a b) (B.side / 1024 / (2 * k)) i j))}

theorem ae_wickGood (hW : IsWhiteNoise P W) {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) :
    ∀ᵐ ω ∂P, ω ∈ wickGood hW γ := by
  have h3 : ∀ᵐ ω ∂P, ∀ (B : DyBox) (a b k i j : ℕ),
      evenSq (sqCorner B a b) (B.side / 1024 / (2 * k)) i j ⊆ dzzV → ∀ c : ℝ,
      (∀ᶠ n in atTop, ∀ᵐ z ∂(volume.restrict (evenSq (sqCorner B a b) (B.side / 1024 / (2 * k)) i j)),
        ENNReal.ofReal c * etaDens W γ (B.side / 1024 / (2 * k) ^ 2) n z ω ≤ wickDensC hW γ n z ω) →
      ENNReal.ofReal c * etaChaos W γ (B.side / 1024 / (2 * k) ^ 2)
          (evenSq (sqCorner B a b) (B.side / 1024 / (2 * k)) i j) ω ≤
        wickQArea γ W ω (evenSq (sqCorner B a b) (B.side / 1024 / (2 * k)) i j) := by
    rw [ae_all_iff]; intro B; rw [ae_all_iff]; intro a; rw [ae_all_iff]; intro b
    rw [ae_all_iff]; intro k; rw [ae_all_iff]; intro i; rw [ae_all_iff]; intro j
    by_cases hS : evenSq (sqCorner B a b) (B.side / 1024 / (2 * k)) i j ⊆ dzzV
    · filter_upwards [ae_ofReal_mul_etaChaos_le hW hγ hγ2 (B.side / 1024 / (2 * k) ^ 2)
        (isCompact_evenSq hS) hS] with ω hω _
      exact hω
    · exact Eventually.of_forall fun ω h => absurd h hS
  filter_upwards [ae_etaCV_center hW, ae_etaCV_split hW, h3] with ω h1 h2 h3
  exact ⟨h1, h2, h3⟩

end DZZ
end LQGMetric
