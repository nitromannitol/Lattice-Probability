/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DDDF.T20CMain at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DDDF.T20CHol
import LatticeProb.Bonanno.LQGMetric.Papers.DDDF.T20

/-!
# DDDF Theorem 20, Step 4 for visited blocks from the pathwise bound (task P2-DDDFT20c)

DDDF = arXiv:1904.08021, `tightness.tex` l. 1156–1172. From the pathwise bound
`T20Step4Pathwise` (l. 1095–1155) we take expectations: Hölder (`T20C.holder_step`) with
Condition (T) (`ConditionT`, exponent `α`), the moments `E e^{lX}` (`expMoment_XAB_shift`),
(5.68) (`prop3_expMoment_shift`, needs `ε₀ < 1/2`, l. 1163), (5.69) (`dddf_t20_ratio_moment`)
and `Λ_{n−K}(φ,p) ≤ C Λ_{n−K}(ψ,p/2)` (`LambdaN_le_LambdaNPsi`, DDDF (5.72) `eq:RatiosPsiPhi`).
The sub-exponential factors `K^d`, `e^{C K^{1/2+ε₀}}`, `e^{C K^{2ε₀}}`, `e^{C K^{2/3}}` (from the
union bound over `O(4^K)` rectangles in (5.69)) are absorbed in `e^{-cK/2}` for `K` large
(`T20C.asymp`), as in (5.70).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal

namespace LQGMetric
namespace DDDF

open WhiteNoise SupTail

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {W : WNSpace → Ω → ℝ}

namespace T20C

/-- the sub-linear terms of Step 4 are eventually below `cK/2` -/
lemma asymp {c ε : ℝ} (hc : 0 < c) (hε0 : 0 < ε) (hε : ε < 1 / 2) (A0 B1 B2 B3 : ℝ) (d : ℕ)
    (hB1 : 0 ≤ B1) (hB2 : 0 ≤ B2) (hB3 : 0 ≤ B3) :
    ∃ K₀ : ℕ, ∀ K : ℕ, K₀ ≤ K → A0 + d * Real.log (K + 1) + B1 * (K : ℝ) ^ (1 / 2 + ε) +
      B2 * (K : ℝ) ^ (2 * ε) + B3 * (K : ℝ) ^ ((2 : ℝ) / 3) ≤ c / 2 * K := by
  set θ : ℝ := max (1 / 2 + ε) ((2 : ℝ) / 3)
  have hθ : θ < 1 := max_lt (by linarith) (by norm_num)
  obtain ⟨K₃, hK₃⟩ := exists_sublinear hθ (|A0| + 4 * d + B1 + B2 + B3) (show 0 < c / 2 by positivity)
  refine ⟨max K₃ 1, fun K hK => ?_⟩
  have hK1 : (1 : ℝ) ≤ K := by exact_mod_cast (le_max_right _ _).trans hK
  have hK0 : (0 : ℝ) < K := by linarith
  have hθ0 : 0 ≤ θ := le_trans (by linarith) (le_max_left _ _)
  have hpow : ∀ a : ℝ, a ≤ θ → (K : ℝ) ^ a ≤ (K : ℝ) ^ θ := fun a ha =>
    Real.rpow_le_rpow_of_exponent_le hK1 ha
  have h1 : (1 : ℝ) ≤ (K : ℝ) ^ θ := Real.one_le_rpow hK1 hθ0
  have hlog : Real.log (K + 1) ≤ 4 * (K : ℝ) ^ θ := by
    have e1 := T20B.log_le_two_sqrt (show (0 : ℝ) < K + 1 by linarith)
    have e2 : √((K : ℝ) + 1) ≤ 2 * √(K : ℝ) := by
      rw [show (2 : ℝ) * √(K : ℝ) = √(4 * K) by
        rw [Real.sqrt_mul (by norm_num), show (4 : ℝ) = 2 ^ 2 by norm_num,
          Real.sqrt_sq (by norm_num)]]
      exact Real.sqrt_le_sqrt (by linarith)
    have e3 : √(K : ℝ) ≤ (K : ℝ) ^ θ := by
      rw [Real.sqrt_eq_rpow]; exact hpow _ (le_trans (by norm_num) (le_max_right _ _))
    linarith
  have hb1 := mul_le_mul_of_nonneg_left (hpow (1 / 2 + ε) (le_max_left _ _)) hB1
  have hb2 := mul_le_mul_of_nonneg_left (hpow (2 * ε) (le_trans (by linarith) (le_max_left _ _))) hB2
  have hb3 := mul_le_mul_of_nonneg_left (hpow ((2 : ℝ) / 3) (le_max_right _ _)) hB3
  have hd : (d : ℝ) * Real.log (K + 1) ≤ 4 * d * (K : ℝ) ^ θ := by
    have := mul_le_mul_of_nonneg_left hlog (Nat.cast_nonneg d); linarith
  have hA : A0 ≤ |A0| * (K : ℝ) ^ θ :=
    (le_abs_self A0).trans (le_mul_of_one_le_right (abs_nonneg _) h1)
  have := hK₃ K ((le_max_left _ _).trans hK)
  nlinarith

/-- the threshold `x₀` of (5.69) grows like `K^{2/3}` for `O(4^K)` rectangles -/
lemma tailX0_le {l C c C₀ N : ℝ} (hl : 0 < l) (hC : 0 < C) (hc : 0 < c) (hC₀ : 0 < C₀)
    (hN : 0 ≤ N) {K : ℕ} (hK : 1 ≤ K) (hNK : N ≤ C₀ * 4 ^ K) :
    T20B.tailX0 l N C c ≤ 3 + (4 * (l + 1) / c) ^ 2 +
      (4 * (Real.log (l * C₀ * C + 1) + Real.log 4) / c) ^ ((2 : ℝ) / 3) *
        (K : ℝ) ^ ((2 : ℝ) / 3) := by
  have hK1 : (1 : ℝ) ≤ K := by exact_mod_cast hK
  have h4 : (1 : ℝ) ≤ 4 ^ K := one_le_pow₀ (by norm_num)
  set a₁ := Real.log (l * C₀ * C + 1)
  have ha₁ : 0 ≤ a₁ := Real.log_nonneg (by nlinarith [mul_pos (mul_pos hl hC₀) hC])
  have hl4 : 0 ≤ Real.log 4 := Real.log_nonneg (by norm_num)
  have hlog : Real.log (l * N * C + 1) ≤ (a₁ + Real.log 4) * K := by
    have e1 : l * N * C + 1 ≤ (l * C₀ * C + 1) * 4 ^ K := by
      have : l * N * C ≤ l * (C₀ * 4 ^ K) * C := by gcongr
      nlinarith [mul_pos (mul_pos hl hC₀) hC]
    have e2 : Real.log ((l * C₀ * C + 1) * 4 ^ K) = a₁ + K * Real.log 4 := by
      rw [Real.log_mul (by positivity) (by positivity), Real.log_pow]
    have e3 := Real.log_le_log (by positivity) e1
    nlinarith
  have hlog0 : 0 ≤ Real.log (l * N * C + 1) := Real.log_nonneg (by nlinarith [mul_pos hl hC])
  have hthird : (4 * Real.log (l * N * C + 1) / c) ^ ((2 : ℝ) / 3) ≤
      (4 * (a₁ + Real.log 4) / c) ^ ((2 : ℝ) / 3) * (K : ℝ) ^ ((2 : ℝ) / 3) := by
    rw [← Real.mul_rpow (by positivity) (by positivity)]
    refine Real.rpow_le_rpow (by positivity) ?_ (by norm_num)
    rw [div_mul_eq_mul_div]
    exact div_le_div_of_nonneg_right (by nlinarith) hc.le
  unfold T20B.tailX0
  have hp1 : 0 ≤ (4 * (l + 1) / c) ^ 2 := sq_nonneg _
  have hp2 : 0 ≤ (4 * Real.log (l * N * C + 1) / c) ^ ((2 : ℝ) / 3) := by positivity
  refine max_le (by linarith) (max_le (by linarith) (by linarith))

/-- the final real estimate of Step 4 -/
lemma final_real {c K β MX' E E' Λφ Λψ CΛ x₀ C₀ D : ℝ} {d : ℕ} (hβ1 : 1 ≤ β)
    (hMX'0 : 0 ≤ MX') (hE0 : 0 ≤ 25 * E) (hEE' : E ≤ E') (hE'1 : 1 ≤ E') (hΛφ : 0 < Λφ)
    (hΛψ : 0 < Λψ) (hCΛ : 0 < CΛ) (hΛφψ : Λφ ≤ CΛ * Λψ) (hx0 : 0 ≤ x₀) (hC₀ : 0 < C₀)
    (hK : 0 ≤ K) (hD : D = C₀ * (MX' + 1) * 26 * CΛ ^ 2)
    (hkey : Real.log (2 * D) + d * Real.log (K + 1) + 1 + 4 * x₀ + Real.log E' ≤ c / 2 * K) :
    C₀ * (K + 1) ^ d * (Real.exp (-(c * K)) * MX' ^ (3 * β)⁻¹ * (25 * E) ^ (3 * β)⁻¹ *
      (Λφ ^ (6 * β) * (Real.exp (2 * (6 * β) * x₀) + 1)) ^ (3 * β)⁻¹) ≤
      Real.exp (-(c / 2 * K)) * Λψ ^ 2 / 2 := by
  set t : ℝ := (3 * β)⁻¹ with ht
  have hβ0 : 0 < β := by linarith
  have ht0 : 0 ≤ t := by positivity
  have ht1 : t ≤ 1 := inv_le_one_of_one_le₀ (by linarith)
  have hm1 : MX' ^ t ≤ MX' + 1 := rpow_le_add_one hMX'0 ht0 ht1
  have hm2 : (25 * E) ^ t ≤ 26 * E' := (rpow_le_add_one hE0 ht0 ht1).trans (by linarith)
  have hm3 : (Λφ ^ (6 * β) * (Real.exp (2 * (6 * β) * x₀) + 1)) ^ t ≤
      CΛ ^ 2 * Λψ ^ 2 * Real.exp (4 * x₀ + 1) := by
    rw [Real.mul_rpow (by positivity) (by positivity), ← Real.rpow_mul hΛφ.le]
    have e1 : 6 * β * t = 2 := by rw [ht]; field_simp; ring
    rw [e1, Real.rpow_two]
    have hq1 : Λφ ^ 2 ≤ CΛ ^ 2 * Λψ ^ 2 := by
      rw [← mul_pow]; exact pow_le_pow_left₀ hΛφ.le hΛφψ 2
    have hq2 : (Real.exp (2 * (6 * β) * x₀) + 1) ^ t ≤ Real.exp (4 * x₀ + 1) := by
      have ey : Real.exp (2 * (6 * β) * x₀) + 1 ≤ Real.exp (2 * (6 * β) * x₀ + 1) := by
        rw [Real.exp_add]
        have := Real.one_le_exp (show 0 ≤ 2 * (6 * β) * x₀ by positivity)
        have h2 : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
        nlinarith
      calc _ ≤ Real.exp (2 * (6 * β) * x₀ + 1) ^ t := Real.rpow_le_rpow (by positivity) ey ht0
        _ = Real.exp ((2 * (6 * β) * x₀ + 1) * t) := by rw [← Real.exp_mul]
        _ ≤ Real.exp (4 * x₀ + 1) := by
          refine Real.exp_le_exp.2 ?_
          have e2 : (2 * (6 * β) * x₀ + 1) * t = 4 * x₀ + t := by rw [ht]; field_simp; ring
          linarith
    exact mul_le_mul hq1 hq2 (by positivity) (by positivity)
  have hKd : (K + 1) ^ d = Real.exp (d * Real.log (K + 1)) := by
    rw [Real.exp_nat_mul, Real.exp_log (by positivity)]
  have hD0 : 0 < D := by rw [hD]; positivity
  have hexp : Real.exp (Real.log (2 * D)) * Real.exp (d * Real.log (K + 1)) *
      Real.exp (-(c * K)) * Real.exp (Real.log E') * Real.exp (4 * x₀ + 1) ≤
      Real.exp (-(c / 2 * K)) := by
    rw [← Real.exp_add, ← Real.exp_add, ← Real.exp_add, ← Real.exp_add]
    exact Real.exp_le_exp.2 (by linarith)
  have hm1' : 0 ≤ MX' ^ t := by positivity
  have hm2' : 0 ≤ (25 * E) ^ t := by positivity
  calc C₀ * (K + 1) ^ d * (Real.exp (-(c * K)) * MX' ^ t * (25 * E) ^ t *
        (Λφ ^ (6 * β) * (Real.exp (2 * (6 * β) * x₀) + 1)) ^ t)
      ≤ C₀ * (K + 1) ^ d * (Real.exp (-(c * K)) * (MX' + 1) * (26 * E') *
        (CΛ ^ 2 * Λψ ^ 2 * Real.exp (4 * x₀ + 1))) := by gcongr
    _ = 1 / 2 * (Real.exp (Real.log (2 * D)) * Real.exp (d * Real.log (K + 1)) *
          Real.exp (-(c * K)) * Real.exp (Real.log E') * Real.exp (4 * x₀ + 1)) * Λψ ^ 2 := by
        rw [Real.exp_log (by positivity), Real.exp_log (by positivity), ← hKd, hD]; ring
    _ ≤ 1 / 2 * Real.exp (-(c / 2 * K)) * Λψ ^ 2 := by gcongr
    _ = Real.exp (-(c / 2 * K)) * Λψ ^ 2 / 2 := by ring

end T20C

open T20C in
/-- **DDDF Step 4, visited blocks, from the pathwise bound** (`tightness.tex` l. 1156–1172):
`T20Step4Pathwise` (l. 1095–1155) and Condition (T) give `T20Step4Visited`. -/
theorem dddf_t20_step4_visited_of_pathwise (hW : IsWhiteNoise P W) (Q : PsiParams)
    (hε : Q.ε₀ < 1 / 2) {ξ : ℝ} (hξ : 0 < ξ) (hT : ConditionT ξ Q W P)
    (hA : T20Step4Pathwise ξ Q W P) : T20Step4Visited ξ Q W P := by
  have := hW.isProbabilityMeasure
  obtain ⟨α, hα, c, hc, K₁, hTη⟩ := hT
  obtain ⟨C₀, hC₀, d, K₂, hpath⟩ := hA
  set β : ℝ := α / (α - 1) with hβ
  have hα0 : 0 < α := by linarith
  have hβ0 : 0 < β := div_pos hα0 (by linarith)
  have hβ1 : 1 ≤ β := by rw [hβ, le_div_iff₀ (by linarith)]; linarith
  set t : ℝ := (3 * β)⁻¹ with ht
  have ht0 : 0 ≤ t := by positivity
  have ht1 : t ≤ 1 := inv_le_one_of_one_le₀ (by linarith)
  obtain ⟨p₀, hp₀, hR⟩ := dddf_t20_ratio_moment (P := P) hW hξ
  refine ⟨min p₀ (1 / 4), lt_min hp₀ (by norm_num), fun p hp hpp => ?_⟩
  obtain ⟨Cr, cr, hCr, hcr, hRp⟩ := hR p hp (hpp.trans (min_le_left _ _))
  have hp4 : p ≤ 1 / 4 := hpp.trans (min_le_right _ _)
  obtain ⟨CΛ, hCΛ, hΛ⟩ := LambdaN_le_LambdaNPsi hW Q ξ hp (by linarith)
  obtain ⟨hXm, MX, hMX⟩ := expMoment_XAB_shift hW Q cBig 5 5 (l := 3 * β * C₀) (by positivity)
  obtain ⟨cO, KO, hO⟩ := prop3_expMoment_shift Q.ε₀_pos (a := 3 * β * C₀) (by positivity)
  set MX' : ℝ := max MX 0 with hMX'
  have hMX'0 : 0 ≤ MX' := le_max_right _ _
  set l : ℝ := 2 * (6 * β) with hl
  set a₁ : ℝ := Real.log (l * C₀ * Cr + 1)
  set D : ℝ := C₀ * (MX' + 1) * 26 * CΛ ^ 2 with hD
  have hD0 : 0 < D := by positivity
  set A0 : ℝ := Real.log (2 * D) + 1 + 4 * (3 + (4 * (l + 1) / cr) ^ 2)
  have hl0 : 0 < l := by positivity
  have ha₁ : 0 ≤ a₁ := Real.log_nonneg (by nlinarith [mul_pos (mul_pos hl0 hC₀) hCr])
  set B3 : ℝ := 4 * (4 * (a₁ + Real.log 4) / cr) ^ ((2 : ℝ) / 3)
  have hB3 : 0 ≤ B3 := mul_nonneg (by norm_num) (Real.rpow_nonneg (div_nonneg (mul_nonneg
    (by norm_num) (add_nonneg ha₁ (Real.log_nonneg (by norm_num)))) hcr.le) _)
  obtain ⟨K₃, hK₃⟩ := asymp hc Q.ε₀_pos hε A0 |cO| |KO| B3 d (abs_nonneg _) (abs_nonneg _) hB3
  refine ⟨c / 2, by positivity, max (max K₁ K₂) (max K₃ 1), fun K hK n hn => ?_⟩
  have hK1' : K₁ ≤ K := (le_max_left _ _).trans ((le_max_left _ _).trans hK)
  have hK2' : K₂ ≤ K := (le_max_right _ _).trans ((le_max_left _ _).trans hK)
  have hK3' : K₃ ≤ K := (le_max_left _ _).trans ((le_max_right _ _).trans hK)
  have hK1 : 1 ≤ K := (le_max_right _ _).trans ((le_max_right _ _).trans hK)
  obtain ⟨s, hσ, J, J', hJ, hJ', hcard, hP⟩ := hpath K hK2' n hn
  refine ⟨s, hσ, ?_⟩
  -- the target `B = e^{-cK/2} Λ_{n-K}(ψ,p/2)²`
  set Λψ : ℝ := LambdaNPsi ξ Q W P (n - K) (ENNReal.ofReal (p / 2))
  set Λφ : ℝ := LambdaN ξ W P (n - K) (ENNReal.ofReal p)
  have hQ2 : ENNReal.ofReal p ≤ 2⁻¹ := by
    rw [← ENNReal.ofReal_ofNat 2, ← ENNReal.ofReal_inv_of_pos (by norm_num)]
    exact ENNReal.ofReal_le_ofReal (by linarith)
  have hΛφ : 0 < Λφ := T20B.LambdaN_pos hW (ENNReal.ofReal_pos.2 hp) hQ2 _
  have hΛφψ : Λφ ≤ CΛ * Λψ := hΛ (n - K)
  have hΛψ : 0 < Λψ := by
    by_contra h; have := not_lt.1 h; nlinarith
  set B : ℝ := Real.exp (-(c / 2 * K)) * Λψ ^ 2 with hB
  have hB0 : 0 < B := by positivity
  set η₀ : ℝ := min 1 (B / (2 * C₀ * 4 ^ K))
  refine ⟨η₀, lt_min one_pos (by positivity), fun η hη hηη => ?_⟩
  obtain ⟨γ, hγ, hTK⟩ := hTη η hη
  refine ⟨γ, hγ, ?_⟩
  obtain ⟨Y, -, hY, -, hYc, -⟩ := exists_C1_modification_phi hW
    (a := ((2 : ℝ) ^ K)⁻¹) (b := 1) (by positivity) (inv_le_one_of_one_le₀ (one_le_pow₀ (by norm_num)))
  have hPz := hP η hη ((hηη.trans (min_le_left _ _))) γ hγ Y hY hYc
  have hKn : K ≤ n := hn
  -- measurability of the four factors
  have hRm := measurable_condTRatio hW Q hγ K n
  have hSm := measurable_lsRatio hW ξ hKn J J' hJ hJ'
  have hOm : AEMeasurable (fun ω => C₀ * (K : ℝ) ^ Q.ε₀ * Obig K Y ω) P :=
    (aemeasurable_sup'_fun offs_nonempty fun c₁ _ => (hO hW K Y hY hYc c₁).1).const_mul _
  have hXm' : AEMeasurable (Xbig Q W P) P := hXm
  set F : Ω → ℝ≥0∞ := fun ω => ENNReal.ofReal (T20.condTRatio ξ K (fun x => psiMN Q W P 0 K x ω)
    (γ n ω) * Real.exp (C₀ * Xbig Q W P ω) * Real.exp (C₀ * (K : ℝ) ^ Q.ε₀ * Obig K Y ω) *
      lsRatio ξ W P K n J J' hJ hJ' ω ^ 2) with hF
  have hFm : AEMeasurable F P :=
    ((((hRm.aemeasurable.mul ((hXm'.const_mul C₀).exp)).mul hOm.exp).mul
      (hSm.aemeasurable.pow_const 2))).ennreal_ofReal
  set AK : ℝ := C₀ * ((K : ℝ) + 1) ^ d with hAK
  have hAK0 : 0 ≤ AK := by positivity
  have hpt : ∀ z : Ω × Ω, ENNReal.ofReal (C₀ * ((K : ℝ) + 1) ^ d * Real.exp (C₀ * Xbig Q W P z.1) *
      Real.exp (C₀ * (K : ℝ) ^ Q.ε₀ * Obig K Y z.1) * lsRatio ξ W P K n J J' hJ hJ' z.1 ^ 2 *
      T20.condTRatio ξ K (fun x => psiMN Q W P 0 K x z.1) (γ n z.1)) =
      ENNReal.ofReal AK * F z.1 := fun z => by
    rw [hF, ← ENNReal.ofReal_mul hAK0]; congr 1; ring
  have hmp := measurePreserving_fst (μ := P) (ν := P)
  have hFP : ∫⁻ z, F z.1 ∂(P.prod P) = ∫⁻ ω, F ω ∂P := by
    conv_rhs => rw [← hmp.map_eq]
    rw [lintegral_map' (by rw [hmp.map_eq]; exact hFm) measurable_fst.aemeasurable]
  -- Hölder
  have hH := holder_step (P := P) hα hβ (R := fun ω => T20.condTRatio ξ K
      (fun x => psiMN Q W P 0 K x ω) (γ n ω)) (X := Xbig Q W P)
    (O := fun ω => C₀ * (K : ℝ) ^ Q.ε₀ * Obig K Y ω) (S := lsRatio ξ W P K n J J' hJ hJ')
    (fun ω => condTRatio_nonneg _ _ _ _) (fun ω => lsRatio_nonneg _ _ _ _ _ _ _ _)
    hRm.aemeasurable hXm' hOm hSm.aemeasurable (C₀ := C₀)
  -- the four moments
  have h1 := hTK K hK1' n hn
  have h2 : (∫⁻ ω, ENNReal.ofReal (Real.exp (3 * β * C₀ * Xbig Q W P ω)) ∂P) ^ t ≤
      ENNReal.ofReal MX' ^ t :=
    ENNReal.rpow_le_rpow (hMX.trans (ENNReal.ofReal_le_ofReal (le_max_left _ _))) ht0
  set E : ℝ := Real.exp (cO * (K : ℝ) ^ (1 / 2 + Q.ε₀) + KO * (K : ℝ) ^ (2 * Q.ε₀)) with hE
  have hI3 : ∫⁻ ω, ENNReal.ofReal (Real.exp (3 * β * (C₀ * (K : ℝ) ^ Q.ε₀ * Obig K Y ω))) ∂P ≤
      ENNReal.ofReal (25 * E) := by
    set Oc : ℂ → Ω → ℝ := fun c₁ ω => ((2 : ℝ) ^ K)⁻¹ *
      ⨆ z : ferniqueBox 0 1, ‖fderiv ℝ (fun x => Y (x + c₁) ω) z‖ with hOc
    have hpt3 : ∀ ω, ENNReal.ofReal (Real.exp (3 * β * (C₀ * (K : ℝ) ^ Q.ε₀ * Obig K Y ω))) ≤
        ∑ c₁ ∈ offs, ENNReal.ofReal (Real.exp (3 * β * C₀ * (K : ℝ) ^ Q.ε₀ * Oc c₁ ω)) := by
      intro ω
      obtain ⟨c₁, hc₁, he⟩ := Finset.exists_mem_eq_sup' offs_nonempty (fun c₁ => Oc c₁ ω)
      have e : Obig K Y ω = Oc c₁ ω := he
      refine le_trans (le_of_eq ?_) (Finset.single_le_sum (f := fun c₁ =>
        ENNReal.ofReal (Real.exp (3 * β * C₀ * (K : ℝ) ^ Q.ε₀ * Oc c₁ ω)))
        (fun _ _ => zero_le) hc₁)
      rw [e]; congr 2; ring
    calc _ ≤ ∫⁻ ω, ∑ c₁ ∈ offs, ENNReal.ofReal (Real.exp (3 * β * C₀ * (K : ℝ) ^ Q.ε₀ *
          Oc c₁ ω)) ∂P := lintegral_mono hpt3
      _ = ∑ c₁ ∈ offs, ∫⁻ ω, ENNReal.ofReal (Real.exp (3 * β * C₀ * (K : ℝ) ^ Q.ε₀ *
          Oc c₁ ω)) ∂P := lintegral_finsetSum' _ fun c₁ _ =>
            (Real.measurable_exp.comp_aemeasurable
              ((hO hW K Y hY hYc c₁).1.const_mul _)).ennreal_ofReal
      _ ≤ ∑ c₁ ∈ offs, ENNReal.ofReal E := Finset.sum_le_sum fun c₁ _ => (hO hW K Y hY hYc c₁).2
      _ = (offs.card : ℝ≥0∞) * ENNReal.ofReal E := by rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ 25 * ENNReal.ofReal E := by
          gcongr; exact_mod_cast card_offs_le
      _ = ENNReal.ofReal (25 * E) := by
          rw [ENNReal.ofReal_mul (by norm_num)]; simp
  have h3 := ENNReal.rpow_le_rpow hI3 ht0
  set x₀ : ℝ := T20B.tailX0 (2 * (6 * β)) (J.card + J'.card) Cr cr with hx₀
  set MS : ℝ := Λφ ^ (6 * β) * (Real.exp (2 * (6 * β) * x₀) + 1) with hMS
  have h4 := ENNReal.rpow_le_rpow (z := t) (hRp (6 * β) (by positivity) K n hKn J J' hJ hJ'
    Prod.fst Prod.fst Prod.snd Prod.snd) ht0
  have hMS0 : 0 ≤ MS := by positivity
  have hE0 : 0 ≤ 25 * E := by positivity
  have hZ : ∫⁻ ω, F ω ∂P ≤ ENNReal.ofReal (Real.exp (-(c * K)) * MX' ^ t * (25 * E) ^ t *
      MS ^ t) := by
    refine hH.trans ((mul_le_mul' (mul_le_mul' (mul_le_mul' h1 h2) h3) h4).trans (le_of_eq ?_))
    rw [ENNReal.ofReal_rpow_of_nonneg hMX'0 ht0, ENNReal.ofReal_rpow_of_nonneg hE0 ht0,
      ENNReal.ofReal_rpow_of_nonneg hMS0 ht0, ← ENNReal.ofReal_mul (by positivity),
      ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity)]
  -- the real inequality (absorbing the sub-exponential factors)
  have hreal : AK * (Real.exp (-(c * K)) * MX' ^ t * (25 * E) ^ t * MS ^ t) ≤ B / 2 := by
    set E' : ℝ := Real.exp (|cO| * (K : ℝ) ^ (1 / 2 + Q.ε₀) + |KO| * (K : ℝ) ^ (2 * Q.ε₀))
      with hE'
    have hEE' : E ≤ E' := Real.exp_le_exp.2 (add_le_add
      (mul_le_mul_of_nonneg_right (le_abs_self _) (by positivity))
      (mul_le_mul_of_nonneg_right (le_abs_self _) (by positivity)))
    have hE'1 : 1 ≤ E' := Real.one_le_exp (by positivity)
    have hx0 : 0 ≤ x₀ := le_trans (by norm_num) (le_max_left _ _)
    have hx : x₀ ≤ 3 + (4 * (l + 1) / cr) ^ 2 +
        (4 * (a₁ + Real.log 4) / cr) ^ ((2 : ℝ) / 3) * (K : ℝ) ^ ((2 : ℝ) / 3) :=
      tailX0_le (l := 2 * (6 * β)) (C := Cr) (c := cr) (C₀ := C₀) (N := (J.card : ℝ) + J'.card)
        (by positivity) hCr hcr hC₀ (by positivity) hK1 hcard
    have hasy := hK₃ K hK3'
    have hA0 : A0 = Real.log (2 * D) + 1 + 4 * (3 + (4 * (l + 1) / cr) ^ 2) := rfl
    have hB3' : B3 * (K : ℝ) ^ ((2 : ℝ) / 3) =
        4 * ((4 * (a₁ + Real.log 4) / cr) ^ ((2 : ℝ) / 3) * (K : ℝ) ^ ((2 : ℝ) / 3)) := by
      show 4 * (4 * (a₁ + Real.log 4) / cr) ^ ((2 : ℝ) / 3) * (K : ℝ) ^ ((2 : ℝ) / 3) = _
      ring
    have hlE : Real.log E' = |cO| * (K : ℝ) ^ (1 / 2 + Q.ε₀) + |KO| * (K : ℝ) ^ (2 * Q.ε₀) :=
      Real.log_exp _
    have hkey : Real.log (2 * D) + d * Real.log (K + 1) + 1 + 4 * x₀ + Real.log E' ≤
        c / 2 * K := by
      rw [hlE]; linarith
    have := final_real (β := β) (d := d) hβ1 hMX'0 hE0 hEE' hE'1 hΛφ hΛψ hCΛ hΛφψ hx0 hC₀
      (Nat.cast_nonneg K) hD hkey
    exact this
  have hηt : C₀ * 4 ^ K * η ^ 2 ≤ B / 2 := by
    have hηB : η ≤ B / (2 * C₀ * 4 ^ K) := hηη.trans (min_le_right _ _)
    have hη1 : η ≤ 1 := hηη.trans (min_le_left _ _)
    have hsq : η ^ 2 ≤ η := by nlinarith
    have h4K : (0 : ℝ) < C₀ * 4 ^ K := by positivity
    calc C₀ * 4 ^ K * η ^ 2 ≤ C₀ * 4 ^ K * (B / (2 * C₀ * 4 ^ K)) :=
          mul_le_mul_of_nonneg_left (hsq.trans hηB) h4K.le
      _ = B / 2 := by field_simp
  calc _ ≤ ∫⁻ z, ∑ b ∈ T20B.nearIdx K, (visSet γ n K b s).indicator
        (fun z => ENNReal.ofReal (incr ξ Q W P K n b z ^ 2)) z ∂(P.prod P) :=
        sum_lintegral_le _ _
    _ ≤ ∫⁻ z, (ENNReal.ofReal (C₀ * 4 ^ K * η ^ 2) + ENNReal.ofReal AK * F z.1) ∂(P.prod P) :=
        lintegral_mono_ae (hPz.mono fun z hz => hz.trans (le_of_eq (by rw [hpt z])))
    _ = ENNReal.ofReal (C₀ * 4 ^ K * η ^ 2) + ENNReal.ofReal AK * ∫⁻ ω, F ω ∂P := by
        rw [lintegral_add_left measurable_const, lintegral_const, measure_univ, mul_one,
          lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, hFP]
    _ ≤ ENNReal.ofReal (B / 2) + ENNReal.ofReal AK * ENNReal.ofReal
        (Real.exp (-(c * K)) * MX' ^ t * (25 * E) ^ t * MS ^ t) :=
        add_le_add (ENNReal.ofReal_le_ofReal hηt) (mul_le_mul_of_nonneg_left hZ zero_le)
    _ = ENNReal.ofReal (B / 2) + ENNReal.ofReal
        (AK * (Real.exp (-(c * K)) * MX' ^ t * (25 * E) ^ t * MS ^ t)) := by
        rw [ENNReal.ofReal_mul hAK0]
    _ ≤ ENNReal.ofReal (B / 2) + ENNReal.ofReal (B / 2) :=
        add_le_add le_rfl (ENNReal.ofReal_le_ofReal hreal)
    _ = ENNReal.ofReal B := by
        rw [← ENNReal.ofReal_add (by positivity) (by positivity)]; ring_nf

end DDDF
end LQGMetric
