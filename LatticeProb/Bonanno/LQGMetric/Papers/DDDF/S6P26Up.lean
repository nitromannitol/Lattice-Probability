/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DDDF.S6P26Up at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DDDF.S6P26Up0
import LatticeProb.Bonanno.LQGMetric.Papers.DDDF.S6Mom
import LatticeProb.Bonanno.LQGMetric.Papers.DDDF.S6P26Low

/-!
# DDDF Prop 26, Step 1: weak submultiplicativity `λ_{n+k} ≤ e^{C√k} λ_n λ_k` (task P2-DDDF6b)

DDDF = Ding–Dubédat–Dunlap–Falconet, arXiv:1904.08021, `literature/src/1904.08021/tightness.tex`
l. 1283–1309. DDDF's argument splits into a pathwise part (l. 1288–1306) and a probabilistic
part (l. 1295–1309):

* pathwise (`S6Step1Circ`, proved in S6P26Sub/S6P26Glue3): `L^{(n+k)}_{1,1} ≤ Σ_{P ∈ π_k^k} L^{(n+k)}(S^{(k,n+k)}(P))
  ≤ Σ_P e^{ξφ_{0,k}(P) + ξ osc_{\hat P}} L^{(k,n+k)}(S^{(k,n+k)}(P))` (l. 1291–1294), with
  `V_P := 1_{P ∈ π_k^k} e^{ξφ_{0,k}(P) + ξ osc_{\hat P}}` measurable w.r.t. `φ_{0,k}` (l. 1288), and
  `Σ_P V_P ≤ 9 · 2^k e^{2ξ 2^{-k}‖∇φ_{0,k}‖} L^{(k)}_{1,1}` (l. 1299–1306). We allow `≤ C₁`
  rectangles `u 2^{-k} R_{3,1} + c` per block (DDDF: the four rectangles surrounding `P`; near
  `∂[0,1]²` the circuit must be cut, cf. D-DDDF-22) and a constant `C₁` throughout.
* probabilistic (proved here, `s6_eq5_76_up`): independence of `φ_{0,k}` and `φ_{k,n+k}`
  (`indepFun_phi_version`), scaling `E L^{(k,n+k)}(u 2^{-k}R_{3,1}+c) = 2^{-k} E L^{(n)}_{3,1}`
  (`T20B.law_mrectLen`), `E L^{(n)}_{3,1} ≤ C λ_n` and `E (L^{(k)}_{1,1})² ≤ C λ_k²` (DDDF l. 1218,
  `s6_moment_L31`, from Prop 18 and `Λ_∞ < ∞`), `E e^{a 2^{-k}‖∇φ_{0,k}‖} ≤ K e^{c√k}`
  (`S6U.obig_expMoment`, DDDF's proof of (2.17) with `ε = 0`), and Cauchy–Schwarz (DDDF l. 1307;
  here in the form `xy ≤ θx²/2 + y²/(2θ)` with `θ = λ_k e^{-c√k}`). DDDF's last step
  "`λ_{n+k} ≤ e^{C√k} λ_n λ_k`" from the mean bound is Markov's inequality: the median is at
  most `3 E` (`S6U.lowerMedian_le_three`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Real
open scoped ENNReal

namespace LQGMetric
namespace DDDF

open WhiteNoise S6 T20C

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {W : WNSpace → Ω → ℝ} {ξ : ℝ}

/-- **DDDF Prop 26, Step 1, pathwise part** (l. 1288–1306): for `k ≥ 2`, `n ≥ 1` there are blocks `I`,
for each block `≤ C₁` long rectangles `u 2^{-k} R_{3,1} + c` (the circuit `S^{(k,n+k)}(P)`), and
weights `V_P ≥ 0` measurable w.r.t. `φ_{0,k}` with, a.s.,
`L^{(n+k)}_{1,1} ≤ Σ_P V_P Σ_{R ∈ S(P)} L^{(k,n+k)}(R)` and
`Σ_P V_P ≤ C₁ 2^k e^{C₁ Obig_k} L^{(k)}_{1,1}`. Proved: `s6Step1Circ_of_glue` (S6P26Sub) with
`s6_step1_glue` (S6P26Glue3). -/
def S6Step1Circ (ξ : ℝ) (W : WNSpace → Ω → ℝ) (P : Measure Ω) : Prop :=
  ∃ C₁ : ℝ, 0 < C₁ ∧ ∀ k n : ℕ, 2 ≤ k → 1 ≤ n →
    ∃ (I : Finset (ℤ × ℤ)) (J : ℤ × ℤ → Finset (Circle × ℂ)) (V : ℤ × ℤ → Ω → ℝ),
      (∀ b ∈ I, ((J b).card : ℝ) ≤ C₁) ∧
      (∀ b ∈ I, Measurable[MeasurableSpace.comap (fun ω x => phiMN W P 0 k x ω) inferInstance]
        (V b)) ∧
      (∀ b ∈ I, ∀ ω, 0 ≤ V b ω) ∧
      ∀ Y : ℂ → Ω → ℝ, (∀ x, (fun ω => Y x ω) =ᵐ[P] phi W ((2 : ℝ) ^ k)⁻¹ 1 x) →
        (∀ ω, ContDiff ℝ 1 fun x => Y x ω) →
        ∀ᵐ ω ∂P, lenN ξ W P 1 1 (n + k) ω ≤
            ∑ b ∈ I, V b ω * ∑ j ∈ J b,
              T20B.mrectLen ξ (fun x => phiMN W P k (n + k) x ω) k j.1 j.2 3 1 ∧
          ∑ b ∈ I, V b ω ≤ C₁ * (2 : ℝ) ^ k * Real.exp (C₁ * Obig k Y ω) * lenN ξ W P 1 1 k ω

namespace S6U

/-- Markov: the lower median of `X ≥ 0` is at most `3 E X`. -/
theorem lowerMedian_le_three [IsProbabilityMeasure P] {X : Ω → ℝ} (hX : Measurable X)
    {R : ℝ} (hR : 0 ≤ R) (h : ∫⁻ ω, ENNReal.ofReal (X ω) ∂P ≤ ENNReal.ofReal R) :
    lowerMedianLaw (P.map X) ≤ 3 * R := by
  refine le_of_forall_pos_le_add fun δ hδ => lowerMedian_le_of hX ?_
  set m := 3 * R + δ
  have hm : 0 < m := by positivity
  calc P {ω | m < X ω} ≤ P {ω | ENNReal.ofReal m ≤ ENNReal.ofReal (X ω)} :=
        measure_mono fun ω hω => ENNReal.ofReal_le_ofReal (le_of_lt hω)
    _ ≤ (∫⁻ ω, ENNReal.ofReal (X ω) ∂P) / ENNReal.ofReal m :=
        meas_ge_le_lintegral_div hX.ennreal_ofReal.aemeasurable
          (ENNReal.ofReal_pos.2 hm).ne' ENNReal.ofReal_ne_top
    _ ≤ ENNReal.ofReal R / ENNReal.ofReal m := by gcongr
    _ = ENNReal.ofReal (R / m) := (ENNReal.ofReal_div_of_pos hm).symm
    _ < 2⁻¹ := by
        rw [← ofReal_half_eq', ENNReal.ofReal_lt_ofReal_iff (by norm_num), div_lt_iff₀ hm]
        simp only [m]; linarith

/-- `E L^{(k,m)}(u 2^{-k} R_{3,1} + c) = 2^{-k} E L^{(m-k)}_{3,1}` (scaling, `T20B.law_mrectLen`) -/
theorem lintegral_mrectLen (hW : IsWhiteNoise P W) {k m : ℕ} (hkm : k ≤ m) (u : Circle)
    (c : ℂ) :
    ∫⁻ ω, ENNReal.ofReal (T20B.mrectLen ξ (fun x => phiMN W P k m x ω) k u c 3 1) ∂P =
      ENNReal.ofReal ((2 : ℝ)⁻¹ ^ k) *
        ∫⁻ ω, ENNReal.ofReal (lenObs ξ (phiMN W P 0 (m - k)) (rectAB 3 1) ω) ∂P := by
  have hf := T20B.measurable_mrectLen (ξ := ξ) hW hkm u c 3 1
  have hφ := isPhiVersion_phiMN hW (Nat.zero_le (m - k))
  have hL := measurable_lenObs (ξ := ξ) hφ.cont hφ.meas (rectAB 3 1)
  have hg : Measurable fun ω => (2 : ℝ)⁻¹ ^ k * lenObs ξ (phiMN W P 0 (m - k)) (rectAB 3 1) ω :=
    hL.const_mul _
  have hmap : P.map (fun ω => T20B.mrectLen ξ (fun x => phiMN W P k m x ω) k u c 3 1) =
      P.map (fun ω => (2 : ℝ)⁻¹ ^ k * lenObs ξ (phiMN W P 0 (m - k)) (rectAB 3 1) ω) := by
    ext S hS
    rw [Measure.map_apply hf hS, Measure.map_apply hg hS]
    exact T20B.law_mrectLen hW hkm u c 3 1 hS
  rw [← lintegral_map ENNReal.measurable_ofReal hf, hmap,
    lintegral_map ENNReal.measurable_ofReal hg, ← lintegral_const_mul _ hL.ennreal_ofReal]
  refine lintegral_congr fun ω => ?_
  exact ENNReal.ofReal_mul (by positivity)

/-- `E L^{(n)}_{3,1} ≤ C λ_n` and `E (L^{(k)}_{1,1})² ≤ C λ_k²` (DDDF l. 1218, `s6_moment_L31`) -/
theorem lintegral_moments (hW : IsWhiteNoise P W) (hξ : 0 < ξ)
    (hΛ : ∃ p₀ : ℝ, 0 < p₀ ∧ ∀ p : ℝ, 0 < p → p ≤ p₀ →
      ∃ B : ℝ, ∀ n, LambdaN ξ W P n (ENNReal.ofReal p) ≤ B) :
    ∃ C₃ C₂ : ℝ, 0 ≤ C₃ ∧ 0 ≤ C₂ ∧ ∀ n : ℕ,
      ∫⁻ ω, ENNReal.ofReal (lenObs ξ (phiMN W P 0 n) (rectAB 3 1) ω) ∂P ≤
        ENNReal.ofReal (C₃ * lambdaN ξ W P n) ∧
      ∫⁻ ω, ENNReal.ofReal (lenN ξ W P 1 1 n ω ^ 2) ∂P ≤
        ENNReal.ofReal (C₂ * lambdaN ξ W P n ^ 2) := by
  obtain ⟨C₃, h1⟩ := s6_moment_L31 hW hξ hΛ 1 le_rfl
  obtain ⟨C₂, h2⟩ := s6_moment_L31 hW hξ hΛ 2 (by norm_num)
  have hl := fun n => (lambdaN_pos (ξ := ξ) hW n)
  refine ⟨max C₃ 0, max C₂ 0, le_max_right _ _, le_max_right _ _, fun n => ⟨?_, ?_⟩⟩
  · obtain ⟨hi, hb⟩ := h1 n
    simp only [pow_one] at hi hb
    rw [← ofReal_integral_eq_lintegral_ofReal hi (ae_of_all _ fun ω => ENNReal.toReal_nonneg)]
    refine ENNReal.ofReal_le_ofReal (hb.trans ?_)
    exact mul_le_mul_of_nonneg_right (le_max_left _ _) (hl n).le
  · obtain ⟨hi, hb⟩ := h2 n
    have hφ := isPhiVersion_phiMN hW (Nat.zero_le n)
    calc ∫⁻ ω, ENNReal.ofReal (lenN ξ W P 1 1 n ω ^ 2) ∂P
        ≤ ∫⁻ ω, ENNReal.ofReal (lenObs ξ (phiMN W P 0 n) (rectAB 3 1) ω ^ 2) ∂P := by
          refine lintegral_mono fun ω => ENNReal.ofReal_le_ofReal ?_
          have h := T20B.lenObs_11_le_31 (ξ := ξ) hφ.cont ω
          have h0 : 0 ≤ lenN ξ W P 1 1 n ω := ENNReal.toReal_nonneg
          exact pow_le_pow_left₀ h0 h 2
      _ = ENNReal.ofReal (∫ ω, lenObs ξ (phiMN W P 0 n) (rectAB 3 1) ω ^ 2 ∂P) :=
          (ofReal_integral_eq_lintegral_ofReal hi (ae_of_all _ fun ω => by positivity)).symm
      _ ≤ _ := ENNReal.ofReal_le_ofReal (hb.trans
          (mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity)))

/-- `xy ≤ θx²/2 + y²/(2θ)` -/
lemma mul_le_amgm {x y θ : ℝ} (hθ : 0 < θ) : x * y ≤ θ / 2 * x ^ 2 + 1 / (2 * θ) * y ^ 2 := by
  have h : θ / 2 * x ^ 2 + 1 / (2 * θ) * y ^ 2 - x * y = (θ * x - y) ^ 2 / (2 * θ) := by
    field_simp; ring
  have : 0 ≤ (θ * x - y) ^ 2 / (2 * θ) := by positivity
  linarith

/-- a crossing-length functional of `G` is `σ(G)`-measurable -/
lemma measurable_comap_sum_mrect {Ω' : Type*} (G : Ω' → ℂ → ℝ) (hGc : ∀ ω, Continuous (G ω))
    (J : Finset (Circle × ℂ)) (k : ℕ) :
    Measurable[MeasurableSpace.comap G inferInstance]
      (fun ω => ∑ j ∈ J, T20B.mrectLen ξ (G ω) k j.1 j.2 3 1) := by
  letI : MeasurableSpace Ω' := MeasurableSpace.comap G inferInstance
  have hm : ∀ x, Measurable fun ω => G ω x :=
    fun x => (measurable_pi_apply x).comp (comap_measurable G)
  refine Finset.measurable_sum _ fun j _ => ?_
  exact (measurable_crossLenIn (Y := fun x ω => G ω x)
    ((rectAB 3 1).isCompact_toSet.image (by unfold T20B.mot; fun_prop)) hGc hm).ennreal_toReal

end S6U

/-- **DDDF Prop 26, Step 1** (l. 1283–1309): from the pathwise circuit bound and `Λ_∞ < ∞`,
`λ_{n+k} ≤ e^{C√k} λ_n λ_k` for all `n, k ≥ 1`. -/
theorem s6_eq5_76_up (hW : IsWhiteNoise P W) (hξ : 0 < ξ)
    (hΛ : ∃ p₀ : ℝ, 0 < p₀ ∧ ∀ p : ℝ, 0 < p → p ≤ p₀ →
      ∃ B : ℝ, ∀ n, LambdaN ξ W P n (ENNReal.ofReal p) ≤ B)
    (h98 : S6Eq6_98 ξ W P) (hC : S6Step1Circ ξ W P) : S6Eq5_76Up ξ W P := by
  have hP := hW.isProbabilityMeasure
  obtain ⟨C₁, hC₁, hcirc⟩ := hC
  obtain ⟨C₃, C₂, hC₃, hC₂, hmom⟩ := S6U.lintegral_moments hW hξ hΛ
  obtain ⟨c, K, hc, hK, hO⟩ := S6U.obig_expMoment (a := 2 * C₁) (by positivity)
  set D : ℝ := 3 * C₁ ^ 2 * C₃ * (25 * K + C₂)
  have hD : 0 ≤ D := by positivity
  obtain ⟨C98, hC98⟩ := h98
  set Cb := |C98| + |Real.log (lambdaN ξ W P 1)|
  refine ⟨max (c + Real.log (D + 1)) Cb, fun n k hn hk => ?_⟩
  rcases (show k = 1 ∨ 2 ≤ k by omega) with rfl | hk2
  · -- `k = 1`: (6.98) with `r = 1` (DDDF l. 1608–1612; own bookkeeping for small `k`)
    have hl0 := lambdaN_pos (ξ := ξ) hW n
    have hl1 := lambdaN_pos (ξ := ξ) hW 1
    have h1 := (hC98 n 1 zero_le_one le_rfl).2
    have e : lambdaDelta ξ W P ((2 : ℝ) ^ (-((n : ℝ) + 1))) = lambdaN ξ W P (n + 1) := by
      rw [← lamT_nat (ξ := ξ) (W := W) (P := P) (n + 1)]
      simp only [lamT]; push_cast; ring_nf
    rw [e] at h1
    have hs1 : √((1 : ℕ) : ℝ) = 1 := by simp
    rw [hs1, mul_one]
    have hb : Real.exp C98 ≤ Real.exp (max (c + Real.log (D + 1)) Cb) * lambdaN ξ W P 1 := by
      have : Real.exp C98 = Real.exp (C98 + -Real.log (lambdaN ξ W P 1)) * lambdaN ξ W P 1 := by
        rw [Real.exp_add, Real.exp_neg, Real.exp_log hl1]; field_simp
      rw [this]
      gcongr
      exact (add_le_add (le_abs_self _) (neg_le_abs _)).trans (le_max_right _ _)
    calc lambdaN ξ W P (n + 1) ≤ Real.exp C98 * lambdaN ξ W P n := h1
      _ ≤ (Real.exp (max (c + Real.log (D + 1)) Cb) * lambdaN ξ W P 1) * lambdaN ξ W P n := by
          gcongr
      _ = _ := by ring
  refine le_trans ?_ (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
    (Real.exp_le_exp.2 (mul_le_mul_of_nonneg_right (le_max_left _ Cb) (Real.sqrt_nonneg _)))
    (lambdaN_pos (ξ := ξ) hW n).le) (lambdaN_pos (ξ := ξ) hW k).le)
  have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hsk : 1 ≤ √(k : ℝ) := Real.one_le_sqrt.2 hk1
  set s := √(k : ℝ)
  have hln := lambdaN_pos (ξ := ξ) hW n
  have hlk := lambdaN_pos (ξ := ξ) hW k
  obtain ⟨I, J, V, hJ, hVm, hV0, hpath⟩ := hcirc k n hk2 hn
  obtain ⟨Y, -, hYa, -, hYc, -⟩ := exists_C1_modification_phi hW (a := ((2 : ℝ) ^ k)⁻¹) (b := 1)
    (by positivity) (inv_le_one_of_one_le₀ (one_le_pow₀ (by norm_num)))
  have hH := hpath Y hYa hYc
  -- the fields and their independence
  set F : Ω → ℂ → ℝ := fun ω x => phiMN W P 0 k x ω
  set G : Ω → ℂ → ℝ := fun ω x => phiMN W P k (n + k) x ω
  have hφF := isPhiVersion_phiMN hW (Nat.zero_le k)
  have hφG := isPhiVersion_phiMN hW (show k ≤ n + k by omega)
  have hFm : Measurable F := measurable_pi_iff.2 fun x => hφF.meas x
  have hGm : Measurable G := measurable_pi_iff.2 fun x => hφG.meas x
  have hGF : IndepFun G F P :=
    indepFun_phi_version hW (a := (2 : ℝ)⁻¹ ^ (n + k)) (b := (2 : ℝ)⁻¹ ^ k)
      (c := (2 : ℝ)⁻¹ ^ 0) (by positivity)
      (pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)) hφG.meas hφF.meas
      hφG.ae_eq hφF.ae_eq
  have hind : Indep (MeasurableSpace.comap F inferInstance) (MeasurableSpace.comap G inferInstance)
      P := (IndepFun_iff_Indep F G P).1 hGF.symm
  -- the circuit sums are `φ_{k,n+k}`-measurable
  set S : ℤ × ℤ → Ω → ℝ := fun b ω => ∑ j ∈ J b,
    T20B.mrectLen ξ (fun x => phiMN W P k (n + k) x ω) k j.1 j.2 3 1
  have hS0 : ∀ b ω, 0 ≤ S b ω := fun b ω =>
    Finset.sum_nonneg fun j _ => ENNReal.toReal_nonneg
  have hSm : ∀ b, Measurable[MeasurableSpace.comap G inferInstance] (S b) := fun b =>
    S6U.measurable_comap_sum_mrect (ξ := ξ) G (fun ω => hφG.cont ω) (J b) k
  have hES : ∀ b ∈ I, ∫⁻ ω, ENNReal.ofReal (S b ω) ∂P ≤
      ENNReal.ofReal (C₁ * (2 : ℝ)⁻¹ ^ k * (C₃ * lambdaN ξ W P n)) := by
    intro b hb
    have hsum : ∫⁻ ω, ENNReal.ofReal (S b ω) ∂P = ∑ j ∈ J b, ENNReal.ofReal ((2 : ℝ)⁻¹ ^ k) *
        ∫⁻ ω, ENNReal.ofReal (lenObs ξ (phiMN W P 0 n) (rectAB 3 1) ω) ∂P := by
      have e : ∀ ω, ENNReal.ofReal (S b ω) = ∑ j ∈ J b, ENNReal.ofReal
          (T20B.mrectLen ξ (fun x => phiMN W P k (n + k) x ω) k j.1 j.2 3 1) := fun ω =>
        ENNReal.ofReal_sum_of_nonneg (fun j _ => ENNReal.toReal_nonneg)
      simp_rw [e]
      rw [lintegral_finsetSum _ fun j _ =>
        (T20B.measurable_mrectLen (ξ := ξ) hW (show k ≤ n + k by omega) j.1 j.2 3 1).ennreal_ofReal]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [S6U.lintegral_mrectLen hW (show k ≤ n + k by omega), Nat.add_sub_cancel]
    rw [hsum, Finset.sum_const, nsmul_eq_mul]
    calc ((J b).card : ℝ≥0∞) * (ENNReal.ofReal ((2 : ℝ)⁻¹ ^ k) *
          ∫⁻ ω, ENNReal.ofReal (lenObs ξ (phiMN W P 0 n) (rectAB 3 1) ω) ∂P)
        ≤ ENNReal.ofReal C₁ * (ENNReal.ofReal ((2 : ℝ)⁻¹ ^ k) *
            ENNReal.ofReal (C₃ * lambdaN ξ W P n)) := by
          gcongr
          · rw [← ENNReal.ofReal_natCast]; exact ENNReal.ofReal_le_ofReal (hJ b hb)
          · exact (hmom n).1
      _ = _ := by
          rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul hC₁.le, mul_assoc]
  -- the `φ_{0,k}` side: `E Σ V ≤ C₁ 2^k E[e^{C₁ O} L^{(k)}]`, AM-GM
  set θ : ℝ := lambdaN ξ W P k * Real.exp (-(c * s))
  have hθ : 0 < θ := by positivity
  set A : ℝ := 25 * K * Real.exp (c * s)
  have hLk : Measurable (lenN ξ W P 1 1 k) := measurable_lenMN (ξ := ξ) hW 1 1 (Nat.zero_le k)
  have hEV : ∫⁻ ω, ∑ b ∈ I, ENNReal.ofReal (V b ω) ∂P ≤
      ENNReal.ofReal (C₁ * (2 : ℝ) ^ k * (θ / 2 * A + 1 / (2 * θ) *
        (C₂ * lambdaN ξ W P k ^ 2))) := by
    have hpt : ∀ᵐ ω ∂P, ∑ b ∈ I, ENNReal.ofReal (V b ω) ≤
        ENNReal.ofReal (C₁ * (2 : ℝ) ^ k * (θ / 2)) *
          ENNReal.ofReal (Real.exp (2 * C₁ * Obig k Y ω)) +
        ENNReal.ofReal (C₁ * (2 : ℝ) ^ k * (1 / (2 * θ))) *
          ENNReal.ofReal (lenN ξ W P 1 1 k ω ^ 2) := by
      filter_upwards [hH] with ω hω
      rw [← ENNReal.ofReal_sum_of_nonneg (fun b hb => hV0 b hb ω),
        ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity),
        ← ENNReal.ofReal_add (by positivity) (by positivity)]
      refine ENNReal.ofReal_le_ofReal (hω.2.trans ?_)
      have hL0 : 0 ≤ lenN ξ W P 1 1 k ω := ENNReal.toReal_nonneg
      have h2 : Real.exp (2 * C₁ * Obig k Y ω) = Real.exp (C₁ * Obig k Y ω) ^ 2 := by
        rw [← Real.exp_nat_mul]; ring_nf
      have := S6U.mul_le_amgm (x := Real.exp (C₁ * Obig k Y ω)) (y := lenN ξ W P 1 1 k ω) hθ
      have h2k : (0 : ℝ) ≤ C₁ * 2 ^ k := by positivity
      rw [h2]
      calc C₁ * 2 ^ k * Real.exp (C₁ * Obig k Y ω) * lenN ξ W P 1 1 k ω
          = C₁ * 2 ^ k * (Real.exp (C₁ * Obig k Y ω) * lenN ξ W P 1 1 k ω) := by ring
        _ ≤ C₁ * 2 ^ k * (θ / 2 * Real.exp (C₁ * Obig k Y ω) ^ 2 +
              1 / (2 * θ) * lenN ξ W P 1 1 k ω ^ 2) := mul_le_mul_of_nonneg_left this h2k
        _ = _ := by ring
    refine (lintegral_mono_ae hpt).trans ?_
    rw [lintegral_add_right' _ ((hLk.pow_const 2).ennreal_ofReal.aemeasurable.const_mul _),
      lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    calc ENNReal.ofReal (C₁ * 2 ^ k * (θ / 2)) *
          ∫⁻ ω, ENNReal.ofReal (Real.exp (2 * C₁ * Obig k Y ω)) ∂P +
        ENNReal.ofReal (C₁ * 2 ^ k * (1 / (2 * θ))) *
          ∫⁻ ω, ENNReal.ofReal (lenN ξ W P 1 1 k ω ^ 2) ∂P
        ≤ ENNReal.ofReal (C₁ * 2 ^ k * (θ / 2)) * ENNReal.ofReal A +
          ENNReal.ofReal (C₁ * 2 ^ k * (1 / (2 * θ))) *
            ENNReal.ofReal (C₂ * lambdaN ξ W P k ^ 2) := by
          gcongr
          · exact hO hW k hk Y hYa hYc
          · exact (hmom k).2
      _ = _ := by
          rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity),
            ← ENNReal.ofReal_add (by positivity) (by positivity)]
          congr 1; ring
  -- the mean of `L^{(n+k)}_{1,1}`
  have hVm' : ∀ b ∈ I, Measurable (V b) := fun b hb =>
    (hVm b hb).mono hFm.comap_le le_rfl
  have hE : ∫⁻ ω, ENNReal.ofReal (lenN ξ W P 1 1 (n + k) ω) ∂P ≤
      ENNReal.ofReal (C₁ * (2 : ℝ) ^ k * (θ / 2 * A + 1 / (2 * θ) *
        (C₂ * lambdaN ξ W P k ^ 2))) *
      ENNReal.ofReal (C₁ * (2 : ℝ)⁻¹ ^ k * (C₃ * lambdaN ξ W P n)) := by
    have hpt : ∀ᵐ ω ∂P, ENNReal.ofReal (lenN ξ W P 1 1 (n + k) ω) ≤
        ∑ b ∈ I, ENNReal.ofReal (V b ω) * ENNReal.ofReal (S b ω) := by
      filter_upwards [hH] with ω hω
      rw [← Finset.sum_congr rfl fun b hb => ENNReal.ofReal_mul (q := S b ω) (hV0 b hb ω),
        ← ENNReal.ofReal_sum_of_nonneg (fun b hb => mul_nonneg (hV0 b hb ω) (hS0 b ω))]
      exact ENNReal.ofReal_le_ofReal hω.1
    refine (lintegral_mono_ae hpt).trans ?_
    rw [lintegral_finsetSum' (f := fun b ω => ENNReal.ofReal (V b ω) * ENNReal.ofReal (S b ω)) _
      fun b hb => by
        exact ((hVm' b hb).ennreal_ofReal.mul
          ((hSm b).mono hGm.comap_le le_rfl).ennreal_ofReal).aemeasurable]
    calc ∑ b ∈ I, ∫⁻ ω, ENNReal.ofReal (V b ω) * ENNReal.ofReal (S b ω) ∂P
        = ∑ b ∈ I, (∫⁻ ω, ENNReal.ofReal (V b ω) ∂P) * ∫⁻ ω, ENNReal.ofReal (S b ω) ∂P := by
          refine Finset.sum_congr rfl fun b hb => ?_
          exact lintegral_mul_eq_lintegral_mul_lintegral_of_independent_measurableSpace
            hFm.comap_le hGm.comap_le hind (hVm b hb).ennreal_ofReal (hSm b).ennreal_ofReal
      _ ≤ ∑ b ∈ I, (∫⁻ ω, ENNReal.ofReal (V b ω) ∂P) *
            ENNReal.ofReal (C₁ * (2 : ℝ)⁻¹ ^ k * (C₃ * lambdaN ξ W P n)) :=
          Finset.sum_le_sum fun b hb => by gcongr; exact hES b hb
      _ = (∫⁻ ω, ∑ b ∈ I, ENNReal.ofReal (V b ω) ∂P) *
            ENNReal.ofReal (C₁ * (2 : ℝ)⁻¹ ^ k * (C₃ * lambdaN ξ W P n)) := by
          rw [← Finset.sum_mul, lintegral_finsetSum _ fun b hb => (hVm' b hb).ennreal_ofReal]
      _ ≤ _ := by gcongr
  rw [← ENNReal.ofReal_mul (by positivity)] at hE
  have hmed := S6U.lowerMedian_le_three (measurable_lenMN (ξ := ξ) hW 1 1 (Nat.zero_le (n + k)))
    (by positivity) hE
  refine hmed.trans ?_
  -- the real algebra
  have h2k : (2 : ℝ) ^ k * (2 : ℝ)⁻¹ ^ k = 1 := by rw [← mul_pow]; norm_num
  have hθA : θ / 2 * A = 25 * K * lambdaN ξ W P k / 2 := by
    simp only [θ, A]
    rw [show lambdaN ξ W P k * Real.exp (-(c * s)) / 2 * (25 * K * Real.exp (c * s)) =
      25 * K * lambdaN ξ W P k / 2 * (Real.exp (-(c * s)) * Real.exp (c * s)) by ring,
      ← Real.exp_add, neg_add_cancel, Real.exp_zero, mul_one]
  have hθB : 1 / (2 * θ) * (C₂ * lambdaN ξ W P k ^ 2) =
      C₂ * lambdaN ξ W P k * Real.exp (c * s) / 2 := by
    simp only [θ]
    rw [Real.exp_neg]
    field_simp
  rw [hθA, hθB]
  have he1 : 1 ≤ Real.exp (c * s) := Real.one_le_exp (by positivity)
  have hbound : 3 * (C₁ * 2 ^ k * (25 * K * lambdaN ξ W P k / 2 +
      C₂ * lambdaN ξ W P k * Real.exp (c * s) / 2) *
      (C₁ * 2⁻¹ ^ k * (C₃ * lambdaN ξ W P n))) ≤
      D * Real.exp (c * s) * lambdaN ξ W P n * lambdaN ξ W P k := by
    have e : 3 * (C₁ * 2 ^ k * (25 * K * lambdaN ξ W P k / 2 +
        C₂ * lambdaN ξ W P k * Real.exp (c * s) / 2) *
        (C₁ * 2⁻¹ ^ k * (C₃ * lambdaN ξ W P n))) =
        3 * C₁ ^ 2 * C₃ * ((2 : ℝ) ^ k * (2 : ℝ)⁻¹ ^ k) *
          (25 * K + C₂ * Real.exp (c * s)) / 2 * lambdaN ξ W P n * lambdaN ξ W P k := by ring
    rw [e, h2k, mul_one]
    have h25 : 25 * K + C₂ * Real.exp (c * s) ≤ (25 * K + C₂) * Real.exp (c * s) := by
      nlinarith
    have hpos : 0 ≤ 3 * C₁ ^ 2 * C₃ := by positivity
    have : 3 * C₁ ^ 2 * C₃ * (25 * K + C₂ * Real.exp (c * s)) / 2 ≤ D * Real.exp (c * s) := by
      simp only [D]
      have := mul_le_mul_of_nonneg_left h25 hpos
      have h0 : 0 ≤ 3 * C₁ ^ 2 * C₃ * (25 * K + C₂ * Real.exp (c * s)) := by positivity
      nlinarith
    gcongr
  refine hbound.trans ?_
  have hD1 : D ≤ Real.exp (Real.log (D + 1) * s) := by
    have hl0 : 0 ≤ Real.log (D + 1) := Real.log_nonneg (by linarith)
    calc D ≤ D + 1 := by linarith
      _ = Real.exp (Real.log (D + 1)) := (Real.exp_log (by linarith)).symm
      _ ≤ _ := Real.exp_le_exp.2 (le_mul_of_one_le_right hl0 hsk)
  have : D * Real.exp (c * s) ≤ Real.exp ((c + Real.log (D + 1)) * s) := by
    rw [add_mul, Real.exp_add, mul_comm D]
    exact mul_le_mul_of_nonneg_left hD1 (Real.exp_pos _).le
  gcongr

end DDDF
end LQGMetric
