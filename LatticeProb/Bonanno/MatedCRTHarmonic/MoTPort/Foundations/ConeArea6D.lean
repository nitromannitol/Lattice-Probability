/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module MatedCRTHarmonic.MoTPort.Foundations.ConeArea6D at commit fdb5cad; only the module paths of local imports are changed.
   Declarations, examples and checks that the copied results do not use are omitted. -/
/- Provenance: ported from an earlier mating-of-trees formalization; only imports and namespace names were changed. -/
import LatticeProb.Bonanno.MatedCRTHarmonic.MoTPort.Foundations.ConeArea6C
import LatticeProb.Bonanno.MatedCRTHarmonic.MoTPort.Foundations.ConeArea5C

/-!
For a whole-plane GFF `X`, `S = B̄(0, 2^{-n})`, `δ = 4·2^{-n}` (`n ≥ 2`) and the circle-average
increment `Ω_δ = h_δ(0) − h_1(0)` (centred Gaussian, variance `−log δ`):

* pathwise (`ofReal_mul_annTC_eq`):
  `e^{−γ h_1(0)} sup_{k ≥ n} μ_{2^{-k}}(S) = e^{γΩ_δ} δ^{γ²/2} · sup_m W_{n+m}(S)` with
  `W_k = massU γ S δ k (wpU X δ)` (ConeArea6/6C);
* `E (e^{γΩ_δ}δ^{γ²/2})^q = δ^{qγ²/2} e^{(−log δ)(qγ)²/2}` (`lintegral_gaussFactor_rpow`, copied
  from QZ `AreaP3b.lintegral_omZ_factor_rpow`);
* `E (sup_m W_{n+m})^q ≤ (|S|)^q + (cRate·δ²)^q (1−r)⁻¹` for `q ≤ 1` (ConeArea6B, with `K = 0`
  from `levelHyp_wpU`).

QZ combines the last two by independence of `Ω_δ` and the inner field. Here we combine them by the
Cauchy–Schwarz inequality instead (mathlib `ENNReal.lintegral_mul_le_Lp_mul_Lq` with exponents
`2, 2`), which avoids measurability questions for functionals of the whole inner field and costs
a factor `2` in the quadratic term of the exponent:

  **`wpSupMomentH`**: `E (e^{−γh_1(0)} sup_{k≥n} μ_{2^{-k}}(B̄(0,2^{-n})))^p ≤
  C 2^{n(γ²p² − p(2+γ²/2))}` for `0 < p ≤ 1/2`, `n ≥ 2`

(instead of `γ²p²/2` in `ConeArea5.WPSupMoment`). This is enough downstream: only small `p` are
used (ConeArea6E). Source: Duplantier–Sheffield, Invent. Math. 185 (2011), §3.2, (14)–(15), and
the QZ chain named above; the Cauchy–Schwarz step is a deviation from QZ's independence step.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Real Set Metric
open scoped NNReal ENNReal

namespace MatedCRTHarmonic.MoTPort
namespace ConeArea6

open QuantumZipper TwoRadiusC AreaP3b LQGMetric LQGMetric.CircleAvg

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}

/-- **The `q`-th moment of a lognormal factor** (copied from QZ
`AreaP3b.lintegral_omZ_factor_rpow`, for any centred Gaussian `Y` of variance `log D − log δ`). -/
theorem lintegral_gaussFactor_rpow {Y : Ω → ℝ} (γ : ℝ) {δ D q : ℝ} (hδ : 0 < δ) (hδD : δ ≤ D)
    (hq : 0 ≤ q) (hL : HasLaw Y (gaussianReal 0 (log D - log δ).toNNReal) P) :
    ∫⁻ ω, ENNReal.ofReal (exp (γ * Y ω) * δ ^ (γ ^ 2 / 2)) ^ q ∂P =
      ENNReal.ofReal (δ ^ (q * (γ ^ 2 / 2)) * exp ((log D - log δ) * (q * γ) ^ 2 / 2)) := by
  have hv : ((log D - log δ).toNNReal : ℝ) = log D - log δ :=
    Real.coe_toNNReal _ (sub_nonneg.mpr (log_le_log hδ hδD))
  have hreal : ∀ ω, exp (γ * Y ω) ^ q * (δ ^ (γ ^ 2 / 2)) ^ q =
      δ ^ (q * (γ ^ 2 / 2)) * exp (q * γ * Y ω) := by
    intro ω
    rw [← exp_mul, ← rpow_mul hδ.le]
    ring
  have hpt : ∀ ω, ENNReal.ofReal (exp (γ * Y ω) * δ ^ (γ ^ 2 / 2)) ^ q =
      ENNReal.ofReal (δ ^ (q * (γ ^ 2 / 2)) * exp (q * γ * Y ω)) := by
    intro ω
    rw [ENNReal.ofReal_rpow_of_nonneg (by positivity) hq,
      Real.mul_rpow (exp_pos _).le (rpow_pos_of_pos hδ _).le]
    exact congrArg ENNReal.ofReal (hreal ω)
  simp_rw [hpt]
  have hint : Integrable (fun ω => exp (0 + q * γ * Y ω)) P :=
    hL.integrable_comp (TwoRadius.integrable_exp_mul_add_gaussianReal _ (q * γ) 0)
  simp only [zero_add] at hint
  rw [← ofReal_integral_eq_lintegral_ofReal (hint.const_mul _)
    (ae_of_all _ fun ω => by simp only [Pi.zero_apply]; positivity), integral_const_mul]
  have h2 : ∫ x, exp (q * γ * x) ∂(gaussianReal 0 (log D - log δ).toNNReal) =
      exp (((log D - log δ).toNNReal : ℝ) * (q * γ) ^ 2 / 2) := by
    simpa only [zero_add] using
      TwoRadius.integral_exp_mul_add_gaussianReal (log D - log δ).toNNReal (q * γ) 0
  rw [show ∫ ω, exp (q * γ * Y ω) ∂P = exp ((log D - log δ) * (q * γ) ^ 2 / 2) by
    have hc := hL.integral_comp (f := fun x => exp (q * γ * x)) (by fun_prop)
    simp only [Function.comp_apply] at hc
    rw [hc, h2, hv]]

variable {X : Ω → Field}

/-- law of `Ω_δ = h_δ(0) − h_1(0)` for `0 < δ ≤ 1` -/
theorem hasLaw_cInc_center (hX : IsWholePlaneGFF X P) {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1) :
    HasLaw (cInc X δ 0 1 0) (gaussianReal 0 (log 1 - log δ).toNNReal) P := by
  refine ⟨(measurable_cInc hX _ _ _ _).aemeasurable, ?_⟩
  rw [(map_cInc hX hδ one_pos 0 0).1]
  congr 2
  simp only [incCov]
  rw [circCov_same hδ hδ, circCov_same hδ one_pos, circCov_same one_pos hδ,
    circCov_same one_pos one_pos, max_self, max_self, max_eq_left hδ1, max_eq_right hδ1]
  ring

omit [MeasurableSpace Ω] in
/-- **pathwise factorization** of the normalized area approximation of `S ⊆ B(0, δ)` -/
theorem ofReal_mul_areaApproxC_eq (γ : ℝ) {δ : ℝ} (hδ : 0 < δ) {S : Set ℂ}
    (hS : MeasurableSet S) (k : ℕ) (ω : Ω) :
    ENNReal.ofReal (exp (-(γ * circleAvg (X ω) 1 0))) * areaApproxC γ (X ω) k S =
      ENNReal.ofReal (exp (γ * cInc X δ 0 1 0 ω) * δ ^ (γ ^ 2 / 2)) *
        massU γ S δ k (wpU X δ) ω := by
  have hr := QuantumZipper.radius_pos k
  rw [areaApproxC, withDensity_apply _ hS, massU, ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
    ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  refine lintegral_congr fun t => ?_
  rw [← ENNReal.ofReal_mul (exp_pos _).le, ← ENNReal.ofReal_mul (by positivity)]
  congr 1
  simp only [wpU, cInc, wDensU]
  rw [div_rpow hr.le hδ.le]
  have hδa : δ ^ (γ ^ 2 / 2) ≠ 0 := (rpow_pos_of_pos hδ _).ne'
  have e : exp (-(γ * circleAvg (X ω) 1 0)) * exp (γ * circleAvg (X ω) (radius k) t) =
      exp (γ * (circleAvg (X ω) δ 0 - circleAvg (X ω) 1 0)) *
        exp (γ * (circleAvg (X ω) (radius k) t - circleAvg (X ω) δ 0)) := by
    rw [← exp_add, ← exp_add]; ring_nf
  field_simp
  linear_combination e

/-- **weak (Cauchy–Schwarz) form of `ConeArea5.WPSupMoment`**: quadratic exponent `γ²p²` instead
of `γ²p²/2`, for `0 < p ≤ 1/2` -/
def WPSupMomentH (γ : ℝ) : Prop :=
  ∀ (Ω : Type) (_ : MeasurableSpace Ω) (P : Measure Ω) (X : Ω → Field),
    IsProbabilityMeasure P → IsWholePlaneGFF X P →
    ∀ p : ℝ, 0 < p → p ≤ 1 / 2 → ∃ C : ℝ≥0∞, C ≠ ⊤ ∧ ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n →
      ∫⁻ ω, (ENNReal.ofReal (Real.exp (-(γ * circleAvg (X ω) 1 0))) *
          AtomlessUncond.annTC (areaApproxC γ (X ω)) 0 n) ^ p ∂P ≤
        C * ENNReal.ofReal ((2 : ℝ) ^ ((n : ℝ) * (γ ^ 2 * p ^ 2 - p * (2 + γ ^ 2 / 2))))

/-- **the whole-plane sup-moment bound** (Cauchy–Schwarz form), for `0 < γ < 2` -/
theorem wpSupMomentH {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) : WPSupMomentH γ := by
  intro Ω _ P X _ hX p hp0 hp1
  have hq0 : 0 < 2 * p := by positivity
  have hq1 : 2 * p ≤ 1 := by linarith
  set β : ℝ := min (2 - γ ^ 2 + (max 0 ((3 * γ - 2) / 2)) ^ 2 / 2) ((2 - γ) ^ 2 / 4) with hβ
  set ρ : ℝ := exp (-(2 * p * β) * (1 / 2 * log 2)) with hρ
  set Cst : ℝ := cRate γ 0 (π / 16) with hCst
  set Ctot : ℝ := (1 : ℝ) ^ ((2 * p * γ) ^ 2 / 2) * (exp (γ ^ 2 / 2 * 0) * (π / 16)) ^ (2 * p) *
        (4 : ℝ) ^ (2 * p * (γ ^ 2 / 2) + 2 * (2 * p) - (2 * p * γ) ^ 2 / 2) +
      (1 : ℝ) ^ ((2 * p * γ) ^ 2 / 2) * Cst ^ (2 * p) * (1 - ρ)⁻¹ *
        (4 : ℝ) ^ (2 * p * (γ ^ 2 / 2) + 2 * (2 * p) - (2 * p * γ) ^ 2 / 2) with hCtot
  have hβ0 : 0 < β := lt_min (areaRateExp_pos hγ hγ2) (by nlinarith)
  have hρ1 : ρ < 1 := by
    rw [hρ, Real.exp_lt_one_iff]
    have := mul_pos (mul_pos hq0 hβ0) (mul_pos (by norm_num : (0 : ℝ) < 1 / 2)
      (log_pos one_lt_two))
    linarith
  have hρ0 : 0 ≤ ρ := (exp_pos _).le
  have hCst0 : 0 ≤ Cst := cRate_nonneg (by positivity)
  have hinv : 0 ≤ (1 - ρ)⁻¹ := inv_nonneg.2 (by linarith)
  refine ⟨ENNReal.ofReal (Ctot ^ (1 / 2 : ℝ)), ENNReal.ofReal_ne_top, 2, fun n hn => ?_⟩
  have hr : 0 < radius n := QuantumZipper.radius_pos n
  have hrn : radius n ≤ 1 / 4 := by
    have : radius n ≤ radius 2 := by
      rw [radius, radius]; exact pow_le_pow_of_le_one (by norm_num) (by norm_num) hn
    exact this.trans (le_of_eq (by rw [radius]; norm_num))
  have hδ : 0 < 4 * radius n := by positivity
  have hδ1 : 4 * radius n ≤ 1 := by linarith
  have hS : MeasurableSet (AtomlessUncond.annIC 0 n) := by
    rw [AtomlessUncond.annIC]; exact isClosed_closedBall.measurableSet
  have hSf : volume (AtomlessUncond.annIC 0 n) < ∞ := by
    rw [AtomlessUncond.annIC, Complex.volume_closedBall]
    exact ENNReal.mul_lt_top (ENNReal.pow_lt_top ENNReal.ofReal_lt_top) (by simp)
  have hSle : volume.real (AtomlessUncond.annIC 0 n) ≤ π / 16 * (4 * radius n) ^ 2 := by
    rw [volumeReal_annIC]; exact le_of_eq (by ring)
  have hlev : ∀ m, LevelHyp P (AtomlessUncond.annIC 0 n) (4 * radius n) 0
      (wpU X (4 * radius n)) (n + m) := by
    intro m
    have hm : radius (n + m) ≤ radius n := by
      rw [radius, radius]; exact pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)
    refine levelHyp_wpU hX (fun t ht => ?_) (by linarith)
    rw [AtomlessUncond.annIC, mem_closedBall, dist_zero_right] at ht
    linarith
  -- the factorization
  set A : Ω → ℝ≥0∞ := fun ω =>
    ENNReal.ofReal (exp (γ * cInc X (4 * radius n) 0 1 0 ω) * (4 * radius n) ^ (γ ^ 2 / 2))
    with hA
  set M : Ω → ℝ≥0∞ := fun ω => ⨆ m, massU γ (AtomlessUncond.annIC 0 n) (4 * radius n) (n + m)
    (wpU X (4 * radius n)) ω with hM
  have hfac : ∀ ω, ENNReal.ofReal (exp (-(γ * circleAvg (X ω) 1 0))) *
      AtomlessUncond.annTC (areaApproxC γ (X ω)) 0 n = A ω * M ω := by
    intro ω
    rw [AtomlessUncond.annTC, ENNReal.mul_iSup, hA, hM, ENNReal.mul_iSup]
    refine iSup_congr fun j => ?_
    rw [ofReal_mul_areaApproxC_eq γ hδ hS (j + n) ω, Nat.add_comm j n]
  have hAm : Measurable A := ENNReal.measurable_ofReal.comp
    ((((measurable_cInc hX _ _ _ _).const_mul γ).exp).mul_const _)
  have hMm : Measurable M := Measurable.iSup fun m =>
    measurable_massU γ _ _ (n + m) (measurable_wpU hX _ (n + m))
  -- Cauchy–Schwarz
  have hCS : ∫⁻ ω, (A ω * M ω) ^ p ∂P ≤
      (∫⁻ ω, A ω ^ (2 * p) ∂P) ^ (1 / 2 : ℝ) * (∫⁻ ω, M ω ^ (2 * p) ∂P) ^ (1 / 2 : ℝ) := by
    have h := ENNReal.lintegral_mul_le_Lp_mul_Lq P Real.HolderConjugate.two_two
      (hAm.pow_const p).aemeasurable (hMm.pow_const p).aemeasurable
    have e2 : ∀ x : ℝ≥0∞, (x ^ p) ^ (2 : ℝ) = x ^ (2 * p) := fun x => by
      rw [← ENNReal.rpow_mul, mul_comm]
    calc ∫⁻ ω, (A ω * M ω) ^ p ∂P
        = ∫⁻ ω, ((fun ω => A ω ^ p) * fun ω => M ω ^ p) ω ∂P :=
          lintegral_congr fun ω => ENNReal.mul_rpow_of_nonneg _ _ hp0.le
      _ ≤ _ := h
      _ = _ := by simp only [e2]
  have hAint := lintegral_gaussFactor_rpow (P := P) γ hδ hδ1 hq0.le (hasLaw_cInc_center hX hδ hδ1)
  have hMint := lintegral_iSup_massU_rpow_le hγ hγ2 hδ hS hSf (by positivity) hSle hq0 hq1 hlev
  set a1 : ℝ := (4 * radius n) ^ (2 * p * (γ ^ 2 / 2)) *
    exp ((log 1 - log (4 * radius n)) * (2 * p * γ) ^ 2 / 2) with ha1
  set a2 : ℝ := (exp (γ ^ 2 / 2 * 0) * (π * radius n ^ 2)) ^ (2 * p) +
    (Cst * (4 * radius n) ^ 2) ^ (2 * p) * (1 - ρ)⁻¹ with ha2
  have ha10 : 0 ≤ a1 := by positivity
  have ha20 : 0 ≤ a2 := add_nonneg (by positivity)
    (mul_nonneg (rpow_nonneg (by positivity) _) hinv)
  have hM' : ∫⁻ ω, M ω ^ (2 * p) ∂P ≤ ENNReal.ofReal a2 := by
    refine hMint.trans (le_of_eq ?_)
    have hqsub : (1 : ℝ≥0∞) - ENNReal.ofReal ρ = ENNReal.ofReal (1 - ρ) := by
      rw [ENNReal.ofReal_sub _ hρ0, ENNReal.ofReal_one]
    rw [volumeReal_annIC, ENNReal.ofReal_rpow_of_nonneg (by positivity) hq0.le, ← hρ, hqsub,
      ← ENNReal.ofReal_inv_of_pos (by linarith : (0 : ℝ) < 1 - ρ),
      ← ENNReal.ofReal_mul (rpow_nonneg (by positivity) _),
      ← ENNReal.ofReal_add (by positivity) (mul_nonneg (rpow_nonneg (by positivity) _) hinv)]
  have hprod : a1 * a2 = Ctot * (2 : ℝ) ^ ((n : ℝ) * (γ ^ 2 * (2 * p) ^ 2 / 2 -
      2 * p * (2 + γ ^ 2 / 2))) :=
    u_mul_factor_eq (γ := γ) (p := 2 * p) (D := 1) (K := 0) (Cst := Cst) (q := ρ) one_pos
      hCst0 n
  have h2pos : (0 : ℝ) < (2 : ℝ) ^ ((n : ℝ) * (γ ^ 2 * (2 * p) ^ 2 / 2 -
      2 * p * (2 + γ ^ 2 / 2))) := by positivity
  have hCtot0 : 0 ≤ Ctot :=
    (mul_nonneg_iff_of_pos_right h2pos).1 (hprod ▸ mul_nonneg ha10 ha20)
  calc ∫⁻ ω, (ENNReal.ofReal (Real.exp (-(γ * circleAvg (X ω) 1 0))) *
          AtomlessUncond.annTC (areaApproxC γ (X ω)) 0 n) ^ p ∂P
      = ∫⁻ ω, (A ω * M ω) ^ p ∂P := lintegral_congr fun ω => by rw [hfac ω]
    _ ≤ (∫⁻ ω, A ω ^ (2 * p) ∂P) ^ (1 / 2 : ℝ) * (∫⁻ ω, M ω ^ (2 * p) ∂P) ^ (1 / 2 : ℝ) := hCS
    _ ≤ (ENNReal.ofReal a1) ^ (1 / 2 : ℝ) * (ENNReal.ofReal a2) ^ (1 / 2 : ℝ) := by
        rw [hAint]
        exact mul_le_mul' le_rfl (ENNReal.rpow_le_rpow hM' (by norm_num))
    _ = ENNReal.ofReal (Ctot ^ (1 / 2 : ℝ)) *
        ENNReal.ofReal ((2 : ℝ) ^ ((n : ℝ) * (γ ^ 2 * p ^ 2 - p * (2 + γ ^ 2 / 2)))) := by
        rw [ENNReal.ofReal_rpow_of_nonneg ha10 (by norm_num),
          ENNReal.ofReal_rpow_of_nonneg ha20 (by norm_num), ← ENNReal.ofReal_mul (by positivity),
          ← ENNReal.ofReal_mul (by positivity), ← Real.mul_rpow ha10 ha20, hprod,
          Real.mul_rpow hCtot0 h2pos.le, ← Real.rpow_mul (by norm_num)]
        congr 3
        ring

end ConeArea6
end MatedCRTHarmonic.MoTPort
