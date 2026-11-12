/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module MatedCRTHarmonic.MoTPort.Foundations.ConeArea6B at commit fdb5cad; only the module paths of local imports are changed.
   Declarations, examples and checks that the copied results do not use are omitted. -/
/- Provenance: ported from an earlier mating-of-trees formalization; only imports and namespace names were changed. -/
import LatticeProb.Bonanno.MatedCRTHarmonic.MoTPort.Foundations.ConeArea6

/-!
Copies of QZ `AreaP3b.integral_abs_massFunC_step_le_rate'` and
`AreaP3b.lintegral_iSup_massFunC_inner_rpow_le` (`QuantumZipper/Proofs/LQG/AreaP3bSup.lean`) for
the abstract inner process of `ConeArea6`, with a general constant `K` in place of
`2 log R − log D − log(2d)`; the proofs are unchanged up to that substitution.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Real
open scoped NNReal ENNReal

namespace MatedCRTHarmonic.MoTPort
namespace ConeArea6

open QuantumZipper TwoRadiusC AreaP3b

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {S : Set ℂ} {δ K : ℝ} {U : ℕ → ℂ → Ω → ℝ}

/-- Rate form of the step bound (QZ `integral_abs_massFunC_step_le_rate'`). -/
theorem integral_abs_massU_step_le_rate {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) (hδ : 0 < δ)
    {V : ℝ} (hS : MeasurableSet S) (hSf : volume S < ∞) (hV : 0 ≤ V)
    (hSle : volume.real S ≤ V * δ ^ 2) {k : ℕ} (h : LevelHyp P S δ K U k)
    (h1 : LevelHyp P S δ K U (k + 1)) :
    ∫ ω, |(massU γ S δ k U ω).toReal - (massU γ S δ (k + 1) U ω).toReal| ∂P
      ≤ cRate γ K V * δ ^ 2 *
        exp (-(min (2 - γ ^ 2 + (max 0 ((3 * γ - 2) / 2)) ^ 2 / 2)
            ((2 - γ) ^ 2 / 4)) * (1 / 2 * log (δ / radius k))) := by
  have hr := radius_pos k
  have hlog : 0 ≤ log (δ / radius k) := log_nonneg (by rw [le_div_iff₀ hr]; linarith [h.1])
  have hraw := integral_abs_massU_step_le hγ hγ2 hδ hS hSf h h1
  rw [cRate]
  set θ := max 0 ((3 * γ - 2) / 2) with hθ
  set L := 1 / 2 * log (δ / radius k) with hL
  set P' : ℝ := exp ((2 * γ ^ 2 - θ ^ 2) * L) with hP
  set Q' : ℝ := exp (-((2 - γ) ^ 2 / 4) * L) with hQ
  set B : ℝ := exp ((2 * γ / 2 + (2 - γ) / 2) ^ 2 * K / 2) with hB
  set A₁ : ℝ := (1 + exp ((2 * γ) ^ 2 / 4 * log 2)) * exp ((2 * γ - θ) ^ 2 * K / 2) with hA₁
  set A : ℝ := (1 + exp ((2 * γ) ^ 2 / 4 * log 2)) * (exp ((2 * γ - θ) ^ 2 * K / 2) * P')
    with hA
  set e₁ : ℝ := 2 - γ ^ 2 + θ ^ 2 / 2 with he₁
  set β : ℝ := min e₁ ((2 - γ) ^ 2 / 4) with hβ
  have hA₁c : A₁ = cRateA γ K := by rw [hA₁, cRateA]
  have hBc : B = cRateB γ K := by rw [hB, cRateB]
  rw [neg_mul, ← hA₁c, ← hBc]
  have hL0 : 0 ≤ L := by rw [hL]; linarith
  have hA₁nn : 0 ≤ A₁ := by rw [hA₁]; positivity
  have hBnn : 0 ≤ B := by rw [hB]; positivity
  have hrad : radius k = δ * exp (-(2 * L)) := by
    rw [hL, show (2 : ℝ) * (1 / 2 * log (δ / radius k)) = log (δ / radius k) by ring,
      exp_neg, exp_log (div_pos hδ hr), inv_div]
    field_simp
  have hexp2 : exp (-(2 * L)) ^ 2 = exp (-(4 * L)) := by
    rw [← Real.exp_nat_mul, Real.exp_eq_exp]
    push_cast
    ring
  have hr2 : (2 * radius k) ^ 2 = 4 * δ ^ 2 * exp (-(4 * L)) := by
    rw [hrad, mul_pow, mul_pow, hexp2]
    ring
  have hprod : P' * (2 * radius k) ^ 2 = 4 * δ ^ 2 * exp (-(e₁ * L)) ^ 2 := by
    have h1 : exp ((2 * γ ^ 2 - θ ^ 2) * L) * exp (-(4 * L)) = exp (-(e₁ * L)) ^ 2 := by
      rw [← Real.exp_nat_mul, ← Real.exp_add, Real.exp_eq_exp, he₁]
      ring
    rw [hP, hr2]
    calc exp ((2 * γ ^ 2 - θ ^ 2) * L) * (4 * δ ^ 2 * exp (-(4 * L)))
        = 4 * δ ^ 2 * (exp ((2 * γ ^ 2 - θ ^ 2) * L) * exp (-(4 * L))) := by ring
      _ = 4 * δ ^ 2 * exp (-(e₁ * L)) ^ 2 := by rw [h1]
  have hAP : A = A₁ * P' := by rw [hA, hA₁]; ring
  have hmain : A * (π * (2 * radius k) ^ 2 * volume.real S)
      = π * A₁ * volume.real S * (4 * δ ^ 2 * exp (-(e₁ * L)) ^ 2) := by
    calc A * (π * (2 * radius k) ^ 2 * volume.real S)
        = π * A₁ * volume.real S * (P' * (2 * radius k) ^ 2) := by rw [hAP]; ring
      _ = π * A₁ * volume.real S * (4 * δ ^ 2 * exp (-(e₁ * L)) ^ 2) := by rw [hprod]
  have hsq : π * A₁ * volume.real S * (4 * δ ^ 2 * exp (-(e₁ * L)) ^ 2)
      = (2 * δ * √(π * A₁ * volume.real S) * exp (-(e₁ * L))) ^ 2 := by
    rw [mul_pow, mul_pow, mul_pow,
      Real.sq_sqrt (mul_nonneg (mul_nonneg pi_pos.le hA₁nn) measureReal_nonneg)]
    ring
  have hs : √(π * A₁ * volume.real S) ≤ δ * √(π * A₁ * V) := by
    have hle : π * A₁ * volume.real S ≤ δ ^ 2 * (π * A₁ * V) := by
      calc π * A₁ * volume.real S ≤ π * A₁ * (V * δ ^ 2) :=
            mul_le_mul_of_nonneg_left hSle (mul_nonneg pi_pos.le hA₁nn)
        _ = δ ^ 2 * (π * A₁ * V) := by ring
    calc √(π * A₁ * volume.real S) ≤ √(δ ^ 2 * (π * A₁ * V)) := Real.sqrt_le_sqrt hle
      _ = δ * √(π * A₁ * V) := by
          rw [Real.sqrt_mul (sq_nonneg δ), Real.sqrt_sq hδ.le]
  have he₁β : β ≤ e₁ := by rw [hβ]; exact min_le_left _ _
  have hβγ : β ≤ (2 - γ) ^ 2 / 4 := by rw [hβ]; exact min_le_right _ _
  have hexpβ : exp (-(e₁ * L)) ≤ exp (-(β * L)) := by
    rw [Real.exp_le_exp]
    have h := mul_le_mul_of_nonneg_right he₁β hL0
    linarith
  have hexpQ : Q' ≤ exp (-(β * L)) := by
    rw [hQ, Real.exp_le_exp]
    have h := mul_le_mul_of_nonneg_right hβγ hL0
    linarith
  have hT1 : √(A * (π * (2 * radius k) ^ 2 * volume.real S))
      ≤ 2 * √(π * A₁ * V) * δ ^ 2 * exp (-(β * L)) := by
    calc √(A * (π * (2 * radius k) ^ 2 * volume.real S))
        = √((2 * δ * √(π * A₁ * volume.real S) * exp (-(e₁ * L))) ^ 2) := by
          rw [hmain, hsq]
      _ = 2 * δ * √(π * A₁ * volume.real S) * exp (-(e₁ * L)) :=
          Real.sqrt_sq (mul_nonneg (mul_nonneg (mul_nonneg two_pos.le hδ.le)
            (Real.sqrt_nonneg _)) (exp_pos _).le)
      _ ≤ 2 * δ * (δ * √(π * A₁ * V)) * exp (-(e₁ * L)) :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hs (by positivity))
            (exp_pos _).le
      _ ≤ 2 * δ * (δ * √(π * A₁ * V)) * exp (-(β * L)) :=
          mul_le_mul_of_nonneg_left hexpβ (mul_nonneg (by positivity)
            (mul_nonneg hδ.le (Real.sqrt_nonneg _)))
      _ = 2 * √(π * A₁ * V) * δ ^ 2 * exp (-(β * L)) := by ring
  have hT2 : 2 * (B * Q') * volume.real S ≤ 2 * B * V * δ ^ 2 * exp (-(β * L)) := by
    have hnnR : 0 ≤ 2 * (B * Q') := by rw [hB, hQ]; positivity
    calc 2 * (B * Q') * volume.real S ≤ 2 * (B * Q') * (V * δ ^ 2) :=
          mul_le_mul_of_nonneg_left hSle hnnR
      _ ≤ 2 * (B * exp (-(β * L))) * (V * δ ^ 2) :=
          mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hexpQ hBnn) two_pos.le)
            (mul_nonneg hV (sq_nonneg δ))
      _ = 2 * B * V * δ ^ 2 * exp (-(β * L)) := by ring
  calc ∫ ω, |(massU γ S δ k U ω).toReal - (massU γ S δ (k + 1) U ω).toReal| ∂P
      ≤ √(A * (π * (2 * radius k) ^ 2 * volume.real S)) + 2 * (B * Q') * volume.real S := hraw
    _ ≤ 2 * √(π * A₁ * V) * δ ^ 2 * exp (-(β * L)) +
          2 * B * V * δ ^ 2 * exp (-(β * L)) := add_le_add hT1 hT2
    _ = (2 * √(π * A₁ * V) + 2 * B * V) * δ ^ 2 * exp (-(β * L)) := by ring

/-- **Fractional moments of the supremum of the rescaled masses** (QZ
`lintegral_iSup_massFunC_inner_rpow_le`): telescoping, subadditivity of `x ↦ x^p` and the
geometric decay of the rate form. -/
theorem lintegral_iSup_massU_rpow_le {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) (hδ : 0 < δ)
    {V p : ℝ} (hS : MeasurableSet S) (hSf : volume S < ∞) (hV : 0 ≤ V)
    (hSle : volume.real S ≤ V * δ ^ 2) (hp0 : 0 < p) (hp1 : p ≤ 1) {k : ℕ}
    (h : ∀ m, LevelHyp P S δ K U (k + m)) :
    ∫⁻ ω, (⨆ m, massU γ S δ (k + m) U ω) ^ p ∂P ≤
      (ENNReal.ofReal (exp (γ ^ 2 / 2 * K) * volume.real S)) ^ p
        + ENNReal.ofReal ((cRate γ K V * δ ^ 2) ^ p) *
          (1 - ENNReal.ofReal (exp (-(p * (min (2 - γ ^ 2 + (max 0 ((3 * γ - 2) / 2)) ^ 2 / 2)
            ((2 - γ) ^ 2 / 4))) * (1 / 2 * log 2))))⁻¹ := by
  have hr := radius_pos k
  set βA : ℝ := min (2 - γ ^ 2 + (max 0 ((3 * γ - 2) / 2)) ^ 2 / 2) ((2 - γ) ^ 2 / 4) with hβA
  set Cst : ℝ := cRate γ K V with hCst
  set a : ℝ := -(βA * (1 / 2 * log 2)) with ha
  set Q : ℝ≥0∞ := ENNReal.ofReal (exp (-(p * βA) * (1 / 2 * log 2))) with hQ
  set W : ℕ → Ω → ℝ≥0∞ := fun m ω => massU γ S δ (k + m) U ω with hW
  set E : ℕ → Ω → ℝ≥0∞ := fun i ω =>
    ENNReal.ofReal |(W i ω).toReal - (W (i + 1) ω).toReal| with hE
  have hβA0 : 0 ≤ βA := by
    rw [hβA]
    exact le_min (areaRateExp_pos hγ hγ2).le (by positivity)
  have hCst0 : 0 ≤ Cst := by rw [hCst]; exact cRate_nonneg hV
  have hWm : ∀ m, Measurable (W m) := fun m =>
    measurable_massU γ S δ (k + m) (h m).2.choose_spec.measU
  have hEm : ∀ i, Measurable (E i) := fun i => ENNReal.measurable_ofReal.comp
    (continuous_abs.measurable.comp ((hWm i).ennreal_toReal.sub (hWm (i + 1)).ennreal_toReal))
  have hLi : ∀ i : ℕ, (i : ℝ) * (1 / 2 * log 2) ≤ 1 / 2 * log (δ / radius (k + i)) := by
    intro i
    have h1 : (i : ℝ) * log 2 ≤ log (δ / radius (k + i)) := by
      have h2 : radius (k + i) = radius k * (2 : ℝ)⁻¹ ^ i := by simp only [radius, pow_add]
      have hk : radius k ≤ δ := by simpa using (h 0).1
      have hlog : 0 ≤ log (δ / radius k) := log_nonneg (by rw [le_div_iff₀ hr]; linarith)
      rw [h2, ← div_div, log_div (div_pos hδ hr).ne' (pow_pos (by norm_num) i).ne', log_pow,
        log_inv]
      linarith
    linarith
  have hpath : ∀ᵐ ω ∂P, (⨆ m, W m ω) ^ p ≤ W 0 ω ^ p + ∑' i, E i ω ^ p := by
    have hall : ∀ᵐ ω ∂P, ∀ m, W m ω < ⊤ :=
      ae_all_iff.2 fun m => ae_massU_lt_top γ hδ hSf (h m)
    filter_upwards [hall] with ω hω
    calc (⨆ m, W m ω) ^ p ≤ (W 0 ω + ∑' i, E i ω) ^ p :=
          ENNReal.rpow_le_rpow (FracMom.iSup_le_add_tsum_abs_sub fun m => (hω m).ne) hp0.le
      _ ≤ W 0 ω ^ p + (∑' i, E i ω) ^ p := ENNReal.rpow_add_le_add_rpow _ _ hp0.le hp1
      _ ≤ W 0 ω ^ p + ∑' i, E i ω ^ p :=
          add_le_add le_rfl (FracMom.rpow_tsum_le_tsum_rpow _ hp0 hp1)
  have hinc : ∀ i : ℕ, ∫⁻ ω, E i ω ∂P ≤ ENNReal.ofReal (Cst * δ ^ 2 * exp (a * i)) := by
    intro i
    have hint : Integrable (fun ω => |(W i ω).toReal - (W (i + 1) ω).toReal|) P :=
      ((integrable_massU_toReal γ hδ hSf (h i)).sub
        (integrable_massU_toReal γ hδ hSf (h (i + 1)))).abs
    rw [hE, ← ofReal_integral_eq_lintegral_ofReal hint (ae_of_all _ fun _ => abs_nonneg _)]
    refine ENNReal.ofReal_le_ofReal ?_
    refine (integral_abs_massU_step_le_rate hγ hγ2 hδ hS hSf hV hSle (h i) (h (i + 1))).trans ?_
    refine mul_le_mul_of_nonneg_left ?_ (mul_nonneg hCst0 (sq_nonneg δ))
    rw [Real.exp_le_exp, ← hβA, ha]
    have h := mul_le_mul_of_nonneg_left (hLi i) hβA0
    linarith
  have hqe : ∀ i : ℕ, (exp (a * i)) ^ p = (exp (p * a)) ^ i := by
    intro i
    rw [Real.rpow_def_of_pos (exp_pos _), Real.log_exp, ← Real.exp_nat_mul]
    congr 1
    ring
  have hreal : ∀ i : ℕ, (Cst * δ ^ 2 * exp (a * i)) ^ p
      = (Cst * δ ^ 2) ^ p * exp (-(p * βA) * (1 / 2 * log 2)) ^ i := by
    intro i
    have h2 : exp (p * a) = exp (-(p * βA) * (1 / 2 * log 2)) := by rw [ha]; ring
    rw [Real.mul_rpow (mul_nonneg hCst0 (sq_nonneg δ)) (exp_pos _).le, hqe i, h2]
  have hinc2 : ∀ i : ℕ, (ENNReal.ofReal (Cst * δ ^ 2 * exp (a * i))) ^ p
      = ENNReal.ofReal ((Cst * δ ^ 2) ^ p) * Q ^ i := by
    intro i
    have h1 : (0 : ℝ) ≤ Cst * δ ^ 2 * exp (a * i) :=
      mul_nonneg (mul_nonneg hCst0 (sq_nonneg δ)) (exp_pos _).le
    have h2 : (0 : ℝ) ≤ (Cst * δ ^ 2) ^ p := Real.rpow_nonneg (mul_nonneg hCst0 (sq_nonneg δ)) p
    rw [ENNReal.ofReal_rpow_of_nonneg h1 hp0.le, hreal i, hQ,
      ← ENNReal.ofReal_pow (exp_pos _).le, ← ENNReal.ofReal_mul h2]
  have h0 : ∫⁻ ω, W 0 ω ∂P ≤ ENNReal.ofReal (exp (γ ^ 2 / 2 * K)) * volume S := by
    simpa only [hW, Nat.add_zero] using lintegral_massU_le (P := P) γ hδ (h 0)
  have hvol : ENNReal.ofReal (exp (γ ^ 2 / 2 * K)) * volume S
      = ENNReal.ofReal (exp (γ ^ 2 / 2 * K) * volume.real S) := by
    have hfin : volume S = ENNReal.ofReal (volume.real S) := by
      rw [measureReal_def, ENNReal.ofReal_toReal hSf.ne]
    rw [hfin, ← ENNReal.ofReal_mul (exp_pos _).le]
  have hfirst : (∫⁻ ω, W 0 ω ^ p ∂P)
      ≤ (ENNReal.ofReal (exp (γ ^ 2 / 2 * K) * volume.real S)) ^ p := by
    have h1 : (∫⁻ ω, W 0 ω ^ p ∂P) ≤ (ENNReal.ofReal (exp (γ ^ 2 / 2 * K)) * volume S) ^ p :=
      (FracMom.lintegral_rpow_le_rpow_lintegral (hWm 0).aemeasurable hp0 hp1).trans
        (ENNReal.rpow_le_rpow h0 hp0.le)
    rwa [hvol] at h1
  have hsecond : (∑' i, ∫⁻ ω, E i ω ^ p ∂P)
      ≤ ∑' i, ENNReal.ofReal ((Cst * δ ^ 2) ^ p) * Q ^ i :=
    ENNReal.tsum_le_tsum fun i =>
      (FracMom.lintegral_rpow_le_rpow_lintegral (hEm i).aemeasurable hp0 hp1).trans
        ((ENNReal.rpow_le_rpow (hinc i) hp0.le).trans (le_of_eq (hinc2 i)))
  calc ∫⁻ ω, (⨆ m, W m ω) ^ p ∂P
      ≤ ∫⁻ ω, (W 0 ω ^ p + ∑' i, E i ω ^ p) ∂P := lintegral_mono_ae hpath
    _ = ∫⁻ ω, W 0 ω ^ p ∂P + ∑' i, ∫⁻ ω, E i ω ^ p ∂P := by
        rw [lintegral_add_left ((hWm 0).pow_const p),
          lintegral_tsum fun i => ((hEm i).pow_const p).aemeasurable]
    _ ≤ (ENNReal.ofReal (exp (γ ^ 2 / 2 * K) * volume.real S)) ^ p
          + ∑' i, ENNReal.ofReal ((Cst * δ ^ 2) ^ p) * Q ^ i := add_le_add hfirst hsecond
    _ = _ := by rw [ENNReal.tsum_mul_left, ENNReal.tsum_geometric]

end ConeArea6
end MatedCRTHarmonic.MoTPort
