/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module MatedCRTHarmonic.GMSAppA.LongRangeCore at commit fdb5cad; only the module paths of local imports are changed.
   Declarations, examples and checks that the copied results do not use are omitted. -/
import Mathlib.MeasureTheory.Function.ConditionalExpectation.Real
import Mathlib.MeasureTheory.Function.ConditionalExpectation.CondJensen
import Mathlib.MeasureTheory.Integral.MeanInequalities
import Mathlib.Analysis.MeanInequalitiesPow

/-!
# The change-of-measure comparison behind [18] Lemma A.3, abstract form

[18] = Gwynne–Miller–Sheffield, *Harmonic functions on mated-CRT maps*, arXiv 1807.07511v3
, proof of Lemma A.3. In the paper, `X ≥ 0` is a functional of
`h|_{B_δ(0)}` and `h_1(0)`, `X̃` is the same functional of a coupled field `h̃` (`h̃_1(0) = h_1(0)`, `h, h̃`
conditionally independent given `h_1(0)`), `M_δ` is the Radon–Nikodym derivative of the conditional law of
`h|_{B_δ(0)}` given `h|_{ℂ∖𝔻}` with respect to that of `h̃|_{B_δ(0)}`, and

  `E[X | h|_{ℂ∖𝔻}] = E[M_δ X̃ | h|_{ℂ∖𝔻}]`, `E[X̃ | h|_{ℂ∖𝔻}] = E[X | h_1(0)]`.

From these two identities alone the paper derives (A.13)–(A.15) :
`|E[X|𝒢] − Y| ≤ t·Y + E[M X̃ 1_{M>1+t} | 𝒢] + E[X̃ 1_{M<1−t} | 𝒢]` (with `t = δ^s`, `Y = E[X | h_1(0)]`), and then
`E|E[X|𝒢] − Y|^p ≲ t^p E[X̃^p] + E[M^p X̃^p 1_{M>1+t}] + E[X̃^p 1_{M<1−t}]`, followed by Hölder (A.17)–(A.18).
This file proves these steps for an arbitrary probability space, sub-σ-algebra `m` and nonnegative `X̃`, `M`.

* `GMSAppA.abs_condExp_sub_le_of_changeOfMeasure` — the sandwich (A.13)–(A.14).
* `GMSAppA.lintegral_rpow_condExp_sub_le` — (A.15) in `ℝ≥0∞` form with constant `4^{p−1}`.
* `GMSAppA.lintegral_tailMul_rpow_le`, `GMSAppA.lintegral_tailInd_rpow_le` — the Hölder steps (A.17), (A.18).
* `GMSAppA.lintegral_rpow_condExp_sub_le_holder` — the assembled bound.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal

namespace MatedCRTHarmonic.GMSAppA

variable {Ω : Type*} {m m0 : MeasurableSpace Ω} {P : Measure Ω}

/-- The upper tail part `M X̃ 1_{M > 1+t}`. -/
def tailMul (M Xt : Ω → ℝ) (t : ℝ) : Ω → ℝ := {ω | 1 + t < M ω}.indicator fun ω => M ω * Xt ω

/-- The lower tail part `X̃ 1_{M < 1−t}`. -/
def tailInd (M Xt : Ω → ℝ) (t : ℝ) : Ω → ℝ := {ω | M ω < 1 - t}.indicator Xt

lemma tailMul_nonneg {M Xt : Ω → ℝ} {t : ℝ} (hM : ∀ ω, 0 ≤ M ω) (hX : ∀ ω, 0 ≤ Xt ω) (ω : Ω) :
    0 ≤ tailMul M Xt t ω :=
  Set.indicator_nonneg (fun ω _ => mul_nonneg (hM ω) (hX ω)) ω

lemma tailInd_nonneg {M Xt : Ω → ℝ} {t : ℝ} (hX : ∀ ω, 0 ≤ Xt ω) (ω : Ω) : 0 ≤ tailInd M Xt t ω :=
  Set.indicator_nonneg (fun ω _ => hX ω) ω

/-- Pointwise upper comparison: `M X̃ ≤ (1+t) X̃ + M X̃ 1_{M>1+t}`. -/
lemma mul_le_tailMul {M Xt : Ω → ℝ} {t : ℝ} (ht : 0 ≤ t) (hX : ∀ ω, 0 ≤ Xt ω) (ω : Ω) :
    M ω * Xt ω ≤ (1 + t) * Xt ω + tailMul M Xt t ω := by
  by_cases h : 1 + t < M ω
  · have : tailMul M Xt t ω = M ω * Xt ω := Set.indicator_of_mem (s := {ω | 1 + t < M ω}) h _
    rw [this]
    have : 0 ≤ (1 + t) * Xt ω := mul_nonneg (by linarith) (hX ω)
    linarith
  · have : tailMul M Xt t ω = 0 := Set.indicator_of_notMem (s := {ω | 1 + t < M ω}) h _
    rw [this, add_zero]
    exact mul_le_mul_of_nonneg_right (not_lt.1 h) (hX ω)

/-- Pointwise lower comparison: `(1−t) X̃ − X̃ 1_{M<1−t} ≤ M X̃` (for `t ≥ 0`, `M ≥ 0`). -/
lemma sub_tailInd_le_mul {M Xt : Ω → ℝ} {t : ℝ} (ht : 0 ≤ t) (hM : ∀ ω, 0 ≤ M ω)
    (hX : ∀ ω, 0 ≤ Xt ω) (ω : Ω) :
    (1 - t) * Xt ω - tailInd M Xt t ω ≤ M ω * Xt ω := by
  by_cases h : M ω < 1 - t
  · have : tailInd M Xt t ω = Xt ω := Set.indicator_of_mem (s := {ω | M ω < 1 - t}) h _
    rw [this]
    nlinarith [hX ω, hM ω]
  · have : tailInd M Xt t ω = 0 := Set.indicator_of_notMem (s := {ω | M ω < 1 - t}) h _
    rw [this, sub_zero]
    exact mul_le_mul_of_nonneg_right (not_lt.1 h) (hX ω)

lemma integrable_tailMul {M Xt : Ω → ℝ} {t : ℝ} (hMm : Measurable M) (hi : Integrable (fun ω => M ω * Xt ω) P) :
    Integrable (tailMul M Xt t) P :=
  hi.indicator (measurableSet_lt measurable_const hMm)

lemma integrable_tailInd {M Xt : Ω → ℝ} {t : ℝ} (hMm : Measurable M) (hi : Integrable Xt P) :
    Integrable (tailInd M Xt t) P :=
  hi.indicator (measurableSet_lt hMm measurable_const)

/-- **[18] (A.13)–(A.14)**, abstract form. Let `X̃, M ≥ 0` with `E[X | m] = E[M X̃ | m]` and `E[X̃ | m] = Y`. Then for
`t ≥ 0`, almost surely `|E[X | m] − Y| ≤ t·Y + E[M X̃ 1_{M>1+t} | m] + E[X̃ 1_{M<1−t} | m]`. -/
theorem abs_condExp_sub_le_of_changeOfMeasure {X Xt M Y : Ω → ℝ} (hMm : Measurable M)
    (hM : ∀ ω, 0 ≤ M ω) (hX : ∀ ω, 0 ≤ Xt ω) (hXti : Integrable Xt P)
    (hMXi : Integrable (fun ω => M ω * Xt ω) P)
    (hcm : P[X | m] =ᵐ[P] P[(fun ω => M ω * Xt ω) | m]) (hY : P[Xt | m] =ᵐ[P] Y) {t : ℝ}
    (ht : 0 ≤ t) :
    ∀ᵐ ω ∂P, |P[X | m] ω - Y ω| ≤
      t * Y ω + P[tailMul M Xt t | m] ω + P[tailInd M Xt t | m] ω := by
  have hTi := integrable_tailMul (P := P) (t := t) hMm hMXi
  have hIi := integrable_tailInd (P := P) (t := t) hMm hXti
  -- upper bound
  have hup : P[(fun ω => M ω * Xt ω) | m] ≤ᵐ[P]
      P[(fun ω => (1 + t) * Xt ω + tailMul M Xt t ω) | m] :=
    condExp_mono hMXi ((hXti.const_mul _).add hTi) (ae_of_all _ fun ω => mul_le_tailMul ht hX ω)
  have hupE : P[(fun ω => (1 + t) * Xt ω + tailMul M Xt t ω) | m] =ᵐ[P]
      fun ω => (1 + t) * P[Xt | m] ω + P[tailMul M Xt t | m] ω := by
    have h1 := condExp_add (m := m) (hXti.const_mul (1 + t)) hTi
    have h2 := condExp_smul (m := m) (μ := P) (1 + t) Xt
    filter_upwards [h1, h2] with ω h1 h2
    have e : (fun ω => (1 + t) * Xt ω + tailMul M Xt t ω) =
        (fun ω => (1 + t) * Xt ω) + tailMul M Xt t := rfl
    rw [e, h1, Pi.add_apply]
    congr 1
  -- lower bound
  have hlo : P[(fun ω => (1 - t) * Xt ω - tailInd M Xt t ω) | m] ≤ᵐ[P]
      P[(fun ω => M ω * Xt ω) | m] :=
    condExp_mono ((hXti.const_mul _).sub hIi) hMXi
      (ae_of_all _ fun ω => sub_tailInd_le_mul ht hM hX ω)
  have hloE : P[(fun ω => (1 - t) * Xt ω - tailInd M Xt t ω) | m] =ᵐ[P]
      fun ω => (1 - t) * P[Xt | m] ω - P[tailInd M Xt t | m] ω := by
    have h1 := condExp_sub (m := m) (hXti.const_mul (1 - t)) hIi
    have h2 := condExp_smul (m := m) (μ := P) (1 - t) Xt
    filter_upwards [h1, h2] with ω h1 h2
    have e : (fun ω => (1 - t) * Xt ω - tailInd M Xt t ω) =
        (fun ω => (1 - t) * Xt ω) - tailInd M Xt t := rfl
    rw [e, h1, Pi.sub_apply]
    congr 1
  have hY0 : 0 ≤ᵐ[P] P[Xt | m] := condExp_nonneg (ae_of_all _ hX)
  have hT0 : 0 ≤ᵐ[P] P[tailMul M Xt t | m] :=
    condExp_nonneg (ae_of_all _ fun ω => tailMul_nonneg hM hX ω)
  have hI0 : 0 ≤ᵐ[P] P[tailInd M Xt t | m] :=
    condExp_nonneg (ae_of_all _ fun ω => tailInd_nonneg hX ω)
  filter_upwards [hcm, hY, hup, hupE, hlo, hloE, hY0, hT0, hI0] with ω hcm hY hup hupE hlo hloE
    hY0 hT0 hI0
  rw [hupE] at hup
  rw [hloE] at hlo
  simp only [Pi.zero_apply] at hY0 hT0 hI0
  rw [hcm, ← hY]
  rw [abs_le]
  constructor <;> nlinarith

/-! ### (A.15): the `p`-th moment -/
/-- `(a + b + c)^p ≤ 4^{p−1}(a^p + b^p + c^p)` in `ℝ≥0∞`, `p ≥ 1`. -/
lemma rpow_add3_le (a b c : ℝ≥0∞) {p : ℝ} (hp : 1 ≤ p) :
    (a + b + c) ^ p ≤ (4 : ℝ≥0∞) ^ (p - 1) * (a ^ p + b ^ p + c ^ p) := by
  have h2 : (2 : ℝ≥0∞) ^ (p - 1) ≤ 4 ^ (p - 1) :=
    ENNReal.rpow_le_rpow (by norm_num) (by linarith)
  have h22 : (2 : ℝ≥0∞) ^ (p - 1) * 2 ^ (p - 1) = 4 ^ (p - 1) := by
    rw [← ENNReal.mul_rpow_of_nonneg _ _ (by linarith)]
    norm_num
  calc (a + b + c) ^ p = (a + (b + c)) ^ p := by rw [add_assoc]
    _ ≤ 2 ^ (p - 1) * (a ^ p + (b + c) ^ p) := ENNReal.rpow_add_le_mul_rpow_add_rpow _ _ hp
    _ ≤ 2 ^ (p - 1) * (a ^ p + 2 ^ (p - 1) * (b ^ p + c ^ p)) := by
        gcongr
        exact ENNReal.rpow_add_le_mul_rpow_add_rpow _ _ hp
    _ = 2 ^ (p - 1) * a ^ p + 4 ^ (p - 1) * (b ^ p + c ^ p) := by
        rw [mul_add, ← mul_assoc, h22]
    _ ≤ 4 ^ (p - 1) * a ^ p + 4 ^ (p - 1) * (b ^ p + c ^ p) := by gcongr
    _ = 4 ^ (p - 1) * (a ^ p + b ^ p + c ^ p) := by rw [← mul_add, add_assoc]

/-- **Conditional Jensen in `ℝ≥0∞` form**: for `f ≥ 0` integrable and `p ≥ 1`,
`∫⁻ E[f | m]^p ≤ ∫⁻ f^p`. -/
theorem lintegral_condExp_rpow_le [IsFiniteMeasure P] (hm : m ≤ m0) {f : Ω → ℝ}
    (hf0 : ∀ ω, 0 ≤ f ω) (hfi : Integrable f P) {p : ℝ} (hp : 1 ≤ p) :
    ∫⁻ ω, ENNReal.ofReal (P[f | m] ω) ^ p ∂P ≤ ∫⁻ ω, ENNReal.ofReal (f ω) ^ p ∂P := by
  have hp0 : 0 ≤ p := by linarith
  by_cases htop : ∫⁻ ω, ENNReal.ofReal (f ω) ^ p ∂P = ⊤
  · rw [htop]; exact le_top
  have hfm : AEStronglyMeasurable f P := hfi.aestronglyMeasurable
  have hfp : Integrable (fun ω => ‖f ω‖ ^ p) P := by
    refine ⟨(hfm.norm.aemeasurable.pow_const p).aestronglyMeasurable, ?_⟩
    rw [hasFiniteIntegral_iff_ofReal (ae_of_all _ fun ω => by positivity)]
    refine lt_of_le_of_lt (le_of_eq ?_) (lt_top_iff_ne_top.2 htop)
    refine lintegral_congr fun ω => ?_
    rw [Real.norm_of_nonneg (hf0 ω), ENNReal.ofReal_rpow_of_nonneg (hf0 ω) hp0]
  have hJ := _root_.Integrable.norm_condExp_rpow_le (m := m) hp hfp
  have hc0 : 0 ≤ᵐ[P] P[f | m] := condExp_nonneg (ae_of_all _ hf0)
  calc ∫⁻ ω, ENNReal.ofReal (P[f | m] ω) ^ p ∂P
      ≤ ∫⁻ ω, ENNReal.ofReal (P[(fun ω => ‖f ω‖ ^ p) | m] ω) ∂P := by
        refine lintegral_mono_ae ?_
        filter_upwards [hJ, hc0] with ω hJ hc0
        simp only [Pi.zero_apply] at hc0
        rw [ENNReal.ofReal_rpow_of_nonneg hc0 hp0]
        refine ENNReal.ofReal_le_ofReal ?_
        rw [← Real.norm_of_nonneg hc0]
        exact hJ
    _ = ENNReal.ofReal (∫ ω, P[(fun ω => ‖f ω‖ ^ p) | m] ω ∂P) := by
        rw [ofReal_integral_eq_lintegral_ofReal integrable_condExp
          (condExp_nonneg (ae_of_all _ fun ω => by positivity))]
    _ = ENNReal.ofReal (∫ ω, ‖f ω‖ ^ p ∂P) := by rw [integral_condExp hm]
    _ = ∫⁻ ω, ENNReal.ofReal (f ω) ^ p ∂P := by
        rw [ofReal_integral_eq_lintegral_ofReal hfp (ae_of_all _ fun ω => by positivity)]
        refine lintegral_congr fun ω => ?_
        rw [Real.norm_of_nonneg (hf0 ω), ENNReal.ofReal_rpow_of_nonneg (hf0 ω) hp0]

/-- **[18] (A.15)**, abstract `ℝ≥0∞` form: under the hypotheses of the sandwich (A.13)–(A.14), for `p ≥ 1`,
`E|E[X | m] − Y|^p ≤ 4^{p−1} (t^p E[X̃^p] + E[(M X̃)^p 1_{M>1+t}] + E[X̃^p 1_{M<1−t}])`. -/
theorem lintegral_rpow_condExp_sub_le [IsFiniteMeasure P] (hm : m ≤ m0) {X Xt M Y : Ω → ℝ}
    (hMm : Measurable M) (hM : ∀ ω, 0 ≤ M ω) (hX : ∀ ω, 0 ≤ Xt ω) (hXti : Integrable Xt P)
    (hMXi : Integrable (fun ω => M ω * Xt ω) P)
    (hcm : P[X | m] =ᵐ[P] P[(fun ω => M ω * Xt ω) | m]) (hY : P[Xt | m] =ᵐ[P] Y) {t : ℝ}
    (ht : 0 ≤ t) {p : ℝ} (hp : 1 ≤ p) :
    ∫⁻ ω, ENNReal.ofReal |P[X | m] ω - Y ω| ^ p ∂P ≤
      (4 : ℝ≥0∞) ^ (p - 1) * (ENNReal.ofReal t ^ p * ∫⁻ ω, ENNReal.ofReal (Xt ω) ^ p ∂P +
        ∫⁻ ω, ENNReal.ofReal (tailMul M Xt t ω) ^ p ∂P +
        ∫⁻ ω, ENNReal.ofReal (tailInd M Xt t ω) ^ p ∂P) := by
  have hp0 : 0 ≤ p := by linarith
  have hsand := abs_condExp_sub_le_of_changeOfMeasure hMm hM hX hXti hMXi hcm hY ht
  have hY0 : 0 ≤ᵐ[P] Y := by
    filter_upwards [hY, condExp_nonneg (m := m) (μ := P) (ae_of_all _ hX)] with ω h1 h2
    rw [← h1]; exact h2
  have hT0 : 0 ≤ᵐ[P] P[tailMul M Xt t | m] :=
    condExp_nonneg (ae_of_all _ fun ω => tailMul_nonneg hM hX ω)
  have hI0 : 0 ≤ᵐ[P] P[tailInd M Xt t | m] :=
    condExp_nonneg (ae_of_all _ fun ω => tailInd_nonneg hX ω)
  have hTi := integrable_tailMul (P := P) (t := t) hMm hMXi
  have hIi := integrable_tailInd (P := P) (t := t) hMm hXti
  -- pointwise bound
  have hpt : ∀ᵐ ω ∂P, ENNReal.ofReal |P[X | m] ω - Y ω| ^ p ≤
      (4 : ℝ≥0∞) ^ (p - 1) * (ENNReal.ofReal t ^ p * ENNReal.ofReal (P[Xt | m] ω) ^ p +
        ENNReal.ofReal (P[tailMul M Xt t | m] ω) ^ p +
        ENNReal.ofReal (P[tailInd M Xt t | m] ω) ^ p) := by
    filter_upwards [hsand, hY0, hT0, hI0, hY] with ω hs hY0 hT0 hI0 hYω
    simp only [Pi.zero_apply] at hY0 hT0 hI0
    rw [hYω]
    calc ENNReal.ofReal |P[X | m] ω - Y ω| ^ p
        ≤ (ENNReal.ofReal (t * Y ω) + ENNReal.ofReal (P[tailMul M Xt t | m] ω) +
            ENNReal.ofReal (P[tailInd M Xt t | m] ω)) ^ p := by
          refine ENNReal.rpow_le_rpow ?_ hp0
          rw [← ENNReal.ofReal_add (mul_nonneg ht hY0) hT0,
            ← ENNReal.ofReal_add (add_nonneg (mul_nonneg ht hY0) hT0) hI0]
          exact ENNReal.ofReal_le_ofReal hs
      _ ≤ _ := rpow_add3_le _ _ _ hp
      _ = _ := by
          rw [ENNReal.ofReal_mul ht, ENNReal.mul_rpow_of_nonneg _ _ hp0]
  have hJY := lintegral_condExp_rpow_le hm hX hXti hp
  have hJT := lintegral_condExp_rpow_le hm (tailMul_nonneg hM hX) hTi hp
  have hJI := lintegral_condExp_rpow_le hm (tailInd_nonneg hX) hIi hp
  have hmeas : ∀ f : Ω → ℝ, AEMeasurable (fun ω => ENNReal.ofReal (P[f | m] ω) ^ p) P :=
    fun f => ((stronglyMeasurable_condExp.mono hm).measurable.ennreal_ofReal.pow_const p).aemeasurable
  calc ∫⁻ ω, ENNReal.ofReal |P[X | m] ω - Y ω| ^ p ∂P
      ≤ ∫⁻ ω, (4 : ℝ≥0∞) ^ (p - 1) * (ENNReal.ofReal t ^ p * ENNReal.ofReal (P[Xt | m] ω) ^ p +
        ENNReal.ofReal (P[tailMul M Xt t | m] ω) ^ p +
        ENNReal.ofReal (P[tailInd M Xt t | m] ω) ^ p) ∂P := lintegral_mono_ae hpt
    _ = (4 : ℝ≥0∞) ^ (p - 1) * (ENNReal.ofReal t ^ p * ∫⁻ ω, ENNReal.ofReal (P[Xt | m] ω) ^ p ∂P +
        ∫⁻ ω, ENNReal.ofReal (P[tailMul M Xt t | m] ω) ^ p ∂P +
        ∫⁻ ω, ENNReal.ofReal (P[tailInd M Xt t | m] ω) ^ p ∂P) := by
        rw [lintegral_const_mul' _ _ (ENNReal.rpow_ne_top_of_nonneg (by linarith) (by norm_num)),
          lintegral_add_right' _ (hmeas _), lintegral_add_left' ((hmeas _).const_mul _),
          lintegral_const_mul' _ _ (ENNReal.rpow_ne_top_of_nonneg hp0 ENNReal.ofReal_ne_top)]
    _ ≤ _ := by gcongr

/-! ### (A.17)–(A.18): Hölder -/

lemma lintegral_indicator_one_rpow {A : Set Ω} (hA : MeasurableSet A) {r : ℝ} (hr : 0 < r) :
    ∫⁻ ω, (A.indicator (fun _ => (1 : ℝ≥0∞)) ω) ^ r ∂P = P A := by
  have : (fun ω => (A.indicator (fun _ => (1 : ℝ≥0∞)) ω) ^ r) = A.indicator fun _ => 1 := by
    funext ω
    by_cases h : ω ∈ A
    · simp [h]
    · simp [h, ENNReal.zero_rpow_of_pos hr]
  rw [this, lintegral_indicator hA, setLIntegral_const, one_mul]

/-- **(A.18)**: `E[X̃^p 1_A] ≤ E[X̃^{p₀}]^{p/p₀} P(A)^{1 − p/p₀}` for `0 < p < p₀`. -/
theorem lintegral_rpow_indicator_le {f : Ω → ℝ≥0∞} (hf : AEMeasurable f P) {A : Set Ω}
    (hA : MeasurableSet A) {p p₀ : ℝ} (hp : 0 < p) (hpp₀ : p < p₀) :
    ∫⁻ ω, A.indicator (fun ω => f ω ^ p) ω ∂P ≤
      (∫⁻ ω, f ω ^ p₀ ∂P) ^ (p / p₀) * P A ^ (1 - p / p₀) := by
  have hp₀ : 0 < p₀ := hp.trans hpp₀
  have hconj : (p₀ / p).HolderConjugate (p₀ / (p₀ - p)) := by
    refine ⟨?_, ?_, ?_⟩
    · rw [inv_div, inv_div, ← add_div, add_sub_cancel, div_self hp₀.ne', inv_one]
    · exact div_pos hp₀ hp
    · exact div_pos hp₀ (by linarith)
  have e : (fun ω => A.indicator (fun ω => f ω ^ p) ω) =
      (fun ω => f ω ^ p) * fun ω => A.indicator (fun _ => (1 : ℝ≥0∞)) ω := by
    funext ω
    by_cases h : ω ∈ A <;> simp [h]
  rw [e]
  refine (ENNReal.lintegral_mul_le_Lp_mul_Lq P hconj (hf.pow_const p)
    (aemeasurable_const.indicator hA)).trans (le_of_eq ?_)
  rw [lintegral_indicator_one_rpow hA (div_pos hp₀ (by linarith))]
  congr 1
  · rw [one_div_div]
    congr 1
    refine lintegral_congr fun ω => ?_
    rw [← ENNReal.rpow_mul, mul_div_cancel₀ _ hp.ne']
  · congr 1
    field_simp

/-- **(A.17)**: `E[M^p X̃^p 1_A] ≤ E[X̃^{p₀}]^{p/p₀} (E[M^{2pr}])^{1/(2r)} P(A)^{1/(2r)}` with
`r = p₀/(p₀ − p)`, for `0 < p < p₀`. -/
theorem lintegral_mul_rpow_indicator_le {f g : Ω → ℝ≥0∞} (hf : AEMeasurable f P)
    (hg : AEMeasurable g P) {A : Set Ω} (hA : MeasurableSet A) {p p₀ : ℝ} (hp : 0 < p)
    (hpp₀ : p < p₀) :
    ∫⁻ ω, A.indicator (fun ω => (g ω * f ω) ^ p) ω ∂P ≤
      (∫⁻ ω, f ω ^ p₀ ∂P) ^ (p / p₀) *
        ((∫⁻ ω, g ω ^ (2 * (p * (p₀ / (p₀ - p)))) ∂P) ^ (1 / 2 : ℝ) * P A ^ (1 / 2 : ℝ)) ^
          (1 - p / p₀) := by
  have hp₀ : 0 < p₀ := hp.trans hpp₀
  set r := p₀ / (p₀ - p) with hr
  have hr0 : 0 < r := div_pos hp₀ (by linarith)
  have hconj : (p₀ / p).HolderConjugate r := by
    refine ⟨?_, ?_, ?_⟩
    · rw [hr, inv_div, inv_div, ← add_div, add_sub_cancel, div_self hp₀.ne', inv_one]
    · exact div_pos hp₀ hp
    · exact hr0
  have e : (fun ω => A.indicator (fun ω => (g ω * f ω) ^ p) ω) =
      (fun ω => f ω ^ p) * fun ω => A.indicator (fun ω => g ω ^ p) ω := by
    funext ω
    by_cases h : ω ∈ A
    · simp [h, ENNReal.mul_rpow_of_nonneg _ _ hp.le, mul_comm]
    · simp [h]
  rw [e]
  have h1 := ENNReal.lintegral_mul_le_Lp_mul_Lq P hconj (hf.pow_const p)
    ((hg.pow_const p).indicator hA)
  refine h1.trans ?_
  have hfirst : (∫⁻ ω, (f ω ^ p) ^ (p₀ / p) ∂P) ^ (1 / (p₀ / p)) =
      (∫⁻ ω, f ω ^ p₀ ∂P) ^ (p / p₀) := by
    rw [one_div_div]
    congr 1
    refine lintegral_congr fun ω => ?_
    rw [← ENNReal.rpow_mul, mul_div_cancel₀ _ hp.ne']
  rw [hfirst]
  gcongr
  -- the second factor: Cauchy–Schwarz
  have e2 : (fun ω => (A.indicator (fun ω => g ω ^ p) ω) ^ r) =
      (fun ω => g ω ^ (p * r)) * fun ω => A.indicator (fun _ => (1 : ℝ≥0∞)) ω := by
    funext ω
    by_cases h : ω ∈ A
    · simp [h, ← ENNReal.rpow_mul]
    · simp [h, ENNReal.zero_rpow_of_pos hr0]
  have hcs : (2 : ℝ).HolderConjugate 2 := ⟨by norm_num, by norm_num, by norm_num⟩
  have h2 := ENNReal.lintegral_mul_le_Lp_mul_Lq P hcs (hg.pow_const (p * r))
    ((aemeasurable_const (b := (1 : ℝ≥0∞))).indicator hA)
  rw [lintegral_indicator_one_rpow hA two_pos] at h2
  have h3 : ∫⁻ ω, (A.indicator (fun ω => g ω ^ p) ω) ^ r ∂P ≤
      (∫⁻ ω, g ω ^ (2 * (p * r)) ∂P) ^ (1 / 2 : ℝ) * P A ^ (1 / 2 : ℝ) := by
    rw [e2]
    refine h2.trans (le_of_eq ?_)
    congr 2
    refine lintegral_congr fun ω => ?_
    rw [← ENNReal.rpow_mul]
    ring_nf
  have hexp : 1 / r = 1 - p / p₀ := by rw [hr]; field_simp
  rw [← hexp]
  exact ENNReal.rpow_le_rpow h3 (by positivity)

end MatedCRTHarmonic.GMSAppA
