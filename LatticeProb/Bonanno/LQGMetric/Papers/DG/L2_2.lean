/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DG.L2_2 at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.LM.L3_4N2
import LatticeProb.Bonanno.LQGMetric.Field.MarkovNorm

/-!
# Ding–Gwynne Lemma 2.2, (2.4): Gaussian tail of the harmonic part (task P2-DG3E)

DG (`literature/src/1807.01072/metric-comparison-final.tex`, Lemma 2.2 `lem-whole-plane-compare`,
DG:618–640): for a whole-plane GFF `h` normalized by `h_1(0) = 0` and its Markov decomposition
`h|_U = h^U + 𝔥` (`𝔥` harmonic on `U`, independent of `h^U`),
`P[max_{z ∈ V̄} |𝔥(z)| ≤ A] ≥ 1 − a₀ e^{−a₁ A²}`.

DG's proof: `𝔥` is a centred Gaussian function with `Var 𝔥(z) ≤ log CR(z;U)⁻¹ + O(1)` (MS IG1
Lemma 6.4), then Borell–TIS. **Deviation (own argument, same scheme as the formalized MQ Lemma 4.4
in `LM.lintegral_exp_nestPhi_le`):** we do not use the Gaussianity of `𝔥` nor IG1 Lemma 6.4.
Instead, by the mean value property (`GM.abs_sub_le_integral_of_harmonic`,
`GM.pair_radBump_of_harmonic`), `max_K |𝔥| ≤ C (∫_S |𝔥(ψ_y − ψ_c)| dy + |S| |𝔥(ψ_c)|)` for
radial bumps `ψ_y` and a compact neighbourhood `S` of `K` in `U`; each pairing has a sub-Gaussian
exponential moment, `E e^{a|𝔥(φ)|} ≤ 2 e^{a² Var h(φ)/2}`, because `h(φ) = 𝔥(φ) + h^U(φ)` with
`h^U(φ)` independent, integrable and centred (`LM.lintegral_exp_le_of_indepFun`); Jensen over `S`
and Chernoff give the Gaussian tail.

* `lintegral_exp_abs_le` — `E e^{a|X|} ≤ 2 e^{a² Var Y/2}` if `X + Z = Y`, `Y` centred Gaussian,
  `Z ⫫ X` centred.
* `tail_of_lintegral_exp` — Chernoff.
* `lintegral_exp_setIntegral_le` — Jensen over a compact `S`.
* **`dg_lemma22_tail`** — (2.4) for every compact `K ⊆ U` and every decomposition
  `h = G + h^U` a.s. with `G ⫫ h^U`, `h^U|_U` a zero-boundary GFF on `U`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Metric InnerProductSpace TopologicalSpace
open scoped ENNReal

namespace LQGMetric
namespace DG
namespace L22

open Blueprint GM LM MarkovNorm MarkovGauss

variable {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

/-- **sub-Gaussian exponential moment of `|X|`**: `X + Z = Y` a.s., `Y` centred Gaussian,
`Z` independent of `X`, integrable and centred. -/
lemma lintegral_exp_abs_le {X Z Y : Ω → ℝ} (hX : Measurable X) (hZ : Measurable Z)
    (hXZ : IndepFun X Z P) (hZi : Integrable Z P) (hZ0 : ∫ ω, Z ω ∂P = 0)
    (hY : HasGaussianLaw Y P) (hY0 : ∫ ω, Y ω ∂P = 0) (hXY : ∀ᵐ ω ∂P, X ω + Z ω = Y ω)
    (a : ℝ) :
    ∫⁻ ω, ENNReal.ofReal (Real.exp (a * |X ω|)) ∂P ≤
      2 * ENNReal.ofReal (Real.exp (Var[Y; P] * a ^ 2 / 2)) := by
  have one : ∀ t : ℝ, ∫⁻ ω, ENNReal.ofReal (Real.exp (t * X ω)) ∂P ≤
      ENNReal.ofReal (Real.exp (Var[Y; P] * t ^ 2 / 2)) := fun t => by
    have hi : IndepFun (fun ω => t * X ω) (fun ω => t * Z ω) P :=
      hXZ.comp (φ := fun x : ℝ => t * x) (ψ := fun x : ℝ => t * x)
        (measurable_id.const_mul t) (measurable_id.const_mul t)
    have h1 := lintegral_exp_le_of_indepFun (hX.const_mul t) (hZ.const_mul t) hi
      (hZi.const_mul t) (by rw [integral_const_mul, hZ0, mul_zero])
    refine h1.trans (le_of_eq ?_)
    rw [← lintegral_exp_gauss hY hY0 t]
    refine lintegral_congr_ae ?_
    filter_upwards [hXY] with ω hω
    rw [← hω, mul_add]
  calc ∫⁻ ω, ENNReal.ofReal (Real.exp (a * |X ω|)) ∂P
      ≤ ∫⁻ ω, (ENNReal.ofReal (Real.exp (a * X ω)) +
          ENNReal.ofReal (Real.exp (-a * X ω))) ∂P := by
        refine lintegral_mono fun ω => ?_
        rw [← ENNReal.ofReal_add (Real.exp_pos _).le (Real.exp_pos _).le]
        refine ENNReal.ofReal_le_ofReal ?_
        rcases abs_cases (X ω) with ⟨h1, -⟩ | ⟨h1, -⟩
        · rw [h1]; linarith [Real.exp_pos (-a * X ω)]
        · rw [h1, mul_neg, ← neg_mul]; linarith [Real.exp_pos (a * X ω)]
    _ = ∫⁻ ω, ENNReal.ofReal (Real.exp (a * X ω)) ∂P +
          ∫⁻ ω, ENNReal.ofReal (Real.exp (-a * X ω)) ∂P :=
        lintegral_add_left (ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp
          (hX.const_mul a))) _
    _ ≤ _ := by
        rw [two_mul]
        refine add_le_add (one a) ((one (-a)).trans_eq ?_)
        rw [neg_sq]

omit [IsProbabilityMeasure P] in
/-- **Chernoff**: `E e^{tY} ≤ 2 e^{B t²}` for `t ≥ 0` gives `P[Y > A] ≤ 2 e^{−A²/(4B)}`. -/
lemma tail_of_lintegral_exp {Y : Ω → ℝ} (hY : Measurable Y) {B : ℝ} (hB : 0 < B)
    (hm : ∀ t : ℝ, 0 ≤ t → ∫⁻ ω, ENNReal.ofReal (Real.exp (t * Y ω)) ∂P ≤
      2 * ENNReal.ofReal (Real.exp (B * t ^ 2))) (A : ℝ) (hA : 0 ≤ A) :
    P {ω | A < Y ω} ≤ ENNReal.ofReal (2 * Real.exp (-(1 / (4 * B)) * A ^ 2)) := by
  set t := A / (2 * B) with ht_def
  have ht : 0 ≤ t := by positivity
  have hf : Measurable fun ω => ENNReal.ofReal (Real.exp (t * Y ω)) :=
    ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp (hY.const_mul t))
  have hsub : {ω | A < Y ω} ⊆
      {ω | ENNReal.ofReal (Real.exp (t * A)) ≤ ENNReal.ofReal (Real.exp (t * Y ω))} :=
    fun ω hω => ENNReal.ofReal_le_ofReal
      (Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left (le_of_lt hω) ht))
  have hmk := mul_meas_ge_le_lintegral (μ := P) hf (ENNReal.ofReal (Real.exp (t * A)))
  have key : P {ω | A < Y ω} ≤ ENNReal.ofReal (Real.exp (-(t * A))) *
      (ENNReal.ofReal (Real.exp (t * A)) * P {ω | ENNReal.ofReal (Real.exp (t * A)) ≤
        ENNReal.ofReal (Real.exp (t * Y ω))}) := by
    rw [← mul_assoc, ← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add, neg_add_cancel,
      Real.exp_zero, ENNReal.ofReal_one, one_mul]
    exact measure_mono hsub
  refine key.trans ((mul_le_mul' le_rfl (hmk.trans (hm t ht))).trans (le_of_eq ?_))
  rw [mul_left_comm, ← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add,
    ← ENNReal.ofReal_ofNat 2, ← ENNReal.ofReal_mul (by norm_num)]
  congr 3
  rw [ht_def]; field_simp; ring

/-- **Jensen over a compact `S`**: uniform sub-Gaussian moments of `F(·, y)`, `y ∈ S`, give one
for `∫_S F(·, y) dy`. -/
lemma lintegral_exp_setIntegral_le {S : Set ℂ} (hS : IsCompact S) (hS0 : volume S ≠ 0)
    {F : Ω → ℂ → ℝ} (hFc : ∀ ω, Continuous (F ω)) (hFm : Measurable (Function.uncurry F))
    {M : ℝ} (hb : ∀ y ∈ S, ∀ a : ℝ,
      ∫⁻ ω, ENNReal.ofReal (Real.exp (a * F ω y)) ∂P ≤ 2 * ENNReal.ofReal (Real.exp (M * a ^ 2 / 2)))
    (κ : ℝ) :
    ∫⁻ ω, ENNReal.ofReal (Real.exp (κ * ∫ y in S, F ω y)) ∂P ≤
      2 * ENNReal.ofReal (Real.exp (M * (κ * (volume S).toReal) ^ 2 / 2)) := by
  have hBt : volume S ≠ ∞ := hS.measure_lt_top.ne
  set m := (volume S).toReal with hm
  have hm0 : 0 < m := ENNReal.toReal_pos hS0 hBt
  set a := κ * m
  have hJ : ∀ ω, ENNReal.ofReal (Real.exp (κ * ∫ y in S, F ω y)) ≤
      ENNReal.ofReal m⁻¹ * ∫⁻ y in S, ENNReal.ofReal (Real.exp (a * F ω y)) := by
    intro ω
    have hc : Continuous (F ω) := hFc ω
    have hi1 : IntegrableOn (fun y => a * F ω y) S :=
      (hc.const_mul a).continuousOn.integrableOn_compact hS
    have hi2 : IntegrableOn (fun y => Real.exp (a * F ω y)) S :=
      (Real.continuous_exp.comp (hc.const_mul a)).continuousOn.integrableOn_compact hS
    have hjen := ConvexOn.map_set_average_le (s := univ) (g := Real.exp) convexOn_exp
      Real.continuous_exp.continuousOn isClosed_univ hS0 hBt
      (Eventually.of_forall fun _ => mem_univ _) hi1 hi2
    rw [setAverage_eq, setAverage_eq, smul_eq_mul, smul_eq_mul, integral_const_mul,
      measureReal_def, ← hm] at hjen
    have hk : m⁻¹ * (a * ∫ y in S, F ω y) = κ * ∫ y in S, F ω y := by
      simp only [a]; field_simp
    rw [hk] at hjen
    refine (ENNReal.ofReal_le_ofReal hjen).trans_eq ?_
    rw [ENNReal.ofReal_mul (inv_nonneg.2 ENNReal.toReal_nonneg), ← hm,
      ofReal_integral_eq_lintegral_ofReal hi2 (Eventually.of_forall fun y => (Real.exp_pos _).le)]
  have hjm : Measurable (Function.uncurry fun ω y => ENNReal.ofReal (Real.exp (a * F ω y))) :=
    ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp (hFm.const_mul a))
  calc ∫⁻ ω, ENNReal.ofReal (Real.exp (κ * ∫ y in S, F ω y)) ∂P
      ≤ ∫⁻ ω, (ENNReal.ofReal m⁻¹ * ∫⁻ y in S, ENNReal.ofReal (Real.exp (a * F ω y))) ∂P :=
        lintegral_mono hJ
    _ = ENNReal.ofReal m⁻¹ * ∫⁻ y in S, (∫⁻ ω, ENNReal.ofReal (Real.exp (a * F ω y)) ∂P) := by
        rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, lintegral_lintegral_swap
          hjm.aemeasurable]
    _ ≤ ENNReal.ofReal m⁻¹ * ∫⁻ _y in S, 2 * ENNReal.ofReal (Real.exp (M * a ^ 2 / 2)) :=
        mul_le_mul' le_rfl (setLIntegral_mono measurable_const fun y hy => hb y hy a)
    _ = _ := by
        rw [setLIntegral_const, ← ENNReal.ofReal_toReal hBt, ← hm]
        have e : ∀ x y z w : ℝ≥0∞, x * (y * z * w) = y * z * (x * w) := fun x y z w => by ring
        rw [mul_comm (2 : ℝ≥0∞), e, ← ENNReal.ofReal_mul (inv_nonneg.2 hm0.le),
          inv_mul_cancel₀ hm0.ne', ENNReal.ofReal_one, mul_one, mul_comm]

end L22
end DG
end LQGMetric
