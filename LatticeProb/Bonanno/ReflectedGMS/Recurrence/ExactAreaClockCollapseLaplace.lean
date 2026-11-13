/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module ReflectedGMS.Recurrence.ExactAreaClockCollapseLaplace at commit fdb5cad; only the module paths of local imports are changed. -/
import Mathlib.Probability.Distributions.Exponential
import Mathlib.Probability.Independence.InfinitePi
import Mathlib.Probability.Independence.Integration
import Mathlib.MeasureTheory.Integral.Lebesgue.Markov
import Mathlib.MeasureTheory.Function.SpecialFunctions.Basic

/-!
# A weighted series of i.i.d. unit exponentials diverges when its weights do

Let `(E_i)_{i ∈ ι}` be i.i.d. `Exponential(1)` variables — the coordinates of
`Measure.infinitePi fun _ : ι => expMeasure 1` — and let `c : ι → [0, ∞)` be
deterministic weights.  The main result is

  `∑ c_i = ∞  ⟹  ∑ c_i E_i = ∞` almost surely       (`ae_tsum_ofReal_mul_eq_top`).

This is the probabilistic input that collapses the exact-holding area-clock residual
`ExactExponentialTimeChange.ExactAreaClockReachesLevelZeroIndices` onto the exponential
one, `EnvironmentWalkDataProducer.AreaClockReachesLevelZeroIndices`; the Fubini step over the
chain path is in `Recurrence/ExactAreaClockCollapse.lean`.  This file is pure probability and
imports Mathlib only.

## Library search (pinned Mathlib, 2026-09-16)

* Kolmogorov's three-series theorem: **absent**.
* Second Borel–Cantelli (`ProbabilityTheory.measure_limsup_eq_one`) and Kolmogorov's 0-1 law
  (`Probability/Independence/ZeroOne.lean`): present; not needed.
* `ProbabilityTheory.lintegral_prod_eq_prod_lintegral_of_indepFun` (finite products of
  independent `ℝ≥0∞`-valued variables) and `ProbabilityTheory.iIndepFun_infinitePi`
  (the coordinates of an infinite product are independent): present, used.
* Laplace transform / moment generating function of `expMeasure`: **absent**;
  `lintegral_exponentialPDF_eq_one` gives it after one pointwise identity.

## Proof: the Laplace transform, without the three-series theorem

* `lintegral_ofReal_exp_neg_mul_expMeasure_one`: `E[e^{-cE}] = 1/(1+c)`, because
  `e^{-t} e^{-ct}` is `(1+c)^{-1}` times the `Exponential(1+c)` density.
* `lintegral_prod_ofReal_exp_neg_mul`: by independence, for a finite `F`,
  `E[∏_{i∈F} e^{-c_i E_i}] = ∏_{i∈F} (1+c_i)^{-1}`.
* `ofReal_exp_neg_mul_measure_le`: Chernoff–Markov through the partial sum over `F`,
  `e^{-M} P(∑ c_i E_i ≤ M) ≤ E[∏_{i∈F} e^{-c_i E_i}]`.
* `one_add_sum_le_prod_one_add`: `1 + ∑_F c_i ≤ ∏_F (1 + c_i)`.

Hence `e^{-M} P(∑ c_i E_i ≤ M) · (1 + ∑_F c_i) ≤ 1` for every finite `F`.  The supremum over
`F` of `1 + ∑_F c_i` is `∞`, so `P(∑ c_i E_i ≤ M) = 0` for every `M ∈ ℕ`, and `∑ c_i E_i = ∞`
almost surely.  No logarithm and no case split on the size of the weights is needed: the
inequality `∏ (1 + c_i) ≥ 1 + ∑ c_i` treats large and small weights at once.
-/

set_option autoImplicit false

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace ReflectedGMS.ExactAreaClockCollapseLaplace

/-! ### Two elementary inequalities in `ℝ≥0∞` -/

/-- `ENNReal.ofReal` is subadditive on finite sums, with no sign condition. -/
theorem ofReal_finset_sum_le {ι : Type*} (s : Finset ι) (f : ι → ℝ) :
    ENNReal.ofReal (∑ i ∈ s, f i) ≤ ∑ i ∈ s, ENNReal.ofReal (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert j s hj ih =>
    rw [Finset.sum_insert hj, Finset.sum_insert hj]
    exact ENNReal.ofReal_add_le.trans (add_le_add le_rfl ih)

/-- `1 + ∑_{i ∈ s} x_i ≤ ∏_{i ∈ s} (1 + x_i)` in `ℝ≥0∞`. -/
theorem one_add_sum_le_prod_one_add {ι : Type*} (s : Finset ι) (x : ι → ℝ≥0∞) :
    1 + ∑ i ∈ s, x i ≤ ∏ i ∈ s, (1 + x i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert j s hj ih =>
    rw [Finset.sum_insert hj, Finset.prod_insert hj]
    calc 1 + (x j + ∑ i ∈ s, x i)
        = (1 + ∑ i ∈ s, x i) + x j * 1 := by ring
      _ ≤ (1 + ∑ i ∈ s, x i) + x j * (1 + ∑ i ∈ s, x i) :=
          add_le_add le_rfl (mul_le_mul' le_rfl le_self_add)
      _ = (1 + x j) * (1 + ∑ i ∈ s, x i) := by ring
      _ ≤ (1 + x j) * ∏ i ∈ s, (1 + x i) := mul_le_mul' le_rfl ih

/-- The per-factor identity `(1 + c)⁻¹ · (1 + c) = 1`, in the form used below. -/
theorem ofReal_one_div_one_add_mul {c : ℝ} (hc : 0 ≤ c) :
    ENNReal.ofReal (1 / (1 + c)) * (1 + ENNReal.ofReal c) = 1 := by
  have h1c : (0 : ℝ) < 1 + c := by linarith
  rw [← ENNReal.ofReal_one, ← ENNReal.ofReal_add zero_le_one hc,
    ← ENNReal.ofReal_mul (one_div_pos.mpr h1c).le, one_div_mul_cancel h1c.ne']

/-! ### The Laplace transform of the unit exponential law -/

/-- **`E[e^{-cE}] = 1/(1+c)`** for a unit exponential `E` and `c ≥ 0`: the integrand times the
unit exponential density is `(1+c)⁻¹` times the `Exponential(1+c)` density. -/
theorem lintegral_ofReal_exp_neg_mul_expMeasure_one {c : ℝ} (hc : 0 ≤ c) :
    ∫⁻ x, ENNReal.ofReal (Real.exp (-(x * c))) ∂(expMeasure 1)
      = ENNReal.ofReal (1 / (1 + c)) := by
  have h1c : (0 : ℝ) < 1 + c := by linarith
  have hpdf : ∀ r : ℝ, Measurable (exponentialPDF r) := fun r =>
    (measurable_exponentialPDFReal r).ennreal_ofReal
  have hmeas : Measurable fun x : ℝ => ENNReal.ofReal (Real.exp (-(x * c))) :=
    (measurable_id.mul_const c).neg.exp.ennreal_ofReal
  have hdens : expMeasure 1 = (volume : Measure ℝ).withDensity (exponentialPDF 1) := rfl
  have hpt : ∀ x : ℝ, (exponentialPDF 1 * fun y => ENNReal.ofReal (Real.exp (-(y * c)))) x
      = ENNReal.ofReal (1 / (1 + c)) * exponentialPDF (1 + c) x := by
    intro x
    show exponentialPDF 1 x * ENNReal.ofReal (Real.exp (-(x * c))) = _
    rcases le_or_gt 0 x with hx | hx
    · rw [exponentialPDF_of_nonneg hx, exponentialPDF_of_nonneg hx,
        ← ENNReal.ofReal_mul (p := 1 * Real.exp (-(1 * x))) (by positivity),
        ← ENNReal.ofReal_mul (p := 1 / (1 + c)) (one_div_pos.mpr h1c).le]
      refine congrArg ENNReal.ofReal ?_
      have hexp : Real.exp (-(1 * x)) * Real.exp (-(x * c)) = Real.exp (-((1 + c) * x)) := by
        rw [← Real.exp_add]
        exact congrArg Real.exp (by ring)
      calc 1 * Real.exp (-(1 * x)) * Real.exp (-(x * c))
          = Real.exp (-((1 + c) * x)) := by rw [one_mul (Real.exp (-(1 * x))), hexp]
        _ = 1 / (1 + c) * ((1 + c) * Real.exp (-((1 + c) * x))) := by
          rw [← mul_assoc, one_div_mul_cancel h1c.ne', one_mul]
    · rw [exponentialPDF_of_neg hx, exponentialPDF_of_neg hx, zero_mul, mul_zero]
  rw [hdens, lintegral_withDensity_eq_lintegral_mul _ (hpdf 1) hmeas, lintegral_congr hpt,
    lintegral_const_mul _ (hpdf (1 + c)), lintegral_exponentialPDF_eq_one h1c, mul_one]

/-- **Independence**: the Laplace functional of a finite weighted sum of the coordinates
factorises, `E[∏_{i∈F} e^{-c_i E_i}] = ∏_{i∈F} (1+c_i)⁻¹`. -/
theorem lintegral_prod_ofReal_exp_neg_mul {ι : Type*} {c : ι → ℝ} (hc : ∀ i, 0 ≤ c i)
    (F : Finset ι) :
    ∫⁻ t, ∏ i ∈ F, ENNReal.ofReal (Real.exp (-(t i * c i)))
        ∂(Measure.infinitePi fun _ : ι => expMeasure (1 : ℝ))
      = ∏ i ∈ F, ENNReal.ofReal (1 / (1 + c i)) := by
  have : IsProbabilityMeasure (expMeasure (1 : ℝ)) := isProbabilityMeasure_expMeasure one_pos
  have hX : ∀ i, Measurable fun x : ℝ => ENNReal.ofReal (Real.exp (-(x * c i))) := fun i =>
    (measurable_id.mul_const (c i)).neg.exp.ennreal_ofReal
  have hind : iIndepFun (fun i (t : ι → ℝ) => ENNReal.ofReal (Real.exp (-(t i * c i))))
      (Measure.infinitePi fun _ : ι => expMeasure (1 : ℝ)) :=
    iIndepFun_infinitePi (P := fun _ : ι => expMeasure (1 : ℝ))
      (X := fun i (x : ℝ) => ENNReal.ofReal (Real.exp (-(x * c i)))) hX
  have hmeas : ∀ i, Measurable fun t : ι → ℝ => ENNReal.ofReal (Real.exp (-(t i * c i))) :=
    fun i => (hX i).comp (measurable_pi_apply i)
  rw [lintegral_prod_eq_prod_lintegral_of_indepFun F _ hind hmeas]
  refine Finset.prod_congr rfl fun i _ => ?_
  have hmap : (Measure.infinitePi fun _ : ι => expMeasure (1 : ℝ)).map (fun t : ι → ℝ => t i)
      = expMeasure 1 := Measure.infinitePi_map_eval _ i
  calc ∫⁻ t, ENNReal.ofReal (Real.exp (-(t i * c i)))
        ∂(Measure.infinitePi fun _ : ι => expMeasure (1 : ℝ))
      = ∫⁻ x, ENNReal.ofReal (Real.exp (-(x * c i)))
          ∂((Measure.infinitePi fun _ : ι => expMeasure (1 : ℝ)).map fun t : ι → ℝ => t i) :=
        (lintegral_map (hX i) (measurable_pi_apply i)).symm
    _ = ∫⁻ x, ENNReal.ofReal (Real.exp (-(x * c i))) ∂(expMeasure 1) := by rw [hmap]
    _ = ENNReal.ofReal (1 / (1 + c i)) := lintegral_ofReal_exp_neg_mul_expMeasure_one (hc i)

/-! ### Chernoff–Markov through a finite partial sum -/

/-- **Chernoff–Markov bound** for the weighted series, through its partial sum over a finite
`F`: on `{∑ c_i t_i ≤ M}` the partial sum is `≤ M`, so `∏_{i∈F} e^{-c_i t_i} ≥ e^{-M}`.  The
measure is arbitrary; negative coordinates only help. -/
theorem ofReal_exp_neg_mul_measure_le {ι : Type*} (μ : Measure (ι → ℝ)) (c : ι → ℝ)
    (M : ℕ) (F : Finset ι) :
    ENNReal.ofReal (Real.exp (-(M : ℝ))) * μ {t | ∑' i, ENNReal.ofReal (t i * c i) ≤ M}
      ≤ ∫⁻ t, ∏ i ∈ F, ENNReal.ofReal (Real.exp (-(t i * c i))) ∂μ := by
  have hX : ∀ i, Measurable fun x : ℝ => ENNReal.ofReal (Real.exp (-(x * c i))) := fun i =>
    (measurable_id.mul_const (c i)).neg.exp.ennreal_ofReal
  have hmeas : ∀ i, Measurable fun t : ι → ℝ => ENNReal.ofReal (Real.exp (-(t i * c i))) :=
    fun i => (hX i).comp (measurable_pi_apply i)
  have hm : Measurable fun t : ι → ℝ => ∏ i ∈ F, ENNReal.ofReal (Real.exp (-(t i * c i))) :=
    Finset.measurable_prod F fun i _ => hmeas i
  have hsub : {t : ι → ℝ | ∑' i, ENNReal.ofReal (t i * c i) ≤ M} ⊆
      {t | ENNReal.ofReal (Real.exp (-(M : ℝ)))
        ≤ ∏ i ∈ F, ENNReal.ofReal (Real.exp (-(t i * c i)))} := by
    intro t ht
    have ht' : ∑' i, ENNReal.ofReal (t i * c i) ≤ M := ht
    have hle : ∑ i ∈ F, t i * c i ≤ M := by
      have h2 : ENNReal.ofReal (∑ i ∈ F, t i * c i) ≤ ENNReal.ofReal (M : ℝ) := by
        rw [ENNReal.ofReal_natCast]
        exact (ofReal_finset_sum_le F fun i => t i * c i).trans
          ((ENNReal.sum_le_tsum F).trans ht')
      exact (ENNReal.ofReal_le_ofReal_iff (Nat.cast_nonneg M)).mp h2
    show ENNReal.ofReal (Real.exp (-(M : ℝ)))
      ≤ ∏ i ∈ F, ENNReal.ofReal (Real.exp (-(t i * c i)))
    calc ENNReal.ofReal (Real.exp (-(M : ℝ)))
        ≤ ENNReal.ofReal (Real.exp (-(∑ i ∈ F, t i * c i))) :=
          ENNReal.ofReal_le_ofReal (Real.exp_le_exp.mpr (neg_le_neg hle))
      _ = ENNReal.ofReal (∏ i ∈ F, Real.exp (-(t i * c i))) := by
          rw [← Finset.sum_neg_distrib, Real.exp_sum]
      _ = ∏ i ∈ F, ENNReal.ofReal (Real.exp (-(t i * c i))) :=
          ENNReal.ofReal_prod_of_nonneg fun i _ => (Real.exp_pos _).le
  calc ENNReal.ofReal (Real.exp (-(M : ℝ))) * μ {t | ∑' i, ENNReal.ofReal (t i * c i) ≤ M}
      ≤ ENNReal.ofReal (Real.exp (-(M : ℝ))) *
          μ {t | ENNReal.ofReal (Real.exp (-(M : ℝ)))
            ≤ ∏ i ∈ F, ENNReal.ofReal (Real.exp (-(t i * c i)))} :=
        mul_le_mul' le_rfl (measure_mono hsub)
    _ ≤ ∫⁻ t, ∏ i ∈ F, ENNReal.ofReal (Real.exp (-(t i * c i))) ∂μ :=
        mul_meas_ge_le_lintegral₀ hm.aemeasurable _

/-! ### The divergence theorem -/

/-- **A weighted series of i.i.d. unit exponentials diverges almost surely as soon as its
weights do**: if `c ≥ 0` and `∑ c_i = ∞`, then `∑ c_i E_i = ∞` almost surely.  The index type
is arbitrary. -/
theorem ae_tsum_ofReal_mul_eq_top {ι : Type*} {c : ι → ℝ} (hc : ∀ i, 0 ≤ c i)
    (hsum : ∑' i, ENNReal.ofReal (c i) = ⊤) :
    ∀ᵐ t ∂(Measure.infinitePi fun _ : ι => expMeasure (1 : ℝ)),
      ∑' i, ENNReal.ofReal (t i * c i) = ⊤ := by
  have key : ∀ (M : ℕ) (F : Finset ι),
      ENNReal.ofReal (Real.exp (-(M : ℝ))) *
          (Measure.infinitePi fun _ : ι => expMeasure (1 : ℝ))
            {t | ∑' i, ENNReal.ofReal (t i * c i) ≤ M} *
        (1 + ∑ i ∈ F, ENNReal.ofReal (c i)) ≤ 1 := by
    intro M F
    calc ENNReal.ofReal (Real.exp (-(M : ℝ))) *
            (Measure.infinitePi fun _ : ι => expMeasure (1 : ℝ))
              {t | ∑' i, ENNReal.ofReal (t i * c i) ≤ M} *
          (1 + ∑ i ∈ F, ENNReal.ofReal (c i))
        ≤ (∏ i ∈ F, ENNReal.ofReal (1 / (1 + c i))) * ∏ i ∈ F, (1 + ENNReal.ofReal (c i)) :=
          mul_le_mul'
            ((ofReal_exp_neg_mul_measure_le _ c M F).trans
              (lintegral_prod_ofReal_exp_neg_mul hc F).le)
            (one_add_sum_le_prod_one_add F _)
      _ = ∏ i ∈ F, (ENNReal.ofReal (1 / (1 + c i)) * (1 + ENNReal.ofReal (c i))) :=
          Finset.prod_mul_distrib.symm
      _ = 1 := Finset.prod_eq_one fun i _ => ofReal_one_div_one_add_mul (hc i)
  have hsup : (⨆ F : Finset ι, (1 + ∑ i ∈ F, ENNReal.ofReal (c i))) = ⊤ := by
    refine top_le_iff.mp ?_
    calc (⊤ : ℝ≥0∞) = ⨆ F : Finset ι, ∑ i ∈ F, ENNReal.ofReal (c i) :=
          hsum.symm.trans ENNReal.tsum_eq_iSup_sum
      _ ≤ ⨆ F : Finset ι, (1 + ∑ i ∈ F, ENNReal.ofReal (c i)) :=
          iSup_mono fun _ => le_add_self
  have hzero : ∀ M : ℕ, (Measure.infinitePi fun _ : ι => expMeasure (1 : ℝ))
      {t | ∑' i, ENNReal.ofReal (t i * c i) ≤ M} = 0 := by
    intro M
    have htop : ENNReal.ofReal (Real.exp (-(M : ℝ))) *
        (Measure.infinitePi fun _ : ι => expMeasure (1 : ℝ))
          {t | ∑' i, ENNReal.ofReal (t i * c i) ≤ M} * ⊤ ≤ 1 := by
      rw [← hsup, ENNReal.mul_iSup]
      exact iSup_le fun F => key M F
    have hprod : ENNReal.ofReal (Real.exp (-(M : ℝ))) *
        (Measure.infinitePi fun _ : ι => expMeasure (1 : ℝ))
          {t | ∑' i, ENNReal.ofReal (t i * c i) ≤ M} = 0 := by
      by_contra hne
      rw [ENNReal.mul_top hne] at htop
      exact not_le.mpr ENNReal.one_lt_top htop
    exact (mul_eq_zero.mp hprod).resolve_left (ENNReal.ofReal_pos.mpr (Real.exp_pos _)).ne'
  have hsub : {t : ι → ℝ | ¬ ∑' i, ENNReal.ofReal (t i * c i) = ⊤} ⊆
      ⋃ M : ℕ, {t | ∑' i, ENNReal.ofReal (t i * c i) ≤ M} := by
    intro t ht
    obtain ⟨n, hn⟩ :=
      ENNReal.exists_nat_gt (show ∑' i, ENNReal.ofReal (t i * c i) ≠ ⊤ from ht)
    exact Set.mem_iUnion.mpr ⟨n, hn.le⟩
  rw [ae_iff]
  exact measure_mono_null hsub (measure_iUnion_null hzero)

end ReflectedGMS.ExactAreaClockCollapseLaplace
