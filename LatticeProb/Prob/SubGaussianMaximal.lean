module

public import Mathlib.Analysis.Complex.Exponential
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Series
public import Mathlib.MeasureTheory.Function.ConditionalExpectation.PullOut
public import Mathlib.MeasureTheory.Measure.Real
public import Mathlib.Probability.ConditionalExpectation
public import Mathlib.Probability.Independence.Basic
public import Mathlib.Probability.Martingale.Basic
public import Mathlib.Probability.Martingale.OptionalStopping
public import Mathlib.Probability.Moments.SubGaussian

@[expose] public section

/-!
# Sub-Gaussian bounds for sums of independent increments

This file collects three exponential bounds on sums of independent random variables.

* `lazySign_mgf_le`: the moment generating function of a lazy vertical step, which is `±1` with
  probability `1/4` each and `0` with probability `1/2`, is at most `exp (t ^ 2 / 4)`.
* `measure_sum_bernoulli_le`: the lower tail of a sum of `m` independent fair Bernoulli variables
  is at most `exp (-(2 r ^ 2) / m)`, by Hoeffding's inequality for centred bounded variables.
* `measure_exists_partialSum_ge_le`: the probability that some partial sum of the first `m`
  increments reaches the level `n` is at most `exp (-n ^ 2 / (2 m v))` when the increments are
  independent and sub-Gaussian with variance proxy `v`. This is Doob's maximal inequality applied
  to the exponential of the partial sums.

The file also records a nonvacuity check for `lazySign_mgf_le`.
-/

open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace LatticeProb

/-- The lazy vertical step, which is `±1` with probability `1/4` each and `0` with probability
`1/2`, has moment generating function at most `exp (t ^ 2 / 4)`. -/
theorem lazySign_mgf_le (t : ℝ) : (1 / 4) * Real.exp t + (1 / 4) * Real.exp (-t) + 1 / 2 ≤
    Real.exp (t ^ 2 / 4) := by
  have ha : Real.exp (t / 2) * (Real.exp (t / 2))⁻¹ = 1 :=
    mul_inv_cancel₀ (Real.exp_pos _).ne'
  have hcosh : Real.cosh (t / 2) = (Real.exp (t / 2) + (Real.exp (t / 2))⁻¹) / 2 := by
    rw [Real.cosh_eq, Real.exp_neg]
  have h1 : Real.exp t = Real.exp (t / 2) * Real.exp (t / 2) := by
    rw [← Real.exp_add]; congr 1; ring
  have h2 : Real.exp (-t) = (Real.exp (t / 2))⁻¹ * (Real.exp (t / 2))⁻¹ := by
    rw [← Real.exp_neg, ← Real.exp_add]; congr 1; ring
  have hid : Real.cosh (t / 2) ^ 2 = (1 / 4) * Real.exp t + (1 / 4) * Real.exp (-t) + 1 / 2 := by
    rw [hcosh, h1, h2]
    linear_combination (1 / 2) * ha
  have hsq : Real.cosh (t / 2) ^ 2 ≤ Real.exp (t ^ 2 / 4) := by
    have h := Real.cosh_le_exp_half_sq (t / 2)
    have hpos := (Real.cosh_pos (t / 2)).le
    calc Real.cosh (t / 2) ^ 2 ≤ Real.exp ((t / 2) ^ 2 / 2) ^ 2 := by gcongr
      _ = Real.exp (t ^ 2 / 4) := by rw [sq, ← Real.exp_add]; congr 1; ring
  linarith

/-- Lower tail for a sum of `m` independent fair Bernoulli variables. -/
theorem measure_sum_bernoulli_le {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
    [IsProbabilityMeasure P] (β : ℕ → Ω → ℝ) (hind : iIndepFun β P)
    (hmeas : ∀ i, Measurable (β i))
    (hβ : ∀ i, ∀ᵐ ω ∂P, β i ω = 0 ∨ β i ω = 1) (hmean : ∀ i, P[β i] = 1 / 2) (m : ℕ) {r : ℝ}
    (hr : 0 ≤ r) :
    P.real {ω | ∑ i ∈ Finset.range m, β i ω ≤ m / 2 - r} ≤ Real.exp (-(2 * r ^ 2) / m) := by
  have hint : ∀ i, Integrable (β i) P := fun i => by
    by_contra h
    have h' := hmean i
    rw [integral_undef h] at h'
    norm_num at h'
  have hX : ∀ i, HasSubgaussianMGF (fun ω => 1 / 2 - β i ω) (1 / 4) P := by
    intro i
    have hb : ∀ᵐ ω ∂P, (1 / 2 - β i ω) ∈ Set.Icc (-(1 / 2)) (1 / 2) := by
      filter_upwards [hβ i] with ω hω
      simp only [Set.mem_Icc]
      rcases hω with h | h <;> rw [h] <;> norm_num
    have hc : ∫ ω, (1 / 2 - β i ω) ∂P = 0 := by
      rw [integral_sub (integrable_const _) (hint i), hmean i]
      simp
    have hH := hasSubgaussianMGF_of_mem_Icc_of_integral_eq_zero
      (X := fun ω => 1 / 2 - β i ω) ((measurable_const.sub (hmeas i)).aemeasurable) hb hc
    convert hH using 2
    norm_num
  have hsum : ∀ ω, ∑ i ∈ Finset.range m, (1 / 2 - β i ω) =
      m / 2 - ∑ i ∈ Finset.range m, β i ω := by
    intro ω
    rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    ring
  have hset : {ω | ∑ i ∈ Finset.range m, β i ω ≤ m / 2 - r} =
      {ω | r ≤ ∑ i ∈ Finset.range m, (1 / 2 - β i ω)} := by
    ext ω
    simp only [Set.mem_setOf_eq, hsum]
    constructor <;> intro h <;> linarith
  have hind' : iIndepFun (fun i ω => 1 / 2 - β i ω) P :=
    hind.comp (fun _ x => 1 / 2 - x) (fun _ => measurable_const.sub measurable_id)
  rw [hset]
  refine (HasSubgaussianMGF.measure_sum_range_ge_le_of_iIndepFun hind' (c := 1 / 4) (n := m)
    (fun i _ => hX i) hr).trans (le_of_eq ?_)
  congr 1
  push_cast
  ring

section MaximalTail

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]

/-- A sub-Gaussian variable satisfies `1 + t * E X ≤ E exp (t X)` for every real `t`. -/
lemma one_add_mul_integral_le_mgf {X : Ω → ℝ} {c : ℝ≥0} (h : HasSubgaussianMGF X c P) (t : ℝ) :
    1 + t * P[X] ≤ mgf X P t := by
  have h1 : Integrable (fun ω => (1 : ℝ) + t * X ω) P :=
    (integrable_const _).add (h.integrable.const_mul t)
  have h2 : Integrable (fun ω => Real.exp (t * X ω)) P := h.integrable_exp_mul t
  have hle : ∫ ω, ((1 : ℝ) + t * X ω) ∂P ≤ ∫ ω, Real.exp (t * X ω) ∂P :=
    integral_mono h1 h2 (fun ω => by linarith [Real.add_one_le_exp (t * X ω)])
  rw [integral_add (integrable_const _) (h.integrable.const_mul t), integral_const,
    integral_const_mul] at hle
  simpa [mgf] using hle

/-- A sub-Gaussian variable has nonpositive mean. -/
lemma integral_le_zero_of_hasSubgaussianMGF {X : Ω → ℝ} {c : ℝ≥0}
    (h : HasSubgaussianMGF X c P) : P[X] ≤ 0 := by
  have hkey : ∀ t : ℝ, 0 < t → (c : ℝ) * t ^ 2 / 2 ≤ 1 → P[X] ≤ (c : ℝ) * t := by
    intro t ht hct
    have hy : 0 ≤ (c : ℝ) * t ^ 2 / 2 := by positivity
    have h3 : Real.exp ((c : ℝ) * t ^ 2 / 2) - 1 ≤ (c : ℝ) * t ^ 2 := by
      have h4 := Real.abs_exp_sub_one_le (x := (c : ℝ) * t ^ 2 / 2)
        (by rw [abs_of_nonneg hy]; exact hct)
      rw [abs_of_nonneg hy] at h4
      linarith [le_abs_self (Real.exp ((c : ℝ) * t ^ 2 / 2) - 1)]
    have h5 : t * P[X] ≤ t * ((c : ℝ) * t) := by
      have h6 := one_add_mul_integral_le_mgf h t
      have h7 := h.mgf_le t
      have h8 : t * ((c : ℝ) * t) = (c : ℝ) * t ^ 2 := by ring
      rw [h8]
      linarith
    exact le_of_mul_le_mul_left h5 ht
  by_contra hpos
  rw [not_le] at hpos
  have hC0 : (0 : ℝ) ≤ (c : ℝ) := c.2
  have hC1 : (0 : ℝ) < (c : ℝ) + 1 := by linarith
  have hε : (0 : ℝ) < P[X] / 2 := by linarith
  obtain ⟨t, ht⟩ : ∃ t : ℝ, t = min (P[X] / 2 / ((c : ℝ) + 1)) (1 / ((c : ℝ) + 1)) :=
    ⟨_, rfl⟩
  have ht0 : 0 < t := by rw [ht]; exact lt_min (div_pos hε hC1) (div_pos one_pos hC1)
  have ht1 : t ≤ P[X] / 2 / ((c : ℝ) + 1) := by rw [ht]; exact min_le_left _ _
  have ht2 : t ≤ 1 / ((c : ℝ) + 1) := by rw [ht]; exact min_le_right _ _
  have hCt : t * ((c : ℝ) + 1) ≤ P[X] / 2 := (le_div_iff₀ hC1).1 ht1
  have ht3 : t * ((c : ℝ) + 1) ≤ 1 := (le_div_iff₀ hC1).1 ht2
  have hCt1 : (c : ℝ) * t ≤ 1 := by nlinarith
  have htle1 : t ≤ 1 := by nlinarith
  have hct : (c : ℝ) * t ^ 2 / 2 ≤ 1 := by
    nlinarith [mul_le_mul hCt1 htle1 ht0.le zero_le_one]
  have hCle : (c : ℝ) * t ≤ P[X] / 2 := by nlinarith
  linarith [hkey t ht0 hct]

/-- A sub-Gaussian variable has mean zero. -/
lemma integral_eq_zero_of_hasSubgaussianMGF {X : Ω → ℝ} {c : ℝ≥0}
    (h : HasSubgaussianMGF X c P) : P[X] = 0 := by
  have h1 := integral_le_zero_of_hasSubgaussianMGF h
  have h2 := integral_le_zero_of_hasSubgaussianMGF h.neg
  have h3 : P[-X] = -P[X] := integral_neg (f := X)
  linarith

/-- The filtration `𝒢 k` generated by the first `k` increments `ξ 0, …, ξ (k - 1)`. -/
def incrFiltration (ξ : ℕ → Ω → ℝ) (hmeas : ∀ i, Measurable (ξ i)) : Filtration ℕ mΩ where
  seq k := ⨆ i ∈ Set.Iio k, MeasurableSpace.comap (ξ i) inferInstance
  mono' := by
    intro k l hkl
    exact iSup₂_le fun i hi =>
      le_iSup₂_of_le i (Set.mem_Iio.2 (lt_of_lt_of_le (Set.mem_Iio.1 hi) hkl)) le_rfl
  le' := by
    intro k
    exact iSup₂_le fun i _ => (hmeas i).comap_le

/-- A partial sum of the first `k` increments is measurable with respect to `𝒢 k`. -/
lemma measurable_partialSum_incr (ξ : ℕ → Ω → ℝ) (hmeas : ∀ i, Measurable (ξ i)) (k : ℕ) :
    Measurable[incrFiltration ξ hmeas k] (fun ω => ∑ i ∈ Finset.range k, ξ i ω) := by
  refine Finset.measurable_sum _ fun i hi => ?_
  have hi' : i < k := Finset.mem_range.1 hi
  exact (comap_measurable (ξ i)).mono
    (le_iSup₂ (f := fun i (_ : i ∈ Set.Iio k) => MeasurableSpace.comap (ξ i) inferInstance) i hi')
    le_rfl

/-- The maximal sub-Gaussian tail: for independent increments with sub-Gaussian moment generating
functions of variance proxy `v`, the running maximum of the partial sums up to `m` exceeds `n ≥ 0`
with probability at most `exp (-n² / (2 m v))`. -/
theorem measure_exists_partialSum_ge_le (ξ : ℕ → Ω → ℝ) (hind : iIndepFun ξ P)
    (hmeas : ∀ i, Measurable (ξ i))
    (v : ℝ≥0) (hξ : ∀ i, HasSubgaussianMGF (ξ i) v P) (m : ℕ) (hm : 0 < m) {n : ℝ} (hn : 0 ≤ n) :
    P.real {ω | ∃ k ≤ m, n ≤ ∑ i ∈ Finset.range k, ξ i ω} ≤ Real.exp (-(n ^ 2) / (2 * m * v)) := by
  have htriv : ∀ A : Set Ω, P.real A ≤ 1 := fun A =>
    (measureReal_mono (Set.subset_univ A)).trans (by simp)
  rcases eq_or_lt_of_le hn with hn0 | hnpos
  · refine (htriv _).trans (le_of_eq ?_)
    rw [← hn0]
    simp
  rcases eq_or_lt_of_le (show (0 : ℝ≥0) ≤ v by positivity) with hv0 | hvpos
  · refine (htriv _).trans (le_of_eq ?_)
    rw [← hv0]
    simp
  have hv : (0 : ℝ) < v := NNReal.coe_pos.2 hvpos
  have hmR : (0 : ℝ) < m := Nat.cast_pos.2 hm
  obtain ⟨θ, hθdef⟩ : ∃ θ : ℝ, θ = n / (m * v) := ⟨_, rfl⟩
  have hθ : 0 < θ := by rw [hθdef]; exact div_pos hnpos (mul_pos hmR hv)
  obtain ⟨f, hf⟩ : ∃ f : ℕ → Ω → ℝ, ∀ k ω, f k ω = Real.exp (θ * ∑ i ∈ Finset.range k, ξ i ω) :=
    ⟨_, fun _ _ => rfl⟩
  have hS : ∀ k, HasSubgaussianMGF (fun ω => ∑ i ∈ Finset.range k, ξ i ω)
      (∑ i ∈ Finset.range k, v) P :=
    fun k => HasSubgaussianMGF.sum_of_iIndepFun hind (c := fun _ => v) (fun i _ => hξ i)
  have hfnn : ∀ k ω, 0 ≤ f k ω := fun k ω => by rw [hf]; exact (Real.exp_pos _).le
  have hint : ∀ k, Integrable (f k) P := by
    intro k
    have hfk : f k = fun ω => Real.exp (θ * ∑ i ∈ Finset.range k, ξ i ω) := funext (hf k)
    rw [hfk]
    exact (hS k).integrable_exp_mul θ
  have hfe : ∀ i, f (i + 1) = f i * fun ω => Real.exp (θ * ξ i ω) := by
    intro i
    funext ω
    simp only [hf, Pi.mul_apply, Finset.sum_range_succ, mul_add, Real.exp_add]
  have hadp : StronglyAdapted (incrFiltration ξ hmeas) f := by
    intro k
    have hfk : f k = fun ω => Real.exp (θ * ∑ i ∈ Finset.range k, ξ i ω) := funext (hf k)
    have hmk : Measurable[incrFiltration ξ hmeas k] (f k) := by
      rw [hfk]
      exact Real.measurable_exp.comp (measurable_const.mul (measurable_partialSum_incr ξ hmeas k))
    exact hmk.stronglyMeasurable
  have hcond : ∀ i, f i ≤ᵐ[P] P[f (i + 1) | incrFiltration ξ hmeas i] := by
    intro i
    have hmi : StronglyMeasurable[incrFiltration ξ hmeas i] (f i) := by
      have hfk : f i = fun ω => Real.exp (θ * ∑ j ∈ Finset.range i, ξ j ω) := funext (hf i)
      have hmk : Measurable[incrFiltration ξ hmeas i] (f i) := by
        rw [hfk]
        exact Real.measurable_exp.comp
          (measurable_const.mul (measurable_partialSum_incr ξ hmeas i))
      exact hmk.stronglyMeasurable
    have hint_e : Integrable (fun ω => Real.exp (θ * ξ i ω)) P := (hξ i).integrable_exp_mul θ
    have hE1 : 1 ≤ P[fun ω => Real.exp (θ * ξ i ω)] := by
      have h1 := one_add_mul_integral_le_mgf (hξ i) θ
      rw [integral_eq_zero_of_hasSubgaussianMGF (hξ i), mul_zero, add_zero] at h1
      exact h1
    have hindep : Indep (incrFiltration ξ hmeas i)
        (MeasurableSpace.comap (ξ i) inferInstance) P := by
      have hbig := indep_iSup_of_disjoint (m := fun j => MeasurableSpace.comap (ξ j) inferInstance)
        (fun j => (hmeas j).comap_le) ((iIndepFun_iff_iIndep (fun _ => inferInstance) ξ P).1 hind)
        (S := Set.Iio i) (T := {i}) (by simp)
      simp only [iSup_singleton] at hbig
      exact hbig
    have hm_e : Measurable[MeasurableSpace.comap (ξ i) inferInstance]
        (fun ω => Real.exp (θ * ξ i ω)) :=
      Real.measurable_exp.comp (measurable_const.mul (comap_measurable (ξ i)))
    have hcond_e : P[fun ω => Real.exp (θ * ξ i ω) | incrFiltration ξ hmeas i] =ᵐ[P]
        fun _ => P[fun ω => Real.exp (θ * ξ i ω)] :=
      condExp_indep_eq (hmeas i).comap_le ((incrFiltration ξ hmeas).le i)
        hm_e.stronglyMeasurable hindep.symm
    have hfg : Integrable (f i * fun ω => Real.exp (θ * ξ i ω)) P := by
      rw [← hfe i]
      exact hint (i + 1)
    have hcond_mul := condExp_mul_of_stronglyMeasurable_left hmi hfg hint_e
    have hcond' : P[f (i + 1) | incrFiltration ξ hmeas i] =ᵐ[P]
        fun ω => f i ω * P[fun ω => Real.exp (θ * ξ i ω)] := by
      rw [hfe i]
      filter_upwards [hcond_mul, hcond_e] with ω h1 h2
      rw [h1, Pi.mul_apply, h2]
    filter_upwards [hcond'] with ω hω
    rw [hω]
    exact le_mul_of_one_le_right (hfnn i ω) hE1
  have hsub : Submartingale f (incrFiltration ξ hmeas) P :=
    submartingale_nat hadp hint hcond
  obtain ⟨ε, hε⟩ : ∃ ε : ℝ≥0, (ε : ℝ) = Real.exp (θ * n) :=
    ⟨Real.toNNReal (Real.exp (θ * n)), Real.coe_toNNReal _ (Real.exp_pos _).le⟩
  have hA : {ω | ∃ k ≤ m, n ≤ ∑ i ∈ Finset.range k, ξ i ω} ⊆
      {ω | (ε : ℝ) ≤ (Finset.range (m + 1)).sup' Finset.nonempty_range_add_one
        (fun k => f k ω)} := by
    intro ω hω
    obtain ⟨k, hk, hnk⟩ := hω
    show (ε : ℝ) ≤ _
    refine le_trans ?_ (Finset.le_sup' (fun k => f k ω) (Finset.mem_range.2 (Nat.lt_succ_of_le hk)))
    show (ε : ℝ) ≤ f k ω
    rw [hε, hf]
    exact Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left hnk hθ.le)
  have hdoob := MeasureTheory.maximal_ineq hsub (fun k ω => hfnn k ω) (ε := ε) m
  have hsumv : (∑ _i ∈ Finset.range m, (v : ℝ)) = m * v := by
    simp
  have hM : ∫ ω, f m ω ∂P ≤ Real.exp ((m * v) * θ ^ 2 / 2) := by
    have hfm : f m = fun ω => Real.exp (θ * ∑ i ∈ Finset.range m, ξ i ω) := funext (hf m)
    have h := (hS m).mgf_le θ
    calc ∫ ω, f m ω ∂P = mgf (fun ω => ∑ i ∈ Finset.range m, ξ i ω) P θ := by
          rw [hfm]; rfl
      _ ≤ Real.exp ((∑ _i ∈ Finset.range m, (v : ℝ)) * θ ^ 2 / 2) := by
          rw [NNReal.coe_sum] at h
          exact h
      _ = Real.exp ((m * v) * θ ^ 2 / 2) := by rw [hsumv]
  have h1 : (ε : ENNReal) * P {ω | ∃ k ≤ m, n ≤ ∑ i ∈ Finset.range k, ξ i ω} ≤
      ENNReal.ofReal (Real.exp ((m * v) * θ ^ 2 / 2)) :=
    (mul_le_mul_of_nonneg_left (measure_mono hA) (by positivity)).trans
      (hdoob.trans (ENNReal.ofReal_le_ofReal
        ((setIntegral_le_integral (hint m) (ae_of_all _ (hfnn m))).trans hM)))
  have h2 := ENNReal.toReal_mono ENNReal.ofReal_ne_top h1
  rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (Real.exp_pos _).le, ENNReal.coe_toReal,
    ← measureReal_def] at h2
  rw [hε] at h2
  have hpos : (0 : ℝ) < Real.exp (θ * n) := Real.exp_pos _
  have key : P.real {ω | ∃ k ≤ m, n ≤ ∑ i ∈ Finset.range k, ξ i ω} ≤
      Real.exp ((m * v) * θ ^ 2 / 2) / Real.exp (θ * n) := by
    rw [le_div_iff₀ hpos]
    linarith [h2, mul_comm (P.real {ω | ∃ k ≤ m, n ≤ ∑ i ∈ Finset.range k, ξ i ω})
      (Real.exp (θ * n))]
  refine key.trans (le_of_eq ?_)
  rw [← Real.exp_sub]
  congr 1
  have hm0 : (m : ℝ) ≠ 0 := hmR.ne'
  have hv0' : (v : ℝ) ≠ 0 := hv.ne'
  rw [hθdef]
  field_simp
  ring

end MaximalTail

namespace SubGaussianMaximalExample

/-- At `t = 1`, the lazy vertical step bound reads `(1/4) e + (1/4) e⁻¹ + 1/2 ≤ e^{1/4}`. -/
theorem lazySign_mgf_le_one :
    (1 / 4) * Real.exp 1 + (1 / 4) * Real.exp (-1) + 1 / 2 ≤ Real.exp (1 ^ 2 / 4) :=
  lazySign_mgf_le 1

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]

/-- The constant zero family is independent. -/
theorem iIndepFun_zero_family : iIndepFun (fun (_ : ℕ) (_ : Ω) => (0 : ℝ)) P := by
  rw [iIndepFun_iff_measure_inter_preimage_eq_mul]
  intro S sets _
  by_cases h : ∀ i ∈ S, (0 : ℝ) ∈ sets i
  · have h1 : ∀ i ∈ S, P ((fun _ : Ω => (0 : ℝ)) ⁻¹' sets i) = 1 := by
      intro i hi
      have hu : (fun _ : Ω => (0 : ℝ)) ⁻¹' sets i = Set.univ := by
        ext ω
        exact ⟨fun _ => Set.mem_univ _, fun _ => h i hi⟩
      rw [hu, measure_univ]
    have h2 : (⋂ i ∈ S, (fun _ : Ω => (0 : ℝ)) ⁻¹' sets i) = Set.univ := by
      ext ω
      exact ⟨fun _ => Set.mem_univ _, fun _ => Set.mem_iInter₂.2 fun i hi => h i hi⟩
    rw [h2, measure_univ, Finset.prod_eq_one h1]
  · push Not at h
    obtain ⟨i, hi, hn⟩ := h
    have h1 : (fun _ : Ω => (0 : ℝ)) ⁻¹' sets i = ∅ := by
      ext ω
      exact ⟨fun hω => hn hω, fun hω => hω.elim⟩
    have hz : P ((fun _ : Ω => (0 : ℝ)) ⁻¹' sets i) = 0 := by
      rw [h1, measure_empty]
    rw [Finset.prod_eq_zero hi hz]
    exact measure_mono_null (Set.iInter₂_subset i hi) hz

/-- The constant zero family is sub-Gaussian with variance proxy `1`. -/
theorem hasSubgaussianMGF_zero_one : HasSubgaussianMGF (fun _ : Ω => (0 : ℝ)) 1 P := by
  have h := hasSubgaussianMGF_of_mem_Icc_of_integral_eq_zero (μ := P)
    (X := fun _ : Ω => (0 : ℝ)) (a := -1) (b := 1) aemeasurable_const
    (ae_of_all _ fun _ => by norm_num) (by simp)
  convert h using 2
  norm_num

/-- Nonvacuity of the maximal tail for the zero family, with variance proxy `1`. -/
theorem measure_exists_partialSum_zero (m : ℕ) (hm : 0 < m) {n : ℝ} (hn : 0 ≤ n) :
    P.real {ω | ∃ k ≤ m, n ≤ ∑ i ∈ Finset.range k, (fun (_ : ℕ) (_ : Ω) => (0 : ℝ)) i ω} ≤
      Real.exp (-(n ^ 2) / (2 * m * ((1 : ℝ≥0) : ℝ))) :=
  LatticeProb.measure_exists_partialSum_ge_le (fun _ _ => 0) iIndepFun_zero_family
    (fun _ => measurable_const) 1 (fun _ => hasSubgaussianMGF_zero_one) m hm hn

end SubGaussianMaximalExample

end LatticeProb
