/-
The second and fourth moments of a finite sum of independent centred real
random variables.

`integral_pow_four_finsetSum_le` is the four-index expansion carried out one
summand at a time: for `j` outside the index set the summand `X j` is
independent of the partial sum `S`, so

  `E[(X j + S)^4] = E[X j^4] + 6 E[X j^2] E[S^2] + E[S^4]`,

the terms with a lone factor of `X j` or of `S` vanishing because both are
centred.  Together with `E[S^2] = ∑ E[X i^2]` this gives

  `E[(∑ X i)^4] ≤ ∑ E[X i^4] + 3 (∑ E[X i^2])^2`,

the bound the fourth-moment method uses.  All the integrability side conditions
come from a single fourth moment: on a probability space `|t|^p ≤ 1 + t^4` for
`p ≤ 4`, and a product of independent integrable functions is integrable.
-/
import Mathlib.Probability.Independence.Integration
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Pi

open MeasureTheory ProbabilityTheory Finset

namespace LatticeProb

variable {Ω ι : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

/-! ### Integrability from a fourth moment -/

theorem abs_pow_le_one_add_pow_four (t : ℝ) {p : ℕ} (hp : p ≤ 4) : |t ^ p| ≤ 1 + t ^ 4 := by
  rw [abs_pow]
  have h4 : (0 : ℝ) ≤ t ^ 4 := by positivity
  rcases le_or_gt |t| 1 with h | h
  · have : |t| ^ p ≤ 1 := pow_le_one₀ (abs_nonneg t) h
    linarith
  · have h1 : (1 : ℝ) ≤ |t| := h.le
    have h2 : |t| ^ p ≤ |t| ^ 4 := pow_le_pow_right₀ h1 hp
    have h3 : |t| ^ 4 = t ^ 4 := by rw [← abs_pow, abs_of_nonneg h4]
    rw [h3] at h2
    linarith

theorem integrable_pow_of_integrable_pow_four {f : Ω → ℝ} (hf : AEStronglyMeasurable f P)
    (h4 : Integrable (fun ω => f ω ^ 4) P) {p : ℕ} (hp : p ≤ 4) :
    Integrable (fun ω => f ω ^ p) P := by
  refine Integrable.mono' ((integrable_const (1 : ℝ)).add h4) (hf.pow p) ?_
  filter_upwards with ω
  rw [Real.norm_eq_abs]
  exact abs_pow_le_one_add_pow_four (f ω) hp

theorem pow_four_add_le (a b : ℝ) : (a + b) ^ 4 ≤ 8 * (a ^ 4 + b ^ 4) := by
  nlinarith [sq_nonneg (a - b), sq_nonneg (a + b), sq_nonneg ((a + b) * (a - b)),
    sq_nonneg (a * a - b * b), sq_nonneg (a * a + b * b), sq_nonneg ((a - b) ^ 2)]

omit [IsProbabilityMeasure P] in
/-- The pointwise finite sum of almost everywhere strongly measurable functions. -/
theorem aestronglyMeasurable_sum_apply (X : ι → Ω → ℝ)
    (hm : ∀ i, AEStronglyMeasurable (X i) P) (s : Finset ι) :
    AEStronglyMeasurable (fun ω => ∑ i ∈ s, X i ω) P := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using (aestronglyMeasurable_const (b := (0 : ℝ)) (μ := P))
  | insert j s hj ih =>
      have hrw : (fun ω => ∑ i ∈ insert j s, X i ω) = fun ω => X j ω + ∑ i ∈ s, X i ω := by
        funext ω; rw [Finset.sum_insert hj]
      rw [hrw]
      exact (hm j).add ih

theorem integrable_sum_pow_four (X : ι → Ω → ℝ) (hm : ∀ i, AEStronglyMeasurable (X i) P)
    (h4 : ∀ i, Integrable (fun ω => X i ω ^ 4) P) (s : Finset ι) :
    Integrable (fun ω => (∑ i ∈ s, X i ω) ^ 4) P := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert j s hj ih =>
      have hrw : (fun ω => (∑ i ∈ insert j s, X i ω) ^ 4)
          = fun ω => (X j ω + ∑ i ∈ s, X i ω) ^ 4 := by
        funext ω; rw [Finset.sum_insert hj]
      have hms : AEStronglyMeasurable (fun ω => X j ω + ∑ i ∈ s, X i ω) P :=
        (hm j).add (aestronglyMeasurable_sum_apply X hm s)
      rw [hrw]
      refine Integrable.mono' (((h4 j).add ih).const_mul 8) (hms.pow 4) ?_
      filter_upwards with ω
      rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      exact pow_four_add_le (X j ω) (∑ i ∈ s, X i ω)

/-! ### The moments of an independent centred sum -/

section
variable (X : ι → Ω → ℝ) (hmeas : ∀ i, Measurable (X i)) (hindep : iIndepFun X P)
  (h4 : ∀ i, Integrable (fun ω => X i ω ^ 4) P) (hmean : ∀ i, ∫ ω, X i ω ∂P = 0)

include hmeas h4 in
theorem integrable_sum_apply (s : Finset ι) :
    Integrable (fun ω => ∑ i ∈ s, X i ω) P := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert j s hj ih =>
      have hrw : (fun ω => ∑ i ∈ insert j s, X i ω) = fun ω => X j ω + ∑ i ∈ s, X i ω := by
        funext ω; rw [Finset.sum_insert hj]
      rw [hrw]
      refine Integrable.add ?_ ih
      have := integrable_pow_of_integrable_pow_four (hmeas j).aestronglyMeasurable (h4 j)
        (p := 1) (by norm_num)
      simpa using this

include hmeas h4 hmean in
theorem integral_sum_apply_eq_zero (s : Finset ι) :
    ∫ ω, (∑ i ∈ s, X i ω) ∂P = 0 := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert j s hj ih =>
      have hrw : (fun ω => ∑ i ∈ insert j s, X i ω) = fun ω => X j ω + ∑ i ∈ s, X i ω := by
        funext ω; rw [Finset.sum_insert hj]
      have hj1 : Integrable (fun ω => X j ω) P := by
        have := integrable_pow_of_integrable_pow_four (hmeas j).aestronglyMeasurable (h4 j)
          (p := 1) (by norm_num)
        simpa using this
      rw [hrw, integral_add hj1 (integrable_sum_apply X hmeas h4 s), ih, hmean j, add_zero]

omit [IsProbabilityMeasure P] in
include hmeas hindep in
/-- A summand is independent of the sum of the others. -/
theorem indepFun_sum_apply {j : ι} {s : Finset ι} (hj : j ∉ s) :
    IndepFun (fun ω => X j ω) (fun ω => ∑ i ∈ s, X i ω) P := by
  have h := hindep.indepFun_finsetSum_of_notMem hmeas hj
  have he : (∑ i ∈ s, X i) = fun ω => ∑ i ∈ s, X i ω := by
    funext ω; exact Finset.sum_apply ω s X
  rw [he] at h
  exact h.symm

include hmeas hindep h4 hmean in
/-- The second moment of an independent centred sum. -/
theorem integral_sq_finsetSum (s : Finset ι) :
    ∫ ω, (∑ i ∈ s, X i ω) ^ 2 ∂P = ∑ i ∈ s, ∫ ω, X i ω ^ 2 ∂P := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert j s hj ih =>
      have hmS : AEStronglyMeasurable (fun ω => ∑ i ∈ s, X i ω) P :=
        aestronglyMeasurable_sum_apply X (fun i => (hmeas i).aestronglyMeasurable) s
      have hSj := indepFun_sum_apply X hmeas hindep hj
      have hj1 : Integrable (fun ω => X j ω) P := by
        have := integrable_pow_of_integrable_pow_four (hmeas j).aestronglyMeasurable (h4 j)
          (p := 1) (by norm_num)
        simpa using this
      have hi2 : Integrable (fun ω => X j ω ^ 2) P :=
        integrable_pow_of_integrable_pow_four (hmeas j).aestronglyMeasurable (h4 j) (by norm_num)
      have hS2 : Integrable (fun ω => (∑ i ∈ s, X i ω) ^ 2) P :=
        integrable_pow_of_integrable_pow_four hmS
          (integrable_sum_pow_four X (fun i => (hmeas i).aestronglyMeasurable) h4 s)
          (by norm_num)
      have hcross : Integrable (fun ω => 2 * (X j ω * ∑ i ∈ s, X i ω)) P :=
        (hSj.integrable_mul hj1 (integrable_sum_apply X hmeas h4 s)).const_mul 2
      have hxc : ∫ ω, X j ω * (∑ i ∈ s, X i ω) ∂P = 0 := by
        rw [hSj.integral_fun_mul_eq_mul_integral (hmeas j).aestronglyMeasurable hmS,
          hmean j, zero_mul]
      have hrw : (fun ω => (∑ i ∈ insert j s, X i ω) ^ 2)
          = fun ω => X j ω ^ 2 + 2 * (X j ω * ∑ i ∈ s, X i ω) + (∑ i ∈ s, X i ω) ^ 2 := by
        funext ω; rw [Finset.sum_insert hj]; ring
      have hpair : Integrable
          (fun ω => X j ω ^ 2 + 2 * (X j ω * ∑ i ∈ s, X i ω)) P := hi2.add hcross
      rw [hrw, integral_add hpair hS2, integral_add hi2 hcross,
        integral_const_mul, hxc, ih, Finset.sum_insert hj]
      ring

include hmeas hindep h4 hmean in
/-- The fourth moment of an independent centred sum, in the form the
fourth-moment method uses. -/
theorem integral_pow_four_finsetSum_le (s : Finset ι) :
    ∫ ω, (∑ i ∈ s, X i ω) ^ 4 ∂P
      ≤ (∑ i ∈ s, ∫ ω, X i ω ^ 4 ∂P) + 3 * (∑ i ∈ s, ∫ ω, X i ω ^ 2 ∂P) ^ 2 := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert j s hj ih =>
      have hmS : AEStronglyMeasurable (fun ω => ∑ i ∈ s, X i ω) P :=
        aestronglyMeasurable_sum_apply X (fun i => (hmeas i).aestronglyMeasurable) s
      have hS4 : Integrable (fun ω => (∑ i ∈ s, X i ω) ^ 4) P :=
        integrable_sum_pow_four X (fun i => (hmeas i).aestronglyMeasurable) h4 s
      have hSj := indepFun_sum_apply X hmeas hindep hj
      have hA : ∀ p : ℕ, p ≤ 4 → Integrable (fun ω => X j ω ^ p) P := fun p hp =>
        integrable_pow_of_integrable_pow_four (hmeas j).aestronglyMeasurable (h4 j) hp
      have hB : ∀ p : ℕ, p ≤ 4 → Integrable (fun ω => (∑ i ∈ s, X i ω) ^ p) P := fun p hp =>
        integrable_pow_of_integrable_pow_four hmS hS4 hp
      have hind : ∀ p q : ℕ,
          IndepFun (fun ω => X j ω ^ p) (fun ω => (∑ i ∈ s, X i ω) ^ q) P := fun p q =>
        hSj.comp (measurable_id.pow_const p) (measurable_id.pow_const q)
      have hmix : ∀ p q : ℕ, p ≤ 4 → q ≤ 4 →
          Integrable (fun ω => X j ω ^ p * (∑ i ∈ s, X i ω) ^ q) P := fun p q hp hq =>
        (hind p q).integrable_mul (hA p hp) (hB q hq)
      have hprod : ∀ p q : ℕ, ∫ ω, X j ω ^ p * (∑ i ∈ s, X i ω) ^ q ∂P
          = (∫ ω, X j ω ^ p ∂P) * ∫ ω, (∑ i ∈ s, X i ω) ^ q ∂P := fun p q =>
        (hind p q).integral_fun_mul_eq_mul_integral
          ((hmeas j).aestronglyMeasurable.pow p) (hmS.pow q)
      have hmeanA : ∫ ω, X j ω ^ 1 ∂P = 0 := by simpa using hmean j
      have hmeanB : ∫ ω, (∑ i ∈ s, X i ω) ^ 1 ∂P = 0 := by
        simpa using integral_sum_apply_eq_zero X hmeas h4 hmean s
      have t1 : Integrable (fun ω => X j ω ^ 4) P := hA 4 le_rfl
      have t2 : Integrable (fun ω => 4 * (X j ω ^ 3 * (∑ i ∈ s, X i ω) ^ 1)) P :=
        (hmix 3 1 (by norm_num) (by norm_num)).const_mul 4
      have t3 : Integrable (fun ω => 6 * (X j ω ^ 2 * (∑ i ∈ s, X i ω) ^ 2)) P :=
        (hmix 2 2 (by norm_num) (by norm_num)).const_mul 6
      have t4 : Integrable (fun ω => 4 * (X j ω ^ 1 * (∑ i ∈ s, X i ω) ^ 3)) P :=
        (hmix 1 3 (by norm_num) (by norm_num)).const_mul 4
      have t5 : Integrable (fun ω => (∑ i ∈ s, X i ω) ^ 4) P := hB 4 le_rfl
      have hrw : (fun ω => (∑ i ∈ insert j s, X i ω) ^ 4)
          = fun ω => X j ω ^ 4 + 4 * (X j ω ^ 3 * (∑ i ∈ s, X i ω) ^ 1)
              + 6 * (X j ω ^ 2 * (∑ i ∈ s, X i ω) ^ 2)
              + 4 * (X j ω ^ 1 * (∑ i ∈ s, X i ω) ^ 3) + (∑ i ∈ s, X i ω) ^ 4 := by
        funext ω; rw [Finset.sum_insert hj]; ring
      have hsplit : ∫ ω, (∑ i ∈ insert j s, X i ω) ^ 4 ∂P
          = (∫ ω, X j ω ^ 4 ∂P)
            + 6 * ((∫ ω, X j ω ^ 2 ∂P) * ∫ ω, (∑ i ∈ s, X i ω) ^ 2 ∂P)
            + ∫ ω, (∑ i ∈ s, X i ω) ^ 4 ∂P := by
        have u12 : Integrable
            (fun ω => X j ω ^ 4 + 4 * (X j ω ^ 3 * (∑ i ∈ s, X i ω) ^ 1)) P := t1.add t2
        have u123 : Integrable
            (fun ω => X j ω ^ 4 + 4 * (X j ω ^ 3 * (∑ i ∈ s, X i ω) ^ 1)
              + 6 * (X j ω ^ 2 * (∑ i ∈ s, X i ω) ^ 2)) P := u12.add t3
        have u1234 : Integrable
            (fun ω => X j ω ^ 4 + 4 * (X j ω ^ 3 * (∑ i ∈ s, X i ω) ^ 1)
              + 6 * (X j ω ^ 2 * (∑ i ∈ s, X i ω) ^ 2)
              + 4 * (X j ω ^ 1 * (∑ i ∈ s, X i ω) ^ 3)) P := u123.add t4
        rw [hrw, integral_add u1234 t5, integral_add u123 t4, integral_add u12 t3,
          integral_add t1 t2, integral_const_mul, integral_const_mul, integral_const_mul,
          hprod 3 1, hprod 2 2, hprod 1 3, hmeanA, hmeanB]
        ring
      have hS2eq : ∫ ω, (∑ i ∈ s, X i ω) ^ 2 ∂P = ∑ i ∈ s, ∫ ω, X i ω ^ 2 ∂P :=
        integral_sq_finsetSum X hmeas hindep h4 hmean s
      have hpos : 0 ≤ ∫ ω, X j ω ^ 2 ∂P := integral_nonneg fun ω => by positivity
      have hpos' : 0 ≤ ∑ i ∈ s, ∫ ω, X i ω ^ 2 ∂P :=
        Finset.sum_nonneg fun i _ => integral_nonneg fun ω => by positivity
      rw [hsplit, hS2eq, Finset.sum_insert hj, Finset.sum_insert hj]
      nlinarith [ih, hpos, hpos', sq_nonneg (∫ ω, X j ω ^ 2 ∂P)]

include hmeas hindep h4 hmean in
/-- Chebyshev's inequality for an independent centred sum: the probability that
the sum reaches `ε` is at most its second moment divided by `ε^2`.  This is the
weak law for a weighted independent sum, applied to `X i = w i (ξ i - m)`: the
right side is `(∑ w i^2 σ^2)/ε^2`, which tends to zero as soon as no single
weight carries a positive fraction of `∑ w i`. -/
theorem measureReal_abs_sum_ge_le (s : Finset ι) {ε : ℝ} (hε : 0 < ε) :
    P.real {ω | ε ≤ |∑ i ∈ s, X i ω|} ≤ (∑ i ∈ s, ∫ ω, X i ω ^ 2 ∂P) / ε ^ 2 := by
  have hmS : AEStronglyMeasurable (fun ω => ∑ i ∈ s, X i ω) P :=
    aestronglyMeasurable_sum_apply X (fun i => (hmeas i).aestronglyMeasurable) s
  have hS2 : Integrable (fun ω => (∑ i ∈ s, X i ω) ^ 2) P :=
    integrable_pow_of_integrable_pow_four hmS
      (integrable_sum_pow_four X (fun i => (hmeas i).aestronglyMeasurable) h4 s) (by norm_num)
  have hset : {ω | ε ≤ |∑ i ∈ s, X i ω|} = {ω | ε ^ 2 ≤ (∑ i ∈ s, X i ω) ^ 2} := by
    ext ω
    simp only [Set.mem_setOf_eq]
    constructor
    · intro h
      nlinarith [abs_nonneg (∑ i ∈ s, X i ω), sq_abs (∑ i ∈ s, X i ω)]
    · intro h
      nlinarith [abs_nonneg (∑ i ∈ s, X i ω), sq_abs (∑ i ∈ s, X i ω)]
  have hmarkov := mul_meas_ge_le_integral_of_nonneg (μ := P)
    (f := fun ω => (∑ i ∈ s, X i ω) ^ 2)
    (Filter.Eventually.of_forall fun ω => by positivity) hS2 (ε ^ 2)
  rw [integral_sq_finsetSum X hmeas hindep h4 hmean s] at hmarkov
  rw [hset, le_div_iff₀ (by positivity)]
  linarith [hmarkov]

end

/-! ### The product-measure form -/

set_option maxHeartbeats 1000000 in
/-- The fourth moment bound for coordinate functions under a product measure. -/
theorem integral_pow_four_sum_pi {ι : Type*} [Fintype ι] (μ : ι → Measure ℝ)
    [∀ i, IsProbabilityMeasure (μ i)] (g : ι → ℝ → ℝ) (hg : ∀ i, Measurable (g i))
    (hg4 : ∀ i, Integrable (fun t => g i t ^ 4) (μ i))
    (hgmean : ∀ i, ∫ t, g i t ∂(μ i) = 0) :
    ∫ ω, (∑ i, g i (ω i)) ^ 4 ∂(Measure.pi μ)
      ≤ (∑ i, ∫ t, g i t ^ 4 ∂(μ i)) + 3 * (∑ i, ∫ t, g i t ^ 2 ∂(μ i)) ^ 2 := by
  classical
  have hmeas : ∀ i, Measurable (fun ω : ι → ℝ => g i (ω i)) := fun i =>
    (hg i).comp (measurable_pi_apply i)
  have hindep : iIndepFun (fun i (ω : ι → ℝ) => g i (ω i)) (Measure.pi μ) :=
    iIndepFun_pi (fun i => (hg i).aemeasurable)
  have hint4 : ∀ i, Integrable (fun ω : ι → ℝ => g i (ω i) ^ 4) (Measure.pi μ) := fun i =>
    integrable_comp_eval (μ := μ) (i := i) (hg4 i)
  have hm : ∀ i, ∫ ω, g i (ω i) ∂(Measure.pi μ) = 0 := fun i => by
    rw [integral_comp_eval (μ := μ) (i := i) (hg i).aestronglyMeasurable]
    exact hgmean i
  have h := integral_pow_four_finsetSum_le (fun i (ω : ι → ℝ) => g i (ω i)) hmeas hindep
    hint4 hm Finset.univ
  have e4 : ∀ i, ∫ ω, g i (ω i) ^ 4 ∂(Measure.pi μ) = ∫ t, g i t ^ 4 ∂(μ i) := fun i =>
    integral_comp_eval (μ := μ) (i := i) ((hg i).pow_const 4).aestronglyMeasurable
  have e2 : ∀ i, ∫ ω, g i (ω i) ^ 2 ∂(Measure.pi μ) = ∫ t, g i t ^ 2 ∂(μ i) := fun i =>
    integral_comp_eval (μ := μ) (i := i) ((hg i).pow_const 2).aestronglyMeasurable
  simp only [e4, e2] at h
  exact h

end LatticeProb
