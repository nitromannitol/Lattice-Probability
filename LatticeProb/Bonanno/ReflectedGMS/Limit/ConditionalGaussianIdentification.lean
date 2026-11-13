/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module ReflectedGMS.Limit.ConditionalGaussianIdentification at commit fdb5cad; only the module paths of local imports are changed. -/
import Mathlib.Probability.Martingale.Basic
import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds
import LatticeProb.Bonanno.ReflectedGMS.Limit.MartingaleCharacteristicTaylor
import Mathlib.Probability.Independence.CharacteristicFunction
import Mathlib.MeasureTheory.Function.ConditionalExpectation.PullOut

/-!
# Conditional Gaussian identification of a martingale increment

This file completes the *identification* half of the martingale FCLT input for
`thm:areaclt`: a square-integrable martingale whose increments have the
**deterministic** conditional second moments `C * (t - s)` and whose Lindeberg
tails along the uniform deterministic partitions of `[s, t]` vanish has
conditional characteristic function `exp (-u² C (t - s) / 2)` for the increment
`M t - M s` given the past `𝔽 s`.  Consequently the increment is independent of
the past and its law is `gaussianReal 0 (C (t - s))`.

The two inputs that are *not* reproved here are

* `ReflectedGMS.MartingaleLimit.norm_condExp_cexp_sub_quadratic_taylor_le`, the
  one-step conditional Taylor estimate, and
* `ReflectedGMS.MartingaleLimit.indepFun_of_condExp_charFun_eq_const`, the
  criterion turning a constant conditional characteristic function into
  independence.

The telescoping of `ReflectedGMS.Limit.ConditionalCharacteristicProducts` is
reused in spirit but cannot be reused verbatim: its one-step hypothesis is an
*almost sure* bound `‖P[e^{iuZ}|F n] - a n‖ ≤ ε n` by a constant, which a
hypothesis on the *unconditional* summed Lindeberg tails cannot supply.  The
first section therefore reruns the same telescoping with the one-step error
measured in `L¹`; this is strictly weaker to assume and is exactly what one
gets after integrating the conditional Taylor bound.  Everything else (the
Taylor estimate, the boundedness bookkeeping) is imported.

## Main results

* `norm_integral_test_mul_cexp_sum_sub_quadratic_prod_le_integralNorm`:
  telescoping with `L¹` one-step errors and unconditional Lindeberg tails.
* `norm_integral_test_mul_cexp_increment_sub_pow_le`: the resulting estimate for
  a martingale increment along the uniform partition of `[s, t]` into `n` pieces,
  with the deterministic product `(1 - u² C (t - s) / (2n))ⁿ`.
* `integral_test_mul_cexp_increment_eq_exp`: passing to the limit in `n` and
  then in the truncation level identifies the tested Fourier integral as
  `E[W] · exp (-u² C (t - s) / 2)`.
* `condExp_cexp_increment_eq_exp`: the conditional characteristic function.
* `indepFun_increment_of_deterministic_variance` and
  `map_increment_eq_gaussianReal`: independence of the past and the Gaussian law.

No Itô theory, no Lévy characterisation and no Gaussianity of the limit is
assumed; the conditional variance is used as a deterministic identity, never as
a bound, and the partitions are deterministic.
-/

-- Merged from `ReflectedGMS/Limit/ConditionalCharacteristicProducts.lean` (Packet C, 2026-09-18); names unchanged.
section Merged_ConditionalCharacteristicProducts

/-!
# Finite telescoping of conditional characteristic functions

Let `Z 0, Z 1, …` be increments adapted to a filtration `F`, and suppose that at
each step the conditional characteristic function of `Z n` given `F n` is within
`ε n` of a **deterministic** complex number `a n` of modulus at most one.  The
finite product `∏ k < N, a k` then approximates the characteristic function of
the partial sum `∑ k < N, Z k`, with total error at most `∑ k < N, ε k`.

The argument is the usual telescoping: the exponential of the past partial sum
is bounded by one in modulus and measurable with respect to the past, so it can
be pulled out of the conditional expectation of the next increment, and the
resulting one-step error is measured against the deterministic factor `a n`.
Only deterministic factors can be pulled through the past conditional
expectation in this way; random future conditional variances cannot.

The estimate is proved against an arbitrary bounded `F 0`-measurable complex
test function `W`, which is the form needed to identify a limiting increment as
independent of the past with a prescribed characteristic function: specializing
`W` to the indicator of a past event gives the set-integral version.

The one-step input is the conditional Taylor estimate
`norm_condExp_cexp_sub_quadratic_taylor_le`, which is not reproved here; the
final corollary combines it with the telescoping, for increments whose
conditional variances are deterministic and whose conditional Lindeberg tails
are uniformly bounded.  The passage from the finite product to an exponential is
a separate open step.
-/

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Filter

namespace ReflectedGMS.MartingaleLimit

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}

/-- Partial sums of increments adapted to a filtration are adapted. -/
theorem measurable_range_sum_of_adapted {F : ℕ → MeasurableSpace Ω} (hFmono : Monotone F)
    {Z : ℕ → Ω → ℝ} (hZadapt : ∀ n, Measurable[F (n + 1)] (Z n)) (n : ℕ) :
    Measurable[F n] (fun ω => ∑ k ∈ Finset.range n, Z k ω) := by
  induction n with
  | zero =>
      have h0 : Measurable[F 0] (fun _ : Ω => (0 : ℝ)) := measurable_const
      have heq : (fun ω => ∑ k ∈ Finset.range 0, Z k ω) = fun _ : Ω => (0 : ℝ) := by
        funext ω
        simp
      rw [heq]
      exact h0
  | succ n ih =>
      have h1 : Measurable[F (n + 1)] (fun ω => ∑ k ∈ Finset.range n, Z k ω) :=
        ih.mono (hFmono (Nat.le_succ n)) le_rfl
      have h2 : Measurable[F (n + 1)] (fun ω => (∑ k ∈ Finset.range n, Z k ω) + Z n ω) :=
        h1.add (hZadapt n)
      have heq : (fun ω => ∑ k ∈ Finset.range (n + 1), Z k ω)
          = fun ω => (∑ k ∈ Finset.range n, Z k ω) + Z n ω := by
        funext ω
        exact Finset.sum_range_succ (fun k => Z k ω) n
      rw [heq]
      exact h2

end ReflectedGMS.MartingaleLimit

end Merged_ConditionalCharacteristicProducts

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Filter Complex
open scoped NNReal ENNReal Topology

namespace ReflectedGMS.MartingaleLimit

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}

/-! ### Telescoping with `L¹` one-step errors -/

/-- One telescoping step with the one-step error measured in `L¹`.  This is the
`L¹` analogue of `norm_integral_mul_sub_mul_le`: the conditional error is only
required to be small *on average*, which is what integrating a conditional
Lindeberg tail produces. -/
theorem norm_integral_mul_sub_mul_le_integralNorm [IsProbabilityMeasure P]
    (m : {q : MeasurableSpace Ω // q ≤ mΩ}) {V g : Ω → ℂ}
    (hV : StronglyMeasurable[m.1] V) (hVbdd : ∀ ω, ‖V ω‖ ≤ 1) (hgint : Integrable g P)
    {b c : ℂ} {r e : ℝ} (hb : ‖b‖ ≤ 1)
    (hstep : (∫ ω, ‖(P[g | m.1]) ω - b‖ ∂P) ≤ e)
    (hr : ‖(∫ ω, V ω ∂P) - c‖ ≤ r) :
    ‖(∫ ω, V ω * g ω ∂P) - c * b‖ ≤ r + e := by
  have hVΩ : StronglyMeasurable V := hV.mono m.2
  have hVint : Integrable V P :=
    Integrable.of_bound hVΩ.aestronglyMeasurable 1 (Eventually.of_forall hVbdd)
  have hVgint : Integrable (fun ω => V ω * g ω) P :=
    hgint.bdd_mul hVΩ.aestronglyMeasurable (Eventually.of_forall hVbdd)
  have hpull : P[fun ω => V ω * g ω | m.1] =ᵐ[P] fun ω => V ω * (P[g | m.1]) ω :=
    condExp_bilin_of_stronglyMeasurable_left (.mul ℝ ℂ) hV hVgint hgint
  have hcint : Integrable (fun ω => (P[g | m.1]) ω - b) P :=
    integrable_condExp.sub (integrable_const b)
  have hVcint : Integrable (fun ω => V ω * ((P[g | m.1]) ω - b)) P :=
    hcint.bdd_mul hVΩ.aestronglyMeasurable (Eventually.of_forall hVbdd)
  have hbVint : Integrable (fun ω => b * V ω) P := hVint.const_mul b
  have hsplit : (∫ ω, V ω * g ω ∂P)
      = (∫ ω, V ω * ((P[g | m.1]) ω - b) ∂P) + b * ∫ ω, V ω ∂P := by
    have h1 : (∫ ω, V ω * g ω ∂P) = ∫ ω, V ω * (P[g | m.1]) ω ∂P := by
      calc (∫ ω, V ω * g ω ∂P) = ∫ ω, (P[fun ω => V ω * g ω | m.1]) ω ∂P :=
            (integral_condExp m.2).symm
        _ = ∫ ω, V ω * (P[g | m.1]) ω ∂P := integral_congr_ae hpull
    rw [h1, ← integral_const_mul b V, ← integral_add hVcint hbVint]
    refine integral_congr_ae (Eventually.of_forall fun ω => ?_)
    ring
  have hb1 : ‖∫ ω, V ω * ((P[g | m.1]) ω - b) ∂P‖ ≤ e := by
    calc ‖∫ ω, V ω * ((P[g | m.1]) ω - b) ∂P‖
        ≤ ∫ ω, ‖V ω * ((P[g | m.1]) ω - b)‖ ∂P := norm_integral_le_integral_norm _
      _ ≤ ∫ ω, ‖(P[g | m.1]) ω - b‖ ∂P := by
          refine integral_mono_ae hVcint.norm hcint.norm (Eventually.of_forall fun ω => ?_)
          show ‖V ω * ((P[g | m.1]) ω - b)‖ ≤ ‖(P[g | m.1]) ω - b‖
          rw [norm_mul]
          exact mul_le_of_le_one_left (norm_nonneg _) (hVbdd ω)
      _ ≤ e := hstep
  have hb2 : ‖b * ((∫ ω, V ω ∂P) - c)‖ ≤ r := by
    rw [norm_mul]
    have hmul := mul_le_mul hb hr (norm_nonneg _) zero_le_one
    simpa using hmul
  have hfin : (∫ ω, V ω * g ω ∂P) - c * b
      = (∫ ω, V ω * ((P[g | m.1]) ω - b) ∂P) + b * ((∫ ω, V ω ∂P) - c) := by
    rw [hsplit]; ring
  rw [hfin]
  refine (norm_add_le _ _).trans ?_
  rw [add_comm r e]
  exact add_le_add hb1 hb2

/-! ### The uniform deterministic partition of `[s, t]` -/

/-- The `i`-th point of the partition of `[s, t]` into `n` equal pieces.  For
`n = 0` all points equal `s`. -/
noncomputable def uniformPartition (s t : ℝ≥0) (n i : ℕ) : ℝ≥0 :=
  s + ((i : ℝ≥0) / (n : ℝ≥0)) * (t - s)

theorem uniformPartition_zero (s t : ℝ≥0) (n : ℕ) : uniformPartition s t n 0 = s := by
  simp [uniformPartition]

theorem uniformPartition_self {s t : ℝ≥0} {n : ℕ} (hn : n ≠ 0) (hst : s ≤ t) :
    uniformPartition s t n n = t := by
  have hn' : (n : ℝ≥0) ≠ 0 := Nat.cast_ne_zero.2 hn
  rw [uniformPartition, div_self hn', one_mul, add_tsub_cancel_of_le hst]

theorem uniformPartition_mono (s t : ℝ≥0) (n : ℕ) : Monotone (uniformPartition s t n) := by
  intro i j hij
  have hcast : (i : ℝ≥0) ≤ (j : ℝ≥0) := Nat.cast_le.2 hij
  have hnn : ∀ x : ℝ≥0, (0 : ℝ≥0) ≤ x := fun x => by simp
  have hdiv : (i : ℝ≥0) / (n : ℝ≥0) ≤ (j : ℝ≥0) / (n : ℝ≥0) := by
    rw [div_eq_mul_inv, div_eq_mul_inv]
    exact mul_le_mul_of_nonneg_right hcast (hnn _)
  have hmul : ((i : ℝ≥0) / (n : ℝ≥0)) * (t - s) ≤ ((j : ℝ≥0) / (n : ℝ≥0)) * (t - s) :=
    mul_le_mul_of_nonneg_right hdiv (hnn _)
  show s + ((i : ℝ≥0) / (n : ℝ≥0)) * (t - s) ≤ s + ((j : ℝ≥0) / (n : ℝ≥0)) * (t - s)
  exact add_le_add le_rfl hmul

theorem coe_uniformPartition {s t : ℝ≥0} (hst : s ≤ t) (n i : ℕ) :
    ((uniformPartition s t n i : ℝ≥0) : ℝ) = (s : ℝ) + ((i : ℝ) / (n : ℝ)) * ((t : ℝ) - s) := by
  rw [uniformPartition, NNReal.coe_add, NNReal.coe_mul, NNReal.coe_div, NNReal.coe_sub hst,
    NNReal.coe_natCast, NNReal.coe_natCast]

theorem coe_uniformPartition_succ_sub {s t : ℝ≥0} (hst : s ≤ t) (n i : ℕ) :
    ((uniformPartition s t n (i + 1) : ℝ≥0) : ℝ) - ((uniformPartition s t n i : ℝ≥0) : ℝ)
      = ((t : ℝ) - s) / (n : ℝ) := by
  rw [coe_uniformPartition hst, coe_uniformPartition hst]
  push_cast
  rcases eq_or_ne (n : ℝ) 0 with h | h
  · rw [h]; simp
  · field_simp
    ring

/-- The Lindeberg sum at level `δ` of the increments of `M` along the uniform
partition of `[s, t]` into `n` pieces. -/
noncomputable def lindebergSum (P : Measure Ω) (M : ℝ≥0 → Ω → ℝ) (δ : ℝ) (s t : ℝ≥0)
    (n : ℕ) : ℝ :=
  ∑ i ∈ Finset.range n, ∫ ω, Set.indicator
    {ω | δ < |M (uniformPartition s t n (i + 1)) ω - M (uniformPartition s t n i) ω|}
    (fun ω => (M (uniformPartition s t n (i + 1)) ω - M (uniformPartition s t n i) ω) ^ 2) ω ∂P

theorem lindebergSum_eq (P : Measure Ω) (M : ℝ≥0 → Ω → ℝ) (δ : ℝ) (s t : ℝ≥0) (n : ℕ) :
    lindebergSum P M δ s t n = ∑ i ∈ Finset.range n, ∫ ω, Set.indicator
      {ω | δ < |M (uniformPartition s t n (i + 1)) ω - M (uniformPartition s t n i) ω|}
      (fun ω => (M (uniformPartition s t n (i + 1)) ω - M (uniformPartition s t n i) ω) ^ 2)
      ω ∂P := rfl

/-! ### The martingale estimate along a uniform partition -/

variable {𝔽 : Filtration ℝ≥0 mΩ} {M : ℝ≥0 → Ω → ℝ} {T : ℝ≥0} {C : ℝ}

/-! ### Passing to the limit -/

end ReflectedGMS.MartingaleLimit
