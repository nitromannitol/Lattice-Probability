/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module ReflectedGMS.Limit.ReverseRationalAE at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.ReflectedGMS.Limit.ReverseRationalMaximal
import LatticeProb.Bonanno.ReflectedGMS.Limit.ReverseConditionalL1

/-! Almost-everywhere reverse convergence of conditional expectations along a
*rational* parameter.

For a finite measure `P`, an antitone family `ms : ℚ → MeasurableSpace Ω` of
sub-sigma-fields of `m0` and a real integrable `f`, the conditional expectations
`P[f | ms q]` converge `P`-almost everywhere, as `q → ∞` through the rationals,
to the tail conditional expectation `P[f | ⨅ r : ℚ, ms r]`.

This is the form needed by rational-time block averaging in temporal
homogenization, where the averaging horizons are rational and not only integer.

The route only combines already checked inputs:

* `ReflectedGMS.ReverseConditional.measure_exists_rat_ge_lt_abs_condExp_le` is
  the rational-family reverse weak-`L¹` maximal inequality.  Applied to the
  centred observable `P[f | ms N] - P[f | ⨅ r, ms r]` at an *integer* horizon
  `N`, the tower property (valid for every rational `q ≥ N`) plus measurability
  of the tail conditional expectation turn it into the centred rational tail
  bound `P {∃ q ≥ N, a < |P[f|ms q] - P[f|⨅ r, ms r]|} ≤ ‖·‖₁ / a`.
* `iInf_rat_eq_iInf_nat` is the cofinality of `ℕ` in `ℚ` for the antitone
  family, so the integer reverse `L¹` theorem
  `ReflectedGMS.MartingaleLimit.tendsto_eLpNorm_one_condExp_iInf` already has
  the *rational* tail sigma-field as its limit.  Hence the tail bound above is
  uniform in `N` and tends to `0`, and each rational tail oscillation event is
  null.
* Countably many thresholds `1 / (j + 1)` give the almost-everywhere limit.

Neither the integer `L¹` convergence nor the maximal inequality is reproved
here, and nothing below identifies the limit with an unconditional mean. -/

set_option autoImplicit false

open MeasureTheory Filter
open scoped ENNReal NNReal Topology

namespace ReflectedGMS.ReverseRationalAE

variable {Ω : Type*} {m0 : MeasurableSpace Ω} {ms : ℚ → MeasurableSpace Ω}
  {P : Measure Ω} [IsFiniteMeasure P]

/-- Cofinality of the integers in the rationals: the tail sigma-field of an antitone
rational family is already reached along integer parameters. -/
theorem iInf_rat_eq_iInf_nat (hanti : Antitone ms) :
    (⨅ q : ℚ, ms q) = ⨅ n : ℕ, ms (n : ℚ) := by
  refine le_antisymm (le_iInf fun n => iInf_le ms (n : ℚ)) (le_iInf fun q => ?_)
  obtain ⟨n, hn⟩ := exists_nat_ge q
  exact le_trans (iInf_le (fun n : ℕ => ms (n : ℚ)) n) (hanti hn)

/-- Tail identity at a rational parameter beyond an integer horizon: conditioning the
centred variable `P[f | ms N] - P[f | ⨅ r, ms r]` on the smaller sigma-field `ms q`,
`q ≥ N`, reproduces the centred variable at `q`.  The first summand uses the tower
property, the second that the tail conditional expectation is `ms q`-measurable. -/
theorem condExp_rat_ge_sub_condExp_iInf (hle : ∀ q, ms q ≤ m0) (hanti : Antitone ms)
    (f : Ω → ℝ) (N : ℕ) {q : ℚ} (hq : (N : ℚ) ≤ q) :
    P[P[f|ms (N : ℚ)] - P[f|⨅ r : ℚ, ms r] | ms q] =ᵐ[P]
      P[f|ms q] - P[f|⨅ r : ℚ, ms r] := by
  have hlater : ms q ≤ ms (N : ℚ) := hanti hq
  have hiInf : (⨅ r : ℚ, ms r) ≤ ms q := iInf_le ms q
  have hsm : StronglyMeasurable[ms q] (P[f|⨅ r : ℚ, ms r]) :=
    (stronglyMeasurable_condExp (m := ⨅ r : ℚ, ms r) (μ := P) (f := f)).mono hiInf
  have hfix : P[P[f|⨅ r : ℚ, ms r] | ms q] = P[f|⨅ r : ℚ, ms r] :=
    condExp_of_stronglyMeasurable (hle q) hsm integrable_condExp
  have hsub := condExp_sub (integrable_condExp (m := ms (N : ℚ)) (μ := P) (f := f))
    (integrable_condExp (m := ⨅ r : ℚ, ms r) (μ := P) (f := f)) (ms q)
  have htower : P[P[f|ms (N : ℚ)] | ms q] =ᵐ[P] P[f|ms q] :=
    condExp_condExp_of_le hlater (hle (N : ℚ))
  filter_upwards [hsub, htower] with ω h1 h2
  simp only [Pi.sub_apply] at h1 ⊢
  rw [h1, h2, hfix]

/-- Centred rational tail maximal inequality: with probability at most
`‖P[f | ms N] - P[f | ⨅ r, ms r]‖₁ / a`, some *rational* parameter `q ≥ N` has
`|P[f | ms q] - P[f | ⨅ r, ms r]| > a`. -/
theorem measure_exists_rat_ge_lt_abs_condExp_sub_iInf_le (hle : ∀ q, ms q ≤ m0)
    (hanti : Antitone ms) (f : Ω → ℝ) {a : ℝ} (ha : 0 < a) (N : ℕ) :
    P {ω | ∃ q : ℚ, (N : ℚ) ≤ q ∧ a < |P[f|ms q] ω - P[f|⨅ r : ℚ, ms r] ω|} ≤
      eLpNorm (P[f|ms (N : ℚ)] - P[f|⨅ r : ℚ, ms r]) 1 P / ENNReal.ofReal a := by
  have hbase := ReflectedGMS.ReverseConditional.measure_exists_rat_ge_lt_abs_condExp_le
    (P := P) (ms := ms) hanti hle (P[f|ms (N : ℚ)] - P[f|⨅ r : ℚ, ms r]) ha (N : ℚ)
  have hae : ∀ᵐ ω ∂P, ∀ q : ℚ, (N : ℚ) ≤ q →
      P[P[f|ms (N : ℚ)] - P[f|⨅ r : ℚ, ms r] | ms q] ω =
        P[f|ms q] ω - P[f|⨅ r : ℚ, ms r] ω := by
    rw [ae_all_iff]
    intro q
    by_cases hq : (N : ℚ) ≤ q
    · filter_upwards [condExp_rat_ge_sub_condExp_iInf hle hanti f N hq] with ω hω
      exact fun _ => by simpa using hω
    · exact Eventually.of_forall fun ω hq' => absurd hq' hq
  have hsets : {ω | ∃ q : ℚ, (N : ℚ) ≤ q ∧ a < |P[f|ms q] ω - P[f|⨅ r : ℚ, ms r] ω|} =ᵐ[P]
      {ω | ∃ q : ℚ, (N : ℚ) ≤ q ∧
        a < |P[P[f|ms (N : ℚ)] - P[f|⨅ r : ℚ, ms r] | ms q] ω|} := by
    rw [Filter.eventuallyEqSet_iff]
    filter_upwards [hae] with ω hω
    refine exists_congr fun q => and_congr_right fun hq => ?_
    rw [hω q hq]
  have hFint : Integrable (P[f|ms (N : ℚ)] - P[f|⨅ r : ℚ, ms r]) P :=
    integrable_condExp.sub integrable_condExp
  have hnorm : ENNReal.ofReal
      (∫ ω, |(P[f|ms (N : ℚ)] - P[f|⨅ r : ℚ, ms r]) ω| ∂P) =
      eLpNorm (P[f|ms (N : ℚ)] - P[f|⨅ r : ℚ, ms r]) 1 P := by
    rw [eLpNorm_one_eq_lintegral_enorm hFint.aestronglyMeasurable,
      ← ofReal_integral_norm_eq_lintegral_enorm hFint]
    simp [Real.norm_eq_abs]
  calc P {ω | ∃ q : ℚ, (N : ℚ) ≤ q ∧ a < |P[f|ms q] ω - P[f|⨅ r : ℚ, ms r] ω|}
      = P {ω | ∃ q : ℚ, (N : ℚ) ≤ q ∧
          a < |P[P[f|ms (N : ℚ)] - P[f|⨅ r : ℚ, ms r] | ms q] ω|} := measure_congr hsets
    _ ≤ ENNReal.ofReal
          ((∫ ω, |(P[f|ms (N : ℚ)] - P[f|⨅ r : ℚ, ms r]) ω| ∂P) / a) := hbase
    _ = ENNReal.ofReal (∫ ω, |(P[f|ms (N : ℚ)] - P[f|⨅ r : ℚ, ms r]) ω| ∂P) /
          ENNReal.ofReal a := ENNReal.ofReal_div_of_pos ha
    _ = eLpNorm (P[f|ms (N : ℚ)] - P[f|⨅ r : ℚ, ms r]) 1 P / ENNReal.ofReal a := by
        rw [hnorm]

/-- Every rational tail oscillation event at a fixed positive level is null: the centred
rational tail bound is uniform in the integer horizon `N`, and the reverse `L¹`
convergence along the integers sends it to `0`. -/
theorem measure_forall_exists_rat_ge_lt_abs_condExp_sub_iInf_eq_zero (hle : ∀ q, ms q ≤ m0)
    (hanti : Antitone ms) {f : Ω → ℝ} (hf : Integrable f P) {a : ℝ} (ha : 0 < a) :
    P {ω | ∀ N : ℕ, ∃ q : ℚ, (N : ℚ) ≤ q ∧
      a < |P[f|ms q] ω - P[f|⨅ r : ℚ, ms r] ω|} = 0 := by
  have hnatanti : Antitone fun n : ℕ => ms (n : ℚ) := fun i j hij =>
    hanti (by exact_mod_cast hij)
  have hL1 := ReflectedGMS.MartingaleLimit.tendsto_eLpNorm_one_condExp_iInf
    (m := fun n : ℕ => ms (n : ℚ)) (μ := P) (fun n => hle (n : ℚ)) hnatanti hf
  rw [← iInf_rat_eq_iInf_nat hanti] at hL1
  have htail : Tendsto
      (fun N : ℕ => eLpNorm (P[f|ms (N : ℚ)] - P[f|⨅ r : ℚ, ms r]) 1 P / ENNReal.ofReal a)
      atTop (𝓝 0) := by
    simpa using ENNReal.Tendsto.div_const hL1 (Or.inr (ENNReal.ofReal_pos.2 ha).ne')
  have hle' : ∀ N : ℕ, P {ω | ∀ N' : ℕ, ∃ q : ℚ, (N' : ℚ) ≤ q ∧
      a < |P[f|ms q] ω - P[f|⨅ r : ℚ, ms r] ω|} ≤
      eLpNorm (P[f|ms (N : ℚ)] - P[f|⨅ r : ℚ, ms r]) 1 P / ENNReal.ofReal a := by
    intro N
    refine le_trans (measure_mono ?_)
      (measure_exists_rat_ge_lt_abs_condExp_sub_iInf_le hle hanti f ha N)
    exact fun ω hω => hω N
  exact le_antisymm (ge_of_tendsto htail (Eventually.of_forall hle')) bot_le

/-- **Almost-everywhere reverse convergence of conditional expectations along the
rationals.** For a finite measure, an antitone rational-indexed family of
sub-sigma-algebras and a real integrable observable, `P[f | ms q]` converges pointwise
almost everywhere, as `q → ∞` through `ℚ`, to the tail conditional expectation
`P[f | ⨅ r : ℚ, ms r]`. -/
theorem tendsto_condExp_iInf_rat_ae (hle : ∀ q, ms q ≤ m0) (hanti : Antitone ms)
    {f : Ω → ℝ} (hf : Integrable f P) :
    ∀ᵐ ω ∂P, Tendsto (fun q : ℚ => P[f|ms q] ω) atTop (𝓝 (P[f|⨅ r : ℚ, ms r] ω)) := by
  have hzero : P (⋃ j : ℕ, {ω | ∀ N : ℕ, ∃ q : ℚ, (N : ℚ) ≤ q ∧
      1 / ((j : ℝ) + 1) < |P[f|ms q] ω - P[f|⨅ r : ℚ, ms r] ω|}) = 0 :=
    measure_iUnion_null fun j =>
      measure_forall_exists_rat_ge_lt_abs_condExp_sub_iInf_eq_zero hle hanti hf (by positivity)
  filter_upwards [measure_eq_zero_iff_ae_notMem.1 hzero] with ω hω
  simp only [Set.mem_iUnion, Set.mem_setOf_eq] at hω
  push_neg at hω
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨j, hj⟩ := exists_nat_one_div_lt hε
  obtain ⟨N, hN⟩ := hω j
  refine ⟨(N : ℚ), fun q hq => ?_⟩
  rw [Real.dist_eq]
  exact lt_of_le_of_lt (hN q hq) hj

end ReflectedGMS.ReverseRationalAE
