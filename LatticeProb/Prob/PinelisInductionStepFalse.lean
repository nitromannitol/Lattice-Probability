/-
# `PinelisInductionStep` is false as stated

`LatticeProb.PinelisInductionStep` (`Prob/BernsteinInduction.lean`) asserts, for every `p ≥ 2`,
a constant `K > 0` such that for every probability space, filtration, martingale-difference
sequence `ξ` and conditional-variance sequence `v` satisfying only the conditional-moment
hypotheses `E[ξ (i+1) | F i] = 0`, `E[ξ (i+1)² | F i] = v (i+1)` and the integrability of the
cross terms `|S i|^{p-2} v (i+1)`, the cumulative bound

  `∑_{i<k} E[|S i|^{p-2} v (i+1)] ≤ K (E V_k^{p/2})^{2/p} (E|S k|^p)^{(p-2)/p} + K ∑_{i≤k} E|ξ i|^p`

holds.  The statement has **no `L^p` hypothesis** on `ξ`.  Mathlib's Bochner integral of a
non-integrable function is `0`, so when `E|S k|^p` and `E|ξ i|^p` are infinite both are read as
`0`, the right-hand side collapses to `0`, and the (finite, positive) left-hand side violates it.
This module proves `LatticeProb.not_pinelisInductionStep : ¬ PinelisInductionStep`, in every
universe.

**The counterexample** (`p = 4`, `k = 2`).  Take the trivial filtration `F i = ⊥`, so that
`E[g | F i] = E g` is a constant (`condExp_bot`) and the hypotheses ask only `E ξ (i+1) = 0`
and `v (i+1) = E ξ (i+1)²`.  Let `Y` be mean zero with `Y ∈ L²` but `Y ∉ L⁴`; put
`ξ 1 = ξ 2 = Y`, `ξ i = 0` otherwise, `v 1 = v 2 = c := E Y² > 0`, `v i = 0` otherwise.  Then
`S 0 = 0`, `S 1 = Y`, `S 2 = 2Y`, and

* the left-hand side is `E[|S 0|² v 1] + E[|S 1|² v 2] = 0 + c · E Y² = c² > 0`;
* `E|S 2|⁴ = 16 E Y⁴` and `E|ξ i|⁴ = E Y⁴` are integrals of non-integrable functions, hence
  `0`, and `0^{(4-2)/4} = 0`, so the right-hand side is `0` for every `K`;
* the cross terms are integrable: they are `0`, `c Y²` and `0`.

**The heavy-tailed `Y`** (`heavyY`).  On `ℕ` with the geometric law of success probability
`7/8` (the atom `{n}` has mass `(1/8)^n (7/8)`), let `X n = 2^n`.  Then `∑ (1/8)^n 2^n`,
`∑ (1/8)^n 4^n` converge, so `X ∈ L¹ ∩ L²`, while `∑ (1/8)^n 16^n = ∑ 2^n` diverges, so
`X ∉ L⁴`; `Y = X - E X` is mean zero, `Y ∈ L²`, and `Y ∉ L⁴` (else `X = Y + E X ∈ L⁴`).  It
is transported to `ULift.{u} ℕ` along `ULift.up` to cover every universe.

**The fix.**  Add the `L^p` hypotheses the intended application has, e.g.
`∀ i, MemLp (ξ i) (ENNReal.ofReal p) μ`, so that `E|S k|^p` and `E|ξ i|^p` are finite and
the junk value `0` of the Bochner integral cannot occur.

No `sorry`, no `axiom`.
-/
import LatticeProb.Prob.BernsteinInduction

open MeasureTheory ProbabilityTheory

universe u

namespace LatticeProb

namespace PinelisInductionStepFalse

/-! ### A heavy-tailed variable on `ℕ` -/

/-- The geometric law on `ℕ` with success probability `7/8`: the atom `{n}` has mass
`(1/8)^n * (7/8)`. -/
noncomputable def heavyMeasure : Measure ℕ :=
  geometricMeasure (⟨7 / 8, by norm_num, by norm_num⟩ : unitInterval)

instance : IsProbabilityMeasure heavyMeasure := by
  unfold heavyMeasure; infer_instance

/-- A function on `ℕ` is `heavyMeasure`-integrable iff `∑ (1/8)^n (7/8) ‖f n‖` converges. -/
theorem integrable_heavyMeasure_iff (f : ℕ → ℝ) :
    Integrable f heavyMeasure ↔
      Summable (fun n : ℕ => (1 / 8 : ℝ) ^ n * (7 / 8) * ‖f n‖) := by
  have h := integrable_geometricMeasure_iff
    (p := (⟨7 / 8, by norm_num, by norm_num⟩ : unitInterval)) (E := ℝ) (f := f) (by
      intro h
      have := congrArg (fun x : unitInterval => (x : ℝ)) h
      norm_num at this)
  unfold heavyMeasure
  rw [h]
  have e : (1 - ((⟨7 / 8, by norm_num, by norm_num⟩ : unitInterval) : ℝ)) = 1 / 8 := by
    norm_num
  simp only [e]

/-- The unbounded variable `X n = 2^n`: it lies in `L¹` and `L²`, but not in `L⁴`. -/
noncomputable def heavyX (n : ℕ) : ℝ := (2 : ℝ) ^ n

theorem integrable_heavyX : Integrable heavyX heavyMeasure := by
  rw [integrable_heavyMeasure_iff]
  have : (fun n : ℕ => (1 / 8 : ℝ) ^ n * (7 / 8) * ‖heavyX n‖) =
      fun n => (7 / 8) * (1 / 4 : ℝ) ^ n := by
    funext n
    simp only [heavyX, Real.norm_eq_abs, abs_of_pos (pow_pos (by norm_num : (0 : ℝ) < 2) n)]
    calc (1 / 8 : ℝ) ^ n * (7 / 8) * 2 ^ n = (7 / 8) * ((1 / 8 : ℝ) ^ n * 2 ^ n) := by ring
      _ = (7 / 8) * (1 / 4 : ℝ) ^ n := by rw [← mul_pow]; norm_num
  rw [this]
  exact (summable_geometric_of_lt_one (by norm_num) (by norm_num)).mul_left _

theorem integrable_heavyX_sq : Integrable (fun n => heavyX n ^ 2) heavyMeasure := by
  rw [integrable_heavyMeasure_iff]
  have : (fun n : ℕ => (1 / 8 : ℝ) ^ n * (7 / 8) * ‖heavyX n ^ 2‖) =
      fun n => (7 / 8) * (1 / 2 : ℝ) ^ n := by
    funext n
    simp only [heavyX, Real.norm_eq_abs,
      abs_of_nonneg (by positivity : (0 : ℝ) ≤ ((2 : ℝ) ^ n) ^ 2)]
    have h4 : ((2 : ℝ) ^ n) ^ 2 = 4 ^ n := by rw [← pow_mul, mul_comm, pow_mul]; norm_num
    rw [h4]
    calc (1 / 8 : ℝ) ^ n * (7 / 8) * 4 ^ n = (7 / 8) * ((1 / 8 : ℝ) ^ n * 4 ^ n) := by ring
      _ = (7 / 8) * (1 / 2 : ℝ) ^ n := by rw [← mul_pow]; norm_num
  rw [this]
  exact (summable_geometric_of_lt_one (by norm_num) (by norm_num)).mul_left _

theorem not_integrable_heavyX_pow_four : ¬ Integrable (fun n => heavyX n ^ 4) heavyMeasure := by
  rw [integrable_heavyMeasure_iff]
  intro hs
  have : (fun n : ℕ => (1 / 8 : ℝ) ^ n * (7 / 8) * ‖heavyX n ^ 4‖) =
      fun n => (7 / 8) * (2 : ℝ) ^ n := by
    funext n
    simp only [heavyX, Real.norm_eq_abs,
      abs_of_nonneg (by positivity : (0 : ℝ) ≤ ((2 : ℝ) ^ n) ^ 4)]
    have h16 : ((2 : ℝ) ^ n) ^ 4 = 16 ^ n := by rw [← pow_mul, mul_comm, pow_mul]; norm_num
    rw [h16]
    calc (1 / 8 : ℝ) ^ n * (7 / 8) * 16 ^ n = (7 / 8) * ((1 / 8 : ℝ) ^ n * 16 ^ n) := by ring
      _ = (7 / 8) * (2 : ℝ) ^ n := by rw [← mul_pow]; norm_num
  rw [this] at hs
  have h2 := (summable_mul_left_iff (by norm_num : (7 / 8 : ℝ) ≠ 0)).1 hs
  rw [summable_geometric_iff_norm_lt_one] at h2
  norm_num at h2

/-! ### Centring and the Bochner integral of a non-integrable function -/

/-- `(a + b)⁴ ≤ 8 a⁴ + 8 b⁴`. -/
theorem pow_four_add_le (a b : ℝ) : (a + b) ^ 4 ≤ 8 * a ^ 4 + 8 * b ^ 4 := by
  have h1 : (a + b) ^ 2 ≤ 2 * (a ^ 2 + b ^ 2) := by nlinarith [sq_nonneg (a - b)]
  have h3 : ((a + b) ^ 2) ^ 2 ≤ (2 * (a ^ 2 + b ^ 2)) ^ 2 :=
    pow_le_pow_left₀ (sq_nonneg _) h1 2
  nlinarith [sq_nonneg (a ^ 2 - b ^ 2)]

/-- If `X⁴` is not integrable, neither is `(X - m)⁴`: otherwise `X = (X - m) + m ∈ L⁴`. -/
theorem not_integrable_pow_four_sub_const {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsFiniteMeasure μ] {X : Ω → ℝ} (hX : AEStronglyMeasurable X μ) (m : ℝ)
    (h4 : ¬ Integrable (fun ω => X ω ^ 4) μ) :
    ¬ Integrable (fun ω => (X ω - m) ^ 4) μ := by
  intro hY
  apply h4
  refine Integrable.mono' (g := fun ω => 8 * (X ω - m) ^ 4 + 8 * m ^ 4)
    ((hY.const_mul 8).add (integrable_const _)) (hX.pow 4)
    (Filter.Eventually.of_forall fun ω => ?_)
  have h := pow_four_add_le (X ω - m) m
  rw [sub_add_cancel] at h
  rwa [Real.norm_eq_abs, abs_of_nonneg (by positivity)]

/-- A square-integrable `Y` with `Y⁴` not integrable has `∫ Y² > 0`: otherwise `Y = 0` a.e. -/
theorem integral_sq_pos_of_not_integrable_pow_four {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} {Y : Ω → ℝ} (hY2 : Integrable (fun ω => Y ω ^ 2) μ)
    (hY4 : ¬ Integrable (fun ω => Y ω ^ 4) μ) : 0 < ∫ ω, Y ω ^ 2 ∂μ := by
  have hnn : 0 ≤ ∫ ω, Y ω ^ 2 ∂μ := integral_nonneg fun ω => sq_nonneg _
  rcases hnn.lt_or_eq with h | h
  · exact h
  · exfalso
    have h0 := (integral_eq_zero_iff_of_nonneg (fun ω => sq_nonneg (Y ω)) hY2).1 h.symm
    apply hY4
    refine (integrable_zero Ω ℝ μ).congr ?_
    filter_upwards [h0] with ω hω
    have hω' : Y ω ^ 2 = 0 := hω
    have hY0 : Y ω = 0 := pow_eq_zero_iff (two_ne_zero) |>.1 hω'
    simp [hY0]

/-- `|x|^(4:ℝ) = x^4`: the real power in `PinelisInductionStep` at `p = 4`. -/
theorem abs_rpow_four (x : ℝ) : |x| ^ (4 : ℝ) = x ^ 4 := by
  rw [show (4 : ℝ) = ((4 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  exact (Even.pow_abs (by decide) x)

/-- `|x|^(4 - 2 : ℝ) = x^2`: the exponent `p - 2` of `PinelisInductionStep` at `p = 4`. -/
theorem abs_rpow_four_sub_two (x : ℝ) : |x| ^ ((4 : ℝ) - 2) = x ^ 2 := by
  rw [show (4 : ℝ) - 2 = 2 by norm_num, Real.rpow_two, sq_abs]

/-- If `Y⁴` is not integrable then `∫ |Y + Y|^4 = 0`, the junk value of the Bochner integral. -/
theorem integral_abs_rpow_four_two_mul_eq_zero {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} {Y : Ω → ℝ} (hY4 : ¬ Integrable (fun ω => Y ω ^ 4) μ) :
    ∫ ω, |Y ω + Y ω| ^ (4 : ℝ) ∂μ = 0 := by
  apply integral_undef
  intro hint
  apply hY4
  have h16 : Integrable (fun ω => (1 / 16 : ℝ) * |Y ω + Y ω| ^ (4 : ℝ)) μ :=
    hint.const_mul _
  refine h16.congr (Filter.Eventually.of_forall fun ω => ?_)
  simp only [abs_rpow_four]
  ring

/-! ### The counterexample on an arbitrary probability space -/

/-- The increments `ξ 1 = ξ 2 = Y`, `ξ i = 0` otherwise. -/
def incr {Ω : Type*} (Y : Ω → ℝ) (i : ℕ) : Ω → ℝ :=
  if i = 1 ∨ i = 2 then Y else 0

/-- The conditional variances `v 1 = v 2 = c`, `v i = 0` otherwise. -/
def variances {Ω : Type*} (c : ℝ) (i : ℕ) : Ω → ℝ :=
  if i = 1 ∨ i = 2 then fun _ => c else 0

theorem partialSum_incr_zero {Ω : Type*} (Y : Ω → ℝ) :
    martingalePartialSum (incr Y) 0 = 0 := by
  funext ω
  simp [martingalePartialSum]

theorem partialSum_incr_one {Ω : Type*} (Y : Ω → ℝ) :
    martingalePartialSum (incr Y) 1 = Y := by
  funext ω
  simp [martingalePartialSum, incr]

theorem partialSum_incr_two {Ω : Type*} (Y : Ω → ℝ) :
    martingalePartialSum (incr Y) 2 = fun ω => Y ω + Y ω := by
  funext ω
  have hI : Finset.Icc 1 2 = {1, 2} := by decide
  simp [martingalePartialSum, hI, incr]

/-- **The core of the refutation.**  A probability space carrying a mean-zero `Y` with `Y ∈ L²`
and `Y ∉ L⁴` refutes `PinelisInductionStep` (at the universe of the space), with `p = 4`,
`k = 2`, the trivial filtration, `ξ 1 = ξ 2 = Y`, and `v 1 = v 2 = E Y²`. -/
theorem not_pinelisInductionStep_of_heavyTail {Ω : Type u} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (Y : Ω → ℝ)
    (hY2 : Integrable (fun ω => Y ω ^ 2) μ)
    (hY4 : ¬ Integrable (fun ω => Y ω ^ 4) μ) (hY0 : ∫ ω, Y ω ∂μ = 0) :
    ¬ PinelisInductionStep.{u} := by
  intro h
  obtain ⟨K, hK0, hK⟩ := h 4 (by norm_num)
  obtain ⟨c, hc⟩ : ∃ c : ℝ, ∫ ω, Y ω ^ 2 ∂μ = c := ⟨_, rfl⟩
  have hcpos : 0 < c := hc ▸ integral_sq_pos_of_not_integrable_pow_four hY2 hY4
  let F : Filtration ℕ (inferInstance : MeasurableSpace Ω) := Filtration.const ℕ ⊥ bot_le
  have hcond : ∀ (g : Ω → ℝ) (i : ℕ), μ[g | F i] = fun _ => ∫ ω, g ω ∂μ :=
    fun g i => condExp_bot g
  have h1 : ∀ i, μ[incr Y (i + 1) | F i] =ᵐ[μ] 0 := by
    intro i
    rw [hcond]
    by_cases hi : i + 1 = 1 ∨ i + 1 = 2
    · simp only [incr, if_pos hi]
      exact Filter.Eventually.of_forall fun ω => by simp [hY0]
    · simp only [incr, if_neg hi]
      exact Filter.Eventually.of_forall fun ω => by simp
  have h2 : ∀ i, μ[fun ω => incr Y (i + 1) ω ^ 2 | F i] =ᵐ[μ] variances c (i + 1) := by
    intro i
    rw [hcond]
    by_cases hi : i + 1 = 1 ∨ i + 1 = 2
    · simp only [incr, variances, if_pos hi]
      exact Filter.Eventually.of_forall fun ω => by simp [hc]
    · simp only [incr, variances, if_neg hi]
      exact Filter.Eventually.of_forall fun ω => by simp
  have h3 : ∀ i, Integrable
      (fun ω => |martingalePartialSum (incr Y) i ω| ^ ((4 : ℝ) - 2) * variances c (i + 1) ω)
      μ := by
    intro i
    simp only [abs_rpow_four_sub_two]
    rcases i with _ | _ | i
    · simp [partialSum_incr_zero]
    · simp only [partialSum_incr_one, zero_add, variances]
      simpa using hY2.mul_const c
    · simp [variances]
  have hmain := hK μ F (incr Y) (variances c) h1 h2 h3 2
  have hI : Finset.Icc 1 2 = {1, 2} := by decide
  have hlhs : ∑ i ∈ Finset.range 2,
      ∫ ω, |martingalePartialSum (incr Y) i ω| ^ ((4 : ℝ) - 2) * variances c (i + 1) ω ∂μ
      = c * c := by
    simp only [abs_rpow_four_sub_two, Finset.sum_range_succ, Finset.sum_range_zero,
      partialSum_incr_zero, partialSum_incr_one, variances]
    simp [integral_mul_const, hc]
  have hS2 : ∫ ω, |martingalePartialSum (incr Y) 2 ω| ^ (4 : ℝ) ∂μ = 0 := by
    simp only [partialSum_incr_two]
    exact integral_abs_rpow_four_two_mul_eq_zero hY4
  have hY4' : ∫ ω, |Y ω| ^ (4 : ℝ) ∂μ = 0 := by
    apply integral_undef
    simpa only [abs_rpow_four] using hY4
  have hξ : ∑ i ∈ Finset.Icc 1 2, ∫ ω, |incr Y i ω| ^ (4 : ℝ) ∂μ = 0 := by
    have e1 : incr Y 1 = Y := by simp [incr]
    have e2 : incr Y 2 = Y := by simp [incr]
    rw [hI, Finset.sum_pair (by norm_num), e1, e2, hY4', add_zero]
  rw [hlhs, hS2, hξ, Real.zero_rpow (by norm_num)] at hmain
  nlinarith [mul_pos hcpos hcpos]

/-! ### The counterexample on `ℕ` -/

/-- The centred heavy-tailed variable `Y n = 2^n - E X`. -/
noncomputable def heavyY (n : ℕ) : ℝ := heavyX n - ∫ k, heavyX k ∂heavyMeasure

theorem integral_heavyY : ∫ n, heavyY n ∂heavyMeasure = 0 := by
  unfold heavyY
  rw [integral_sub integrable_heavyX (integrable_const _)]
  simp

theorem integrable_heavyY_sq : Integrable (fun n => heavyY n ^ 2) heavyMeasure := by
  set m : ℝ := ∫ k, heavyX k ∂heavyMeasure with hm
  have h := (integrable_heavyX_sq.sub (integrable_heavyX.const_mul (2 * m))).add
    (integrable_const (μ := heavyMeasure) (m ^ 2))
  refine h.congr (Filter.Eventually.of_forall fun n => ?_)
  simp only [heavyY, Pi.add_apply, Pi.sub_apply, ← hm]
  ring

theorem not_integrable_heavyY_pow_four : ¬ Integrable (fun n => heavyY n ^ 4) heavyMeasure :=
  not_integrable_pow_four_sub_const (μ := heavyMeasure) (X := heavyX)
    Measurable.of_discrete.aestronglyMeasurable _ not_integrable_heavyX_pow_four

end PinelisInductionStepFalse

open PinelisInductionStepFalse in
/-- **`PinelisInductionStep` is false as stated**, in every universe.  It carries no `L^p`
hypothesis, so for a mean-zero `Y ∈ L²` with `Y ∉ L⁴` (`ξ 1 = ξ 2 = Y`, `p = 4`, `k = 2`, the
trivial filtration) the Bochner integrals `∫ |S 2|^4` and `∫ |ξ i|^4` of non-integrable
functions are `0`, the right-hand side vanishes, and the left-hand side is `(E Y²)² > 0`.
The repair is to assume `∀ i, MemLp (ξ i) (ENNReal.ofReal p) μ`.  The universe-`u` statement is
obtained by transporting the example on `ℕ` along `ULift.up`. -/
theorem not_pinelisInductionStep : ¬ PinelisInductionStep.{u} := by
  have hemb : MeasurableEmbedding (ULift.up : ℕ → ULift.{u} ℕ) :=
    MeasurableEquiv.ulift.symm.measurableEmbedding
  refine not_pinelisInductionStep_of_heavyTail (heavyMeasure.map ULift.up)
    (fun ω => heavyY ω.down) ?_ ?_ ?_
  · rw [hemb.integrable_map_iff]
    exact integrable_heavyY_sq
  · rw [hemb.integrable_map_iff]
    exact not_integrable_heavyY_pow_four
  · rw [hemb.integral_map]
    exact integral_heavyY

end LatticeProb
