/-
The Fuk-Nagaev tail inequality: for `p ≥ 2` there are `c > 0` and `C_p < ∞` with

    P(|∑ Y_i| ≥ t) ≤ C_p M_p / t^p + 2 exp(-c t²/B²)

for independent centred `Y_i` with `M_p = ∑ E|Y_i|^p` and `B² = ∑ E[Y_i²] > 0`.

A single truncation cannot prove this.  The polynomial term forces a truncation level
`τ ≥ t/y₀` with `y₀` a constant, while a Gaussian factor `exp(-c t²/B²)` out of Bernstein's
inequality forces `τ ≲ B²/t`; the two are compatible only when `t² ≲ B²`.  The proof below
cuts the variables at TWO levels, the low level

    τ = max (6 B²/t) (M_p^{1/p})            and the high level   β = t/(2p),

and treats the middle block with the Poisson bound of `LatticeProb.poisson_tail`, whose
factor `(e μ/s)^{s/β} = (2e μ/t)^p` supplies the missing power of `M_p`.  Writing
`m = M_p/t^p` and `u = t²/B²`:

* the block above `β` costs `M_p/β^p = (2p)^p m` by Markov at exponent `p`;
* the middle block costs `(2e M_p/(τ^{p-1} t))^p ≤ (2e)^p m`;
* the block below `τ`, recentred, costs `2 exp(-(t²/32)/(B² + τt/6))` by Bernstein, which is
  `2 exp(-u/64)` when `τ = 6B²/t`, and is `2 exp(-(3/32) m^{-1/p}) ≤ 2 (32p/(3e))^p m` when
  `τ = M_p^{1/p}`, by `z^p e^{-z} ≤ (p/e)^p`.

The two regimes `m ≥ (2p)^{-p}` and `u < 12p` are trivial for `C_p ≥ (2p)^p` and
`c ≤ (log 2)/(12 p)` respectively.
-/
import LatticeProb.Prob.Bernstein
import LatticeProb.Prob.PoissonTail
import LatticeProb.Prob.VonBahrEsseenSum

open MeasureTheory ProbabilityTheory

namespace LatticeProb

/-! ### The two blocks of a truncation -/

/-- `y` truncated at level `τ`. -/
noncomputable def truncAt (τ y : ℝ) : ℝ := if |y| ≤ τ then y else 0

/-- The middle block of `y`: its absolute value when `τ < |y| ≤ β`, and `0` otherwise. -/
noncomputable def midAt (τ β y : ℝ) : ℝ := if |y| ≤ τ then 0 else if |y| ≤ β then |y| else 0

theorem measurable_truncAt (τ : ℝ) : Measurable (truncAt τ) := by
  have hset : MeasurableSet {y : ℝ | |y| ≤ τ} :=
    measurableSet_le measurable_id.abs measurable_const
  exact Measurable.ite hset measurable_id measurable_const

theorem measurable_midAt (τ β : ℝ) : Measurable (midAt τ β) := by
  have hset : MeasurableSet {y : ℝ | |y| ≤ τ} :=
    measurableSet_le measurable_id.abs measurable_const
  have hset' : MeasurableSet {y : ℝ | |y| ≤ β} :=
    measurableSet_le measurable_id.abs measurable_const
  exact Measurable.ite hset measurable_const
    (Measurable.ite hset' measurable_id.abs measurable_const)

theorem abs_truncAt_le {τ : ℝ} (hτ : 0 ≤ τ) (y : ℝ) : |truncAt τ y| ≤ τ := by
  unfold truncAt
  split_ifs with h
  · exact h
  · simpa using hτ

theorem truncAt_sq_le (τ y : ℝ) : truncAt τ y ^ 2 ≤ y ^ 2 := by
  unfold truncAt
  split_ifs with h
  · exact le_refl _
  · simpa using sq_nonneg y

theorem midAt_nonneg (τ β y : ℝ) : 0 ≤ midAt τ β y := by
  unfold midAt
  split_ifs <;> simp [abs_nonneg]

theorem midAt_le {β : ℝ} (hβ : 0 ≤ β) (τ y : ℝ) : midAt τ β y ≤ β := by
  unfold midAt
  split_ifs with h1 h2
  · exact hβ
  · exact h2
  · exact hβ

/-- Below the high level the discarded part of a truncation is exactly the middle block. -/
theorem abs_sub_truncAt {β : ℝ} (τ : ℝ) {y : ℝ} (h : |y| ≤ β) :
    |y - truncAt τ y| = midAt τ β y := by
  unfold truncAt midAt
  split_ifs with h1
  · simp
  · simp

/-! ### Two elementary inequalities -/

/-- Above the truncation level a variable is dominated by its `p`-th power. -/
theorem abs_le_rpow_div_rpow {p τ y : ℝ} (hp : 1 ≤ p) (hτ : 0 < τ) (h : τ ≤ |y|) :
    |y| ≤ |y| ^ p / τ ^ (p - 1) := by
  have hy : 0 < |y| := lt_of_lt_of_le hτ h
  have hτp : (0:ℝ) < τ ^ (p - 1) := Real.rpow_pos_of_pos hτ _
  rw [le_div_iff₀ hτp]
  have hsplit : |y| ^ p = |y| * |y| ^ (p - 1) := by
    have h1 : (1:ℝ) + (p - 1) = p := by ring
    calc |y| ^ p = |y| ^ ((1:ℝ) + (p - 1)) := by rw [h1]
      _ = |y| ^ (1:ℝ) * |y| ^ (p - 1) := Real.rpow_add hy 1 (p - 1)
      _ = |y| * |y| ^ (p - 1) := by rw [Real.rpow_one]
  have hmono : τ ^ (p - 1) ≤ |y| ^ (p - 1) := Real.rpow_le_rpow hτ.le h (by linarith)
  calc |y| * τ ^ (p - 1) ≤ |y| * |y| ^ (p - 1) := by
        exact mul_le_mul_of_nonneg_left hmono hy.le
    _ = |y| ^ p := hsplit.symm

/-- `z^p e^{-z} ≤ (p/e)^p`: the exponential beats every power. -/
theorem rpow_mul_exp_neg_le {p z : ℝ} (hp : 0 < p) (hz : 0 < z) :
    z ^ p * Real.exp (-z) ≤ (p / Real.exp 1) ^ p := by
  have hpe : (0:ℝ) < p / Real.exp 1 := by positivity
  have hkey : Real.log (z / p) ≤ z / p - 1 := Real.log_le_sub_one_of_pos (by positivity)
  have hlogzp : Real.log (z / p) = Real.log z - Real.log p := Real.log_div hz.ne' hp.ne'
  have hlog : p * Real.log z - z ≤ p * Real.log (p / Real.exp 1) := by
    rw [Real.log_div hp.ne' (Real.exp_ne_zero 1), Real.log_exp]
    rw [hlogzp] at hkey
    have h3 := mul_le_mul_of_nonneg_left hkey hp.le
    have hzp : p * (z / p) = z := by field_simp
    rw [mul_sub, mul_sub, hzp, mul_one] at h3
    linarith
  have h1 : z ^ p * Real.exp (-z) = Real.exp (p * Real.log z - z) := by
    rw [Real.rpow_def_of_pos hz, ← Real.exp_add]
    ring_nf
  have h2 : (p / Real.exp 1) ^ p = Real.exp (p * Real.log (p / Real.exp 1)) := by
    rw [Real.rpow_def_of_pos hpe]
    ring_nf
  rw [h1, h2]
  exact Real.exp_le_exp.mpr hlog

/-- The discarded part of a truncation is dominated by the `p`-th power. -/
theorem abs_sub_truncAt_le_rpow {p τ : ℝ} (hp : 1 ≤ p) (hτ : 0 < τ) (y : ℝ) :
    |y - truncAt τ y| ≤ |y| ^ p / τ ^ (p - 1) := by
  unfold truncAt
  split_ifs with h
  · have : y - y = 0 := by ring
    rw [this, abs_zero]
    positivity
  · rw [sub_zero]
    exact abs_le_rpow_div_rpow hp hτ (le_of_lt (lt_of_not_ge h))

/-- The middle block is dominated by the `p`-th power. -/
theorem midAt_le_rpow {p τ β : ℝ} (hp : 1 ≤ p) (hτ : 0 < τ) (y : ℝ) :
    midAt τ β y ≤ |y| ^ p / τ ^ (p - 1) := by
  unfold midAt
  split_ifs with h1 h2
  · positivity
  · exact abs_le_rpow_div_rpow hp hτ (le_of_lt (lt_of_not_ge h1))
  · positivity

/-! ### The truncated variable -/

section OneVariable

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P] {Y : Ω → ℝ}

theorem integrable_truncAt (hY : AEStronglyMeasurable Y P) {τ : ℝ} (hτ : 0 ≤ τ) :
    Integrable (fun ω => truncAt τ (Y ω)) P := by
  refine Integrable.mono' (integrable_const τ)
    (((measurable_truncAt τ).comp_aemeasurable hY.aemeasurable).aestronglyMeasurable) ?_
  refine Filter.Eventually.of_forall fun ω => ?_
  rw [Real.norm_eq_abs]
  exact abs_truncAt_le hτ _

theorem integrable_truncAt_sq (hY : AEStronglyMeasurable Y P) {τ : ℝ} (hτ : 0 ≤ τ) :
    Integrable (fun ω => truncAt τ (Y ω) ^ 2) P := by
  refine Integrable.mono' (integrable_const (τ ^ 2))
    ((((measurable_truncAt τ).pow_const 2).comp_aemeasurable hY.aemeasurable).aestronglyMeasurable) ?_
  refine Filter.Eventually.of_forall fun ω => ?_
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  have h := abs_truncAt_le hτ (Y ω)
  nlinarith [abs_nonneg (truncAt τ (Y ω)), sq_abs (truncAt τ (Y ω))]

theorem integrable_midAt (hY : AEStronglyMeasurable Y P) {τ β : ℝ} (hβ : 0 ≤ β) :
    Integrable (fun ω => midAt τ β (Y ω)) P := by
  refine Integrable.mono' (integrable_const β)
    (((measurable_midAt τ β).comp_aemeasurable hY.aemeasurable).aestronglyMeasurable) ?_
  refine Filter.Eventually.of_forall fun ω => ?_
  rw [Real.norm_eq_abs, abs_of_nonneg (midAt_nonneg _ _ _)]
  exact midAt_le hβ _ _

/-- The mean of the middle block is at most `E|Y|^p / τ^{p-1}`. -/
theorem integral_midAt_le (hY : AEStronglyMeasurable Y P) {p τ β : ℝ} (hp : 1 ≤ p)
    (hτ : 0 < τ) (hβ : 0 ≤ β) (hpint : Integrable (fun ω => |Y ω| ^ p) P) :
    ∫ ω, midAt τ β (Y ω) ∂P ≤ (∫ ω, |Y ω| ^ p ∂P) / τ ^ (p - 1) := by
  have h := integral_mono (integrable_midAt hY hβ) (hpint.div_const (τ ^ (p - 1)))
    (fun ω => midAt_le_rpow hp hτ (Y ω))
  rwa [integral_div] at h

/-- The mean of the truncated variable is at most `E|Y|^p / τ^{p-1}` in absolute value. -/
theorem abs_integral_truncAt_le (hint : Integrable Y P) (hmean : ∫ ω, Y ω ∂P = 0)
    {p τ : ℝ} (hp : 1 ≤ p) (hτ : 0 < τ) (hpint : Integrable (fun ω => |Y ω| ^ p) P) :
    |∫ ω, truncAt τ (Y ω) ∂P| ≤ (∫ ω, |Y ω| ^ p ∂P) / τ ^ (p - 1) := by
  have hZ : Integrable (fun ω => truncAt τ (Y ω)) P :=
    integrable_truncAt hint.aestronglyMeasurable hτ.le
  have hdiff : Integrable (fun ω => Y ω - truncAt τ (Y ω)) P := hint.sub hZ
  have h1 : ∫ ω, truncAt τ (Y ω) ∂P = -∫ ω, (Y ω - truncAt τ (Y ω)) ∂P := by
    rw [integral_sub hint hZ, hmean]
    ring
  rw [h1, abs_neg]
  refine (abs_integral_le_integral_abs).trans ?_
  have h2 := integral_mono hdiff.abs (hpint.div_const (τ ^ (p - 1)))
    (fun ω => abs_sub_truncAt_le_rpow hp hτ (Y ω))
  rwa [integral_div] at h2

/-- Recentring does not increase the second moment. -/
theorem integral_sub_const_sq_le (Z : Ω → ℝ) (hZ : Integrable Z P)
    (hZ2 : Integrable (fun ω => Z ω ^ 2) P) :
    ∫ ω, (Z ω - ∫ x, Z x ∂P) ^ 2 ∂P ≤ ∫ ω, Z ω ^ 2 ∂P := by
  set c : ℝ := ∫ x, Z x ∂P with hc
  have hexp : ∀ ω, (Z ω - c) ^ 2 = Z ω ^ 2 - 2 * c * Z ω + c ^ 2 := by
    intro ω; ring
  have hint1 : Integrable (fun ω => Z ω ^ 2 - 2 * c * Z ω) P :=
    hZ2.sub (hZ.const_mul (2 * c))
  have hval : ∫ ω, (Z ω - c) ^ 2 ∂P = ∫ ω, Z ω ^ 2 ∂P - 2 * c * c + c ^ 2 := by
    simp_rw [hexp]
    rw [integral_add hint1 (integrable_const _), integral_sub hZ2 (hZ.const_mul (2 * c)),
      integral_const_mul, integral_const]
    simp [← hc]
  rw [hval]
  nlinarith [sq_nonneg c]

end OneVariable

/-! ### Bernstein's inequality with the variance only bounded -/

/-- Bernstein's inequality in the form where the total variance is merely bounded by `V`.
The degenerate case is real: if the total variance vanishes the sum is almost surely `0`. -/
theorem bernstein_var_le {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι] (P : Measure Ω)
    [IsProbabilityMeasure P] (Y : ι → Ω → ℝ) (hindep : iIndepFun Y P)
    (hint : ∀ i, Integrable (Y i) P) (hmean : ∀ i, ∫ ω, Y i ω ∂P = 0)
    (M V : ℝ) (hM : 0 < M) (hV : 0 < V) (hb : ∀ i, ∀ᵐ ω ∂P, |Y i ω| ≤ M)
    (hV2 : ∑ i, ∫ ω, Y i ω ^ 2 ∂P ≤ V) (hsq : ∀ i, Integrable (fun ω => Y i ω ^ 2) P)
    (t : ℝ) (ht : 0 < t) :
    P {ω | t ≤ |∑ i, Y i ω|}
      ≤ ENNReal.ofReal (2 * Real.exp (-(t ^ 2 / 2) / (V + M * t / 3))) := by
  classical
  have hnn : ∀ i : ι, 0 ≤ ∫ ω, Y i ω ^ 2 ∂P := fun i => integral_nonneg fun ω => sq_nonneg _
  rcases eq_or_lt_of_le (Finset.sum_nonneg fun i (_ : i ∈ Finset.univ) => hnn i) with hzero | hpos
  · have hz : ∀ i : ι, ∫ ω, Y i ω ^ 2 ∂P = 0 := by
      intro i
      have h := (Finset.sum_eq_zero_iff_of_nonneg (fun i (_ : i ∈ Finset.univ) => hnn i)).mp
        hzero.symm
      exact h i (Finset.mem_univ i)
    have hae : ∀ i : ι, ∀ᵐ ω ∂P, Y i ω = 0 := by
      intro i
      have h0 : (fun ω => Y i ω ^ 2) =ᵐ[P] 0 :=
        (integral_eq_zero_iff_of_nonneg (fun ω => sq_nonneg _) (hsq i)).mp (hz i)
      filter_upwards [h0] with ω hω
      have hx : Y i ω ^ 2 = 0 := hω
      exact sq_eq_zero_iff.mp hx
    have hsum : ∀ᵐ ω ∂P, ∑ i, Y i ω = 0 := by
      have hall := ae_all_iff.mpr hae
      filter_upwards [hall] with ω hω
      exact Finset.sum_eq_zero fun i _ => hω i
    have hq : ∀ᵐ ω ∂P, |∑ i, Y i ω| < t := by
      filter_upwards [hsum] with ω hω
      rw [hω, abs_zero]
      exact ht
    have hset : {ω | t ≤ |∑ i, Y i ω|} = {ω | ¬ (|∑ i, Y i ω| < t)} := by
      ext ω
      simp [not_lt]
    rw [hset, ae_iff.mp hq]
    simp
  · set B : ℝ := Real.sqrt (∑ i, ∫ ω, Y i ω ^ 2 ∂P) with hBdef
    have hBpos : 0 < B := Real.sqrt_pos.mpr hpos
    have hB2 : B ^ 2 = ∑ i, ∫ ω, Y i ω ^ 2 ∂P := Real.sq_sqrt (le_of_lt hpos)
    have hmain := bernstein P Y hindep hint hmean M B hM hBpos hb hB2 hsq t ht
    refine hmain.trans (ENNReal.ofReal_le_ofReal ?_)
    have hle : B ^ 2 ≤ V := by rw [hB2]; exact hV2
    have hd1 : (0:ℝ) < B ^ 2 + M * t / 3 := by positivity
    have hd2 : (0:ℝ) < V + M * t / 3 := by positivity
    have hnum : (0:ℝ) ≤ t ^ 2 / 2 := by positivity
    have h5 : (t ^ 2 / 2) / (V + M * t / 3) ≤ (t ^ 2 / 2) / (B ^ 2 + M * t / 3) :=
      div_le_div_of_nonneg_left hnum hd1 (by linarith)
    have hexp : Real.exp (-(t ^ 2 / 2) / (B ^ 2 + M * t / 3))
        ≤ Real.exp (-(t ^ 2 / 2) / (V + M * t / 3)) := by
      refine Real.exp_le_exp.mpr ?_
      rw [neg_div, neg_div]
      linarith
    linarith

/-! ### Arithmetic of the constants -/

theorem rpow_one_div_rpow {x p : ℝ} (hx : 0 ≤ x) (hp : 0 < p) : (x ^ (1 / p)) ^ p = x := by
  rw [← Real.rpow_mul hx, one_div, inv_mul_cancel₀ hp.ne', Real.rpow_one]

theorem rpow_rpow_one_div {x p : ℝ} (hx : 0 ≤ x) (hp : 0 < p) : (x ^ p) ^ (1 / p) = x := by
  rw [← Real.rpow_mul hx, mul_one_div, div_self hp.ne', Real.rpow_one]

/-- At a level above `M^{1/p}` the truncated mean bound `M/τ^{p-1}` is at most `M^{1/p}`. -/
theorem div_rpow_sub_one_le {Mp τ p : ℝ} (hMp : 0 < Mp) (hp : 1 ≤ p) (_hτ : 0 < τ)
    (h : Mp ^ (1 / p) ≤ τ) : Mp / τ ^ (p - 1) ≤ Mp ^ (1 / p) := by
  have hp0 : (0:ℝ) < p := by linarith
  have hle : (Mp ^ (1 / p)) ^ (p - 1) ≤ τ ^ (p - 1) :=
    Real.rpow_le_rpow (Real.rpow_nonneg hMp.le _) h (by linarith)
  have hpos : (0:ℝ) < (Mp ^ (1 / p)) ^ (p - 1) :=
    Real.rpow_pos_of_pos (Real.rpow_pos_of_pos hMp _) _
  have hval : (Mp ^ (1 / p)) ^ (p - 1) = Mp / Mp ^ (1 / p) := by
    rw [← Real.rpow_mul hMp.le]
    have he : (1 / p) * (p - 1) = 1 - 1 / p := by field_simp
    rw [he, Real.rpow_sub hMp, Real.rpow_one]
  have h2 : Mp / τ ^ (p - 1) ≤ Mp / (Mp ^ (1 / p)) ^ (p - 1) :=
    div_le_div_of_nonneg_left hMp.le hpos hle
  rw [hval] at h2
  have h3 : Mp / (Mp / Mp ^ (1 / p)) = Mp ^ (1 / p) := by
    have hne : Mp ^ (1 / p) ≠ 0 := (Real.rpow_pos_of_pos hMp _).ne'
    field_simp
  linarith [h2, h3.symm.le, h3.le]

/-- The middle term at the level `M^{1/p}`. -/
theorem mid_term_value {Mp t p : ℝ} (hMp : 0 ≤ Mp) (ht : 0 < t) (hp : 0 < p) :
    (2 * Real.exp 1 * Mp ^ (1 / p) / t) ^ p = (2 * Real.exp 1) ^ p * Mp / t ^ p := by
  rw [Real.div_rpow (by positivity) ht.le,
    Real.mul_rpow (by positivity) (Real.rpow_nonneg hMp _), rpow_one_div_rpow hMp hp]

/-- The exponential is below every power. -/
theorem two_exp_neg_le {z p : ℝ} (hz : 0 < z) (hp : 0 < p) :
    2 * Real.exp (-z) ≤ 2 * (p / Real.exp 1) ^ p / z ^ p := by
  have hzp : (0:ℝ) < z ^ p := Real.rpow_pos_of_pos hz _
  have h := rpow_mul_exp_neg_le hp hz
  have h1 : Real.exp (-z) ≤ (p / Real.exp 1) ^ p / z ^ p := by
    rw [le_div_iff₀ hzp]
    nlinarith [h]
  calc 2 * Real.exp (-z) ≤ 2 * ((p / Real.exp 1) ^ p / z ^ p) := by linarith
    _ = 2 * (p / Real.exp 1) ^ p / z ^ p := by ring

/-- If every summand vanishes almost surely the sum has no tail. -/
theorem measure_abs_sum_ge_eq_zero {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι]
    (P : Measure Ω) (Y : ι → Ω → ℝ) (hae : ∀ i, ∀ᵐ ω ∂P, Y i ω = 0) {t : ℝ} (ht : 0 < t) :
    P {ω | t ≤ |∑ i, Y i ω|} = 0 := by
  have hsum : ∀ᵐ ω ∂P, ∑ i, Y i ω = 0 := by
    have hall := ae_all_iff.mpr hae
    filter_upwards [hall] with ω hω
    exact Finset.sum_eq_zero fun i _ => hω i
  have hq : ∀ᵐ ω ∂P, |∑ i, Y i ω| < t := by
    filter_upwards [hsum] with ω hω
    rw [hω, abs_zero]
    exact ht
  have hset : {ω | t ≤ |∑ i, Y i ω|} = {ω | ¬ (|∑ i, Y i ω| < t)} := by
    ext ω
    simp [not_lt]
  rw [hset]
  exact ae_iff.mp hq

/-- A vanishing `p`-th moment forces the variable to vanish. -/
theorem ae_eq_zero_of_integral_abs_rpow_eq_zero {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (Y : Ω → ℝ) {p : ℝ} (_hp : 0 < p)
    (hint : Integrable (fun ω => |Y ω| ^ p) P) (h : ∫ ω, |Y ω| ^ p ∂P = 0) :
    ∀ᵐ ω ∂P, Y ω = 0 := by
  have h0 : (fun ω => |Y ω| ^ p) =ᵐ[P] 0 :=
    (integral_eq_zero_iff_of_nonneg (fun ω => Real.rpow_nonneg (abs_nonneg _) _) hint).mp h
  filter_upwards [h0] with ω hω
  have hx : |Y ω| ^ p = 0 := hω
  have habs : |Y ω| = 0 := by
    by_contra hne
    have hpos : 0 < |Y ω| := lt_of_le_of_ne (abs_nonneg _) (Ne.symm hne)
    exact absurd hx (ne_of_gt (Real.rpow_pos_of_pos hpos p))
  exact abs_eq_zero.mp habs

/-! ### The two-level truncation -/

/-- The Fuk-Nagaev bound at a fixed low level `τ`, with the high level `t/(2p)`:
the block above `t/(2p)`, the middle block and the recentred low block. -/
theorem fukNagaev_trunc {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι] (P : Measure Ω)
    [IsProbabilityMeasure P] (Y : ι → Ω → ℝ) (hindep : iIndepFun Y P)
    (hint : ∀ i, Integrable (Y i) P) (hmean : ∀ i, ∫ ω, Y i ω ∂P = 0)
    {p : ℝ} (hp : 2 ≤ p) (hpint : ∀ i, Integrable (fun ω => |Y i ω| ^ p) P)
    (hsq : ∀ i, Integrable (fun ω => Y i ω ^ 2) P)
    {Mp B t τ : ℝ} (hMp : Mp = ∑ i, ∫ ω, |Y i ω| ^ p ∂P) (hMp0 : 0 < Mp)
    (hB : 0 < B) (hB2 : B ^ 2 = ∑ i, ∫ ω, Y i ω ^ 2 ∂P)
    (ht : 0 < t) (hτ : 0 < τ) (hτβ : 2 * p * τ ≤ t) (hrec : Mp / τ ^ (p - 1) ≤ t / 4) :
    P {ω | t ≤ |∑ i, Y i ω|}
      ≤ ENNReal.ofReal ((2 * p) ^ p * Mp / t ^ p)
        + ENNReal.ofReal ((2 * Real.exp 1 * (Mp / τ ^ (p - 1)) / t) ^ p)
        + ENNReal.ofReal (2 * Real.exp (-(t ^ 2 / 32) / (B ^ 2 + τ * t / 6))) := by
  classical
  have hp0 : (0:ℝ) < p := by linarith
  have hp1 : (1:ℝ) ≤ p := by linarith
  set β : ℝ := t / (2 * p) with hβdef
  have hβpos : 0 < β := by rw [hβdef]; positivity
  have hτβ' : τ ≤ β := by
    rw [hβdef, le_div_iff₀ (by positivity)]
    linarith
  set Z : ι → Ω → ℝ := fun i ω => truncAt τ (Y i ω) with hZdef
  set W : ι → Ω → ℝ := fun i ω => midAt τ β (Y i ω) with hWdef
  set μ : ℝ := Mp / τ ^ (p - 1) with hμdef
  have hτp : (0:ℝ) < τ ^ (p - 1) := Real.rpow_pos_of_pos hτ _
  have hμpos : 0 < μ := by rw [hμdef]; positivity
  -- the block above the high level
  have hbig : P (⋃ i, {ω | β < |Y i ω|}) ≤ ENNReal.ofReal ((2 * p) ^ p * Mp / t ^ p) := by
    have h1 : ∀ i, P {ω | β < |Y i ω|} ≤ ENNReal.ofReal ((∫ ω, |Y i ω| ^ p ∂P) / β ^ p) := by
      intro i
      refine le_trans (measure_mono ?_)
        (measure_abs_ge_le_div_rpow P hp1 (hint i).aestronglyMeasurable (hpint i) hβpos)
      intro ω hω
      simp only [Set.mem_setOf_eq] at hω ⊢
      exact le_of_lt hω
    have hnn : ∀ i : ι, 0 ≤ (∫ ω, |Y i ω| ^ p ∂P) / β ^ p := by
      intro i
      have : 0 ≤ ∫ ω, |Y i ω| ^ p ∂P :=
        integral_nonneg fun ω => Real.rpow_nonneg (abs_nonneg _) _
      positivity
    have hval : (∑ i, (∫ ω, |Y i ω| ^ p ∂P) / β ^ p) = (2 * p) ^ p * Mp / t ^ p := by
      rw [← Finset.sum_div, ← hMp, hβdef, Real.div_rpow ht.le (by positivity)]
      field_simp
    calc P (⋃ i, {ω | β < |Y i ω|}) ≤ ∑' i, P {ω | β < |Y i ω|} := measure_iUnion_le _
      _ = ∑ i, P {ω | β < |Y i ω|} := tsum_fintype _
      _ ≤ ∑ i, ENNReal.ofReal ((∫ ω, |Y i ω| ^ p ∂P) / β ^ p) :=
          Finset.sum_le_sum fun i _ => h1 i
      _ = ENNReal.ofReal (∑ i, (∫ ω, |Y i ω| ^ p ∂P) / β ^ p) :=
          (ENNReal.ofReal_sum_of_nonneg (fun i _ => hnn i)).symm
      _ = ENNReal.ofReal ((2 * p) ^ p * Mp / t ^ p) := by rw [hval]
  -- the middle block
  have hmidbound : P {ω | t / 2 ≤ ∑ i, W i ω}
      ≤ ENNReal.ofReal ((2 * Real.exp 1 * μ / t) ^ p) := by
    have hWindep : iIndepFun W P :=
      hindep.comp (fun _ : ι => midAt τ β) (fun _ => measurable_midAt τ β)
    have hWint : ∀ i, Integrable (W i) P :=
      fun i => integrable_midAt (hint i).aestronglyMeasurable hβpos.le
    have hW0 : ∀ i, ∀ᵐ ω ∂P, 0 ≤ W i ω :=
      fun i => Filter.Eventually.of_forall fun ω => midAt_nonneg _ _ _
    have hWβ : ∀ i, ∀ᵐ ω ∂P, W i ω ≤ β :=
      fun i => Filter.Eventually.of_forall fun ω => midAt_le hβpos.le _ _
    have hWmean : ∑ i, ∫ ω, W i ω ∂P ≤ μ := by
      have h1 : ∀ i : ι, ∫ ω, W i ω ∂P ≤ (∫ ω, |Y i ω| ^ p ∂P) / τ ^ (p - 1) :=
        fun i => integral_midAt_le (hint i).aestronglyMeasurable hp1 hτ hβpos.le (hpint i)
      calc ∑ i, ∫ ω, W i ω ∂P ≤ ∑ i, (∫ ω, |Y i ω| ^ p ∂P) / τ ^ (p - 1) :=
            Finset.sum_le_sum fun i _ => h1 i
        _ = μ := by rw [← Finset.sum_div, ← hMp, hμdef]
    have hst : μ ≤ t / 2 := le_trans hrec (by linarith)
    have h := poisson_tail P W hWindep hWint β hβpos hW0 hWβ μ (t / 2) hμpos hWmean hst
    have hexp : (t / 2) / β = p := by
      rw [hβdef]
      field_simp
    have hval : Real.exp 1 * μ / (t / 2) = 2 * Real.exp 1 * μ / t := by
      field_simp
    rwa [hexp, hval] at h
  -- the recentred low block
  have hZint : ∀ i, Integrable (Z i) P :=
    fun i => integrable_truncAt (hint i).aestronglyMeasurable hτ.le
  set a : ι → ℝ := fun i => ∫ ω, Z i ω ∂P with hadef
  set Z' : ι → Ω → ℝ := fun i ω => Z i ω - a i with hZ'def
  have haτ : ∀ i, |a i| ≤ τ := by
    intro i
    refine (abs_integral_le_integral_abs).trans ?_
    have h2 : ∫ ω, |Z i ω| ∂P ≤ ∫ _ω : Ω, τ ∂P :=
      integral_mono (hZint i).abs (integrable_const τ) fun ω => abs_truncAt_le hτ.le _
    simpa using h2
  have habsa : |∑ i, a i| ≤ μ := by
    have h1 : ∀ i : ι, |a i| ≤ (∫ ω, |Y i ω| ^ p ∂P) / τ ^ (p - 1) :=
      fun i => abs_integral_truncAt_le (hint i) (hmean i) hp1 hτ (hpint i)
    calc |∑ i, a i| ≤ ∑ i, |a i| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ i, (∫ ω, |Y i ω| ^ p ∂P) / τ ^ (p - 1) := Finset.sum_le_sum fun i _ => h1 i
      _ = μ := by rw [← Finset.sum_div, ← hMp, hμdef]
  have hZ'int : ∀ i, Integrable (Z' i) P := fun i => (hZint i).sub (integrable_const _)
  have hZ'indep : iIndepFun Z' P :=
    hindep.comp (fun i => fun y => truncAt τ y - a i)
      (fun i => (measurable_truncAt τ).sub measurable_const)
  have hZ'mean : ∀ i, ∫ ω, Z' i ω ∂P = 0 := by
    intro i
    have h1 : ∫ ω, (Z i ω - a i) ∂P = (∫ ω, Z i ω ∂P) - a i := by
      rw [integral_sub (hZint i) (integrable_const _), integral_const]
      simp
    simpa [hadef] using h1
  have hZ'abs : ∀ i, ∀ ω, |Z' i ω| ≤ 2 * τ := by
    intro i ω
    have h1 : |Z i ω| ≤ τ := abs_truncAt_le hτ.le _
    have h2 : |a i| ≤ τ := haτ i
    have h3 : |Z i ω - a i| ≤ |Z i ω| + |a i| := by
      have h4 := abs_add_le (Z i ω) (-(a i))
      rw [← sub_eq_add_neg, abs_neg] at h4
      exact h4
    calc |Z' i ω| = |Z i ω - a i| := rfl
      _ ≤ |Z i ω| + |a i| := h3
      _ ≤ 2 * τ := by linarith
  have hZ'b : ∀ i, ∀ᵐ ω ∂P, |Z' i ω| ≤ 2 * τ :=
    fun i => Filter.Eventually.of_forall fun ω => hZ'abs i ω
  have hZ'sq : ∀ i, Integrable (fun ω => Z' i ω ^ 2) P := by
    intro i
    have hmeas : AEStronglyMeasurable (fun ω => Z' i ω ^ 2) P :=
      (((((measurable_truncAt τ).sub measurable_const).pow_const 2)).comp_aemeasurable
        (hint i).aemeasurable).aestronglyMeasurable
    refine Integrable.mono' (integrable_const ((2 * τ) ^ 2)) hmeas ?_
    refine Filter.Eventually.of_forall fun ω => ?_
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    have h1 := hZ'abs i ω
    nlinarith [abs_nonneg (Z' i ω), sq_abs (Z' i ω)]
  have hvar : ∑ i, ∫ ω, Z' i ω ^ 2 ∂P ≤ B ^ 2 := by
    have h1 : ∀ i : ι, ∫ ω, Z' i ω ^ 2 ∂P ≤ ∫ ω, Y i ω ^ 2 ∂P := by
      intro i
      have hZsq : Integrable (fun ω => Z i ω ^ 2) P :=
        integrable_truncAt_sq (hint i).aestronglyMeasurable hτ.le
      have hstep1 : ∫ ω, Z' i ω ^ 2 ∂P ≤ ∫ ω, Z i ω ^ 2 ∂P :=
        integral_sub_const_sq_le (Z i) (hZint i) hZsq
      have hstep2 : ∫ ω, Z i ω ^ 2 ∂P ≤ ∫ ω, Y i ω ^ 2 ∂P :=
        integral_mono hZsq (hsq i) fun ω => truncAt_sq_le τ (Y i ω)
      linarith
    calc ∑ i, ∫ ω, Z' i ω ^ 2 ∂P ≤ ∑ i, ∫ ω, Y i ω ^ 2 ∂P := Finset.sum_le_sum fun i _ => h1 i
      _ = B ^ 2 := hB2.symm
  have hlow : P {ω | t / 2 ≤ |∑ i, Z i ω|}
      ≤ ENNReal.ofReal (2 * Real.exp (-(t ^ 2 / 32) / (B ^ 2 + τ * t / 6))) := by
    have hbern := bernstein_var_le P Z' hZ'indep hZ'int hZ'mean (2 * τ) (B ^ 2)
      (by positivity) (by positivity) hZ'b hvar hZ'sq (t / 4) (by positivity)
    have hincl : {ω | t / 2 ≤ |∑ i, Z i ω|} ⊆ {ω | t / 4 ≤ |∑ i, Z' i ω|} := by
      intro ω hω
      have hsplit : ∑ i, Z i ω = (∑ i, Z' i ω) + ∑ i, a i := by
        rw [← Finset.sum_add_distrib]
        exact Finset.sum_congr rfl fun i _ => by rw [hZ'def]; ring
      have h1 : |∑ i, Z i ω| ≤ |∑ i, Z' i ω| + |∑ i, a i| := by
        rw [hsplit]
        exact abs_add_le _ _
      have h2 : t / 2 ≤ |∑ i, Z i ω| := hω
      have h3 : |∑ i, a i| ≤ t / 4 := le_trans habsa (le_trans hrec (le_refl _))
      show t / 4 ≤ |∑ i, Z' i ω|
      linarith
    have hval : -((t / 4) ^ 2 / 2) / (B ^ 2 + 2 * τ * (t / 4) / 3)
        = -(t ^ 2 / 32) / (B ^ 2 + τ * t / 6) := by
      ring_nf
    calc P {ω | t / 2 ≤ |∑ i, Z i ω|} ≤ P {ω | t / 4 ≤ |∑ i, Z' i ω|} := measure_mono hincl
      _ ≤ ENNReal.ofReal (2 * Real.exp (-((t / 4) ^ 2 / 2) / (B ^ 2 + 2 * τ * (t / 4) / 3))) :=
          hbern
      _ = ENNReal.ofReal (2 * Real.exp (-(t ^ 2 / 32) / (B ^ 2 + τ * t / 6))) := by rw [hval]
  -- the decomposition
  have hsub : {ω | t ≤ |∑ i, Y i ω|}
      ⊆ (⋃ i, {ω | β < |Y i ω|}) ∪ ({ω | t / 2 ≤ ∑ i, W i ω} ∪ {ω | t / 2 ≤ |∑ i, Z i ω|}) := by
    intro ω hω
    by_cases hbig' : ∃ i, β < |Y i ω|
    · obtain ⟨i, hi⟩ := hbig'
      exact Or.inl (Set.mem_iUnion.mpr ⟨i, hi⟩)
    · have hball : ∀ i, |Y i ω| ≤ β := by
        intro i
        by_contra hc
        exact hbig' ⟨i, lt_of_not_ge hc⟩
      by_cases hmid : t / 2 ≤ ∑ i, W i ω
      · exact Or.inr (Or.inl hmid)
      · have hmid' : ∑ i, W i ω < t / 2 := lt_of_not_ge hmid
        refine Or.inr (Or.inr ?_)
        have hdiff : |(∑ i, Y i ω) - ∑ i, Z i ω| ≤ ∑ i, W i ω := by
          rw [← Finset.sum_sub_distrib]
          refine (Finset.abs_sum_le_sum_abs _ _).trans (le_of_eq ?_)
          exact Finset.sum_congr rfl fun i _ => abs_sub_truncAt τ (hball i)
        have h1 : |∑ i, Y i ω| - |∑ i, Z i ω| ≤ |(∑ i, Y i ω) - ∑ i, Z i ω| :=
          abs_sub_abs_le_abs_sub _ _
        have h2 : t ≤ |∑ i, Y i ω| := hω
        show t / 2 ≤ |∑ i, Z i ω|
        linarith [hmid']
  calc P {ω | t ≤ |∑ i, Y i ω|}
      ≤ P ((⋃ i, {ω | β < |Y i ω|}) ∪
          ({ω | t / 2 ≤ ∑ i, W i ω} ∪ {ω | t / 2 ≤ |∑ i, Z i ω|})) := measure_mono hsub
    _ ≤ P (⋃ i, {ω | β < |Y i ω|})
          + P ({ω | t / 2 ≤ ∑ i, W i ω} ∪ {ω | t / 2 ≤ |∑ i, Z i ω|}) := measure_union_le _ _
    _ ≤ P (⋃ i, {ω | β < |Y i ω|})
          + (P {ω | t / 2 ≤ ∑ i, W i ω} + P {ω | t / 2 ≤ |∑ i, Z i ω|}) :=
        add_le_add le_rfl (measure_union_le _ _)
    _ ≤ ENNReal.ofReal ((2 * p) ^ p * Mp / t ^ p)
          + (ENNReal.ofReal ((2 * Real.exp 1 * μ / t) ^ p)
            + ENNReal.ofReal (2 * Real.exp (-(t ^ 2 / 32) / (B ^ 2 + τ * t / 6)))) :=
        add_le_add hbig (add_le_add hmidbound hlow)
    _ = ENNReal.ofReal ((2 * p) ^ p * Mp / t ^ p)
          + ENNReal.ofReal ((2 * Real.exp 1 * μ / t) ^ p)
          + ENNReal.ofReal (2 * Real.exp (-(t ^ 2 / 32) / (B ^ 2 + τ * t / 6))) :=
        (add_assoc _ _ _).symm


/-! ### The Fuk-Nagaev inequality -/

/-- The constant of the polynomial term. -/
noncomputable def fukNagaevConst (p : ℝ) : ℝ :=
  (2 * p) ^ p + (2 * Real.exp 1) ^ p + 2 * (32 * p / (3 * Real.exp 1)) ^ p

/-- The constant of the exponential term. -/
noncomputable def fukNagaevExp (p : ℝ) : ℝ := Real.log 2 / (64 * p)

theorem fukNagaevConst_pos {p : ℝ} (hp : 2 ≤ p) : 0 < fukNagaevConst p := by
  unfold fukNagaevConst
  have h1 : (0:ℝ) < (2 * p) ^ p := Real.rpow_pos_of_pos (by linarith) _
  have h2 : (0:ℝ) < (2 * Real.exp 1) ^ p := Real.rpow_pos_of_pos (by positivity) _
  have h3 : (0:ℝ) < (32 * p / (3 * Real.exp 1)) ^ p := Real.rpow_pos_of_pos (by positivity) _
  linarith

theorem fukNagaevExp_pos {p : ℝ} (hp : 2 ≤ p) : 0 < fukNagaevExp p := by
  unfold fukNagaevExp
  have hlog : (0:ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hp0 : (0:ℝ) < p := by linarith
  positivity

theorem fukNagaevExp_le {p : ℝ} (hp : 2 ≤ p) : fukNagaevExp p ≤ 1 / 64 := by
  unfold fukNagaevExp
  have hp0 : (0:ℝ) < p := by linarith
  have h1 : Real.log 2 ≤ p := by nlinarith [Real.log_two_lt_d9]
  have h2 : Real.log 2 / (64 * p) ≤ p / (64 * p) := by gcongr
  have h3 : p / (64 * p) = 1 / 64 := by field_simp
  linarith

/-- **The Fuk-Nagaev inequality.**  For independent centred summands with `p`-th moments,

    P(|∑ Y_i| ≥ t) ≤ C_p M_p/t^p + 2 exp(-c_p t²/B²) . -/
theorem fukNagaev_bound {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι] (P : Measure Ω)
    [IsProbabilityMeasure P] (Y : ι → Ω → ℝ) (hindep : iIndepFun Y P)
    (hint : ∀ i, Integrable (Y i) P) (hmean : ∀ i, ∫ ω, Y i ω ∂P = 0)
    {p : ℝ} (hp : 2 ≤ p) (hpint : ∀ i, Integrable (fun ω => |Y i ω| ^ p) P)
    (hsq : ∀ i, Integrable (fun ω => Y i ω ^ 2) P)
    {Mp B t : ℝ} (hMpdef : Mp = ∑ i, ∫ ω, |Y i ω| ^ p ∂P)
    (hB : 0 < B) (hB2 : B ^ 2 = ∑ i, ∫ ω, Y i ω ^ 2 ∂P) (ht : 0 < t) :
    P {ω | t ≤ |∑ i, Y i ω|}
      ≤ ENNReal.ofReal (fukNagaevConst p * Mp / t ^ p
          + 2 * Real.exp (-(fukNagaevExp p) * t ^ 2 / B ^ 2)) := by
  classical
  have hp0 : (0:ℝ) < p := by linarith
  have hp1 : (1:ℝ) ≤ p := by linarith
  have hCpos : 0 < fukNagaevConst p := fukNagaevConst_pos hp
  have hcpos : 0 < fukNagaevExp p := fukNagaevExp_pos hp
  have hB2pos : (0:ℝ) < B ^ 2 := by positivity
  have htp : (0:ℝ) < t ^ p := Real.rpow_pos_of_pos ht p
  have hMpnn : 0 ≤ Mp := by
    rw [hMpdef]
    exact Finset.sum_nonneg fun i _ =>
      integral_nonneg fun ω => Real.rpow_nonneg (abs_nonneg _) _
  have hexpnn : (0:ℝ) ≤ 2 * Real.exp (-(fukNagaevExp p) * t ^ 2 / B ^ 2) := by positivity
  have hpolynn : (0:ℝ) ≤ fukNagaevConst p * Mp / t ^ p := by positivity
  by_cases htriv : 1 ≤ fukNagaevConst p * Mp / t ^ p
  · refine le_trans prob_le_one ?_
    rw [← ENNReal.ofReal_one]
    exact ENNReal.ofReal_le_ofReal (by linarith)
  have htriv' : fukNagaevConst p * Mp / t ^ p < 1 := lt_of_not_ge htriv
  by_cases hu : t ^ 2 < 12 * p * B ^ 2
  · refine le_trans prob_le_one ?_
    have hratio : t ^ 2 / B ^ 2 < 12 * p := by
      rw [div_lt_iff₀ hB2pos]
      linarith
    have hlog : -(Real.log 2) ≤ -(fukNagaevExp p) * t ^ 2 / B ^ 2 := by
      have hlog2 : (0:ℝ) < Real.log 2 := Real.log_pos (by norm_num)
      have hval : -(fukNagaevExp p) * t ^ 2 / B ^ 2
          = -(Real.log 2 / (64 * p) * (t ^ 2 / B ^ 2)) := by
        unfold fukNagaevExp
        field_simp
      rw [hval, neg_le_neg_iff]
      have h1 : Real.log 2 / (64 * p) * (t ^ 2 / B ^ 2)
          ≤ Real.log 2 / (64 * p) * (12 * p) :=
        mul_le_mul_of_nonneg_left hratio.le (by positivity)
      have h2 : Real.log 2 / (64 * p) * (12 * p) = 12 * Real.log 2 / 64 := by
        field_simp
      linarith
    have hexpge : (1:ℝ) / 2 ≤ Real.exp (-(fukNagaevExp p) * t ^ 2 / B ^ 2) := by
      have h3 : Real.exp (-(Real.log 2)) ≤ Real.exp (-(fukNagaevExp p) * t ^ 2 / B ^ 2) :=
        Real.exp_le_exp.mpr hlog
      have h4 : Real.exp (-(Real.log 2)) = 1 / 2 := by
        rw [Real.exp_neg, Real.exp_log (by norm_num : (0:ℝ) < 2)]
        norm_num
      linarith
    rw [← ENNReal.ofReal_one]
    refine ENNReal.ofReal_le_ofReal ?_
    linarith
  have hu' : 12 * p * B ^ 2 ≤ t ^ 2 := not_lt.mp hu
  rcases eq_or_lt_of_le hMpnn with hMp0 | hMp0
  · have hae : ∀ i, ∀ᵐ ω ∂P, Y i ω = 0 := by
      intro i
      have hnn : ∀ j : ι, 0 ≤ ∫ ω, |Y j ω| ^ p ∂P :=
        fun j => integral_nonneg fun ω => Real.rpow_nonneg (abs_nonneg _) _
      have hsum0 : ∑ j, ∫ ω, |Y j ω| ^ p ∂P = 0 := by rw [← hMpdef, ← hMp0]
      have hz : ∫ ω, |Y i ω| ^ p ∂P = 0 :=
        (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => hnn j)).mp hsum0 i (Finset.mem_univ i)
      exact ae_eq_zero_of_integral_abs_rpow_eq_zero P (Y i) hp0 (hpint i) hz
    rw [measure_abs_sum_ge_eq_zero P Y hae ht]
    simp
  -- the main case
  have hMplt : Mp ^ (1 / p) < t / (2 * p) := by
    have hge : (2 * p) ^ p ≤ fukNagaevConst p := by
      unfold fukNagaevConst
      have h2 : (0:ℝ) < (2 * Real.exp 1) ^ p := Real.rpow_pos_of_pos (by positivity) _
      have h3 : (0:ℝ) < (32 * p / (3 * Real.exp 1)) ^ p := Real.rpow_pos_of_pos (by positivity) _
      linarith
    have hlt : fukNagaevConst p * Mp < t ^ p := (div_lt_one htp).mp htriv'
    have h1 : Mp < (t / (2 * p)) ^ p := by
      rw [Real.div_rpow ht.le (by positivity),
        lt_div_iff₀ (Real.rpow_pos_of_pos (by positivity : (0:ℝ) < 2 * p) p)]
      nlinarith [hge, hMp0, hlt]
    have h2 : Mp ^ (1 / p) < ((t / (2 * p)) ^ p) ^ (1 / p) :=
      Real.rpow_lt_rpow hMpnn h1 (by positivity)
    rwa [rpow_rpow_one_div (by positivity) hp0] at h2
  have hquarter : t / (2 * p) ≤ t / 4 :=
    div_le_div_of_nonneg_left ht.le (by norm_num) (by linarith)
  by_cases hcase : Mp ^ (1 / p) ≤ 6 * B ^ 2 / t
  · -- the low level is `6B²/t`: the Bernstein term keeps its Gaussian form
    have hτ : (0:ℝ) < 6 * B ^ 2 / t := by positivity
    have hτβ : 2 * p * (6 * B ^ 2 / t) ≤ t := by
      have hval : 2 * p * (6 * B ^ 2 / t) = 12 * p * B ^ 2 / t := by
        field_simp
        ring
      rw [hval, div_le_iff₀ ht]
      nlinarith [hu']
    have hmean' := div_rpow_sub_one_le hMp0 hp1 hτ hcase
    have hrec : Mp / (6 * B ^ 2 / t) ^ (p - 1) ≤ t / 4 := by linarith
    have hmain := fukNagaev_trunc P Y hindep hint hmean hp hpint hsq hMpdef hMp0 hB hB2 ht hτ
      hτβ hrec
    refine hmain.trans ?_
    rw [← ENNReal.ofReal_add (by positivity) (by positivity),
      ← ENNReal.ofReal_add (by positivity) (by positivity)]
    refine ENNReal.ofReal_le_ofReal ?_
    have hmidle : (2 * Real.exp 1 * (Mp / (6 * B ^ 2 / t) ^ (p - 1)) / t) ^ p
        ≤ (2 * Real.exp 1) ^ p * Mp / t ^ p := by
      have hstep : 2 * Real.exp 1 * (Mp / (6 * B ^ 2 / t) ^ (p - 1)) / t
          ≤ 2 * Real.exp 1 * Mp ^ (1 / p) / t := by gcongr
      have h6 := Real.rpow_le_rpow (by positivity) hstep hp0.le
      rwa [mid_term_value hMpnn ht hp0] at h6
    have hexple : 2 * Real.exp (-(t ^ 2 / 32) / (B ^ 2 + 6 * B ^ 2 / t * t / 6))
        ≤ 2 * Real.exp (-(fukNagaevExp p) * t ^ 2 / B ^ 2) := by
      have hden : B ^ 2 + 6 * B ^ 2 / t * t / 6 = 2 * B ^ 2 := by
        have hcancel : 6 * B ^ 2 / t * t = 6 * B ^ 2 := div_mul_cancel₀ _ ht.ne'
        rw [hcancel]
        ring
      rw [hden]
      have hc := fukNagaevExp_le hp
      have h7 : fukNagaevExp p * (t ^ 2 / B ^ 2) ≤ (1 / 64) * (t ^ 2 / B ^ 2) :=
        mul_le_mul_of_nonneg_right hc (by positivity)
      have h8 : -(t ^ 2 / 32) / (2 * B ^ 2) = -((1 / 64) * (t ^ 2 / B ^ 2)) := by
        field_simp
        norm_num
      have h9 : -(fukNagaevExp p) * t ^ 2 / B ^ 2 = -(fukNagaevExp p * (t ^ 2 / B ^ 2)) := by
        field_simp
      have h10 : Real.exp (-(t ^ 2 / 32) / (2 * B ^ 2))
          ≤ Real.exp (-(fukNagaevExp p) * t ^ 2 / B ^ 2) := by
        refine Real.exp_le_exp.mpr ?_
        rw [h8, h9]
        linarith
      linarith
    have hthird : (0:ℝ) ≤ 2 * (32 * p / (3 * Real.exp 1)) ^ p * Mp / t ^ p := by positivity
    unfold fukNagaevConst
    have hexpand : ((2 * p) ^ p + (2 * Real.exp 1) ^ p + 2 * (32 * p / (3 * Real.exp 1)) ^ p)
          * Mp / t ^ p
        = (2 * p) ^ p * Mp / t ^ p + (2 * Real.exp 1) ^ p * Mp / t ^ p
          + 2 * (32 * p / (3 * Real.exp 1)) ^ p * Mp / t ^ p := by
      ring
    rw [hexpand]
    linarith [hmidle, hexple, hthird]
  · -- the low level is `Mp^{1/p}`: the Bernstein term becomes polynomial
    have hcase' : 6 * B ^ 2 / t < Mp ^ (1 / p) := lt_of_not_ge hcase
    have hτ : (0:ℝ) < Mp ^ (1 / p) := Real.rpow_pos_of_pos hMp0 _
    have hτβ : 2 * p * Mp ^ (1 / p) ≤ t := by
      have h1 : Mp ^ (1 / p) * (2 * p) < t := by
        rw [← lt_div_iff₀ (by positivity : (0:ℝ) < 2 * p)]
        exact hMplt
      linarith
    have hmean' := div_rpow_sub_one_le hMp0 hp1 hτ (le_refl (Mp ^ (1 / p)))
    have hrec : Mp / (Mp ^ (1 / p)) ^ (p - 1) ≤ t / 4 := by linarith
    have hmain := fukNagaev_trunc P Y hindep hint hmean hp hpint hsq hMpdef hMp0 hB hB2 ht hτ
      hτβ hrec
    refine hmain.trans ?_
    rw [← ENNReal.ofReal_add (by positivity) (by positivity),
      ← ENNReal.ofReal_add (by positivity) (by positivity)]
    refine ENNReal.ofReal_le_ofReal ?_
    have hmidle : (2 * Real.exp 1 * (Mp / (Mp ^ (1 / p)) ^ (p - 1)) / t) ^ p
        ≤ (2 * Real.exp 1) ^ p * Mp / t ^ p := by
      have hstep : 2 * Real.exp 1 * (Mp / (Mp ^ (1 / p)) ^ (p - 1)) / t
          ≤ 2 * Real.exp 1 * Mp ^ (1 / p) / t := by gcongr
      have h6 := Real.rpow_le_rpow (by positivity) hstep hp0.le
      rwa [mid_term_value hMpnn ht hp0] at h6
    have hBsmall : B ^ 2 < Mp ^ (1 / p) * t / 6 := by
      rw [div_lt_iff₀ ht] at hcase'
      linarith
    have hden0 : (0:ℝ) < B ^ 2 + Mp ^ (1 / p) * t / 6 := by positivity
    have hden : B ^ 2 + Mp ^ (1 / p) * t / 6 ≤ Mp ^ (1 / p) * t / 3 := by linarith
    have hzpos : (0:ℝ) < 3 * t / (32 * Mp ^ (1 / p)) := by positivity
    have hexp1 : -(t ^ 2 / 32) / (B ^ 2 + Mp ^ (1 / p) * t / 6)
        ≤ -(3 * t / (32 * Mp ^ (1 / p))) := by
      have hd : (t ^ 2 / 32) / (Mp ^ (1 / p) * t / 3)
          ≤ (t ^ 2 / 32) / (B ^ 2 + Mp ^ (1 / p) * t / 6) :=
        div_le_div_of_nonneg_left (by positivity) hden0 hden
      have heq : (t ^ 2 / 32) / (Mp ^ (1 / p) * t / 3) = 3 * t / (32 * Mp ^ (1 / p)) := by
        field_simp
      rw [neg_div]
      rw [heq] at hd
      linarith
    have hexp3 : 2 * (p / Real.exp 1) ^ p / (3 * t / (32 * Mp ^ (1 / p))) ^ p
        = 2 * (32 * p / (3 * Real.exp 1)) ^ p * Mp / t ^ p := by
      rw [mul_div_assoc, ← Real.div_rpow (by positivity) (by positivity)]
      have hval : (p / Real.exp 1) / (3 * t / (32 * Mp ^ (1 / p)))
          = 32 * p / (3 * Real.exp 1) * (Mp ^ (1 / p) / t) := by
        field_simp
      rw [hval, Real.mul_rpow (by positivity) (by positivity),
        Real.div_rpow (Real.rpow_nonneg hMpnn _) ht.le, rpow_one_div_rpow hMpnn hp0]
      ring
    have hexple : 2 * Real.exp (-(t ^ 2 / 32) / (B ^ 2 + Mp ^ (1 / p) * t / 6))
        ≤ 2 * (32 * p / (3 * Real.exp 1)) ^ p * Mp / t ^ p := by
      have h1 : Real.exp (-(t ^ 2 / 32) / (B ^ 2 + Mp ^ (1 / p) * t / 6))
          ≤ Real.exp (-(3 * t / (32 * Mp ^ (1 / p)))) := Real.exp_le_exp.mpr hexp1
      have h2 := two_exp_neg_le hzpos hp0
      rw [hexp3] at h2
      linarith
    unfold fukNagaevConst
    have hfirst : (0:ℝ) ≤ (2 * p) ^ p * Mp / t ^ p := by positivity
    have hexpand : ((2 * p) ^ p + (2 * Real.exp 1) ^ p + 2 * (32 * p / (3 * Real.exp 1)) ^ p)
          * Mp / t ^ p
        = (2 * p) ^ p * Mp / t ^ p + (2 * Real.exp 1) ^ p * Mp / t ^ p
          + 2 * (32 * p / (3 * Real.exp 1)) ^ p * Mp / t ^ p := by
      ring
    rw [hexpand]
    linarith [hmidle, hexple, hexpnn]


/-- The one-sided form of the Fuk-Nagaev inequality. -/
theorem fukNagaev_bound_one_sided {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι] (P : Measure Ω)
    [IsProbabilityMeasure P] (Y : ι → Ω → ℝ) (hindep : iIndepFun Y P)
    (hint : ∀ i, Integrable (Y i) P) (hmean : ∀ i, ∫ ω, Y i ω ∂P = 0)
    {p : ℝ} (hp : 2 ≤ p) (hpint : ∀ i, Integrable (fun ω => |Y i ω| ^ p) P)
    (hsq : ∀ i, Integrable (fun ω => Y i ω ^ 2) P)
    {Mp B t : ℝ} (hMpdef : Mp = ∑ i, ∫ ω, |Y i ω| ^ p ∂P)
    (hB : 0 < B) (hB2 : B ^ 2 = ∑ i, ∫ ω, Y i ω ^ 2 ∂P) (ht : 0 < t) :
    P {ω | t ≤ ∑ i, Y i ω}
      ≤ ENNReal.ofReal (fukNagaevConst p * Mp / t ^ p
          + 2 * Real.exp (-(fukNagaevExp p) * t ^ 2 / B ^ 2)) := by
  refine le_trans (measure_mono ?_)
    (fukNagaev_bound P Y hindep hint hmean hp hpint hsq hMpdef hB hB2 ht)
  intro ω hω
  simp only [Set.mem_setOf_eq] at hω ⊢
  exact le_trans hω (le_abs_self _)

/-- The Fuk-Nagaev inequality when the total variance is only bounded above. -/
theorem fukNagaev_bound_var_le {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι] (P : Measure Ω)
    [IsProbabilityMeasure P] (Y : ι → Ω → ℝ) (hindep : iIndepFun Y P)
    (hint : ∀ i, Integrable (Y i) P) (hmean : ∀ i, ∫ ω, Y i ω ∂P = 0)
    {p : ℝ} (hp : 2 ≤ p) (hpint : ∀ i, Integrable (fun ω => |Y i ω| ^ p) P)
    (hsq : ∀ i, Integrable (fun ω => Y i ω ^ 2) P)
    {Mp V t : ℝ} (hMpdef : Mp = ∑ i, ∫ ω, |Y i ω| ^ p ∂P)
    (hVar : ∑ i, ∫ ω, Y i ω ^ 2 ∂P ≤ V) (ht : 0 < t) :
    P {ω | t ≤ |∑ i, Y i ω|}
      ≤ ENNReal.ofReal (fukNagaevConst p * Mp / t ^ p
          + 2 * Real.exp (-(fukNagaevExp p) * t ^ 2 / V)) := by
  classical
  have hnn : ∀ i : ι, 0 ≤ ∫ ω, Y i ω ^ 2 ∂P := fun i => integral_nonneg fun ω => sq_nonneg _
  rcases eq_or_lt_of_le (Finset.sum_nonneg fun i (_ : i ∈ Finset.univ) => hnn i) with hzero | hpos
  · have hae : ∀ i : ι, ∀ᵐ ω ∂P, Y i ω = 0 := by
      intro i
      have hz : ∫ ω, Y i ω ^ 2 ∂P = 0 :=
        (Finset.sum_eq_zero_iff_of_nonneg (fun j (_ : j ∈ Finset.univ) => hnn j)).mp hzero.symm i
          (Finset.mem_univ i)
      have h0 : (fun ω => Y i ω ^ 2) =ᵐ[P] 0 :=
        (integral_eq_zero_iff_of_nonneg (fun ω => sq_nonneg _) (hsq i)).mp hz
      filter_upwards [h0] with ω hω
      exact sq_eq_zero_iff.mp hω
    rw [measure_abs_sum_ge_eq_zero P Y hae ht]
    simp
  · set B : ℝ := Real.sqrt (∑ i, ∫ ω, Y i ω ^ 2 ∂P) with hBdef
    have hBpos : 0 < B := Real.sqrt_pos.mpr hpos
    have hB2 : B ^ 2 = ∑ i, ∫ ω, Y i ω ^ 2 ∂P := Real.sq_sqrt hpos.le
    have hmain := fukNagaev_bound P Y hindep hint hmean hp hpint hsq hMpdef hBpos hB2 ht
    refine hmain.trans (ENNReal.ofReal_le_ofReal ?_)
    have hle : B ^ 2 ≤ V := by rw [hB2]; exact hVar
    have hB2pos : (0:ℝ) < B ^ 2 := by positivity
    have hexp : Real.exp (-(fukNagaevExp p) * t ^ 2 / B ^ 2)
        ≤ Real.exp (-(fukNagaevExp p) * t ^ 2 / V) := by
      refine Real.exp_le_exp.mpr ?_
      have hc : 0 < fukNagaevExp p := fukNagaevExp_pos hp
      have hnum : (0:ℝ) ≤ fukNagaevExp p * t ^ 2 := by positivity
      have h1 : (fukNagaevExp p * t ^ 2) / V ≤ (fukNagaevExp p * t ^ 2) / B ^ 2 :=
        div_le_div_of_nonneg_left hnum hB2pos hle
      have h2 : -(fukNagaevExp p) * t ^ 2 / B ^ 2 = -((fukNagaevExp p * t ^ 2) / B ^ 2) := by
        ring
      have h3 : -(fukNagaevExp p) * t ^ 2 / V = -((fukNagaevExp p * t ^ 2) / V) := by
        ring
      rw [h2, h3]
      linarith
    linarith

/-- The Fuk-Nagaev inequality packaged with the constants existentially quantified and the
`p`-th moments given by lower integrals, the form in which it is quoted. -/
theorem fukNagaev_tail :
    ∀ p : ℝ, 2 ≤ p → ∃ c Cp : ℝ, 0 < c ∧ 0 < Cp ∧
      ∀ {Ω ι : Type} [MeasurableSpace Ω] [Fintype ι] (P : Measure Ω), IsProbabilityMeasure P →
        ∀ (Y : ι → Ω → ℝ), iIndepFun Y P → (∀ i, Integrable (Y i) P) →
        (∀ i, ∫ ω, Y i ω ∂P = 0) →
        ∀ Mp B : ℝ, Mp = ∑ i, (∫⁻ ω, ENNReal.ofReal (|Y i ω| ^ p) ∂P).toReal →
          (∀ i, (∫⁻ ω, ENNReal.ofReal (|Y i ω| ^ p) ∂P) ≠ ⊤) →
          0 < B → B ^ 2 = ∑ i, ∫ ω, Y i ω ^ 2 ∂P → (∀ i, Integrable (fun ω => Y i ω ^ 2) P) →
          ∀ t : ℝ, 0 < t →
            P {ω | t ≤ |∑ i, Y i ω|}
              ≤ ENNReal.ofReal (Cp * Mp / t ^ p + 2 * Real.exp (-c * t ^ 2 / B ^ 2)) := by
  intro p hp
  refine ⟨fukNagaevExp p, fukNagaevConst p, fukNagaevExp_pos hp, fukNagaevConst_pos hp, ?_⟩
  intro Ω ι _ _ P hP Y hindep hint hmean Mp B hMp hfin hB hB2 hsq t ht
  haveI := hP
  have hbr : ∀ i, Integrable (fun ω => |Y i ω| ^ p) P ∧
      (∫⁻ ω, ENNReal.ofReal (|Y i ω| ^ p) ∂P).toReal = ∫ ω, |Y i ω| ^ p ∂P :=
    fun i => integrable_abs_rpow_of_lintegral P (hint i).aestronglyMeasurable (hfin i)
  have hMp' : Mp = ∑ i, ∫ ω, |Y i ω| ^ p ∂P := by
    rw [hMp]
    exact Finset.sum_congr rfl fun i _ => (hbr i).2
  exact fukNagaev_bound P Y hindep hint hmean hp (fun i => (hbr i).1) hsq hMp' hB hB2 ht

end LatticeProb
