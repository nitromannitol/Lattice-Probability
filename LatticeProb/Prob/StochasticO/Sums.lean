import LatticeProb.Prob.StochasticO
import Mathlib.MeasureTheory.Integral.Lebesgue.Markov

/-!
# Finite sums of stretched-exponential variables

Half-exponential moments and finite Jensen's inequality give a sum bound with a constant
independent of the number of summands. Zero scales force nonpositive summands almost everywhere.
-/

namespace LatticeProb

open MeasureTheory

variable {Ω : Type*} [MeasurableSpace Ω]

/-- A zero-scale stochastic bound with exponent at least one forces nonpositivity a.e. -/
theorem OsBound.ae_nonpos_of_scale_zero {P : Measure Ω} {s : ℝ} {X : Ω → ℝ}
    (hX : OsBound P s 0 X) (hs : 1 ≤ s) : ∀ᵐ ω ∂P, X ω ≤ 0 := by
  have hunit := hX.of_exponent_le hs
  have htend : Filter.Tendsto (fun t : ℝ => ENNReal.ofReal (Real.exp (-t)))
      Filter.atTop (nhds 0) := by
    simpa only [ENNReal.ofReal_zero, Function.comp_apply] using
      ENNReal.tendsto_ofReal (Real.tendsto_exp_atBot.comp Filter.tendsto_neg_atTop_atBot)
  have hzero : P {ω | 0 < X ω} ≤ 0 := by
    apply ge_of_tendsto htend
    filter_upwards [Filter.eventually_ge_atTop (1 : ℝ)] with t ht
    simpa only [mul_zero, Real.rpow_one, lt_max_iff, lt_self_iff_false, or_false] using
      hunit t ht
  rw [ae_iff]
  simpa only [not_le] using le_antisymm hzero bot_le

/-- A half-exponential moment bounded by `exp 2` gives a stochastic bound
at the explicit scale `6 ^ (s⁻¹)`. -/
theorem osBound_of_lintegral_exp_half {P : Measure Ω} {s : ℝ} {Y : Ω → ℝ}
    (hs : 0 < s) (hm : Measurable Y) (hn : ∀ ω, 0 ≤ Y ω)
    (he : ∫⁻ ω, ENNReal.ofReal (Real.exp (Y ω ^ s / 2)) ∂P ≤
      ENNReal.ofReal (Real.exp 2)) : OsBound P s (6 ^ s⁻¹) Y := by
  intro t ht
  have ht0 : 0 ≤ t := zero_le_one.trans ht
  have htp : 1 ≤ t ^ s := Real.one_le_rpow ht hs.le
  have hC : 0 ≤ (6 : ℝ) ^ s⁻¹ := Real.rpow_nonneg (by norm_num) _
  have hmark := meas_le_lintegral₀ (μ := P)
    (f := fun ω => ENNReal.ofReal (Real.exp (-(3 * t ^ s))) *
      ENNReal.ofReal (Real.exp (Y ω ^ s / 2)))
    (by fun_prop) (s := {ω | t * 6 ^ s⁻¹ < max (Y ω) 0}) (by
      intro ω hω
      change t * 6 ^ s⁻¹ < max (Y ω) 0 at hω
      rw [max_eq_left (hn ω)] at hω
      have hp := Real.rpow_le_rpow (mul_nonneg ht0 hC) hω.le hs.le
      rw [Real.mul_rpow ht0 hC, Real.rpow_inv_rpow (by norm_num) hs.ne'] at hp
      rw [← ENNReal.ofReal_mul (Real.exp_nonneg _), ← Real.exp_add]
      simpa only [ENNReal.ofReal_one] using ENNReal.ofReal_le_ofReal
        (Real.one_le_exp (by linarith : 0 ≤ -(3 * t ^ s) + Y ω ^ s / 2)))
  calc
    _ ≤ _ := hmark
    _ = ENNReal.ofReal (Real.exp (-(3 * t ^ s))) *
        ∫⁻ ω, ENNReal.ofReal (Real.exp (Y ω ^ s / 2)) ∂P :=
      lintegral_const_mul _ (by fun_prop)
    _ ≤ ENNReal.ofReal (Real.exp (-(3 * t ^ s))) * ENNReal.ofReal (Real.exp 2) :=
      mul_le_mul_right he _
    _ ≤ ENNReal.ofReal (Real.exp (-(t ^ s))) := by
      rw [← ENNReal.ofReal_mul (Real.exp_nonneg _), ← Real.exp_add]
      exact ENNReal.ofReal_le_ofReal (Real.exp_le_exp.mpr (by linarith))

/-- Finite sums of Oₛ variables, for `s ≥ 1`, have scale at most
`6 ^ (s⁻¹)` times the sum of the individual scales, independently of cardinality. -/
theorem osBound_sum (s : ℝ) (hs : 1 ≤ s) :
    ∃ C > 0, ∀ {Ω : Type*} [MeasurableSpace Ω]
      (P : Measure Ω) [IsProbabilityMeasure P] (ι : Type*) [Fintype ι]
      (X : ι → Ω → ℝ) (θ : ι → ℝ), (∀ i, Measurable (X i)) →
      (∀ i, 0 ≤ θ i) → (∀ i, OsBound P s (θ i) (X i)) →
      OsBound P s (C * ∑ i, θ i) (fun ω => ∑ i, X i ω) := by
  refine ⟨6 ^ s⁻¹, Real.rpow_pos_of_pos (by norm_num) _, ?_⟩
  intro Ω _ P _ ι _ X θ hm hθ hX
  classical
  have hs0 : 0 < s := zero_lt_one.trans_le hs
  let W := ∑ i, θ i
  have hW : 0 ≤ W := Finset.sum_nonneg (fun i _ => hθ i)
  have hzero : ∀ᵐ ω ∂P, ∀ i, θ i = 0 → X i ω ≤ 0 := by
    apply ae_all_iff.mpr
    intro i
    by_cases hi : θ i = 0
    · exact ((hi ▸ hX i).ae_nonpos_of_scale_zero hs).mono (fun _ hx _ => hx)
    · exact ae_of_all _ (fun _ hx => (hi hx).elim)
  by_cases hW0 : W = 0
  · have hall : ∀ i, θ i = 0 := fun i =>
      (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => hθ j)).mp hW0 i (Finset.mem_univ i)
    intro t _
    have hnot : ∀ᵐ ω ∂P,
        ¬t * (6 ^ s⁻¹ * ∑ i, θ i) < max (∑ i, X i ω) 0 := by
      filter_upwards [hzero] with ω hω
      have hsum : ∑ i, X i ω ≤ 0 := Finset.sum_nonpos (fun i _ => hω i (hall i))
      rw [max_eq_right hsum]
      change ¬t * (6 ^ s⁻¹ * W) < 0
      simp only [hW0, mul_zero, lt_self_iff_false, not_false_eq_true]
    have hnull : P {ω | t * (6 ^ s⁻¹ * ∑ i, θ i) < max (∑ i, X i ω) 0} = 0 := by
      simpa only [not_not] using ae_iff.mp hnot
    rw [hnull]
    exact bot_le
  have hWpos : 0 < W := lt_of_le_of_ne hW (Ne.symm hW0)
  let w (i : ι) := θ i / W
  let Z (i : ι) (ω : Ω) := max (X i ω) 0 / θ i
  let Y (ω : Ω) := ∑ i, w i * Z i ω
  have hw (i : ι) : 0 ≤ w i := div_nonneg (hθ i) hW
  have hw_sum : ∑ i, w i = 1 := by
    dsimp [w]
    rw [← Finset.sum_div, div_self hW0]
  have hZ (i : ι) (ω : Ω) : 0 ≤ Z i ω := div_nonneg (le_max_right _ _) (hθ i)
  have hY (ω : Ω) : 0 ≤ Y ω := Finset.sum_nonneg (fun i _ => mul_nonneg (hw i) (hZ i ω))
  have hmoment (i : ι) :
      ∫⁻ ω, ENNReal.ofReal (Real.exp (Z i ω ^ s / 2)) ∂P ≤
        ENNReal.ofReal (Real.exp 2) := by
    by_cases hi : θ i = 0
    · simp only [Z, hi, div_zero, Real.zero_rpow hs0.ne', zero_div, Real.exp_zero,
        ENNReal.ofReal_one, lintegral_const, one_mul, measure_univ]
      simpa only [ENNReal.ofReal_one] using
        ENNReal.ofReal_le_ofReal (Real.one_le_exp (by norm_num : (0 : ℝ) ≤ 2))
    · exact ((hX i).normalized_rpow hs0 (lt_of_le_of_ne (hθ i) (Ne.symm hi))).lintegral_exp_half
        (by fun_prop) (fun ω => Real.rpow_nonneg (hZ i ω) _)
  have hconv : ConvexOn ℝ (Set.Ici 0) (fun y : ℝ => Real.exp (y ^ s / 2)) := by
    refine ⟨convex_Ici 0, ?_⟩
    intro x hx y hy a b ha hb hab
    have hp := (convexOn_rpow hs).2 hx hy ha hb hab
    have he := convexOn_exp.2 (Set.mem_univ (x ^ s / 2))
      (Set.mem_univ (y ^ s / 2)) ha hb hab
    simp only [smul_eq_mul] at hp he ⊢
    apply le_trans (Real.exp_le_exp.mpr ?_) he
    linarith
  have hmomentY : ∫⁻ ω, ENNReal.ofReal (Real.exp (Y ω ^ s / 2)) ∂P ≤
      ENNReal.ofReal (Real.exp 2) := by
    calc
      _ ≤ ∫⁻ ω, ∑ i, ENNReal.ofReal (w i) *
          ENNReal.ofReal (Real.exp (Z i ω ^ s / 2)) ∂P := by
        apply lintegral_mono
        intro ω
        have hj := hconv.map_sum_le (t := Finset.univ) (fun i _ => hw i) hw_sum
          (fun i _ => hZ i ω)
        have hjreal : Real.exp (Y ω ^ s / 2) ≤
            ∑ i, w i * Real.exp (Z i ω ^ s / 2) := by
          simpa only [smul_eq_mul] using hj
        calc
          _ ≤ ENNReal.ofReal (∑ i, w i * Real.exp (Z i ω ^ s / 2)) :=
            ENNReal.ofReal_le_ofReal hjreal
          _ = _ := by
            rw [ENNReal.ofReal_sum_of_nonneg
              (fun i _ => mul_nonneg (hw i) (Real.exp_nonneg _))]
            apply Finset.sum_congr rfl
            intro i _
            exact ENNReal.ofReal_mul (hw i)
      _ = ∑ i, ENNReal.ofReal (w i) *
          ∫⁻ ω, ENNReal.ofReal (Real.exp (Z i ω ^ s / 2)) ∂P := by
        rw [lintegral_finsetSum _ (fun i _ => by fun_prop)]
        congr 1
        ext i
        exact lintegral_const_mul _ (by fun_prop)
      _ ≤ ∑ i, ENNReal.ofReal (w i) * ENNReal.ofReal (Real.exp 2) :=
        Finset.sum_le_sum (fun i _ => mul_le_mul_right (hmoment i) _)
      _ = ENNReal.ofReal (Real.exp 2) := by
        rw [← Finset.sum_mul, ← ENNReal.ofReal_sum_of_nonneg (fun i _ => hw i), hw_sum]
        simp only [ENNReal.ofReal_one, one_mul]
  have hbound := osBound_of_lintegral_exp_half hs0 (by fun_prop) hY hmomentY
  intro t ht
  apply le_trans (measure_mono_ae ?_) (hbound t ht)
  filter_upwards [hzero] with ω hω
  have hsum : ∑ i, X i ω ≤ W * Y ω := by
    dsimp [Y]
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro i _
    by_cases hi : θ i = 0
    · simpa only [w, hi, zero_div, zero_mul, mul_zero] using hω i hi
    · have heq : W * (w i * Z i ω) = max (X i ω) 0 := by
        dsimp [w, Z]
        field_simp [hW0, hi]
      rw [heq]
      exact le_max_left _ _
  intro hωtail
  change t * (6 ^ s⁻¹ * W) < max (∑ i, X i ω) 0 at hωtail
  change t * 6 ^ s⁻¹ < max (Y ω) 0
  rw [max_eq_left (hY ω)]
  have hmax := max_le hsum (mul_nonneg hW (hY ω))
  exact (mul_lt_mul_iff_right₀ hWpos).mp (by
    simpa only [mul_assoc, mul_comm W] using hωtail.trans_le hmax)

end LatticeProb
