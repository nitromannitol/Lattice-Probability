import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.MeasureTheory.Integral.Layercake
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Analysis.Convex.Jensen
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.MeasureTheory.Measure.MeasureSpace

/-!+# Stretched-exponential stochastic bounds

The stochastic notation controls the strict upper tail of the positive part at every
threshold at least one. Nonnegative constants satisfy this bound, which is preserved
by decreasing the exponent or increasing the scale and the random variable's upper bound.
-/

namespace LatticeProb

open MeasureTheory

variable {Ω : Type*} [MeasurableSpace Ω]

/-- `X ≤ 𝒪_s(θ)`: for every `t ≥ 1`, `P[max(X, 0) > tθ] ≤ exp(-t^s)`. -/
def OsBound {Ω : Type*} [MeasurableSpace Ω] (P : MeasureTheory.Measure Ω) (s θ : ℝ)
    (X : Ω → ℝ) : Prop :=
  ∀ t : ℝ, 1 ≤ t → P {ω | t * θ < max (X ω) 0} ≤ ENNReal.ofReal (Real.exp (-(t ^ s)))

/-- A nonnegative constant satisfies the stochastic bound at its own scale. -/
theorem osBound_const (P : Measure Ω) (s A : ℝ) (hA : 0 ≤ A) :
    OsBound P s A (fun _ => A) := by
  intro t ht
  have hthreshold : A ≤ t * A := by
    simpa only [one_mul] using mul_le_mul_of_nonneg_right ht hA
  have hempty : {ω : Ω | t * A < max A 0} = ∅ := by
    apply Set.eq_empty_iff_forall_notMem.mpr
    intro ω
    simpa only [Set.mem_setOf_eq, max_eq_left hA] using not_lt_of_ge hthreshold
  rw [hempty, measure_empty]
  exact bot_le

/-- A stochastic bound with a larger exponent implies the bound with a smaller exponent. -/
theorem OsBound.of_exponent_le {P : Measure Ω} {s s' θ : ℝ} {X : Ω → ℝ}
    (hss' : s ≤ s') (hX : OsBound P s' θ X) : OsBound P s θ X := by
  intro t ht
  exact (hX t ht).trans (ENNReal.ofReal_le_ofReal (Real.exp_le_exp.mpr
    (neg_le_neg (Real.rpow_le_rpow_of_exponent_le ht hss'))))

/-- Increasing a nonnegative scale and decreasing the variable preserves the bound. -/
theorem OsBound.mono {P : Measure Ω} {s θ θ' : ℝ} {X Y : Ω → ℝ}
    (hθθ' : θ ≤ θ') (hθ : 0 ≤ θ) (hXY : ∀ ω, X ω ≤ Y ω)
    (hY : OsBound P s θ Y) : OsBound P s θ' X := by
  intro t ht
  have ht0 : 0 ≤ t := zero_le_one.trans ht
  have hscale : t * θ ≤ t * θ' := mul_le_mul_of_nonneg_left hθθ' ht0
  apply le_trans (measure_mono (show {ω | t * θ' < max (X ω) 0} ⊆
    {ω | t * θ < max (Y ω) 0} from ?_)) (hY t ht)
  intro ω hω
  change t * θ' < max (X ω) 0 at hω
  rcases lt_max_iff.mp hω with hX | hzero
  · exact lt_of_le_of_lt hscale (hX.trans_le ((hXY ω).trans (le_max_left _ _)))
  · exact (not_lt_of_ge ((mul_nonneg ht0 hθ).trans hscale) hzero).elim

/-- A Gaussian two-sided tail with positive deviation scale gives an O₂ bound
with the absolute constant `C₀ = 2`. -/
theorem osBound_abs_of_gaussian_tail {P : Measure Ω} {σ : ℝ} {X : Ω → ℝ}
    (hσ : 0 < σ)
    (hX : ∀ t > 0, P {ω | t ≤ |X ω|} ≤
      ENNReal.ofReal (2 * Real.exp (-t ^ 2 / (2 * σ ^ 2)))) :
    OsBound P 2 (2 * σ) (fun ω => |X ω|) := by
  intro t ht
  have ht0 : 0 < t := lt_of_lt_of_le zero_lt_one ht
  have hsq : 1 ≤ t ^ 2 := one_le_pow₀ ht
  have hexp : 2 ≤ Real.exp (t ^ 2) := by
    exact (by linarith : (2 : ℝ) ≤ t ^ 2 + 1).trans (Real.add_one_le_exp _)
  have hquot : -(t * (2 * σ)) ^ 2 / (2 * σ ^ 2) = -(t ^ 2) - t ^ 2 := by
    (field_simp; ring)
  calc
    P {ω | t * (2 * σ) < max |X ω| 0} ≤ P {ω | t * (2 * σ) ≤ |X ω|} := by
      apply measure_mono
      intro ω hω
      change t * (2 * σ) < max |X ω| 0 at hω
      exact le_of_lt (by simpa only [max_eq_left (abs_nonneg (X ω))] using hω)
    _ ≤ ENNReal.ofReal (2 * Real.exp (-(t * (2 * σ)) ^ 2 / (2 * σ ^ 2))) :=
      hX _ (by positivity)
    _ ≤ ENNReal.ofReal (Real.exp (-(t ^ (2 : ℝ)))) := by
      apply ENNReal.ofReal_le_ofReal
      rw [Real.rpow_two, hquot, Real.exp_sub, ← mul_div_assoc]
      exact (div_le_iff₀ (Real.exp_pos _)).mpr
        (by
          calc
            _ ≤ Real.exp (t ^ 2) * Real.exp (-(t ^ 2)) :=
              mul_le_mul_of_nonneg_right hexp (Real.exp_nonneg _)
            _ = _ := mul_comm _ _)

/-- Squaring a pointwise nonnegative O₂ variable gives an O₁ variable at the squared scale. -/
theorem OsBound.sq {P : Measure Ω} {θ : ℝ} {X : Ω → ℝ}
    (hX : OsBound P 2 θ X) (hθ : 0 ≤ θ) (hpos : ∀ ω, 0 ≤ X ω) :
    OsBound P 1 (θ ^ 2) (fun ω => X ω ^ 2) := by
  intro t ht
  have ht0 : 0 ≤ t := zero_le_one.trans ht
  have hsqrt : 1 ≤ Real.sqrt t := (Real.le_sqrt (by norm_num) ht0).mpr (by simpa)
  have htail := hX (Real.sqrt t) hsqrt
  rw [Real.rpow_two, Real.sq_sqrt ht0] at htail
  simpa only [Real.rpow_one] using le_trans (measure_mono (show
    {ω | t * θ ^ 2 < max (X ω ^ 2) 0} ⊆
      {ω | Real.sqrt t * θ < max (X ω) 0} from by
        intro ω hω
        simp only [Set.mem_setOf_eq, max_eq_left (sq_nonneg _)] at hω
        simp only [Set.mem_setOf_eq, max_eq_left (hpos ω)]
        by_contra hle
        have hsq := (sq_le_sq₀ (hpos ω)
          (mul_nonneg (Real.sqrt_nonneg t) hθ)).mpr (le_of_not_gt hle)
        rw [mul_pow, Real.sq_sqrt ht0] at hsq
        nlinarith)) htail

/-- Normalizing the positive part and raising to the tail exponent gives a unit O₁ bound. -/
theorem OsBound.normalized_rpow {P : Measure Ω} {s θ : ℝ} {X : Ω → ℝ}
    (hX : OsBound P s θ X) (hs : 0 < s) (hθ : 0 < θ) :
    OsBound P 1 1 (fun ω => (max (X ω) 0 / θ) ^ s) := by
  intro t ht
  have ht0 : 0 ≤ t := zero_le_one.trans ht
  have hroot : 1 ≤ t ^ s⁻¹ := Real.one_le_rpow ht (inv_nonneg.mpr hs.le)
  have hp := hX (t ^ s⁻¹) hroot
  rw [Real.rpow_inv_rpow ht0 hs.ne'] at hp
  simpa only [mul_one, Real.rpow_one] using le_trans (measure_mono (show
    {ω | t * 1 < max ((max (X ω) 0 / θ) ^ s) 0} ⊆
      {ω | t ^ s⁻¹ * θ < max (X ω) 0} from by
        intro ω hω
        have hy : 0 ≤ max (X ω) 0 / θ := div_nonneg (le_max_right _ _) hθ.le
        simp only [Set.mem_setOf_eq, mul_one, max_eq_left (Real.rpow_nonneg hy s)] at hω
        change t ^ s⁻¹ * θ < max (X ω) 0
        by_contra hnot
        have hle : max (X ω) 0 / θ ≤ t ^ s⁻¹ :=
          (div_le_iff₀ hθ).mpr (le_of_not_gt hnot)
        have hp_le := Real.rpow_le_rpow hy hle hs.le
        rw [Real.rpow_inv_rpow ht0 hs.ne'] at hp_le
        exact (not_lt_of_ge hp_le hω))) hp

/-- A nonnegative variable with a unit O₁ tail has a uniformly bounded half-exponential moment. -/
theorem OsBound.lintegral_exp_half {P : Measure Ω} [IsProbabilityMeasure P]
    {Y : Ω → ℝ} (hY : OsBound P 1 1 Y) (hm : Measurable Y) (hn : ∀ ω, 0 ≤ Y ω) :
    ∫⁻ ω, ENNReal.ofReal (Real.exp (Y ω / 2)) ∂P ≤ ENNReal.ofReal (Real.exp 2) := by
  have htail (t : ℝ) : P {ω | t < Y ω} ≤ ENNReal.ofReal (Real.exp (1 - t)) := by
    by_cases ht : 1 ≤ t
    · have hevent : {ω | t < Y ω} = {ω | t * 1 < max (Y ω) 0} := by
        simp only [mul_one, max_eq_left (hn _)]
      rw [hevent]
      exact (hY t ht).trans (ENNReal.ofReal_le_ofReal
        (Real.exp_le_exp.mpr (by rw [Real.rpow_one]; linarith)))
    · exact (prob_le_one).trans (by
        simpa only [ENNReal.ofReal_one] using
          ENNReal.ofReal_le_ofReal (Real.one_le_exp (by linarith : 0 ≤ 1 - t)))
  have hprimitive (x : ℝ) :
      (∫ t in (0 : ℝ)..x, Real.exp (t / 2) / 2) = Real.exp (x / 2) - 1 := by
    have hd (t : ℝ) : HasDerivAt (fun t : ℝ => Real.exp (t / 2))
        (Real.exp (t / 2) / 2) t := by
      convert ((hasDerivAt_id t).div_const 2).exp using 1 <;> simp [div_eq_mul_inv]
    simpa only [zero_div, Real.exp_zero] using
      intervalIntegral.integral_eq_sub_of_hasDerivAt (a := 0) (b := x)
        (fun t _ => hd t)
        (Continuous.intervalIntegrable (by fun_prop) _ _)
  have hlayer := lintegral_comp_eq_lintegral_meas_lt_mul P
    (ae_of_all P hn) hm.aemeasurable
    (g := fun t : ℝ => Real.exp (t / 2) / 2)
    (fun t _ => Continuous.intervalIntegrable (by fun_prop) _ _)
    (ae_of_all _ fun _ => by positivity)
  simp_rw [hprimitive] at hlayer
  have hbound : (∫⁻ ω, ENNReal.ofReal (Real.exp (Y ω / 2) - 1) ∂P) ≤
      ENNReal.ofReal (Real.exp 1) := by
    rw [hlayer]
    calc
      _ ≤ ∫⁻ t in Set.Ioi (0 : ℝ),
          ENNReal.ofReal (Real.exp 1 / 2 * Real.exp (-(1 / 2 : ℝ) * t)) := by
        apply lintegral_mono
        intro t
        calc
          _ ≤ ENNReal.ofReal (Real.exp (1 - t)) *
              ENNReal.ofReal (Real.exp (t / 2) / 2) :=
            mul_le_mul_left (htail t) _
          _ = _ := by
            rw [← ENNReal.ofReal_mul (Real.exp_nonneg _)]
            congr 1
            rw [← mul_div_assoc, ← Real.exp_add]
            rw [show 1 - t + t / 2 = 1 + -(1 / 2 : ℝ) * t by ring,
              Real.exp_add]
            ring
      _ = ENNReal.ofReal (Real.exp 1) := by
        rw [← ofReal_integral_eq_lintegral_ofReal
          ((integrableOn_exp_mul_Ioi (by norm_num : -(1 / 2 : ℝ) < 0) 0).const_mul _)
          (ae_of_all _ fun _ => by positivity), integral_const_mul,
          integral_exp_mul_Ioi (by norm_num : -(1 / 2 : ℝ) < 0)]
        congr 1
        simp
  have heq (ω : Ω) : ENNReal.ofReal (Real.exp (Y ω / 2)) =
      ENNReal.ofReal (Real.exp (Y ω / 2) - 1) + 1 := by
    rw [← ENNReal.ofReal_one, ← ENNReal.ofReal_add
      (sub_nonneg.mpr (Real.one_le_exp (div_nonneg (hn ω) (by norm_num))))
      (by norm_num), sub_add_cancel]
  simp_rw [heq]
  rw [lintegral_add_right _ measurable_const, lintegral_const, measure_univ, mul_one]
  calc
    _ ≤ ENNReal.ofReal (Real.exp 1) + 1 := add_le_add hbound le_rfl
    _ ≤ ENNReal.ofReal (Real.exp 2) := by
      rw [← ENNReal.ofReal_one, ← ENNReal.ofReal_add (Real.exp_nonneg _) zero_le_one]
      apply ENNReal.ofReal_le_ofReal
      have he : 2 ≤ Real.exp 1 := by simpa only [one_add_one_eq_two] using Real.add_one_le_exp 1
      rw [show (2 : ℝ) = 1 + 1 by norm_num, Real.exp_add]
      nlinarith

/-- A power is bounded by a stretched exponential with a constant depending only on the powers. -/
theorem rpow_le_stretched_exp (s p : ℝ) (hs : 0 < s) (hp : 0 ≤ p) :
    ∃ A > 0, ∀ x : ℝ, 0 ≤ x → x ^ p ≤ A * Real.exp (x ^ s / 2) := by
  let n : ℕ := ⌈p / s⌉₊
  let B : ℝ := 2 ^ n * (n.factorial : ℝ)
  have hB : 0 < B := mul_pos (pow_pos (by norm_num) _)
    (by exact_mod_cast Nat.factorial_pos n)
  refine ⟨B + 1, by positivity, fun x hx => ?_⟩
  have hy : 0 ≤ x ^ s := Real.rpow_nonneg hx _
  have he : 1 ≤ Real.exp (x ^ s / 2) := Real.one_le_exp (by positivity)
  by_cases hx1 : 1 ≤ x
  · have hexponent : p ≤ s * (n : ℝ) := by
      have hn : p / s ≤ (n : ℝ) := Nat.le_ceil _
      exact (div_le_iff₀ hs).mp hn |>.trans_eq (mul_comm _ _)
    have hpow := Real.rpow_le_rpow_of_exponent_le hx1 hexponent
    rw [Real.rpow_mul hx, Real.rpow_natCast] at hpow
    have hseries := Real.pow_div_factorial_le_exp (x ^ s / 2) (div_nonneg hy (by norm_num)) n
    have hfact : (0 : ℝ) < n.factorial := by exact_mod_cast Nat.factorial_pos n
    have hseries' : (x ^ s) ^ n ≤ B * Real.exp (x ^ s / 2) := by
      have hm := (div_le_iff₀ hfact).mp hseries
      rw [div_pow] at hm
      have hm' := (div_le_iff₀ (pow_pos (by norm_num : (0 : ℝ) < 2) n)).mp hm
      calc
        _ ≤ (Real.exp (x ^ s / 2) * n.factorial) * 2 ^ n := hm'
        _ = _ := by dsimp [B]; ring
    exact hpow.trans (hseries'.trans (mul_le_mul_of_nonneg_right
      (le_add_of_nonneg_right zero_le_one) (Real.exp_nonneg _)))
  · have hsmall : x ^ p ≤ 1 := Real.rpow_le_one hx (le_of_not_ge hx1) hp
    exact hsmall.trans (one_le_mul_of_one_le_of_one_le (by dsimp [B]; linarith) he)

/-- Every nonnegative Oₛ variable has uniformly bounded moments.
The constant is selected before the probability measure, scale and random variable. -/
theorem osBound_moment (s p : ℝ) (hs : 0 < s) (hp : 1 ≤ p) :
    ∃ C > 0, ∀ {Ω : Type*} [MeasurableSpace Ω]
      (P : Measure Ω) [IsProbabilityMeasure P] (θ : ℝ) (X : Ω → ℝ),
      0 < θ → Measurable X → (∀ ω, 0 ≤ X ω) → OsBound P s θ X →
      ∫⁻ ω, ENNReal.ofReal (X ω ^ p) ∂P ≤ ENNReal.ofReal (C * θ ^ p) := by
  obtain ⟨A, hA, hpower⟩ := rpow_le_stretched_exp s p hs (zero_le_one.trans hp)
  refine ⟨A * Real.exp 2, mul_pos hA (Real.exp_pos _), ?_⟩
  intro Ω _ P _ θ X hθ hm hn hX
  have hnorm := hX.normalized_rpow hs hθ
  have hmnorm : Measurable (fun ω => (max (X ω) 0 / θ) ^ s) := by fun_prop
  have hnnorm (ω : Ω) : 0 ≤ (max (X ω) 0 / θ) ^ s :=
    Real.rpow_nonneg (div_nonneg (le_max_right _ _) hθ.le) s
  have he := hnorm.lintegral_exp_half hmnorm hnnorm
  have hscale (ω : Ω) : X ω ^ p = θ ^ p * (X ω / θ) ^ p := by
    rw [Real.div_rpow (hn ω) hθ.le]
    field_simp [ne_of_gt (Real.rpow_pos_of_pos hθ p)]
  calc
    _ ≤ ∫⁻ ω, ENNReal.ofReal (θ ^ p * A) *
        ENNReal.ofReal (Real.exp ((max (X ω) 0 / θ) ^ s / 2)) ∂P := by
      apply lintegral_mono
      intro ω
      dsimp only
      rw [← ENNReal.ofReal_mul (mul_nonneg (Real.rpow_nonneg hθ.le _) hA.le)]
      apply ENNReal.ofReal_le_ofReal
      rw [hscale, max_eq_left (hn ω), mul_assoc]
      exact mul_le_mul_of_nonneg_left (hpower _ (div_nonneg (hn ω) hθ.le))
        (Real.rpow_nonneg hθ.le _)
    _ = ENNReal.ofReal (θ ^ p * A) *
        ∫⁻ ω, ENNReal.ofReal (Real.exp ((max (X ω) 0 / θ) ^ s / 2)) ∂P :=
      lintegral_const_mul _ (by fun_prop)
    _ ≤ ENNReal.ofReal (θ ^ p * A) * ENNReal.ofReal (Real.exp 2) :=
      mul_le_mul_right he _
    _ = ENNReal.ofReal (A * Real.exp 2 * θ ^ p) := by
      rw [← ENNReal.ofReal_mul (mul_nonneg (Real.rpow_nonneg hθ.le _) hA.le)]
      congr 1
      ring

end LatticeProb
