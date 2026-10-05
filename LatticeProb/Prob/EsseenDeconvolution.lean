/-
# Esseen's smoothing inequality: the deconvolution step

Let `μ`, `γ` be probability measures on `ℝ` with distribution functions `F x = μ (Iic x)` and
`G x = γ (Iic x)`, put `Δ x = F x - G x`, and suppose `G` is `m`-Lipschitz.  If `k` is a
probability density with tail bound `∫_{|w| > h} k ≤ a / h`, and the smoothed difference
`x ↦ ∫ Δ (x - w) k w dw` is bounded by `B` everywhere, then
`sup |Δ| ≤ 2 B + 16 a m`.

This is the purely real-variable half of Esseen's smoothing inequality: no Fourier analysis and
no specific kernel are involved.  The proof takes `η = sup |Δ|`, a point `x₀` at which `|Δ|` is
within `κ` of `η`, and shifts by `h = η / (4 m)` in the direction of the deviation.  Since `F` is
nondecreasing and `G` is `m`-Lipschitz, `Δ` stays within `η / 2 - κ` of the extreme value on a
`h`-ball of the kernel, and the kernel's tail beyond `h` is controlled by `a / h`.

* `LatticeProb.integral_mul_ge_of_bound_on_ball` — the kernel-splitting estimate.
* `LatticeProb.abs_le_of_smoothed_abstract` — the deconvolution step for an abstract `Δ`.
* `LatticeProb.measure_Iic_toReal_mono`, `LatticeProb.abs_cdf_sub_le_one` — elementary
  properties of distribution functions.
* `LatticeProb.sup_cdf_sub_le_of_smoothed` — the deconvolution step for distribution functions.
-/
import Mathlib

open MeasureTheory

namespace LatticeProb

/-- The distribution function `x ↦ (μ (Iic x)).toReal` of a probability measure is
nondecreasing. -/
theorem measure_Iic_toReal_mono (μ : Measure ℝ) [IsProbabilityMeasure μ] :
    Monotone fun x : ℝ => (μ (Set.Iic x)).toReal := by
  intro x y hxy
  exact ENNReal.toReal_mono (measure_ne_top μ _) (measure_mono (Set.Iic_subset_Iic.mpr hxy))

/-- The values of the distribution function `x ↦ (μ (Iic x)).toReal` of a probability measure
lie in `[0, 1]`. -/
theorem measure_Iic_toReal_mem_Icc (μ : Measure ℝ) [IsProbabilityMeasure μ] (x : ℝ) :
    0 ≤ (μ (Set.Iic x)).toReal ∧ (μ (Set.Iic x)).toReal ≤ 1 := by
  refine ⟨ENNReal.toReal_nonneg, ?_⟩
  have h : μ (Set.Iic x) ≤ 1 := prob_le_one
  simpa using ENNReal.toReal_mono ENNReal.one_ne_top h

/-- The difference of the distribution functions of two probability measures is bounded by `1`
in absolute value. -/
theorem abs_cdf_sub_le_one (μ γ : Measure ℝ) [IsProbabilityMeasure μ] [IsProbabilityMeasure γ]
    (x : ℝ) : |(μ (Set.Iic x)).toReal - (γ (Set.Iic x)).toReal| ≤ 1 := by
  obtain ⟨h1, h2⟩ := measure_Iic_toReal_mem_Icc μ x
  obtain ⟨h3, h4⟩ := measure_Iic_toReal_mem_Icc γ x
  rw [abs_le]
  constructor <;> linarith

/-- **Kernel splitting.**  Let `k` be a probability density, `S = {w | h < |w|}` and
`τ = ∫_S k`.  If `-η ≤ f` everywhere and `c ≤ f` on `{|w| ≤ h}`, then
`∫ f k ≥ c (1 - τ) - η τ`. -/
theorem integral_mul_ge_of_bound_on_ball
    {k : ℝ → ℝ} (hk0 : ∀ w, 0 ≤ k w) (hk1 : Integrable k) (hk : ∫ w, k w = 1)
    {f : ℝ → ℝ} (hfk : Integrable (fun w => f w * k w))
    {η c h : ℝ} (hη : ∀ w, -η ≤ f w) (hc : ∀ w, |w| ≤ h → c ≤ f w) :
    c * (1 - ∫ w in {w : ℝ | h < |w|}, k w) - η * ∫ w in {w : ℝ | h < |w|}, k w ≤
      ∫ w, f w * k w := by
  have hS : MeasurableSet {w : ℝ | h < |w|} := measurableSet_lt measurable_const measurable_abs
  have hsplit_k := integral_add_compl hS hk1
  have hsplit_f := integral_add_compl hS hfk
  rw [hk] at hsplit_k
  -- the part over the tail
  have htail : -η * ∫ w in {w : ℝ | h < |w|}, k w ≤ ∫ w in {w : ℝ | h < |w|}, f w * k w := by
    rw [← integral_const_mul]
    refine setIntegral_mono_on (hk1.const_mul (-η)).integrableOn hfk.integrableOn hS ?_
    intro w _
    exact mul_le_mul_of_nonneg_right (hη w) (hk0 w)
  -- the part over the ball
  have hball : c * ∫ w in ({w : ℝ | h < |w|})ᶜ, k w ≤
      ∫ w in ({w : ℝ | h < |w|})ᶜ, f w * k w := by
    rw [← integral_const_mul]
    refine setIntegral_mono_on (hk1.const_mul c).integrableOn hfk.integrableOn hS.compl ?_
    intro w hw
    have hw' : |w| ≤ h := not_lt.mp hw
    exact mul_le_mul_of_nonneg_right (hc w hw') (hk0 w)
  have hcompl : ∫ w in ({w : ℝ | h < |w|})ᶜ, k w = 1 - ∫ w in {w : ℝ | h < |w|}, k w := by
    linarith
  rw [hcompl] at hball
  linarith

/-- **The deconvolution step, abstractly.**  Let `D` be a measurable bounded function which
increases by at most `m z` when its argument decreases by `z ≥ 0`, and decreases by at most `m z`
when its argument increases by `z ≥ 0` (a Lipschitz-perturbation-of-monotone property).  If `k` is
a probability density with tail bound `∫_{|w| > h} k ≤ a / h` and every smoothed value
`∫ D (x - w) k w dw` is bounded by `B` in absolute value, then `|D x| ≤ 2 B + 16 a m`. -/
theorem abs_le_of_smoothed_abstract
    {D : ℝ → ℝ} (hDm : Measurable D) {M : ℝ} (hDM : ∀ x, |D x| ≤ M)
    {m : ℝ} (hm : 0 < m)
    (hup : ∀ x z : ℝ, 0 ≤ z → D x - m * z ≤ D (x + z))
    (hdown : ∀ x z : ℝ, 0 ≤ z → D (x - z) ≤ D x + m * z)
    {k : ℝ → ℝ} (hk0 : ∀ w, 0 ≤ k w) (hk1 : Integrable k) (hk : ∫ w, k w = 1)
    {a : ℝ} (hka : ∀ h : ℝ, 0 < h → ∫ w in {w : ℝ | h < |w|}, k w ≤ a / h)
    {B : ℝ} (hB : ∀ x : ℝ, |∫ w, D (x - w) * k w| ≤ B) (x : ℝ) :
    |D x| ≤ 2 * B + 16 * a * m := by
  have hint : ∀ y : ℝ, Integrable (fun w => D (y - w) * k w) := by
    intro y
    refine hk1.bdd_mul (c := M) ?_ (Filter.Eventually.of_forall fun w => ?_)
    · exact (hDm.comp (measurable_const.sub measurable_id)).aestronglyMeasurable
    · simpa using hDM (y - w)
  have ha : 0 ≤ a := by
    have h1 := hka 1 one_pos
    have h2 : 0 ≤ ∫ w in {w : ℝ | 1 < |w|}, k w :=
      setIntegral_nonneg (measurableSet_lt measurable_const measurable_abs) fun w _ => hk0 w
    simpa using h2.trans h1
  have hB0 : 0 ≤ B := (abs_nonneg _).trans (hB 0)
  have hbdd : BddAbove (Set.range fun y => |D y|) := ⟨M, by rintro _ ⟨y, rfl⟩; exact hDM y⟩
  set η : ℝ := ⨆ y, |D y| with hη
  have hle : ∀ y, |D y| ≤ η := fun y => le_ciSup hbdd y
  have hη0 : 0 ≤ η := (abs_nonneg _).trans (hle 0)
  have key : η ≤ 2 * B + 16 * a * m := by
    rcases hη0.eq_or_lt with h0 | hpos
    · rw [← h0]; positivity
    have step : ∀ κ : ℝ, 0 < κ → η ≤ 2 * B + 16 * a * m + 2 * κ := by
      intro κ hκ
      obtain ⟨x₀, hx₀⟩ := exists_lt_of_lt_ciSup (show η - κ < ⨆ y, |D y| by linarith)
      set h : ℝ := η / (4 * m) with hh
      have hh0 : 0 < h := by positivity
      have hmh : m * h = η / 4 := by rw [hh]; field_simp
      set τ : ℝ := ∫ w in {w : ℝ | h < |w|}, k w with hτ
      have hτ0 : 0 ≤ τ :=
        setIntegral_nonneg (measurableSet_lt measurable_const measurable_abs) fun w _ => hk0 w
      have hτa : η * τ ≤ 4 * m * a := by
        have h1 : η * τ ≤ η * (a / h) := mul_le_mul_of_nonneg_left (hka h hh0) hη0
        have h2 : η * (a / h) = 4 * m * a := by rw [hh]; field_simp
        linarith
      have hpos' : 0 ≤ η / 2 + κ := by positivity
      have harith := mul_nonneg hτ0 hpos'
      rcases lt_abs.mp hx₀ with hx | hx
      · -- upper deviation: shift to the right by `h`
        have hc : ∀ w, |w| ≤ h → η / 2 - κ ≤ D (x₀ + h - w) := by
          intro w hw
          obtain ⟨hw1, hw2⟩ := abs_le.mp hw
          have e : x₀ + h - w = x₀ + (h - w) := by ring
          have h1 := hup x₀ (h - w) (by linarith)
          have h2 : m * (h - w) ≤ m * (2 * h) :=
            mul_le_mul_of_nonneg_left (by linarith) hm.le
          rw [e]
          linarith
        have hη' : ∀ w, -η ≤ D (x₀ + h - w) := fun w => (abs_le.mp (hle _)).1
        have h3 := integral_mul_ge_of_bound_on_ball hk0 hk1 hk (hint (x₀ + h)) hη' hc
        have h4 := (abs_le.mp (hB (x₀ + h))).2
        linarith
      · -- lower deviation: shift to the left by `h`
        have hc : ∀ w, |w| ≤ h → η / 2 - κ ≤ -D (x₀ - h - w) := by
          intro w hw
          obtain ⟨hw1, hw2⟩ := abs_le.mp hw
          have e : x₀ - h - w = x₀ - (h + w) := by ring
          have h1 := hdown x₀ (h + w) (by linarith)
          have h2 : m * (h + w) ≤ m * (2 * h) :=
            mul_le_mul_of_nonneg_left (by linarith) hm.le
          rw [e]
          linarith
        have hη' : ∀ w, -η ≤ -D (x₀ - h - w) := fun w => by
          linarith [(abs_le.mp (hle (x₀ - h - w))).2]
        have hfk : Integrable (fun w => -D (x₀ - h - w) * k w) := by
          simpa [neg_mul] using (hint (x₀ - h)).neg
        have h3 := integral_mul_ge_of_bound_on_ball hk0 hk1 hk hfk hη' hc
        simp only [neg_mul, integral_neg] at h3
        have h4 := (abs_le.mp (hB (x₀ - h))).1
        linarith
    exact le_of_forall_pos_le_add fun ε hε => by linarith [step (ε / 2) (half_pos hε)]
  exact (hle x).trans key

/-- **Esseen's deconvolution step.**  Let `μ`, `γ` be probability measures on `ℝ` whose
distribution functions satisfy: the one of `γ` is `m`-Lipschitz.  Let `k` be a probability
density with tail bound `∫_{|w| > h} k ≤ a / h` for every `h > 0`.  If the smoothed difference
`x ↦ ∫ (F - G) (x - w) k w dw` of the distribution functions `F`, `G` of `μ`, `γ` is bounded by
`B` in absolute value for every `x`, then `|F x - G x| ≤ 2 B + 16 a m` for every `x`. -/
theorem sup_cdf_sub_le_of_smoothed
    {μ γ : Measure ℝ} [IsProbabilityMeasure μ] [IsProbabilityMeasure γ] {m : ℝ} (hm : 0 < m)
    (hG : ∀ x y : ℝ, |(γ (Set.Iic x)).toReal - (γ (Set.Iic y)).toReal| ≤ m * |x - y|)
    {k : ℝ → ℝ} (hk0 : ∀ w, 0 ≤ k w) (hk1 : Integrable k) (hk : ∫ w, k w = 1)
    {a : ℝ} (hka : ∀ h : ℝ, 0 < h → ∫ w in {w : ℝ | h < |w|}, k w ≤ a / h)
    {B : ℝ}
    (hB : ∀ x : ℝ, |∫ w, ((μ (Set.Iic (x - w))).toReal - (γ (Set.Iic (x - w))).toReal) * k w| ≤ B)
    (x : ℝ) :
    |(μ (Set.Iic x)).toReal - (γ (Set.Iic x)).toReal| ≤ 2 * B + 16 * a * m := by
  refine abs_le_of_smoothed_abstract
    (D := fun y => (μ (Set.Iic y)).toReal - (γ (Set.Iic y)).toReal)
    ((measure_Iic_toReal_mono μ).measurable.sub (measure_Iic_toReal_mono γ).measurable)
    (M := 1) (abs_cdf_sub_le_one μ γ) hm ?_ ?_ hk0 hk1 hk hka hB x
  · intro y z hz
    have h1 : (μ (Set.Iic y)).toReal ≤ (μ (Set.Iic (y + z))).toReal :=
      measure_Iic_toReal_mono μ (by linarith)
    have h2 := (abs_le.mp (hG (y + z) y)).2
    rw [add_sub_cancel_left, abs_of_nonneg hz] at h2
    show (μ (Set.Iic y)).toReal - (γ (Set.Iic y)).toReal - m * z ≤
      (μ (Set.Iic (y + z))).toReal - (γ (Set.Iic (y + z))).toReal
    linarith
  · intro y z hz
    have h1 : (μ (Set.Iic (y - z))).toReal ≤ (μ (Set.Iic y)).toReal :=
      measure_Iic_toReal_mono μ (by linarith)
    have h2 := (abs_le.mp (hG y (y - z))).2
    rw [sub_sub_cancel, abs_of_nonneg hz] at h2
    show (μ (Set.Iic (y - z))).toReal - (γ (Set.Iic (y - z))).toReal ≤
      (μ (Set.Iic y)).toReal - (γ (Set.Iic y)).toReal + m * z
    linarith

end LatticeProb
