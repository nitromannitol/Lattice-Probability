/-
# Multivariate Esseen deconvolution: the structural core

Route C1 of `scratch/pk/mvbe-route.md` (Raič's multivariate orthant smoothing with the `m^{1/4}`
factor) needs a multivariate analogue of Esseen's deconvolution step
`LatticeProb.sup_cdf_sub_le_of_smoothed` (`EsseenDeconvolution.lean`): if `G` — the orthant
distribution function of a target measure `γ` on `ℝ^m` — is Lipschitz, `k` is a probability
density with a tail bound, and the `k`-smoothed difference of the orthant distribution
functions is bounded by `B`, then the unsmoothed difference is at most `2B + 16 a m`.

The purely structural inputs of that step are independent of the kernel and of the Fourier
analysis, and they are what this file lands:

* `orthant_prob_mono` — the orthant probability is monotone in the threshold vector (the
  `Fin m`-dimensional analogue of `LatticeProb.measure_Iic_toReal_mono`);
* `abs_orthant_prob_sub_le_one` — the difference of two orthant probabilities is at most `1` (the
  analogue of `LatticeProb.abs_cdf_sub_le_one`);
* `abs_le_of_smoothed_abstract_pi` — the `Fin m`-dimensional deconvolution step, assembling the
  two inputs above into `|D x| ≤ 2B + 16 a L m`;
* `integral_mul_ge_of_bound_on_ball_pi` — the `Fin m`-dimensional kernel-splitting estimate (the
  analogue of `integral_mul_ge_of_bound_on_ball`), the second input of the deconvolution step;
* `orthant_cdf_shift_le` — the "Lipschitz-from-below" property of `D = F - G`: shifting the
  threshold up by a nonnegative vector `z` raises `D` by at least `-L ∑ j z_j` whenever `G` is
  `L`-Lipschitz in the coordinate-sum (`ℓ¹`) metric (the `Fin m`-dimensional analogue of the
  `hup`/`hdown` hypotheses of `LatticeProb.abs_le_of_smoothed_abstract`).

## The gap

With these, the multivariate deconvolution step is the remaining adaptation of
`abs_le_of_smoothed_abstract` and `integral_mul_ge_of_bound_on_ball` to `(Fin m → ℝ)`; the shift
`h · 1 - w` over the ball `‖w‖∞ ≤ h` has coordinate sum at most `2 m h`, so the `η/(4L)`
of the one-dimensional proof becomes `η/(4 L m)` and the conclusion carries the extra factor `m`
(`|D x| ≤ 2B + 16 a L m`), which is harmless for C1 because the `m^{1/4}` factor comes from the
smoothing-bandwidth optimisation, not from here.  The `m^{1/4}` Sazonov smoothing inequality itself
— the Gaussian-smoothed orthant kernel, its Fourier transform, and the balance producing `m^{1/4}`
— remains the research-level blocker (C1).
-/
import Mathlib

open MeasureTheory

namespace LatticeProb

/-- **The orthant probability is monotone in the threshold.**  The `Fin m`-dimensional analogue of
`measure_Iic_toReal_mono`. -/
theorem orthant_prob_mono {m : ℕ} (μ : Measure (Fin m → ℝ)) [IsProbabilityMeasure μ]
    {x y : Fin m → ℝ} (hxy : ∀ j, x j ≤ y j) :
    (μ {z : Fin m → ℝ | ∀ j, z j ≤ x j}).toReal ≤
      (μ {z : Fin m → ℝ | ∀ j, z j ≤ y j}).toReal := by
  refine ENNReal.toReal_mono (measure_ne_top μ _) (measure_mono ?_)
  intro z hz j
  exact le_trans (hz j) (hxy j)

/-- **The difference of two orthant probabilities is at most `1`.**  The `Fin m`-dimensional
analogue of `abs_cdf_sub_le_one`. -/
theorem abs_orthant_prob_sub_le_one {m : ℕ} (μ γ : Measure (Fin m → ℝ))
    [IsProbabilityMeasure μ] [IsProbabilityMeasure γ] (x : Fin m → ℝ) :
    |(μ {z : Fin m → ℝ | ∀ j, z j ≤ x j}).toReal -
        (γ {z : Fin m → ℝ | ∀ j, z j ≤ x j}).toReal| ≤ 1 := by
  have h1 : (μ {z : Fin m → ℝ | ∀ j, z j ≤ x j}).toReal ≤ 1 := by
    simpa using ENNReal.toReal_mono ENNReal.one_ne_top (prob_le_one (μ := μ))
  have h2 : (γ {z : Fin m → ℝ | ∀ j, z j ≤ x j}).toReal ≤ 1 := by
    simpa using ENNReal.toReal_mono ENNReal.one_ne_top (prob_le_one (μ := γ))
  have h3 : 0 ≤ (μ {z : Fin m → ℝ | ∀ j, z j ≤ x j}).toReal := ENNReal.toReal_nonneg
  have h4 : 0 ≤ (γ {z : Fin m → ℝ | ∀ j, z j ≤ x j}).toReal := ENNReal.toReal_nonneg
  rw [abs_le]
  exact ⟨by linarith, by linarith⟩

/-- **The `ℓ¹`-Lipschitz-from-below property of `D = F - G`.**  If the orthant distribution
function of `γ` is `L`-Lipschitz in the coordinate-sum metric,
`G (x + z) - G x ≤ L ∑ j z_j` for `z ≥ 0`, then shifting the threshold up by `z` raises
`D y = F y - G y` by at least `-L ∑ j z_j`.  This is the `Fin m`-dimensional analogue of the `hup`
hypothesis of `abs_le_of_smoothed_abstract`. -/
theorem orthant_cdf_shift_le {m : ℕ} {μ γ : Measure (Fin m → ℝ)}
    [IsProbabilityMeasure μ] [IsProbabilityMeasure γ] {L : ℝ}
    (hG : ∀ x z : Fin m → ℝ, (∀ j, 0 ≤ z j) →
      (γ {y : Fin m → ℝ | ∀ j, y j ≤ x j + z j}).toReal -
          (γ {y : Fin m → ℝ | ∀ j, y j ≤ x j}).toReal ≤ L * ∑ j, z j)
    (x z : Fin m → ℝ) (hz : ∀ j, 0 ≤ z j) :
    ((μ {y : Fin m → ℝ | ∀ j, y j ≤ x j}).toReal -
        (γ {y : Fin m → ℝ | ∀ j, y j ≤ x j}).toReal) - L * ∑ j, z j ≤
      (μ {y : Fin m → ℝ | ∀ j, y j ≤ x j + z j}).toReal -
        (γ {y : Fin m → ℝ | ∀ j, y j ≤ x j + z j}).toReal := by
  have h1 : (μ {y : Fin m → ℝ | ∀ j, y j ≤ x j}).toReal ≤
      (μ {y : Fin m → ℝ | ∀ j, y j ≤ x j + z j}).toReal :=
    orthant_prob_mono μ fun j => by linarith [hz j]
  have h2 := hG x z hz
  linarith

/-- **The m-dimensional kernel-splitting estimate.**  Let `k` be a probability density on
`Fin m → ℝ`, `S` the complement of the `ℓ∞` ball `{w | ∀ j, |w j| ≤ h}` and
`τ = ∫_S k`.  If `-η ≤ f` everywhere and `c ≤ f` on the ball, then
`c (1 - τ) - η τ ≤ ∫ f k`.  This is the `Fin m`-dimensional analogue of
`LatticeProb.integral_mul_ge_of_bound_on_ball`, and one of the two inputs of the multivariate
deconvolution step. -/
theorem integral_mul_ge_of_bound_on_ball_pi {m : ℕ} {k : (Fin m → ℝ) → ℝ}
    (hk0 : ∀ w, 0 ≤ k w)
    (hk1 : Integrable k) (hk : ∫ w, k w = 1) {f : (Fin m → ℝ) → ℝ}
    (hfk : Integrable (fun w => f w * k w))
    {η c h : ℝ} (hη : ∀ w, -η ≤ f w) (hc : ∀ w, (∀ j, |w j| ≤ h) → c ≤ f w) :
    c * (1 - ∫ w in {w : Fin m → ℝ | ∃ j, h < |w j|}, k w) -
        η * ∫ w in {w : Fin m → ℝ | ∃ j, h < |w j|}, k w ≤
      ∫ w, f w * k w := by
  have hS : MeasurableSet {w : Fin m → ℝ | ∃ j, h < |w j|} := by
    rw [show {w : Fin m → ℝ | ∃ j, h < |w j|} = ⋃ j, {w : Fin m → ℝ | h < |w j|} by
      ext w; simp]
    exact MeasurableSet.iUnion fun j =>
      measurableSet_lt (measurable_const : Measurable fun _ : Fin m → ℝ => h)
        (measurable_pi_apply j).abs
  have hsplit_k := integral_add_compl hS hk1
  have hsplit_f := integral_add_compl hS hfk
  rw [hk] at hsplit_k
  have htail : -η * ∫ w in {w : Fin m → ℝ | ∃ j, h < |w j|}, k w ≤
      ∫ w in {w : Fin m → ℝ | ∃ j, h < |w j|}, f w * k w := by
    rw [← integral_const_mul]
    refine setIntegral_mono_on (hk1.const_mul (-η)).integrableOn hfk.integrableOn hS ?_
    intro w _
    exact mul_le_mul_of_nonneg_right (hη w) (hk0 w)
  have hball : c * ∫ w in ({w : Fin m → ℝ | ∃ j, h < |w j|})ᶜ, k w ≤
      ∫ w in ({w : Fin m → ℝ | ∃ j, h < |w j|})ᶜ, f w * k w := by
    rw [← integral_const_mul]
    refine setIntegral_mono_on (hk1.const_mul c).integrableOn hfk.integrableOn hS.compl ?_
    intro w hw
    have hw' : ∀ j, |w j| ≤ h := by
      intro j
      by_contra hcon
      exact hw ⟨j, lt_of_not_ge hcon⟩
    exact mul_le_mul_of_nonneg_right (hc w hw') (hk0 w)
  have hcompl : ∫ w in ({w : Fin m → ℝ | ∃ j, h < |w j|})ᶜ, k w =
      1 - ∫ w in {w : Fin m → ℝ | ∃ j, h < |w j|}, k w := by linarith
  rw [hcompl] at hball
  linarith

/-- **The `Fin m`-dimensional deconvolution step.**  The multivariate analogue of
`LatticeProb.abs_le_of_smoothed_abstract`: for a bounded measurable `D` that is "Lipschitz from
below" in the pointwise order (`D x - L ∑ j z j ≤ D (x + z)` and
`D (x - z) ≤ D x + L ∑ j z j` for pointwise nonnegative `z`), a probability density `k` with
tail bound
`∫_{∃ j, h < |w j|} k ≤ a / h`, and a smoothed bound `|∫ D (x - w) k w| ≤ B`, one has
`|D x| ≤ 2B + 16 a L m` for every `x`.  The extra factor `m` (against the one-dimensional
`16 a m`) comes from the shift `h · 1 - w` over the `ℓ∞` ball, whose coordinate sum is at
most `2 m h`. -/
theorem abs_le_of_smoothed_abstract_pi {m : ℕ} (hm : 0 < m) {D : (Fin m → ℝ) → ℝ}
    (hDm : Measurable D) {M : ℝ} (hDM : ∀ x, |D x| ≤ M) {L : ℝ} (hL : 0 < L)
    (hup : ∀ x (z : Fin m → ℝ), (∀ j, 0 ≤ z j) → D x - L * ∑ j, z j ≤ D (x + z))
    (hdown : ∀ x (z : Fin m → ℝ), (∀ j, 0 ≤ z j) → D (x - z) ≤ D x + L * ∑ j, z j)
    {k : (Fin m → ℝ) → ℝ} (hk0 : ∀ w, 0 ≤ k w)
    (hk1 : Integrable k) (hk : ∫ w, k w = 1)
    {a : ℝ} (hka : ∀ h : ℝ, 0 < h →
      ∫ w in {w : Fin m → ℝ | ∃ j, h < |w j|}, k w ≤ a / h)
    {B : ℝ} (hB : ∀ x : Fin m → ℝ, |∫ w, D (x - w) * k w| ≤ B) (x : Fin m → ℝ) :
    |D x| ≤ 2 * B + 16 * a * L * m := by
  have hint : ∀ y : Fin m → ℝ, Integrable (fun w => D (y - w) * k w) := by
    intro y
    refine hk1.bdd_mul (c := M) ?_ (Filter.Eventually.of_forall fun w => ?_)
    · exact (hDm.comp (measurable_const.sub measurable_id)).aestronglyMeasurable
    · simpa using hDM (y - w)
  have ha : 0 ≤ a := by
    have h1 := hka 1 one_pos
    have h2 : 0 ≤ ∫ w in {w : Fin m → ℝ | ∃ j, (1 : ℝ) < |w j|}, k w := by
      refine setIntegral_nonneg ?_ fun w _ => hk0 w
      rw [show {w : Fin m → ℝ | ∃ j, (1 : ℝ) < |w j|}
          = ⋃ j, {w : Fin m → ℝ | (1 : ℝ) < |w j|} by ext w; simp]
      exact MeasurableSet.iUnion fun j =>
        measurableSet_lt (measurable_const : Measurable fun _ : Fin m → ℝ => (1 : ℝ))
          (measurable_pi_apply j).abs
    simpa using h2.trans h1
  have hB0 : 0 ≤ B := (abs_nonneg _).trans (hB 0)
  have hbdd : BddAbove (Set.range fun y : Fin m → ℝ => |D y|) :=
    ⟨M, by rintro _ ⟨y, rfl⟩; exact hDM y⟩
  set η : ℝ := ⨆ y : Fin m → ℝ, |D y| with hη
  have hle : ∀ y : Fin m → ℝ, |D y| ≤ η := fun y => le_ciSup hbdd y
  have hη0 : 0 ≤ η := (abs_nonneg _).trans (hle 0)
  have key : η ≤ 2 * B + 16 * a * L * m := by
    rcases hη0.eq_or_lt with h0 | hpos
    · rw [← h0]; positivity
    have hLm : 0 < 4 * L * m := by positivity
    have step : ∀ κ : ℝ, 0 < κ → η ≤ 2 * B + 16 * a * L * m + 2 * κ := by
      intro κ hκ
      obtain ⟨x₀, hx₀⟩ := exists_lt_of_lt_ciSup
        (show η - κ < ⨆ y : Fin m → ℝ, |D y| by linarith)
      set h : ℝ := η / (4 * L * m) with hh
      have hh0 : 0 < h := by positivity
      have hmh : L * (2 * m * h) = η / 2 := by
        rw [hh]; field_simp; ring
      set τ : ℝ := ∫ w in {w : Fin m → ℝ | ∃ j, h < |w j|}, k w with hτ
      have hτ0 : 0 ≤ τ := by
        refine setIntegral_nonneg ?_ fun w _ => hk0 w
        rw [show {w : Fin m → ℝ | ∃ j, h < |w j|}
            = ⋃ j, {w : Fin m → ℝ | h < |w j|} by ext w; simp]
        exact MeasurableSet.iUnion fun j =>
          measurableSet_lt (measurable_const : Measurable fun _ : Fin m → ℝ => h)
            (measurable_pi_apply j).abs
      have hτa : η * τ ≤ 4 * L * m * a := by
        have h1 : η * τ ≤ η * (a / h) := mul_le_mul_of_nonneg_left (hka h hh0) hη0
        have h2 : η * (a / h) = 4 * L * m * a := by rw [hh]; field_simp
        linarith
      have hpos' : 0 ≤ η / 2 + κ := by positivity
      have hsum : ∀ w : Fin m → ℝ, (∀ j, |w j| ≤ h) →
          ∑ j, ((fun _ : Fin m => h) - w) j ≤ 2 * m * h := by
        intro w hw
        calc ∑ j, ((fun _ : Fin m => h) - w) j ≤ ∑ _j : Fin m, (2 * h) :=
              Finset.sum_le_sum fun j _ => by
                have := (abs_le.mp (hw j)).1
                simp only [Pi.sub_apply]
                linarith
          _ = 2 * m * h := by
              rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
              ring
      have hcomb : (η / 2 - κ) * (1 - τ) - η * τ ≤ B →
          η / 2 - κ ≤ B + 4 * L * m * a + 2 * L * m * a := by
        intro h5
        have h6 : (η / 2 - κ) * τ ≤ 2 * L * m * a := by
          have hτ1 : (η / 2 - κ) * τ ≤ (η / 2) * τ := by nlinarith [hτ0, hκ.le]
          have h7 : η / 2 * τ = η * τ / 2 := by ring
          rw [h7] at hτ1
          nlinarith [hτa]
        have hexp : (η / 2 - κ) * (1 - τ) = (η / 2 - κ) - (η / 2 - κ) * τ := by ring
        rw [hexp] at h5
        linarith [h5, h6, hτa]
      rcases lt_abs.mp hx₀ with hx | hx
      · have hc : ∀ w : Fin m → ℝ, (∀ j, |w j| ≤ h) →
            η / 2 - κ ≤ D (x₀ + (fun _ : Fin m => h) - w) := by
          intro w hw
          have hz : ∀ j, 0 ≤ ((fun _ : Fin m => h) - w) j := fun j => by
            simp only [Pi.sub_apply]; linarith [(abs_le.mp (hw j)).2]
          have h1 := hup x₀ ((fun _ : Fin m => h) - w) hz
          have h2 : L * ∑ j, ((fun _ : Fin m => h) - w) j ≤ L * (2 * m * h) :=
            mul_le_mul_of_nonneg_left (hsum w hw) hL.le
          have h2' : L * ∑ j, ((fun _ : Fin m => h) - w) j ≤ η / 2 := h2.trans (le_of_eq hmh)
          have he : (x₀ + (fun _ : Fin m => h)) - w = x₀ + ((fun _ : Fin m => h) - w) := by
            ext j; simp only [Pi.add_apply, Pi.sub_apply]; ring
          rw [he]
          linarith [h1, h2', hx]
        have hη' : ∀ w : Fin m → ℝ, -η ≤ D (x₀ + (fun _ : Fin m => h) - w) :=
          fun w => (abs_le.mp (hle _)).1
        have h3 := integral_mul_ge_of_bound_on_ball_pi hk0 hk1 hk
          (hint (x₀ + (fun _ : Fin m => h))) hη' (fun w hw => hc w hw)
        have h4 := (abs_le.mp (hB (x₀ + (fun _ : Fin m => h)))).2
        have h5 : (η / 2 - κ) * (1 - τ) - η * τ ≤ B := le_trans h3 h4
        have h8 := hcomb h5
        nlinarith [h8]
      · have hc : ∀ w : Fin m → ℝ, (∀ j, |w j| ≤ h) →
            η / 2 - κ ≤ - D (x₀ - (fun _ : Fin m => h) - w) := by
          intro w hw
          have hz : ∀ j, 0 ≤ ((fun _ : Fin m => h) + w) j := fun j => by
            simp only [Pi.add_apply]; linarith [(abs_le.mp (hw j)).1]
          have h1 := hdown x₀ ((fun _ : Fin m => h) + w) hz
          have hsum' : ∑ j, ((fun _ : Fin m => h) + w) j ≤ 2 * m * h := by
            calc ∑ j, ((fun _ : Fin m => h) + w) j ≤ ∑ _j : Fin m, (2 * h) :=
                  Finset.sum_le_sum fun j _ => by
                    have := (abs_le.mp (hw j)).2
                    simp only [Pi.add_apply]
                    linarith
              _ = 2 * m * h := by
                  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
                  ring
          have h2 : L * ∑ j, ((fun _ : Fin m => h) + w) j ≤ L * (2 * m * h) :=
            mul_le_mul_of_nonneg_left hsum' hL.le
          have h2' : L * ∑ j, ((fun _ : Fin m => h) + w) j ≤ η / 2 := h2.trans (le_of_eq hmh)
          have he : x₀ - ((fun _ : Fin m => h) + w) = x₀ - (fun _ : Fin m => h) - w := by
            ext j; simp only [Pi.sub_apply, Pi.add_apply]; ring
          rw [he] at h1
          linarith [h1, h2', hx]
        have hη' : ∀ w : Fin m → ℝ, -η ≤ - D (x₀ - (fun _ : Fin m => h) - w) :=
          fun w => by linarith [(abs_le.mp (hle (x₀ - (fun _ : Fin m => h) - w))).2]
        have hfk : Integrable (fun w => -D (x₀ - (fun _ : Fin m => h) - w) * k w) := by
          simpa [neg_mul] using (hint (x₀ - (fun _ : Fin m => h))).neg
        have h3 := integral_mul_ge_of_bound_on_ball_pi hk0 hk1 hk hfk hη' hc
        simp only [neg_mul, integral_neg] at h3
        have h4 := (abs_le.mp (hB (x₀ - (fun _ : Fin m => h)))).1
        have h5 : (η / 2 - κ) * (1 - τ) - η * τ ≤ B := by linarith [h3, h4]
        have h8 := hcomb h5
        nlinarith [h8]
    exact le_of_forall_pos_le_add fun ε hε => by linarith [step (ε / 2) (half_pos hε)]
  exact (hle x).trans key

/-- **The `hdown` companion** of `orthant_cdf_shift_le`: shifting the threshold *down* by a
pointwise nonnegative `z` increases `D = F - G` by at most `L ∑ j z j`. -/
theorem orthant_cdf_shift_ge {m : ℕ} {μ γ : Measure (Fin m → ℝ)}
    [IsProbabilityMeasure μ] [IsProbabilityMeasure γ] {L : ℝ}
    (hG : ∀ x z : Fin m → ℝ, (∀ j, 0 ≤ z j) →
      (γ {y : Fin m → ℝ | ∀ j, y j ≤ x j}).toReal -
          (γ {y : Fin m → ℝ | ∀ j, y j ≤ x j - z j}).toReal ≤ L * ∑ j, z j)
    (x z : Fin m → ℝ) (hz : ∀ j, 0 ≤ z j) :
    (μ {y : Fin m → ℝ | ∀ j, y j ≤ x j - z j}).toReal -
        (γ {y : Fin m → ℝ | ∀ j, y j ≤ x j - z j}).toReal ≤
      ((μ {y : Fin m → ℝ | ∀ j, y j ≤ x j}).toReal -
        (γ {y : Fin m → ℝ | ∀ j, y j ≤ x j}).toReal) + L * ∑ j, z j := by
  have h1 : (μ {y : Fin m → ℝ | ∀ j, y j ≤ x j - z j}).toReal ≤
      (μ {y : Fin m → ℝ | ∀ j, y j ≤ x j}).toReal :=
    orthant_prob_mono μ fun j => by linarith [hz j]
  have h2 := hG x z hz
  linarith

/-- **The multivariate Esséen smoothing inequality for the orthant.**  Assembling
`abs_le_of_smoothed_abstract_pi` with the structural inputs `abs_orthant_prob_sub_le_one`,
`orthant_cdf_shift_le` and `orthant_cdf_shift_ge`: for two probability measures `μ, γ` on
`Fin m → ℝ` whose target orthant CDF is `L`-Lipschitz in the coordinate-sum metric, a
probability density `k` with tail bound `∫_{∃ j, h < |w j|} k ≤ a / h`, and a smoothed
difference bounded by `B`, the unsmoothed difference of orthant probabilities is at most
`2B + 16 a L m`.  This is the
`Fin m`-dimensional analogue of `LatticeProb.sup_cdf_sub_le_of_smoothed`; the measurability of the
orthant CDF is kept as the hypothesis `hDm`. -/
theorem orthant_smoothing_of_smoothed {m : ℕ} (hm : 0 < m) {μ γ : Measure (Fin m → ℝ)}
    [IsProbabilityMeasure μ] [IsProbabilityMeasure γ] {L : ℝ} (hL : 0 < L)
    (hGup : ∀ x z : Fin m → ℝ, (∀ j, 0 ≤ z j) →
      (γ {y : Fin m → ℝ | ∀ j, y j ≤ x j + z j}).toReal -
          (γ {y : Fin m → ℝ | ∀ j, y j ≤ x j}).toReal ≤ L * ∑ j, z j)
    (hGdown : ∀ x z : Fin m → ℝ, (∀ j, 0 ≤ z j) →
      (γ {y : Fin m → ℝ | ∀ j, y j ≤ x j}).toReal -
          (γ {y : Fin m → ℝ | ∀ j, y j ≤ x j - z j}).toReal ≤ L * ∑ j, z j)
    {k : (Fin m → ℝ) → ℝ} (hk0 : ∀ w, 0 ≤ k w)
    (hk1 : Integrable k) (hk : ∫ w, k w = 1)
    {a : ℝ} (hka : ∀ h : ℝ, 0 < h →
      ∫ w in {w : Fin m → ℝ | ∃ j, h < |w j|}, k w ≤ a / h)
    {B : ℝ} (hB : ∀ x : Fin m → ℝ,
      |∫ w, ((μ {y : Fin m → ℝ | ∀ j, y j ≤ x j - w j}).toReal -
        (γ {y : Fin m → ℝ | ∀ j, y j ≤ x j - w j}).toReal) * k w| ≤ B)
    (hDm : Measurable fun y : Fin m → ℝ =>
      (μ {z : Fin m → ℝ | ∀ j, z j ≤ y j}).toReal -
        (γ {z : Fin m → ℝ | ∀ j, z j ≤ y j}).toReal)
    (x : Fin m → ℝ) :
    |(μ {z : Fin m → ℝ | ∀ j, z j ≤ x j}).toReal -
        (γ {z : Fin m → ℝ | ∀ j, z j ≤ x j}).toReal| ≤ 2 * B + 16 * a * L * m := by
  refine abs_le_of_smoothed_abstract_pi hm hDm (M := 1) (fun y => ?_) hL (fun y z hz => ?_)
    (fun y z hz => ?_) hk0 hk1 hk hka (fun y => ?_) x
  · exact abs_orthant_prob_sub_le_one μ γ y
  · exact orthant_cdf_shift_le hGup y z hz
  · exact orthant_cdf_shift_ge hGdown y z hz
  · exact hB y

end LatticeProb
