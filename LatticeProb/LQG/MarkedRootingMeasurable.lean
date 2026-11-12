import Mathlib
import LatticeProb.LQG.MarkedRootingUnitDisk
import LatticeProb.Prob.OpenIndicatorApprox
import LatticeProb.Prob.RandomMeasureIntensity

/-!
# The marked rooting identity for open sets of marks

For a whole-plane Gaussian free field `h`, a `γ`-Liouville quantum gravity measure `μ` of `h` and finitely many
test functions `φ_i`, the identity of `integral_mul_integral_lqgMeasure_eq_of_tsupport_subset_ball` for products
`g(z) F((h, φ_i)_i)` of continuous functions is extended to indicators of open sets: for `A` open in the unit disk
and `V` open in `ℝ^m`,
`E [1_V ((h, φ_i)_i) μ (A)] = ∫_A P ((h, φ_i) + γ ∫ φ_i(x) Cov (h(x), h(z)) dx ∈ V) dz`,
together with the almost everywhere measurability of `ω ↦ 1_V ((h, φ_i)_i) μ (A)`.  The extension is monotone
convergence along continuous functions increasing to the indicators.

## Main statements

* `LatticeProb.Gauss.measurable_integral_mul_wholePlaneCov`: measurability of the root shift.
* `LatticeProb.Gauss.IsWholePlaneGFF.integrable_integral_lqgMeasure`: integrability of the mass `∫ g dμ`.
* `LatticeProb.Gauss.IsWholePlaneGFF.lintegral_mul_lintegral_lqgMeasure_eq`: the identity in `[0, ∞]`-valued form.
* `LatticeProb.Gauss.IsWholePlaneGFF.lintegral_indicator_mul_measure_eq_of_isOpen`: the identity for open sets.
-/

open MeasureTheory ProbabilityTheory Filter Topology Metric
open scoped ENNReal

namespace LatticeProb.Gauss

/-- The root shift `z ↦ ∫ φ(x) Cov (h(x), h(z)) dx` of a test function is measurable. -/
theorem measurable_integral_mul_wholePlaneCov {φ : ℂ → ℝ} (hφ : IsTestFunction Set.univ φ) :
    Measurable fun z : ℂ => ∫ x, φ x * wholePlaneCov x z := by
  refine measurable_of_tendsto_metrizable (f := fun k : ℕ => fun z : ℂ =>
    wholePlaneGFFCov (.pairing φ) (.circle (LQG.dyadicScale k) z))
    (fun k => measurable_wholePlaneGFFCov_pairing_circle hφ (dyadicScale_pos_aux k))
    (tendsto_pi_nhds.2 fun z => ?_)
  exact (tendsto_wholePlaneGFFCov_pairing_circle hφ z).comp tendsto_dyadicScale_nhdsGT

namespace IsWholePlaneGFF

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {hC : Ω → (ℂ → ℝ) → ℝ}
  {hcirc : Ω → ℝ → ℂ → ℝ}

/-- The mass `∫ g dμ` of a `γ`-LQG measure against a nonnegative continuous `g` supported in the open unit disk
is integrable. -/
theorem integrable_integral_lqgMeasure (hh : IsWholePlaneGFF P hC hcirc) {γ : ℝ} (hγ0 : 0 < γ) (hγ2 : γ < 2)
    {μ : Ω → Measure ℂ} (hμ : LQG.IsLQGMeasure P γ hcirc μ) {g : ℂ → ℝ} (hgc : Continuous g)
    (hgs : HasCompactSupport g) (hg0 : ∀ z, 0 ≤ g z) (hg1 : tsupport g ⊆ Metric.ball 0 1) :
    Integrable (fun ω => ∫ z, g z ∂(μ ω)) P := by
  have hP := hh.isProbabilityMeasure
  by_cases hg : ∫ z, g z = 0
  · have hgi : Integrable g := hgc.integrable_of_hasCompactSupport hgs
    have hae : g =ᵐ[volume] 0 := (integral_eq_zero_iff_of_nonneg hg0 hgi).1 hg
    have : g = 0 := (hgc.ae_eq_iff_eq volume continuous_const).1 hae
    simp [this]
  · by_contra hni
    have key := hh.integral_mul_integral_lqgMeasure_eq_of_tsupport_subset_ball hγ0 hγ2 hμ hgc hgs hg0 hg1
      (m := 0) (φ := fun i => i.elim0) (fun i => i.elim0) (F := fun _ => 1) continuous_const (M := 1)
      (fun _ => le_rfl) (fun _ => zero_le_one)
    simp only [one_mul, mul_one, integral_const, smul_eq_mul] at key
    rw [integral_undef hni] at key
    simp at key
    exact hg key.symm

/-- The marked rooting identity in `[0, ∞]`-valued form: for `g ≥ 0` continuous with compact support in the open
unit disk and continuous `F` with values in `[0, 1]`, both sides of the identity of
`integral_mul_integral_lqgMeasure_eq_of_tsupport_subset_ball` are the lower integrals of the same nonnegative
functions. -/
theorem lintegral_mul_lintegral_lqgMeasure_eq (hh : IsWholePlaneGFF P hC hcirc) {γ : ℝ} (hγ0 : 0 < γ)
    (hγ2 : γ < 2) {μ : Ω → Measure ℂ} (hμ : LQG.IsLQGMeasure P γ hcirc μ) {g : ℂ → ℝ}
    (hgc : Continuous g) (hgs : HasCompactSupport g) (hg0 : ∀ z, 0 ≤ g z)
    (hg1 : tsupport g ⊆ Metric.ball 0 1) {m : ℕ} {φ : Fin m → ℂ → ℝ}
    (hφ : ∀ i, IsTestFunction Set.univ (φ i)) {F : (Fin m → ℝ) → ℝ} (hFc : Continuous F)
    (hFM : ∀ x, F x ≤ 1) (hF0 : ∀ x, 0 ≤ F x) :
    ∫⁻ ω, ENNReal.ofReal (F (fun i => hC ω (φ i))) * ∫⁻ z, ENNReal.ofReal (g z) ∂(μ ω) ∂P =
      ∫⁻ z, ENNReal.ofReal (g z) * ∫⁻ ω, ENNReal.ofReal
        (F (fun i => hC ω (φ i) + γ * ∫ x, φ i x * wholePlaneCov x z)) ∂P := by
  have hP := hh.isProbabilityMeasure
  have key := hh.integral_mul_integral_lqgMeasure_eq_of_tsupport_subset_ball hγ0 hγ2 hμ hgc hgs hg0 hg1 hφ hFc
    hFM hF0
  have hint := hh.integrable_integral_lqgMeasure hγ0 hγ2 hμ hgc hgs hg0 hg1
  have hgi : Integrable g := hgc.integrable_of_hasCompactSupport hgs
  have hmeasP : ∀ i, Measurable fun ω => hC ω (φ i) := fun i => hh.measurable_pairing _ (hφ i)
  have hFm : Measurable fun ω => F (fun i => hC ω (φ i)) :=
    hFc.measurable.comp (measurable_pi_iff.2 hmeasP)
  have hL : ∫⁻ ω, ENNReal.ofReal (F (fun i => hC ω (φ i))) * ∫⁻ z, ENNReal.ofReal (g z) ∂(μ ω) ∂P =
      ENNReal.ofReal (∫ ω, F (fun i => hC ω (φ i)) * ∫ z, g z ∂(μ ω) ∂P) := by
    have hi : Integrable (fun ω => F (fun i => hC ω (φ i)) * ∫ z, g z ∂(μ ω)) P :=
      hint.mono' (hFm.aestronglyMeasurable.mul hint.aestronglyMeasurable) (ae_of_all _ fun ω => by
        rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (hF0 _) (integral_nonneg hg0))]
        exact mul_le_of_le_one_left (integral_nonneg hg0) (hFM _))
    rw [ofReal_integral_eq_lintegral_ofReal hi
      (ae_of_all _ fun ω => mul_nonneg (hF0 _) (integral_nonneg hg0))]
    refine lintegral_congr_ae ?_
    filter_upwards [hμ] with ω hω
    have := hω.isLocallyFiniteMeasure
    rw [ENNReal.ofReal_mul (hF0 _), ofReal_integral_eq_lintegral_ofReal
      (hgc.integrable_of_hasCompactSupport hgs) (ae_of_all _ hg0)]
  have hsm : ∀ i, Measurable fun z : ℂ => ∫ x, φ i x * wholePlaneCov x z := fun i =>
    measurable_integral_mul_wholePlaneCov (hφ i)
  have hFj : Measurable fun q : ℂ × Ω => F (fun i => hC q.2 (φ i) +
      γ * ∫ x, φ i x * wholePlaneCov x q.1) :=
    hFc.measurable.comp (measurable_pi_iff.2 fun i =>
      ((hmeasP i).comp measurable_snd).add (((hsm i).comp measurable_fst).const_mul γ))
  have hEb : ∀ z : ℂ, 0 ≤ ∫ ω, F (fun i => hC ω (φ i) + γ * ∫ x, φ i x * wholePlaneCov x z) ∂P ∧
      ∫ ω, F (fun i => hC ω (φ i) + γ * ∫ x, φ i x * wholePlaneCov x z) ∂P ≤ 1 := fun z =>
    integral_mem_Icc_of_forall fun ω => ⟨hF0 _, hFM _⟩
  have hR : ∫⁻ z, ENNReal.ofReal (g z) * ∫⁻ ω, ENNReal.ofReal
        (F (fun i => hC ω (φ i) + γ * ∫ x, φ i x * wholePlaneCov x z)) ∂P =
      ENNReal.ofReal (∫ z, g z * ∫ ω, F (fun i => hC ω (φ i) +
        γ * ∫ x, φ i x * wholePlaneCov x z) ∂P) := by
    have hEm : Measurable fun z : ℂ => ∫ ω, F (fun i => hC ω (φ i) +
        γ * ∫ x, φ i x * wholePlaneCov x z) ∂P :=
      hFj.stronglyMeasurable.integral_prod_right'.measurable
    have hi : Integrable (fun z => g z * ∫ ω, F (fun i => hC ω (φ i) +
        γ * ∫ x, φ i x * wholePlaneCov x z) ∂P) :=
      hgi.mono' (hgc.aestronglyMeasurable.mul hEm.aestronglyMeasurable) (ae_of_all _ fun z => by
        rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (hg0 z) (hEb z).1)]
        exact mul_le_of_le_one_right (hg0 z) (hEb z).2)
    rw [ofReal_integral_eq_lintegral_ofReal hi (ae_of_all _ fun z => mul_nonneg (hg0 z) (hEb z).1)]
    refine lintegral_congr fun z => ?_
    have hFi : Integrable (fun ω => F (fun i => hC ω (φ i) +
        γ * ∫ x, φ i x * wholePlaneCov x z)) P :=
      (integrable_const (1 : ℝ)).mono' (hFj.comp (measurable_const.prodMk measurable_id)).aestronglyMeasurable
        (ae_of_all _ fun ω => by
          rw [Real.norm_eq_abs, abs_of_nonneg (hF0 _)]; exact hFM _)
    rw [ENNReal.ofReal_mul (hg0 z), ofReal_integral_eq_lintegral_ofReal hFi (ae_of_all _ fun ω => hF0 _)]
  rw [hL, hR, key]

theorem ofReal_indicator_one_aux {α : Type*} (s : Set α) (x : α) :
    ENNReal.ofReal (s.indicator (1 : α → ℝ) x) = s.indicator (fun _ => (1 : ℝ≥0∞)) x := by
  by_cases h : x ∈ s <;> simp [h]

theorem indicator_one_ne_top_aux {α : Type*} (s : Set α) (x : α) :
    s.indicator (fun _ => (1 : ℝ≥0∞)) x ≠ ∞ := by
  by_cases h : x ∈ s <;> simp [h]

/-- **The marked rooting identity for products of open sets.** For `A` open in the unit disk and `V` open in
`ℝ^m`, `E [1_V ((h, φ_i)_i) μ (A)] = ∫_A P ((h, φ_i) + γ ∫ φ_i(x) Cov (h(x), h(z)) dx ∈ V) dz`. -/
theorem lintegral_indicator_mul_measure_eq_of_isOpen (hh : IsWholePlaneGFF P hC hcirc) {γ : ℝ}
    (hγ0 : 0 < γ) (hγ2 : γ < 2) {μ : Ω → Measure ℂ} (hμ : LQG.IsLQGMeasure P γ hcirc μ) {m : ℕ}
    {φ : Fin m → ℂ → ℝ} (hφ : ∀ i, IsTestFunction Set.univ (φ i)) {A : Set ℂ} (hA : IsOpen A)
    (hAb : A ⊆ Metric.ball 0 1) {V : Set (Fin m → ℝ)} (hV : IsOpen V) :
    AEMeasurable (fun ω => V.indicator (fun _ => (1 : ℝ≥0∞)) (fun i => hC ω (φ i)) * μ ω A) P ∧
    ∫⁻ ω, V.indicator (fun _ => (1 : ℝ≥0∞)) (fun i => hC ω (φ i)) * μ ω A ∂P =
      ∫⁻ z in A, ∫⁻ ω, V.indicator (fun _ => (1 : ℝ≥0∞))
        (fun i => hC ω (φ i) + γ * ∫ x, φ i x * wholePlaneCov x z) ∂P := by
  have hP := hh.isProbabilityMeasure
  have hmeasP : ∀ i, Measurable fun ω => hC ω (φ i) := fun i => hh.measurable_pairing _ (hφ i)
  have hxm : Measurable fun ω => fun i => hC ω (φ i) := measurable_pi_iff.2 hmeasP
  have hsm : ∀ i, Measurable fun z : ℂ => ∫ x, φ i x * wholePlaneCov x z := fun i =>
    measurable_integral_mul_wholePlaneCov (hφ i)
  set r : ℕ → ℝ := fun n => 1 - 1 / ((n : ℝ) + 2) with hr
  have hr_lt : ∀ n, r n < 1 := fun n => by
    have : 0 < 1 / ((n : ℝ) + 2) := by positivity
    simp only [hr]; linarith
  have hr_mono : Monotone r := fun a b hab => by
    have h0 : (a : ℝ) ≤ b := Nat.cast_le.2 hab
    have h1 : 1 / ((b : ℝ) + 2) ≤ 1 / ((a : ℝ) + 2) := one_div_le_one_div_of_le (by positivity) (by linarith)
    simp only [hr]; linarith
  have hr_lim : ∀ t : ℝ, t < 1 → ∃ n, t < r n := fun t ht => by
    obtain ⟨n, hn⟩ := exists_nat_gt (1 / (1 - t))
    have h1t : 0 < 1 - t := by linarith
    have h2 : 1 / (1 - t) < (n : ℝ) + 2 := by linarith [Nat.cast_nonneg (α := ℝ) n]
    have h3 : 1 < ((n : ℝ) + 2) * (1 - t) := (div_lt_iff₀ h1t).1 h2
    refine ⟨n, ?_⟩
    have : 1 / ((n : ℝ) + 2) < 1 - t := by
      rw [div_lt_iff₀ (by positivity)]; linarith
    simp only [hr]; linarith
  set U : ℕ → Set ℂ := fun n => A ∩ Metric.ball 0 (r n) with hU
  have hUo : ∀ n, IsOpen (U n) := fun n => hA.inter Metric.isOpen_ball
  have hUm : Monotone U := fun a b hab =>
    Set.inter_subset_inter_right _ (Metric.ball_subset_ball (hr_mono hab))
  have hUi : (⋃ n, U n) = A := by
    ext z
    simp only [Set.mem_iUnion, hU, Set.mem_inter_iff, mem_ball_zero_iff]
    constructor
    · rintro ⟨n, hz, -⟩; exact hz
    · intro hz
      obtain ⟨n, hn⟩ := hr_lim ‖z‖ (mem_ball_zero_iff.1 (hAb hz))
      exact ⟨n, hz, hn⟩
  obtain ⟨g, hgc, hgb, hgs, hgmono, hgt⟩ := exists_monotone_continuous_tendsto_indicator_iUnion U hUo hUm
  obtain ⟨F, hFc, hFb, -, hFmono, hFt⟩ := exists_monotone_continuous_tendsto_indicator_iUnion
    (fun _ : ℕ => V) (fun _ => hV) monotone_const
  simp only [hUi, Set.iUnion_const] at hgt hFt
  have hgcs : ∀ n, HasCompactSupport (g n) := fun n =>
    HasCompactSupport.intro (isCompact_closedBall (0 : ℂ) (r n)) fun z hz => by
      by_contra h
      exact hz (Metric.ball_subset_closedBall (hgs n z h).2)
  have hgts : ∀ n, tsupport (g n) ⊆ Metric.ball 0 1 := fun n z hz =>
    Metric.closedBall_subset_ball (hr_lt n) (closure_minimal (fun w hw =>
      Metric.ball_subset_closedBall (hgs n w hw).2) isClosed_closedBall hz)
  have hn : ∀ n, ∫⁻ ω, ENNReal.ofReal (F n (fun i => hC ω (φ i))) *
      ∫⁻ z, ENNReal.ofReal (g n z) ∂(μ ω) ∂P = ∫⁻ z, ENNReal.ofReal (g n z) * ∫⁻ ω, ENNReal.ofReal
        (F n (fun i => hC ω (φ i) + γ * ∫ x, φ i x * wholePlaneCov x z)) ∂P := fun n =>
    hh.lintegral_mul_lintegral_lqgMeasure_eq hγ0 hγ2 hμ (hgc n) (hgcs n) (fun z => (hgb n z).1) (hgts n)
      hφ (hFc n) (fun x => (hFb n x).2) (fun x => (hFb n x).1)
  -- pointwise suprema
  have hmono2 : ∀ y z, Monotone fun n => ENNReal.ofReal (F n y) * ENNReal.ofReal (g n z) := fun y z a b hab =>
    mul_le_mul' (ENNReal.ofReal_le_ofReal (hFmono y hab)) (ENNReal.ofReal_le_ofReal (hgmono z hab))
  have hsup : ∀ y z, ⨆ n, ENNReal.ofReal (F n y) * ENNReal.ofReal (g n z) =
      V.indicator (fun _ => (1 : ℝ≥0∞)) y * A.indicator (fun _ => (1 : ℝ≥0∞)) z := fun y z => by
    have h1 : Tendsto (fun n => ENNReal.ofReal (F n y)) atTop (𝓝 (V.indicator (fun _ => (1 : ℝ≥0∞)) y)) := by
      rw [← ofReal_indicator_one_aux]; exact ENNReal.tendsto_ofReal (hFt y)
    have h2 : Tendsto (fun n => ENNReal.ofReal (g n z)) atTop (𝓝 (A.indicator (fun _ => (1 : ℝ≥0∞)) z)) := by
      rw [← ofReal_indicator_one_aux]; exact ENNReal.tendsto_ofReal (hgt z)
    have h3 := ENNReal.Tendsto.mul h1 (Or.inr (indicator_one_ne_top_aux A z)) h2
      (Or.inr (indicator_one_ne_top_aux V y))
    exact (tendsto_nhds_unique (tendsto_atTop_iSup (hmono2 y z)) h3)
  have hFmeas : ∀ n, Measurable (F n) := fun n => (hFc n).measurable
  have hintg : ∀ n, Integrable (fun ω => ∫ z, g n z ∂(μ ω)) P := fun n =>
    hh.integrable_integral_lqgMeasure hγ0 hγ2 hμ (hgc n) (hgcs n) (fun z => (hgb n z).1) (hgts n)
  have hLmeas : ∀ n, AEMeasurable (fun ω => ENNReal.ofReal (F n (fun i => hC ω (φ i))) *
      ∫⁻ z, ENNReal.ofReal (g n z) ∂(μ ω)) P := fun n => by
    have h1 : (fun ω => ∫⁻ z, ENNReal.ofReal (g n z) ∂(μ ω)) =ᵐ[P]
        fun ω => ENNReal.ofReal (∫ z, g n z ∂(μ ω)) := by
      filter_upwards [hμ] with ω hω
      have := hω.isLocallyFiniteMeasure
      exact (ofReal_integral_eq_lintegral_ofReal ((hgc n).integrable_of_hasCompactSupport (hgcs n))
        (ae_of_all _ fun z => (hgb n z).1)).symm
    exact (((hFmeas n).comp hxm).ennreal_ofReal.aemeasurable).mul
      ((ENNReal.measurable_ofReal.comp_aemeasurable (hintg n).aemeasurable).congr h1.symm)
  have hLmono : ∀ ω, Monotone fun n => ENNReal.ofReal (F n (fun i => hC ω (φ i))) *
      ∫⁻ z, ENNReal.ofReal (g n z) ∂(μ ω) := fun ω a b hab =>
    mul_le_mul' (ENNReal.ofReal_le_ofReal (hFmono _ hab))
      (lintegral_mono fun z => ENNReal.ofReal_le_ofReal (hgmono z hab))
  have hLsup : ∀ ω, ⨆ n, ENNReal.ofReal (F n (fun i => hC ω (φ i))) *
      ∫⁻ z, ENNReal.ofReal (g n z) ∂(μ ω) =
      V.indicator (fun _ => (1 : ℝ≥0∞)) (fun i => hC ω (φ i)) * μ ω A := fun ω => by
    have e1 : ∀ n, ENNReal.ofReal (F n (fun i => hC ω (φ i))) * ∫⁻ z, ENNReal.ofReal (g n z) ∂(μ ω) =
        ∫⁻ z, ENNReal.ofReal (F n (fun i => hC ω (φ i))) * ENNReal.ofReal (g n z) ∂(μ ω) := fun n =>
      (lintegral_const_mul _ (hgc n).measurable.ennreal_ofReal).symm
    simp_rw [e1]
    rw [← lintegral_iSup (f := fun n z => ENNReal.ofReal (F n (fun i => hC ω (φ i))) *
      ENNReal.ofReal (g n z)) (fun n => measurable_const.mul (hgc n).measurable.ennreal_ofReal)
      (fun a b hab z => hmono2 _ z hab)]
    simp_rw [hsup]
    rw [lintegral_const_mul _ (measurable_const.indicator hA.measurableSet),
      lintegral_indicator_const hA.measurableSet, one_mul]
  have hYm : Measurable fun q : ℂ × Ω => fun i => hC q.2 (φ i) + γ * ∫ x, φ i x * wholePlaneCov x q.1 :=
    measurable_pi_iff.2 fun i => ((hmeasP i).comp measurable_snd).add (((hsm i).comp measurable_fst).const_mul γ)
  have hYz : ∀ z : ℂ, Measurable fun ω => fun i => hC ω (φ i) + γ * ∫ x, φ i x * wholePlaneCov x z :=
    fun z => hYm.comp (measurable_const.prodMk measurable_id)
  have hbeq : ∀ n z, ENNReal.ofReal (g n z) * ∫⁻ ω, ENNReal.ofReal
      (F n (fun i => hC ω (φ i) + γ * ∫ x, φ i x * wholePlaneCov x z)) ∂P =
      ∫⁻ ω, ENNReal.ofReal (F n (fun i => hC ω (φ i) + γ * ∫ x, φ i x * wholePlaneCov x z)) *
        ENNReal.ofReal (g n z) ∂P := fun n z => by
    rw [mul_comm]
    exact (lintegral_mul_const _ (((hFmeas n).comp (hYz z)).ennreal_ofReal)).symm
  have hbmeas : ∀ n, Measurable fun z : ℂ => ENNReal.ofReal (g n z) * ∫⁻ ω, ENNReal.ofReal
      (F n (fun i => hC ω (φ i) + γ * ∫ x, φ i x * wholePlaneCov x z)) ∂P := fun n =>
    (hgc n).measurable.ennreal_ofReal.mul
      (((hFmeas n).comp hYm).ennreal_ofReal.lintegral_prod_right')
  have hbmono : ∀ z, Monotone fun n => ENNReal.ofReal (g n z) * ∫⁻ ω, ENNReal.ofReal
      (F n (fun i => hC ω (φ i) + γ * ∫ x, φ i x * wholePlaneCov x z)) ∂P := fun z a b hab =>
    mul_le_mul' (ENNReal.ofReal_le_ofReal (hgmono z hab))
      (lintegral_mono fun ω => ENNReal.ofReal_le_ofReal (hFmono _ hab))
  have hbsup : ∀ z, ⨆ n, ENNReal.ofReal (g n z) * ∫⁻ ω, ENNReal.ofReal
      (F n (fun i => hC ω (φ i) + γ * ∫ x, φ i x * wholePlaneCov x z)) ∂P =
      A.indicator (fun _ => (1 : ℝ≥0∞)) z * ∫⁻ ω, V.indicator (fun _ => (1 : ℝ≥0∞))
        (fun i => hC ω (φ i) + γ * ∫ x, φ i x * wholePlaneCov x z) ∂P := fun z => by
    simp_rw [hbeq]
    rw [← lintegral_iSup (f := fun n ω => ENNReal.ofReal
      (F n (fun i => hC ω (φ i) + γ * ∫ x, φ i x * wholePlaneCov x z)) * ENNReal.ofReal (g n z))
      (fun n => ((hFmeas n).comp (hYz z)).ennreal_ofReal.mul_const _)
      (fun a b hab ω => mul_le_mul' (ENNReal.ofReal_le_ofReal (hFmono _ hab))
        (ENNReal.ofReal_le_ofReal (hgmono z hab)))]
    simp_rw [hsup]
    rw [mul_comm]
    exact lintegral_mul_const _ ((measurable_const.indicator hV.measurableSet).comp (hYz z))
  refine ⟨?_, ?_⟩
  · have : (fun ω => V.indicator (fun _ => (1 : ℝ≥0∞)) (fun i => hC ω (φ i)) * μ ω A) =
        fun ω => ⨆ n, ENNReal.ofReal (F n (fun i => hC ω (φ i))) *
          ∫⁻ z, ENNReal.ofReal (g n z) ∂(μ ω) := funext fun ω => (hLsup ω).symm
    rw [this]
    exact AEMeasurable.iSup hLmeas
  calc ∫⁻ ω, V.indicator (fun _ => (1 : ℝ≥0∞)) (fun i => hC ω (φ i)) * μ ω A ∂P
      = ∫⁻ ω, ⨆ n, ENNReal.ofReal (F n (fun i => hC ω (φ i))) *
          ∫⁻ z, ENNReal.ofReal (g n z) ∂(μ ω) ∂P := lintegral_congr fun ω => (hLsup ω).symm
    _ = ⨆ n, ∫⁻ ω, ENNReal.ofReal (F n (fun i => hC ω (φ i))) *
          ∫⁻ z, ENNReal.ofReal (g n z) ∂(μ ω) ∂P := lintegral_iSup' hLmeas (ae_of_all _ hLmono)
    _ = ⨆ n, ∫⁻ z, ENNReal.ofReal (g n z) * ∫⁻ ω, ENNReal.ofReal
          (F n (fun i => hC ω (φ i) + γ * ∫ x, φ i x * wholePlaneCov x z)) ∂P := by simp_rw [hn]
    _ = ∫⁻ z, ⨆ n, ENNReal.ofReal (g n z) * ∫⁻ ω, ENNReal.ofReal
          (F n (fun i => hC ω (φ i) + γ * ∫ x, φ i x * wholePlaneCov x z)) ∂P :=
      (lintegral_iSup hbmeas fun a b hab z => hbmono z hab).symm
    _ = ∫⁻ z, A.indicator (fun _ => (1 : ℝ≥0∞)) z * ∫⁻ ω, V.indicator (fun _ => (1 : ℝ≥0∞))
          (fun i => hC ω (φ i) + γ * ∫ x, φ i x * wholePlaneCov x z) ∂P := lintegral_congr hbsup
    _ = _ := by
      rw [← lintegral_indicator hA.measurableSet]
      refine lintegral_congr fun z => ?_
      by_cases hz : z ∈ A <;> simp [hz]


end IsWholePlaneGFF

end LatticeProb.Gauss
