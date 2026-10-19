import Mathlib.MeasureTheory.Function.UniformIntegrable
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Function.L1Space.Integrable
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
import Mathlib.Topology.Instances.ENNReal.Lemmas
import Mathlib.Topology.Algebra.Order.Field
import Mathlib.Analysis.SpecificLimits.Basic

/-!
# A Vitali-type limit for products

If `T n` is bounded in second moment, `∫ T n → 1`, `‖T n U n‖ ≤ 1` and `U n → a` in measure, then
`∫ T n U n → a`. The proof writes `∫ T U = ∫ T (U - a) + a ∫ T`, shows that `T (U - a)` is uniformly
integrable and tends to zero in measure, and applies Vitali's theorem. The auxiliary lemmas give
uniform integrability of bounded families and of `L²`-bounded families at exponent `1`, and the
convergence in measure of a product with a factor bounded in second moment.
-/

open MeasureTheory Filter Topology
open scoped ENNReal NNReal

namespace LatticeProb.McLeish

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}

/-- A family of complex functions bounded in norm by one is uniformly integrable at exponent `1`,
on any measure: its level sets above the threshold `2` are empty. -/
theorem unifIntegrable_one_of_norm_le_one {g : ℕ → Ω → ℂ} (hg : ∀ n, AEStronglyMeasurable (g n) P)
    (h1 : ∀ n ω, ‖g n ω‖ ≤ 1) : UnifIntegrable g 1 P := by
  refine unifIntegrable_of le_rfl ENNReal.one_ne_top hg fun ε _ => ⟨2, fun n => ?_⟩
  have hempty : {x : Ω | (2 : ℝ≥0) ≤ ‖g n x‖₊} = ∅ := by
    ext x
    simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, not_le]
    have h2 : ‖g n x‖₊ ≤ 1 := by exact_mod_cast h1 n x
    exact lt_of_le_of_lt h2 one_lt_two
  rw [hempty, Set.indicator_empty]
  simp

/-- A family bounded in `L²` by a common constant is uniformly integrable at exponent `1` on a
probability space. The level sets `{C ≤ ‖f n‖}` are controlled by Markov's inequality for the
second moment: on such a set `‖f n‖ ≤ ‖f n‖² / C`. -/
theorem unifIntegrable_one_of_sq_integral_le [IsProbabilityMeasure P] {f : ℕ → Ω → ℂ}
    (hf : ∀ n, MemLp (f n) 2 P) {K : ℝ} (hK : ∀ n, ∫ ω, ‖f n ω‖ ^ 2 ∂P ≤ K) :
    UnifIntegrable f 1 P := by
  refine unifIntegrable_of le_rfl ENNReal.one_ne_top (fun n => (hf n).aestronglyMeasurable) ?_
  intro ε hε
  obtain ⟨C, hCpos, hCK⟩ : ∃ C : ℝ, 0 < C ∧ K / C ≤ ε := by
    refine ⟨(|K| + 1) / ε, div_pos (by positivity) hε, ?_⟩
    have h : ε * ((|K| + 1) / ε) = |K| + 1 := by field_simp
    rw [div_le_iff₀ (div_pos (by positivity) hε), h]
    linarith [le_abs_self K]
  refine ⟨⟨C, hCpos.le⟩, fun n => ?_⟩
  have hpt : ∀ x, ‖{x : Ω | (⟨C, hCpos.le⟩ : ℝ≥0) ≤ ‖f n x‖₊}.indicator (f n) x‖ₑ ≤
      ENNReal.ofReal (‖f n x‖ ^ 2 / C) := by
    intro x
    rw [Set.indicator_apply]
    split_ifs with hx
    · have hx' : C ≤ ‖f n x‖ := by
        have h2 : (⟨C, hCpos.le⟩ : ℝ≥0) ≤ ‖f n x‖₊ := hx
        exact_mod_cast h2
      rw [← ofReal_norm]
      refine ENNReal.ofReal_le_ofReal ?_
      rw [le_div_iff₀ hCpos]
      nlinarith [norm_nonneg (f n x)]
    · simp
  have hint : Integrable (fun ω => ‖f n ω‖ ^ 2 / C) P :=
    ((memLp_two_iff_integrable_sq_norm (hf n).aestronglyMeasurable).1 (hf n)).div_const C
  calc eLpNorm ({x : Ω | (⟨C, hCpos.le⟩ : ℝ≥0) ≤ ‖f n x‖₊}.indicator (f n)) 1 P
      = ∫⁻ x, ‖{x : Ω | (⟨C, hCpos.le⟩ : ℝ≥0) ≤ ‖f n x‖₊}.indicator (f n) x‖ₑ ∂P :=
        eLpNorm_one_eq_lintegral_enorm
    _ ≤ ∫⁻ ω, ENNReal.ofReal (‖f n ω‖ ^ 2 / C) ∂P := lintegral_mono hpt
    _ = ENNReal.ofReal (∫ ω, ‖f n ω‖ ^ 2 / C ∂P) :=
        (ofReal_integral_eq_lintegral_ofReal hint
          (Filter.Eventually.of_forall fun ω => by positivity)).symm
    _ ≤ ENNReal.ofReal ε := by
        refine ENNReal.ofReal_le_ofReal ?_
        rw [integral_div]
        exact (div_le_div_of_nonneg_right (hK n) hCpos.le).trans hCK

/-- Chebyshev's inequality for the second moment: if `∫ ‖T‖² ≤ K`, then `P (M ≤ ‖T‖) ≤ K / M²`. -/
theorem measure_norm_ge_le_ofReal_div_sq [IsProbabilityMeasure P] {T : Ω → ℂ} (hT : MemLp T 2 P)
    {K M : ℝ} (hM : 0 < M) (hK : ∫ ω, ‖T ω‖ ^ 2 ∂P ≤ K) :
    P {ω | M ≤ ‖T ω‖} ≤ ENNReal.ofReal (K / M ^ 2) := by
  have hint : Integrable (fun ω => ‖T ω‖ ^ 2) P :=
    (memLp_two_iff_integrable_sq_norm hT.aestronglyMeasurable).1 hT
  have hnn : 0 ≤ᵐ[P] fun ω => ‖T ω‖ ^ 2 := Filter.Eventually.of_forall fun ω => by positivity
  have hK0 : 0 ≤ K := (integral_nonneg fun ω => by positivity).trans hK
  have hsub : {ω | M ≤ ‖T ω‖} ⊆ {ω | M ^ 2 ≤ ‖T ω‖ ^ 2} := fun ω hω =>
    pow_le_pow_left₀ hM.le hω 2
  have h1 := mul_meas_ge_le_integral_of_nonneg hnn hint (M ^ 2)
  have h2 : P.real {ω | M ≤ ‖T ω‖} ≤ P.real {ω | M ^ 2 ≤ ‖T ω‖ ^ 2} :=
    measureReal_mono hsub
  have h3 : M ^ 2 * P.real {ω | M ≤ ‖T ω‖} ≤ K :=
    (mul_le_mul_of_nonneg_left h2 (by positivity)).trans (h1.trans hK)
  have h4 : P.real {ω | M ≤ ‖T ω‖} ≤ K / M ^ 2 := by
    rw [le_div_iff₀ (by positivity)]
    linarith [h3]
  rw [← ENNReal.ofReal_toReal (measure_ne_top P _)]
  exact ENNReal.ofReal_le_ofReal h4

/-- Product in measure: a sequence bounded in second moment (by a common constant) times a sequence
tending to zero in measure tends to zero in measure. -/
theorem tendstoInMeasure_mul_zero_of_sq_integral_le [IsProbabilityMeasure P] {T V : ℕ → Ω → ℂ}
    (hT : ∀ n, MemLp (T n) 2 P) {K : ℝ} (hK : ∀ n, ∫ ω, ‖T n ω‖ ^ 2 ∂P ≤ K)
    (hV : TendstoInMeasure P V atTop (fun _ => 0)) :
    TendstoInMeasure P (fun n ω => T n ω * V n ω) atTop (fun _ => 0) := by
  rw [tendstoInMeasure_iff_norm] at hV ⊢
  simp only [sub_zero] at hV ⊢
  intro ε hε
  rw [ENNReal.tendsto_nhds_zero]
  intro c hc
  obtain ⟨η, hη, hηc⟩ : ∃ η : ℝ, 0 < η ∧ ENNReal.ofReal η ≤ c := by
    by_cases htop : c = ⊤
    · exact ⟨1, one_pos, by rw [htop]; exact le_top⟩
    · exact ⟨c.toReal, ENNReal.toReal_pos hc.ne' htop, (ENNReal.ofReal_toReal htop).le⟩
  have hlim : Tendsto (fun M : ℝ => K / M ^ 2) atTop (𝓝 0) :=
    Filter.Tendsto.div_atTop tendsto_const_nhds (tendsto_pow_atTop two_ne_zero)
  obtain ⟨M, hMK, hM⟩ := ((hlim.eventually (gt_mem_nhds (half_pos hη))).and
    (eventually_gt_atTop 0)).exists
  have hC := ENNReal.tendsto_nhds_zero.1 (hV (ε / M) (div_pos hε hM))
    (ENNReal.ofReal (η / 2)) (ENNReal.ofReal_pos.2 (half_pos hη))
  filter_upwards [hC] with n hn
  have hsub : {ω | ε ≤ ‖T n ω * V n ω‖} ⊆
      {ω | M ≤ ‖T n ω‖} ∪ {ω | ε / M ≤ ‖V n ω‖} := by
    intro ω hω
    by_contra hcon
    simp only [Set.mem_union, Set.mem_setOf_eq, not_or, not_le] at hcon hω
    obtain ⟨h1, h2⟩ := hcon
    rw [lt_div_iff₀ hM] at h2
    rw [norm_mul] at hω
    nlinarith [norm_nonneg (T n ω), norm_nonneg (V n ω)]
  calc P {ω | ε ≤ ‖T n ω * V n ω‖}
      ≤ P ({ω | M ≤ ‖T n ω‖} ∪ {ω | ε / M ≤ ‖V n ω‖}) := measure_mono hsub
    _ ≤ P {ω | M ≤ ‖T n ω‖} + P {ω | ε / M ≤ ‖V n ω‖} := measure_union_le _ _
    _ ≤ ENNReal.ofReal (η / 2) + ENNReal.ofReal (η / 2) :=
        add_le_add ((measure_norm_ge_le_ofReal_div_sq (hT n) hM (hK n)).trans
          (ENNReal.ofReal_le_ofReal hMK.le)) hn
    _ = ENNReal.ofReal η := by
        rw [← ENNReal.ofReal_add (half_pos hη).le (half_pos hη).le]
        congr 1
        ring
    _ ≤ c := hηc

/-- Vitali-type limit for products: if `T` is bounded in second moment, `∫ T → 1`, `|T U| ≤ 1`
and `U → a` in measure, then `∫ T U → a`. The difference `T (U - a)` is uniformly integrable and
tends to zero in measure, so its integral tends to zero, and `∫ T U = ∫ T (U - a) + a ∫ T`. -/
theorem tendsto_integral_mul_of_bdd {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
    [IsProbabilityMeasure P]
    (T U : ℕ → Ω → ℂ) (a : ℂ)
    (hTm : ∀ n, AEStronglyMeasurable (T n) P) (hUm : ∀ n, AEStronglyMeasurable (U n) P)
    (hT2 : ∃ C : ℝ, ∀ n, MemLp (T n) 2 P ∧ ∫ ω, ‖T n ω‖ ^ 2 ∂P ≤ C)
    (hT1 : Filter.Tendsto (fun n => ∫ ω, T n ω ∂P) Filter.atTop (nhds 1))
    (hTU : ∀ n ω, ‖T n ω * U n ω‖ ≤ 1)
    (hU : TendstoInMeasure P U Filter.atTop (fun _ => a)) :
    Filter.Tendsto (fun n => ∫ ω, T n ω * U n ω ∂P) Filter.atTop (nhds a) := by
  obtain ⟨K, hK⟩ := hT2
  have hTint : ∀ n, Integrable (T n) P := fun n => MemLp.integrable one_le_two (hK n).1
  have hTUint : ∀ n, Integrable (fun ω => T n ω * U n ω) P := fun n =>
    Integrable.of_bound ((hTm n).mul (hUm n)) 1 (Filter.Eventually.of_forall (hTU n))
  have hZint : ∀ n, Integrable (fun ω => T n ω * (U n ω - a)) P := fun n => by
    have heq : (fun ω => T n ω * (U n ω - a)) = fun ω => T n ω * U n ω - a * T n ω := by
      funext ω; ring
    rw [heq]
    exact (hTUint n).sub ((hTint n).const_mul a)
  -- The difference `U - a` tends to zero in measure, hence so does `T (U - a)`.
  have hVa : TendstoInMeasure P (fun n ω => U n ω - a) atTop (fun _ => 0) := by
    rw [tendstoInMeasure_iff_norm] at hU ⊢
    simpa only [sub_zero] using hU
  have hZ0 : TendstoInMeasure P (fun n ω => T n ω * (U n ω - a)) atTop (fun _ => 0) :=
    tendstoInMeasure_mul_zero_of_sq_integral_le (fun n => (hK n).1) (fun n => (hK n).2) hVa
  -- Uniform integrability of `T (U - a) = T U + (-(a T))`.
  have hK' : ∀ n, ∫ ω, ‖a * T n ω‖ ^ 2 ∂P ≤ ‖a‖ ^ 2 * K := fun n => by
    simp_rw [norm_mul, mul_pow]
    rw [integral_const_mul]
    exact mul_le_mul_of_nonneg_left (hK n).2 (by positivity)
  have hUI1 : UnifIntegrable (fun n ω => T n ω * U n ω) 1 P :=
    unifIntegrable_one_of_norm_le_one (fun n => (hTm n).mul (hUm n)) hTU
  have hUI2 : UnifIntegrable (fun n ω => a * T n ω) 1 P :=
    unifIntegrable_one_of_sq_integral_le (fun n => (hK n).1.const_mul a) hK'
  have hUI3 : UnifIntegrable (fun n ω => -(a * T n ω)) 1 P := hUI2.neg
  have hUI : UnifIntegrable (fun n ω => T n ω * (U n ω - a)) 1 P := by
    have heq : (fun n ω => T n ω * (U n ω - a)) =
        (fun n ω => T n ω * U n ω) + (fun n ω => -(a * T n ω)) := by
      funext n ω
      simp only [Pi.add_apply]
      ring
    rw [heq]
    exact hUI1.add hUI3 le_rfl (fun n => (hTm n).mul (hUm n))
      (fun n => ((hTm n).const_mul a).neg)
  -- Vitali's theorem in `L¹`, then convergence of the integrals.
  have hVit := tendsto_Lp_finite_of_tendstoInMeasure (μ := P) (p := 1) le_rfl ENNReal.one_ne_top
    (f := fun n ω => T n ω * (U n ω - a)) (g := fun _ => 0)
    (fun n => (hTm n).mul ((hUm n).sub aestronglyMeasurable_const)) (memLp_const 0) hUI hZ0
  have hZ : Filter.Tendsto (fun n => ∫ ω, T n ω * (U n ω - a) ∂P) Filter.atTop (nhds 0) := by
    have hF : Filter.Tendsto (fun n => ∫⁻ ω, ‖T n ω * (U n ω - a) - 0‖ₑ ∂P) Filter.atTop
        (nhds 0) := by
      simpa only [eLpNorm_one_eq_lintegral_enorm, Pi.sub_apply, sub_zero] using hVit
    simpa using tendsto_integral_of_L1 (fun _ => (0 : ℂ)) aestronglyMeasurable_const
      (Filter.Eventually.of_forall hZint) hF
  -- `∫ T U = ∫ T (U - a) + a ∫ T` and `∫ T → 1`.
  have key : ∀ n, ∫ ω, T n ω * U n ω ∂P =
      ∫ ω, T n ω * (U n ω - a) ∂P + a * ∫ ω, T n ω ∂P := fun n => by
    have heq : (fun ω => T n ω * U n ω) =
        fun ω => T n ω * (U n ω - a) + a * T n ω := by
      funext ω; ring
    rw [heq, integral_add (hZint n) ((hTint n).const_mul a), integral_const_mul]
  have hsum := hZ.add (hT1.const_mul a)
  rw [zero_add, mul_one] at hsum
  exact hsum.congr fun n => (key n).symm

end LatticeProb.McLeish
