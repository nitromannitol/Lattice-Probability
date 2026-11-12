/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DFGPS.L2_1RadialMeas at commit fdb5cad; only the module paths of local imports are changed.
   Declarations, examples and checks that the copied results do not use are omitted. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DFGPS.L2_1Radial
import LatticeProb.Bonanno.LQGMetric.Papers.DFGPS.L2_3Tail
import LatticeProb.Bonanno.LQGMetric.Field.CircleAvgRate
import LatticeProb.Bonanno.LQGMetric.Field.CircleAvgAffine

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
For a whole-plane GFF `g`:

* `lintegral_enorm_circBump_sub_circleAvg_le`: for `r > 0`,
  `E|⟨g, σ_{z,r} * ψ_n⟩ − g_r(z)| ≤ (2/√r) t^n (1 − t)⁻¹` with `t = √(1/2)`; from
  `Var(⟨g, σ_{z,r} * (ψ_{j+1} − ψ_j)⟩) ≤ (4/r) 2^{-j}` (`CircleAvg.logCov_circDiff_succ_le`), the
  elementary bound `E|X| ≤ (E X²/B + B)/2`, and telescoping;
* `measurable_pair_circBump`: `(ω, r) ↦ ⟨g ω, σ_{z,r} * ψ_n⟩` is jointly measurable
  (Carathéodory, mathlib `measurable_uncurry_of_continuous_of_measurable`);
* `aemeasurable_circleAvgVersion`: a jointly continuous version `H` of the circle-average process
  is `P ⊗ dr`-a.e. measurable in `(ω, r)` (dyadic approximation from above in `r`).

These are the routine measure-theoretic steps behind DFGPS T:715–717 ("using the circle average
process we may write in polar coordinates"); own elementary arguments.
-/

noncomputable section

open MeasureTheory Set Filter Topology Metric
open scoped Real ENNReal

namespace LQGMetric.DFGPS

open CircleAvg

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {g : Ω → DistC}

/-- `(ω, r) ↦ ⟨g ω, σ_{z,r} * ψ_n⟩` is jointly measurable. -/
lemma measurable_pair_circBump (hg : Measurable g) (n : ℕ) (z : ℂ) :
    Measurable fun p : Ω × ℝ => g p.1 (circBump n z p.2) := by
  have h := measurable_uncurry_of_continuous_of_measurable
    (u := fun (r : ℝ) (ω : Ω) => g ω (circBump n z r)) (fun ω => ?_)
    (fun r => (measurable_distOn_apply _).comp hg)
  · exact h.comp measurable_swap
  · have : (fun r => g ω (circBump n z r)) =
        Real.circleAverage (fun x => g ω (bumpTest n x)) z :=
      funext fun r => (circleAverage_pairing _ n z r).symm
    rw [this]
    exact Real.Continuous.circleAverage ((g ω).continuous.comp (continuous_bumpTest n))

lemma abs_le_sq_div_add {x B : ℝ} (hB : 0 < B) : |x| ≤ (x ^ 2 / B + B) / 2 := by
  have h1 : 2 * B * |x| ≤ x ^ 2 + B ^ 2 := by nlinarith [sq_nonneg (|x| - B), sq_abs x]
  have e : (x ^ 2 / B + B) / 2 = (x ^ 2 + B ^ 2) / (2 * B) := by field_simp
  rw [e, le_div_iff₀ (by positivity)]
  linarith

/-- **`L¹` rate of the mollified circle averages.** -/
theorem lintegral_enorm_circBump_sub_circleAvg_le (hg : IsWholePlaneGFF g P) (z : ℂ) {r : ℝ}
    (hr : 0 < r) (n : ℕ) :
    ∫⁻ ω, ‖g ω (circBump n z r) - circleAvg (g ω) r z‖ₑ ∂P ≤
      ENNReal.ofReal (2 / √r) * ENNReal.ofReal (√(2⁻¹ : ℝ)) ^ n *
        (1 - ENNReal.ofReal (√(2⁻¹ : ℝ)))⁻¹ := by
  have := hg.gaussian.isProbabilityMeasure
  set s : ℝ := √(2⁻¹ : ℝ) with hs
  have hs0 : 0 < s := Real.sqrt_pos.2 (by norm_num)
  set X : ℕ → Ω → ℝ := fun k ω => g ω (circBump k z r)
  set D : ℕ → Ω → ℝ := fun j ω => g ω (circDiff (j + 1) z r j z r).1
  have hD : ∀ j ω, D j ω = X (j + 1) ω - X j ω := by
    intro j ω
    show g ω (circBump (j + 1) z r - circBump j z r) = _
    rw [map_sub]
  have hED : ∀ j, ∫⁻ ω, ‖D j ω‖ₑ ∂P ≤ ENNReal.ofReal (2 / √r * s ^ j) := by
    intro j
    set B := 2 / √r * s ^ j
    have hr' : 0 < √r := Real.sqrt_pos.2 hr
    have hB : 0 < B := by positivity
    have hB2 : B ^ 2 = 4 / r * 2⁻¹ ^ j := by
      simp only [B]
      rw [mul_pow, div_pow, Real.sq_sqrt hr.le, ← pow_mul, mul_comm j 2, pow_mul, hs,
        Real.sq_sqrt (by norm_num)]
      norm_num
    obtain ⟨hi, he⟩ := integral_sq_pair hg (circDiff (j + 1) z r j z r)
    have hle : ∫ ω, D j ω ^ 2 ∂P ≤ B ^ 2 := by
      rw [hB2]; exact he.trans_le (logCov_circDiff_succ_le hr z j)
    have hint : Integrable (fun ω => (D j ω ^ 2 / B + B) / 2) P :=
      ((hi.div_const B).add (integrable_const B)).div_const 2
    calc ∫⁻ ω, ‖D j ω‖ₑ ∂P ≤ ∫⁻ ω, ENNReal.ofReal ((D j ω ^ 2 / B + B) / 2) ∂P := by
          refine lintegral_mono fun ω => ?_
          rw [← ofReal_norm, Real.norm_eq_abs]
          exact ENNReal.ofReal_le_ofReal (abs_le_sq_div_add hB)
      _ = ENNReal.ofReal (∫ ω, (D j ω ^ 2 / B + B) / 2 ∂P) :=
          (ofReal_integral_eq_lintegral_ofReal hint
            (Eventually.of_forall fun ω => by positivity)).symm
      _ ≤ ENNReal.ofReal B := by
          refine ENNReal.ofReal_le_ofReal ?_
          rw [integral_div, integral_add (hi.div_const B) (integrable_const B), integral_div,
            integral_const, probReal_univ, one_smul]
          have : (∫ ω, D j ω ^ 2 ∂P) / B ≤ B := by
            rw [div_le_iff₀ hB]; nlinarith
          linarith
  have hpt : ∀ᵐ ω ∂P, ‖X n ω - circleAvg (g ω) r z‖ₑ ≤ ∑' j, ‖D (n + j) ω‖ₑ := by
    filter_upwards [ae_tendsto_mollAvg hg z hr] with ω ⟨a, ha⟩
    rw [circleAvg_eq_of_tendsto ha]
    have hX : Tendsto (fun k => X k ω) atTop (𝓝 a) :=
      ha.congr fun k => mollAvg_eq _ _ _ _
    have h2 : Tendsto (fun k => ‖X n ω - X (k + n) ω‖ₑ) atTop (𝓝 ‖X n ω - a‖ₑ) :=
      (continuous_enorm.tendsto _).comp
        (tendsto_const_nhds.sub (hX.comp (tendsto_add_atTop_nat n)))
    refine le_of_tendsto' h2 fun k => ?_
    have htel := Finset.sum_range_sub (fun i => X (n + i) ω) k
    simp only [add_zero] at htel
    calc ‖X n ω - X (k + n) ω‖ₑ = ‖∑ j ∈ Finset.range k, D (n + j) ω‖ₑ := by
          rw [← enorm_neg, neg_sub, add_comm k n, ← htel]
          congr 1
          refine Finset.sum_congr rfl fun j _ => ?_
          rw [hD]; rfl
      _ ≤ ∑ j ∈ Finset.range k, ‖D (n + j) ω‖ₑ := enorm_sum_le _ _
      _ ≤ ∑' j, ‖D (n + j) ω‖ₑ := ENNReal.sum_le_tsum _
  have hDm : ∀ j, Measurable (D j) := fun j => (measurable_distOn_apply _).comp hg.measurable
  calc ∫⁻ ω, ‖X n ω - circleAvg (g ω) r z‖ₑ ∂P ≤ ∫⁻ ω, ∑' j, ‖D (n + j) ω‖ₑ ∂P :=
        lintegral_mono_ae hpt
    _ = ∑' j, ∫⁻ ω, ‖D (n + j) ω‖ₑ ∂P :=
        lintegral_tsum fun j => (hDm (n + j)).enorm.aemeasurable
    _ ≤ ∑' j, ENNReal.ofReal (2 / √r * s ^ (n + j)) := ENNReal.tsum_le_tsum fun j => hED _
    _ = ENNReal.ofReal (2 / √r) * ENNReal.ofReal s ^ n * (1 - ENNReal.ofReal s)⁻¹ := by
        have e : ∀ j, ENNReal.ofReal (2 / √r * s ^ (n + j)) =
            ENNReal.ofReal (2 / √r) * ENNReal.ofReal s ^ n * ENNReal.ofReal s ^ j := by
          intro j
          rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_pow hs0.le, pow_add, mul_assoc]
        simp_rw [e]
        rw [ENNReal.tsum_mul_left, ENNReal.tsum_geometric]

/-- the dyadic point above `r` at level `m` -/
def dyUp (m : ℕ) (r : ℝ) : ℝ := ((⌊r * 2 ^ m⌋₊ : ℝ) + 1) / 2 ^ m

lemma measurable_dyUp (m : ℕ) : Measurable (dyUp m) := by
  unfold dyUp
  exact ((measurable_from_nat.comp (Nat.measurable_floor.comp (measurable_id.mul_const _))).add_const
    1).div_const _

lemma tendsto_dyUp {r : ℝ} (hr : 0 ≤ r) : Tendsto (fun m => dyUp m r) atTop (𝓝[>] r) := by
  have h2 : ∀ m : ℕ, (0 : ℝ) < 2 ^ m := fun m => by positivity
  have hlo : ∀ m, r < dyUp m r := by
    intro m
    unfold dyUp
    rw [lt_div_iff₀ (h2 m)]
    exact Nat.lt_floor_add_one _
  have hup : ∀ m, dyUp m r ≤ r + 2⁻¹ ^ m := by
    intro m
    unfold dyUp
    rw [div_le_iff₀ (h2 m), add_mul, inv_pow, inv_mul_cancel₀ (h2 m).ne']
    linarith [Nat.floor_le (mul_nonneg hr (h2 m).le)]
  have hlim : Tendsto (fun m : ℕ => r + (2⁻¹ : ℝ) ^ m) atTop (𝓝 r) := by
    simpa using tendsto_const_nhds.add
      (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 2⁻¹) (by norm_num))
  refine tendsto_nhdsWithin_iff.2 ⟨tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
    hlim (fun m => (hlo m).le) hup, Eventually.of_forall hlo⟩

/-- A jointly continuous version of the circle-average process is a.e. measurable in `(ω, r)`. -/
theorem aemeasurable_circleAvgVersion [SFinite P] {H : ℝ → ℂ → Ω → ℝ}
    (hg : Measurable g) (hH : IsCircleAvgVersion g P H) (z : ℂ) :
    AEMeasurable (fun p : Ω × ℝ => H p.2 z p.1) (P.prod (volume.restrict (Ioi (0 : ℝ)))) := by
  set ν : Measure ℝ := volume.restrict (Ioi (0 : ℝ))
  have hgood : ∀ᵐ ω ∂P, ∀ m k : ℕ,
      H (((k : ℝ) + 1) / 2 ^ m) z ω = circleAvg (g ω) (((k : ℝ) + 1) / 2 ^ m) z := by
    rw [ae_all_iff]; intro m; rw [ae_all_iff]; intro k
    exact hH.ae_eq _ (by positivity) z
  have happrox : ∀ m : ℕ, AEMeasurable (fun p : Ω × ℝ => H (dyUp m p.2) z p.1) (P.prod ν) := by
    intro m
    have hm : Measurable fun p : Ω × ℝ => ((g p.1, dyUp m p.2, z) : DistC × ℝ × ℂ) :=
      (hg.comp measurable_fst).prodMk (((measurable_dyUp m).comp measurable_snd).prodMk
        measurable_const)
    refine ⟨fun p => circleAvg (g p.1) (dyUp m p.2) z,
      measurable_circleAvg.comp (f := fun p : Ω × ℝ => ((g p.1, dyUp m p.2, z) : DistC × ℝ × ℂ))
        hm, ?_⟩
    filter_upwards [Measure.quasiMeasurePreserving_fst.ae hgood] with p hp
    show H (((⌊p.2 * 2 ^ m⌋₊ : ℝ) + 1) / 2 ^ m) z p.1 =
      circleAvg (g p.1) (((⌊p.2 * 2 ^ m⌋₊ : ℝ) + 1) / 2 ^ m) z
    exact hp m _
  refine aemeasurable_of_tendsto_metrizable_ae' happrox ?_
  filter_upwards [Measure.quasiMeasurePreserving_snd.ae (ae_restrict_mem measurableSet_Ioi)]
    with p hp
  have hp' : (0 : ℝ) < p.2 := hp
  have hc : ContinuousWithinAt (fun r => H r z p.1) (Ioi 0) p.2 :=
    ((hH.cont p.1).comp (continuous_id.prodMk continuous_const).continuousOn
      fun r hr => ⟨hr, mem_univ _⟩) p.2 hp'
  exact hc.tendsto.comp ((tendsto_dyUp hp'.le).mono_right (nhdsWithin_mono _ fun x hx =>
    lt_trans hp' hx))

end LQGMetric.DFGPS
