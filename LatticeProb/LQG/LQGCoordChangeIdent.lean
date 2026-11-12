import LatticeProb.LQG.GMCDyadicLimit
import LatticeProb.LQG.LQGCoordChangeFixed

/-!
# The LQG limit along the scales `r 2^{-k}`

Let `h` be a whole-plane Gaussian free field with circle averages `h_ε(z)` and `0 < γ < 2`. The γ-LQG measure `μ`
is the almost sure vague limit of `m_ε = ε^{γ²/2} e^{γ h_ε(z)} dz` along the dyadic scales `ε = 2^{-k}`. For a fixed
`r > 0` the approximations `m_{r 2^{-k}}` converge vaguely to the same measure `μ`, almost surely, provided the
`L¹` increments between two scales of ratio in `[1/2, 1]` decay like a power of the larger scale
(`ScaleIncrementL1Bound`; for the ratio `1/2` this is `IsWholePlaneGFF.integral_abs_integral_increment_le_exp`).

The proof interleaves the scales: `τ_{2k} = 2^{-k}`, `τ_{2k+1} = r 2^{-k}` for `1/2 ≤ r ≤ 1`. Consecutive ratios lie in
`[1/2, 1]`, so the increments along `τ` are summable in `L¹` and `∫ g dm_{τ_n}` converges almost surely for every
`g` of a countable determining family. Hence `m_{τ_n}` converges vaguely; its even subsequence is the dyadic one,
whose limit is `μ`, so the odd subsequence `m_{r 2^{-k}}` converges vaguely to `μ`. A general `r > 0` reduces to
`r ∈ (1/2, 1]` by a shift of the index.

## Main results

* `LatticeProb.Gauss.ScaleIncrementL1Bound`: the scale-ratio `L¹` increment bound.
* `IsWholePlaneGFF.ae_exists_tendsto_integral_lqgApprox_of_scales`: almost sure convergence of `∫ g dm_{σ_n}` along
  every sequence of scales `σ_n ≤ 1` with ratios in `[1/2, 1]` and `∑ σ_n^c < ∞`.
* `IsWholePlaneGFF.ae_tendsto_integral_lqgApprox_mul`: almost surely, `m_{r 2^{-k}} → μ` vaguely, for every `r > 0`.
* `IsWholePlaneGFF.exists_coordChange_of_scaleIncrementL1Bound`: the LQG coordinate change rule for the map
  `x ↦ (x - z) / r`, for one `r > 0` and one `z`.
-/

open MeasureTheory ProbabilityTheory Real Function Filter Topology
open scoped ENNReal NNReal

namespace LatticeProb.LQG

/-- The interleaved scales `τ_{2k} = 2^{-k}`, `τ_{2k+1} = r 2^{-k}`. -/
noncomputable def interleavedScale (r : ℝ) (n : ℕ) : ℝ :=
  if Even n then dyadicScale (n / 2) else r * dyadicScale (n / 2)

theorem interleavedScale_two_mul (r : ℝ) (k : ℕ) : interleavedScale r (2 * k) = dyadicScale k := by
  rw [interleavedScale, ite_eq_left (even_two_mul k), Nat.mul_div_cancel_left k two_pos]

theorem interleavedScale_two_mul_add_one (r : ℝ) (k : ℕ) :
    interleavedScale r (2 * k + 1) = r * dyadicScale k := by
  have hk : (2 * k + 1) / 2 = k := by omega
  rw [interleavedScale, ite_eq_right (Nat.not_even_iff_odd.mpr (odd_two_mul_add_one k)), hk]

theorem dyadicScale_pos' (k : ℕ) : 0 < dyadicScale k := pow_pos (by norm_num) k

theorem interleavedScale_pos {r : ℝ} (hr : 0 < r) (n : ℕ) : 0 < interleavedScale r n := by
  unfold interleavedScale
  split_ifs
  · exact dyadicScale_pos' _
  · exact mul_pos hr (dyadicScale_pos' _)

theorem interleavedScale_zero (r : ℝ) : interleavedScale r 0 = 1 := by
  simpa [dyadicScale] using interleavedScale_two_mul r 0

/-- Consecutive interleaved scales have ratio in `[1/2, 1]` when `1/2 ≤ r ≤ 1`. -/
theorem interleavedScale_succ {r : ℝ} (hr1 : 1 / 2 ≤ r) (hr2 : r ≤ 1) (n : ℕ) :
    interleavedScale r n / 2 ≤ interleavedScale r (n + 1) ∧ interleavedScale r (n + 1) ≤ interleavedScale r n := by
  obtain ⟨k, rfl | rfl⟩ := Nat.even_or_odd' n
  · rw [interleavedScale_two_mul_add_one, interleavedScale_two_mul]
    have := dyadicScale_pos' k
    constructor <;> nlinarith
  · rw [show 2 * k + 1 + 1 = 2 * (k + 1) by ring, interleavedScale_two_mul, interleavedScale_two_mul_add_one]
    have hd : dyadicScale (k + 1) = dyadicScale k / 2 := by
      rw [dyadicScale, dyadicScale, pow_succ, div_eq_mul_inv]
    rw [hd]
    have := dyadicScale_pos' k
    constructor <;> nlinarith

theorem summable_interleavedScale_rpow {r : ℝ} (hr : 0 < r) {c : ℝ} (hc : 0 < c) :
    Summable fun n => interleavedScale r n ^ c := by
  have he : Summable fun k : ℕ => dyadicScale k ^ c := by
    refine (Gauss.summable_exp_log_dyadicScale_mul hc).congr fun k => ?_
    rw [Real.rpow_def_of_pos (dyadicScale_pos' k)]
  refine Summable.even_add_odd ?_ ?_
  · simpa only [interleavedScale_two_mul] using he
  · simp only [interleavedScale_two_mul_add_one]
    refine (he.mul_left (r ^ c)).congr fun k => ?_
    rw [Real.mul_rpow hr.le (dyadicScale_pos' k).le]

end LatticeProb.LQG

namespace LatticeProb.Gauss

/-- **Scale-ratio `L¹` increment bound.** For every continuous compactly supported weight `g` there are a radius
`R > 0` with `‖z‖ + 1 ≤ R` on the support of `g` and constants `K` and `c > 0` such that, for `0 < ε ≤ 1` and
`ε / 2 ≤ s ≤ ε`,
`E |∫ g(z) (s^{γ²/2} e^{γ (h_s(z) - h_R(0))} - ε^{γ²/2} e^{γ (h_ε(z) - h_R(0))}) dz| ≤ K ε^c`.
For `s = ε / 2` this is `IsWholePlaneGFF.integral_abs_integral_increment_le_exp`. -/
def ScaleIncrementL1Bound {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (γ : ℝ)
    (hcirc : Ω → ℝ → ℂ → ℝ) : Prop :=
  ∀ g : ℂ → ℝ, Continuous g → HasCompactSupport g → ∃ R K c : ℝ, 0 < R ∧ 0 < c ∧
    (∀ z, g z ≠ 0 → ‖z‖ + 1 ≤ R) ∧ ∀ ε s : ℝ, 0 < ε → ε ≤ 1 → ε / 2 ≤ s → s ≤ ε →
      ∫ ω, |∫ z, g z * (s ^ (γ ^ 2 / 2) * rexp (γ * (hcirc ω s z - hcirc ω R 0)) -
        ε ^ (γ ^ 2 / 2) * rexp (γ * (hcirc ω ε z - hcirc ω R 0)))| ∂P ≤ K * ε ^ c

namespace IsWholePlaneGFF

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}

/-- Integrability of the increment between the recentred normalized exponentials at two radii `s` and `ε`. -/
theorem integrable_integral_increment_scales (hh : IsWholePlaneGFF P hC hcirc) {s ε R : ℝ} (hs : 0 < s)
    (hε : 0 < ε) (hR : 0 < R) (ν : Measure ℂ) [SFinite ν] {g : ℂ → ℝ} (hgm : Measurable g)
    (hg : Integrable g ν) (hgs : ∀ z, g z ≠ 0 → ‖z‖ + s ≤ R) (hgε : ∀ z, g z ≠ 0 → ‖z‖ + ε ≤ R) (γ : ℝ) :
    Integrable (fun ω => ∫ z, g z * (s ^ (γ ^ 2 / 2) * rexp (γ * (hcirc ω s z - hcirc ω R 0)) -
        ε ^ (γ ^ 2 / 2) * rexp (γ * (hcirc ω ε z - hcirc ω R 0))) ∂ν) P := by
  have := hh.isProbabilityMeasure
  obtain ⟨H, -, hHm, hHae⟩ := hh.exists_jointlyMeasurable_circleAverage
  have h1 := (hh.integrable_prod_mul_exp_recentred hHm hHae hs hR ν hgm hg hgs γ).const_mul (s ^ (γ ^ 2 / 2))
  have h2 := (hh.integrable_prod_mul_exp_recentred hHm hHae hε hR ν hgm hg hgε γ).const_mul (ε ^ (γ ^ 2 / 2))
  have h3 := (h1.sub h2).integral_prod_left
  refine h3.congr ?_
  filter_upwards [hHae] with ω hω
  refine integral_congr_ae (ae_of_all _ fun z => ?_)
  simp only [Pi.sub_apply, hω]
  ring

/-- **Almost sure convergence along scales with ratios in `[1/2, 1]`.** If the `L¹` increments between the scales
`s` and `ε`, `ε / 2 ≤ s ≤ ε ≤ 1`, are at most `K ε^c`, then for every sequence of scales `σ_n ≤ 1` with
`σ_n / 2 ≤ σ_{n+1} ≤ σ_n` and `∑ σ_n^c < ∞`, almost surely `∫ g d(σ_n^{γ²/2} e^{γ h_{σ_n}(z)} dz)` converges. -/
theorem ae_exists_tendsto_integral_lqgApprox_of_scales (hh : IsWholePlaneGFF P hC hcirc) (γ : ℝ)
    {g : ℂ → ℝ} (hgc : Continuous g) (hgs : HasCompactSupport g) {R K c : ℝ} (hR : 0 < R)
    (hgR : ∀ z, g z ≠ 0 → ‖z‖ + 1 ≤ R)
    (hB : ∀ ε s : ℝ, 0 < ε → ε ≤ 1 → ε / 2 ≤ s → s ≤ ε →
      ∫ ω, |∫ z, g z * (s ^ (γ ^ 2 / 2) * rexp (γ * (hcirc ω s z - hcirc ω R 0)) -
        ε ^ (γ ^ 2 / 2) * rexp (γ * (hcirc ω ε z - hcirc ω R 0)))| ∂P ≤ K * ε ^ c)
    {σ : ℕ → ℝ} (hσ0 : ∀ n, 0 < σ n) (hσ1 : σ 0 ≤ 1)
    (hσs : ∀ n, σ n / 2 ≤ σ (n + 1) ∧ σ (n + 1) ≤ σ n) (hσc : Summable fun n => σ n ^ c) :
    ∀ᵐ ω ∂P, ∃ ℓ : ℝ,
      Tendsto (fun n : ℕ => ∫ z, g z ∂(LQG.lqgApprox γ (hcirc ω) (σ n))) atTop (𝓝 ℓ) := by
  have := hh.isProbabilityMeasure
  have hg : Integrable g := hgc.integrable_of_hasCompactSupport hgs
  have hgm : Measurable g := hgc.measurable
  have hσle : ∀ n, σ n ≤ 1 := by
    intro n
    induction n with
    | zero => exact hσ1
    | succ n ih => exact (hσs n).2.trans ih
  have hgσ : ∀ n z, g z ≠ 0 → ‖z‖ + σ n ≤ R := fun n z hz => by linarith [hgR z hz, hσle n]
  obtain ⟨H, hHc, -, hHae⟩ := hh.exists_jointlyMeasurable_circleAverage
  have hcont : ∀ᵐ ω ∂P, ∀ r, 0 < r → Continuous (hcirc ω r) := by
    filter_upwards [hHae] with ω hω r hr
    rw [← funext (hω r)]
    exact hHc ω r hr
  have hzint : ∀ ω, (∀ r, 0 < r → Continuous (hcirc ω r)) → ∀ r, 0 < r → ∀ c : ℝ,
      Integrable (fun z => g z * (c * rexp (γ * (hcirc ω r z - hcirc ω R 0)))) := fun ω hω r hr c =>
    (hgc.mul (continuous_const.mul (Real.continuous_exp.comp (continuous_const.mul
      ((hω r hr).sub continuous_const))))).integrable_of_hasCompactSupport hgs.mul_right
  set Y : ℕ → Ω → ℝ := fun n ω => ∫ z, g z * (σ n ^ (γ ^ 2 / 2) *
    rexp (γ * (hcirc ω (σ n) z - hcirc ω R 0))) with hYdef
  have heqk : ∀ n, ∀ᵐ ω ∂P, Y (n + 1) ω - Y n ω = ∫ z, g z *
      (σ (n + 1) ^ (γ ^ 2 / 2) * rexp (γ * (hcirc ω (σ (n + 1)) z - hcirc ω R 0)) -
        σ n ^ (γ ^ 2 / 2) * rexp (γ * (hcirc ω (σ n) z - hcirc ω R 0))) := by
    intro n
    filter_upwards [hcont] with ω hω
    simp only [hYdef]
    rw [← integral_sub (hzint ω hω _ (hσ0 _) _) (hzint ω hω _ (hσ0 n) _)]
    refine integral_congr_ae (ae_of_all _ fun z => ?_)
    ring
  have hint : ∀ n, Integrable (fun ω => Y (n + 1) ω - Y n ω) P := fun n =>
    (hh.integrable_integral_increment_scales (hσ0 _) (hσ0 n) hR volume hgm hg (hgσ _) (hgσ n) γ).congr
      ((heqk n).mono fun ω hω => hω.symm)
  have hbd : ∀ n, ∫ ω, |Y (n + 1) ω - Y n ω| ∂P ≤ K * σ n ^ c := fun n => by
    rw [integral_congr_ae ((heqk n).mono fun ω hω => by rw [hω])]
    exact hB _ _ (hσ0 n) (hσle n) (hσs n).1 (hσs n).2
  have hV := SummableIncrements.ae_exists_tendsto_of_integral_abs_sub_le hint hbd (hσc.mul_left K)
  filter_upwards [hV, hcont] with ω hω hωc
  obtain ⟨ℓ, hℓ⟩ := hω
  refine ⟨rexp (γ * hcirc ω R 0) * ℓ, (hℓ.const_mul _).congr fun n => ?_⟩
  have hdens : Measurable fun z => ENNReal.ofReal (σ n ^ (γ ^ 2 / 2) * rexp (γ * hcirc ω (σ n) z)) :=
    ENNReal.measurable_ofReal.comp (measurable_const.mul (Real.measurable_exp.comp
      (measurable_const.mul (hωc _ (hσ0 n)).measurable)))
  rw [LQG.lqgApprox, integral_withDensity_eq_integral_toReal_smul hdens
    (ae_of_all _ fun _ => ENNReal.ofReal_lt_top), hYdef, ← integral_const_mul]
  refine integral_congr_ae (ae_of_all _ fun z => ?_)
  simp only [smul_eq_mul]
  rw [ENNReal.toReal_ofReal (mul_nonneg (Real.rpow_nonneg (hσ0 n).le _) (Real.exp_pos _).le), mul_sub,
    Real.exp_sub]
  field_simp

/-- **The limit along `r 2^{-k}`, `1/2 ≤ r ≤ 1`.** Given the scale-ratio `L¹` increment bound, almost surely the
approximations at the scales `r 2^{-k}` converge vaguely to the γ-LQG measure. -/
theorem ae_tendsto_integral_lqgApprox_mul_of_mem_Icc (hh : IsWholePlaneGFF P hC hcirc) {γ : ℝ}
    (hB : ScaleIncrementL1Bound P γ hcirc) {μ : Ω → Measure ℂ} (hμ : LQG.IsLQGMeasure P γ hcirc μ) {r : ℝ}
    (hr1 : 1 / 2 ≤ r) (hr2 : r ≤ 1) :
    ∀ᵐ ω ∂P, ∀ f : ℂ → ℝ, Continuous f → HasCompactSupport f →
      Tendsto (fun k : ℕ => ∫ x, f x ∂(LQG.lqgApprox γ (hcirc ω) (r * LQG.dyadicScale k))) atTop
        (𝓝 (∫ x, f x ∂(μ ω))) := by
  classical
  have hr : 0 < r := by linarith
  obtain ⟨D, hDc, hDcc, hD⟩ := LatticeProb.VagueLimit.exists_countable_determining_vague_limit (X := ℂ)
  have : Countable D := hDc.to_subtype
  have hall : ∀ᵐ ω ∂P, ∀ g : D, ∃ ℓ : ℝ, Tendsto (fun n : ℕ =>
      ∫ z, (g : ℂ → ℝ) z ∂(LQG.lqgApprox γ (hcirc ω) (LQG.interleavedScale r n))) atTop (𝓝 ℓ) :=
    ae_all_iff.mpr fun g => by
      obtain ⟨R, K, c, hR, hc, hgR, hBg⟩ := hB g (hDcc g g.2).1 (hDcc g g.2).2
      exact hh.ae_exists_tendsto_integral_lqgApprox_of_scales γ (hDcc g g.2).1 (hDcc g g.2).2 hR hgR hBg
        (LQG.interleavedScale_pos hr) (LQG.interleavedScale_zero r).le (LQG.interleavedScale_succ hr1 hr2)
        (LQG.summable_interleavedScale_rpow hr hc)
  obtain ⟨H, hHc, -, hHae⟩ := hh.exists_jointlyMeasurable_circleAverage
  filter_upwards [hall, hHae, hμ] with ω hω hωH hωμ
  have hfin : ∀ n, IsFiniteMeasureOnCompacts (LQG.lqgApprox γ (hcirc ω) (LQG.interleavedScale r n)) :=
    fun n => by
      have hcn : Continuous (hcirc ω (LQG.interleavedScale r n)) := by
        rw [← funext (hωH _)]
        exact hHc ω _ (LQG.interleavedScale_pos hr n)
      have : IsLocallyFiniteMeasure (LQG.lqgApprox γ (hcirc ω) (LQG.interleavedScale r n)) := by
        unfold LQG.lqgApprox
        exact IsLocallyFiniteMeasure.withDensity_ofReal
          (continuous_const.mul (Real.continuous_exp.comp (continuous_const.mul hcn)))
      infer_instance
  obtain ⟨ν, -, hν⟩ := hD _ hfin fun g hg => hω ⟨g, hg⟩
  intro f hfc hfs
  have hev : Tendsto (fun k : ℕ => 2 * k) atTop atTop :=
    tendsto_atTop_atTop.mpr fun b => ⟨b, fun k hk => by omega⟩
  have hodd : Tendsto (fun k : ℕ => 2 * k + 1) atTop atTop :=
    tendsto_atTop_atTop.mpr fun b => ⟨b, fun k hk => by omega⟩
  have h1 : Tendsto (fun k : ℕ => ∫ x, f x ∂(LQG.lqgApprox γ (hcirc ω) (LQG.dyadicScale k))) atTop
      (𝓝 (∫ x, f x ∂ν)) := by
    have := (hν f hfc hfs).comp hev
    simpa only [Function.comp_def, LQG.interleavedScale_two_mul] using this
  have heq : ∫ x, f x ∂ν = ∫ x, f x ∂(μ ω) := tendsto_nhds_unique h1 (hωμ.tendsto_integral f hfc hfs)
  rw [← heq]
  have := (hν f hfc hfs).comp hodd
  simpa only [Function.comp_def, LQG.interleavedScale_two_mul_add_one] using this

/-- **The limit along `r 2^{-k}`.** Given the scale-ratio `L¹` increment bound, for every `r > 0`, almost surely
the approximations at the scales `r 2^{-k}` converge vaguely to the γ-LQG measure. -/
theorem ae_tendsto_integral_lqgApprox_mul (hh : IsWholePlaneGFF P hC hcirc) {γ : ℝ}
    (hB : ScaleIncrementL1Bound P γ hcirc) {μ : Ω → Measure ℂ} (hμ : LQG.IsLQGMeasure P γ hcirc μ) {r : ℝ}
    (hr : 0 < r) :
    ∀ᵐ ω ∂P, ∀ f : ℂ → ℝ, Continuous f → HasCompactSupport f →
      Tendsto (fun k : ℕ => ∫ x, f x ∂(LQG.lqgApprox γ (hcirc ω) (r * LQG.dyadicScale k))) atTop
        (𝓝 (∫ x, f x ∂(μ ω))) := by
  obtain ⟨n, hn1, hn2⟩ := exists_mem_Ioc_zpow hr (by norm_num : (1 : ℝ) < 2)
  have h2pos : (0 : ℝ) < 2 ^ (n + 1) := zpow_pos two_pos _
  set r₀ := r / 2 ^ (n + 1) with hr₀
  have hr1 : 1 / 2 ≤ r₀ := by
    rw [hr₀, le_div_iff₀ h2pos, zpow_add_one₀ two_ne_zero]
    linarith
  have hr2 : r₀ ≤ 1 := by
    rw [hr₀, div_le_one h2pos]
    exact hn2
  filter_upwards [hh.ae_tendsto_integral_lqgApprox_mul_of_mem_Icc hB hμ hr1 hr2] with ω hω f hfc hfs
  have hu : Tendsto (fun k : ℕ => ((k : ℤ) - (n + 1)).toNat) atTop atTop :=
    tendsto_atTop_atTop.mpr fun b => ⟨(b + n + 1).toNat, fun k hk => by omega⟩
  refine ((hω f hfc hfs).comp hu).congr' ?_
  filter_upwards [eventually_ge_atTop (n + 1).toNat] with k hk
  have hj : ((((k : ℤ) - (n + 1)).toNat : ℕ) : ℤ) = k - (n + 1) := Int.toNat_of_nonneg (by omega)
  have e1 : ∀ j : ℕ, LQG.dyadicScale j = (2 : ℝ) ^ (-(j : ℤ)) := fun j => by
    rw [LQG.dyadicScale, zpow_neg, zpow_natCast, inv_pow]
  have hsc : r₀ * LQG.dyadicScale (((k : ℤ) - (n + 1)).toNat) = r * LQG.dyadicScale k := by
    rw [e1, e1, hj, show -((k : ℤ) - (n + 1)) = -(k : ℤ) + (n + 1) by ring, zpow_add₀ two_ne_zero, hr₀]
    field_simp
  simp only [Function.comp_apply, hsc]

/-- **LQG coordinate change for `x ↦ (x - z) / r`.** Given the scale-ratio `L¹` increment bound, for a whole-plane
GFF `h`, its γ-LQG measure `μ`, `r > 0` and `z ∈ ℂ`, there are a whole-plane GFF `h''` (the recentred field
`h(r · + z) - h_r(z)`), its γ-LQG measure `μ''` and an almost surely positive finite random constant `c` with
`(x ↦ (x - z) / r)_* μ = c μ''` almost surely. -/
theorem exists_coordChange_of_scaleIncrementL1Bound {γ : ℝ} (hγ : 0 < γ) (hG : IsWholePlaneGFF P hC hcirc)
    (hB : ScaleIncrementL1Bound P γ hcirc) {μ : Ω → Measure ℂ} (hμ : LQG.IsLQGMeasure P γ hcirc μ) {r : ℝ}
    (hr : 0 < r) (z : ℂ) :
    ∃ (hC'' : Ω → (ℂ → ℝ) → ℝ) (hcirc'' : Ω → ℝ → ℂ → ℝ) (μ'' : Ω → Measure ℂ) (c : Ω → ℝ≥0∞),
      IsWholePlaneGFF P hC'' hcirc'' ∧ LQG.IsLQGMeasure P γ hcirc'' μ'' ∧
      ∀ᵐ ω ∂P, c ω ≠ 0 ∧ c ω ≠ ∞ ∧ (μ ω).map (fun x => (x - z) / (r : ℂ)) = c ω • μ'' ω :=
  LQG.LQGCoordChangeFixed.exists_coordChange_of_tendsto hγ hG hμ hr z (hG.ae_tendsto_integral_lqgApprox_mul hB hμ hr)

end IsWholePlaneGFF

end LatticeProb.Gauss
