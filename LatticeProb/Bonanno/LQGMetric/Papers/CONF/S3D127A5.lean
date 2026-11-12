/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.CONF.S3D127A5 at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.CONF.S3D127A4
import LatticeProb.Bonanno.QuantumZipper.GFF.Defs

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# D127 N1, part 5: the heat identity for an open set (P-127A)

For an open `U` and `g` smooth with compact support in `U`, `t > 0`:

  `E[g(z + B_t); τ_U > t] − g(z) = ½ ∫₀ᵗ E[Δg(z + B_u); τ_U > u] du`   (`HeatA.open_identity`),

from `HeatA.closed_identity` on the closed inner sets `KilledHeat.innerSet U k`
(`{x | B(x, 1/(k+1)) ⊆ U}`), which contain `tsupport g` for large `k` and exhaust every compact
path image in `U` (monotone convergence of the staying events, dominated convergence).
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Laplacian
open scoped NNReal ENNReal

namespace LQGMetric
namespace CONF
namespace ZBM
namespace HeatA

open KilledHeat KilledHeatSq

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {B : ℝ≥0 → Ω → ℂ} {P : Measure Ω}

/-- The constants for a compactly supported smooth function. -/
lemma exists_bounds {g : ℂ → ℝ} (hg : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) g)
    (hc : HasCompactSupport g) : ∃ C, 0 ≤ C ∧ (∀ x, |g x| ≤ C) ∧ (∀ x, ‖fderiv ℝ g x‖ ≤ C) ∧
      (∀ x, ‖iteratedFDeriv ℝ 2 g x‖ ≤ C) ∧
      ∀ x y, ‖iteratedFDeriv ℝ 2 g x - iteratedFDeriv ℝ 2 g y‖ ≤ C * ‖x - y‖ := by
  obtain ⟨C0, h0⟩ := hg.continuous.bounded_above_of_compact_support hc
  obtain ⟨C1, h1⟩ := (hg.continuous_fderiv (by simp)).bounded_above_of_compact_support
    (hc.fderiv (𝕜 := ℝ))
  obtain ⟨C2, h2⟩ := (hg.continuous_iteratedFDeriv (m := 2) (by simp)).bounded_above_of_compact_support
    (hc.iteratedFDeriv 2)
  obtain ⟨C3, h3⟩ := (hg.continuous_iteratedFDeriv (m := 3) (by simp)).bounded_above_of_compact_support
    (hc.iteratedFDeriv 3)
  have hd : Differentiable ℝ fun x ↦ iteratedFDeriv ℝ 2 g x :=
    (hg.of_le (show ((3 : ℕ) : WithTop ℕ∞) ≤ _ by simp)).differentiable_iteratedFDeriv (m := 2)
      (by norm_num)
  refine ⟨|C0| + |C1| + |C2| + |C3|, by positivity, fun x ↦ ?_, fun x ↦ ?_, fun x ↦ ?_,
    fun x y ↦ ?_⟩
  · rw [← Real.norm_eq_abs]
    linarith [h0 x, le_abs_self C0, abs_nonneg C1, abs_nonneg C2, abs_nonneg C3]
  · linarith [h1 x, le_abs_self C1, abs_nonneg C0, abs_nonneg C2, abs_nonneg C3]
  · linarith [h2 x, le_abs_self C2, abs_nonneg C0, abs_nonneg C1, abs_nonneg C3]
  · have := Convex.norm_image_sub_le_of_norm_fderiv_le (f := fun x ↦ iteratedFDeriv ℝ 2 g x)
      (s := Set.univ) (C := C3) (fun x _ ↦ hd x) (fun x _ ↦ by
        rw [norm_fderiv_iteratedFDeriv]; exact h3 x) convex_univ (Set.mem_univ y)
        (Set.mem_univ x)
    refine this.trans (mul_le_mul_of_nonneg_right ?_ (norm_nonneg _))
    linarith [le_abs_self C3, abs_nonneg C0, abs_nonneg C1, abs_nonneg C2]

lemma eventually_subset_innerSet {K U : Set ℂ} (hK : IsCompact K) (hU : IsOpen U) (hKU : K ⊆ U) :
    ∀ᶠ k : ℕ in atTop, K ⊆ innerSet U k := by
  obtain ⟨δ, hδ, hth⟩ := hK.exists_thickening_subset_open hU hKU
  obtain ⟨k0, hk0⟩ := exists_nat_one_div_lt hδ
  filter_upwards [eventually_ge_atTop k0] with k hk x hx y hy
  refine hth (Metric.mem_thickening_iff.mpr ⟨x, hx, ?_⟩)
  rw [Metric.mem_ball] at hy
  have : 1 / ((k : ℝ) + 1) ≤ 1 / ((k0 : ℝ) + 1) :=
    one_div_le_one_div_of_le (by positivity) (by exact_mod_cast Nat.add_le_add_right hk 1)
  have := dist_comm x y
  linarith

lemma aestronglyMeasurable_indicator_stayAll (hB : IsPlanarBM B P) {Q : Set ℂ} (hQ : IsClosed Q)
    (z : ℂ) {u : ℝ≥0} (hu : 0 < u) :
    AEStronglyMeasurable (fun ω ↦ (stayAll Q B z u).indicator (1 : Ω → ℝ) ω) P := by
  refine aestronglyMeasurable_of_tendsto_ae atTop
    (f := fun n ω ↦ (stayUpTo Q B z u n (2 ^ n + 1)).indicator (1 : Ω → ℝ) ω)
    (fun n ↦ (aemeasurable_indicator_stayUpTo hB hQ.measurableSet z u n _).aestronglyMeasurable) ?_
  filter_upwards [hB.cont] with ω hc
  exact tendsto_indicator_grid hc hQ hu hu (fun n ω' hω' j hj ↦ hω' _ (gridT_le (by omega)))
    (fun n j hj hω ↦ hω j (by have := lt_pow_of_gridT_lt hj; omega))

/-- Staying in the inner sets converges to staying in `U`. -/
lemma tendsto_indicator_inner {ω : Ω} (hc : Continuous fun s ↦ B s ω) {U : Set ℂ}
    (hU : IsOpen U) (z : ℂ) (u : ℝ≥0) :
    Tendsto (fun k : ℕ ↦ (stayAll (innerSet U k) B z u).indicator (1 : Ω → ℝ) ω) atTop
      (𝓝 ((stayAll U B z u).indicator 1 ω)) := by
  by_cases hω : ω ∈ stayAll U B z u
  · have hK : IsCompact ((fun s ↦ z + B s ω) '' Set.Icc 0 u) :=
      isCompact_Icc.image (continuous_const.add hc)
    have hKU : (fun s ↦ z + B s ω) '' Set.Icc 0 u ⊆ U := by
      rintro _ ⟨s, hs, rfl⟩; exact hω s hs.2
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [eventually_subset_innerSet hK hU hKU] with k hk
    have : ω ∈ stayAll (innerSet U k) B z u := fun s hs ↦ hk ⟨s, ⟨zero_le, hs⟩, rfl⟩
    rw [Set.indicator_of_mem hω, Set.indicator_of_mem this]
  · rw [Set.indicator_of_notMem hω]
    refine tendsto_const_nhds.congr' (Eventually.of_forall fun k ↦ ?_)
    show _ = (stayAll (innerSet U k) B z u).indicator 1 ω
    rw [Set.indicator_of_notMem (fun (h : ω ∈ stayAll (innerSet U k) B z u) ↦ hω fun s hs ↦
      innerSet_subset U k
      ((show ∀ s ≤ u, z + B s ω ∈ innerSet U k from h) s hs))]

/-- Measurability in `u` of `E[Δg(z + B_u); in Q on [0, u]]` (as an a.e. limit of the grid
versions of `closed_identity`). -/
lemma aesm_closed_rhs (hB : IsPlanarBM B P) {Q : Set ℂ} (hQ : IsClosed Q) {g : ℂ → ℝ} {C : ℝ}
    (hC : 0 ≤ C) (hD2 : ∀ x, ‖iteratedFDeriv ℝ 2 g x‖ ≤ C)
    (hLip2 : ∀ x y, ‖iteratedFDeriv ℝ 2 g x - iteratedFDeriv ℝ 2 g y‖ ≤ C * ‖x - y‖)
    (z : ℂ) {t : ℝ≥0} (ht : 0 < t) :
    AEStronglyMeasurable (fun u : ℝ ↦ ∫ ω, (stayAll Q B z u.toNNReal).indicator 1 ω *
      Δ g (z + B u.toNNReal ω) ∂P) (volume.restrict (Set.uIoc (0 : ℝ) t)) := by
  have := hB.gauss.isProbabilityMeasure
  have hQm := hQ.measurableSet
  have ht' : (0 : ℝ) < t := by exact_mod_cast ht
  have hΔb := abs_lap_le hD2
  have hΔc : Continuous (Δ g) := (lipschitz_lap hC hLip2).continuous
  have hBu : ∀ u : ℝ≥0, AEMeasurable (fun ω ↦ z + B u ω) P := fun u ↦
    aemeasurable_const.add (aemeasurable_B hB u)
  set Φ : ℕ → ℝ → ℝ := fun n u ↦ ∫ ω, (stayUpTo Q B z t n ⌈u * 2 ^ n / t⌉₊).indicator 1 ω *
    Δ g (z + B u.toNNReal ω) ∂P with hΦ
  set f : ℕ → ℕ → ℝ → ℝ := fun n m u ↦ ∫ ω, (stayUpTo Q B z t n (m + 1)).indicator 1 ω *
    Δ g (z + B u.toNNReal ω) ∂P with hf
  have hfc : ∀ n m, Continuous (f n m) := fun n m ↦
    continuous_expect_lap hB (aemeasurable_indicator_stayUpTo hB hQm z t n _).aestronglyMeasurable
      (fun ω ↦ abs_indicator_one_le _ _) hC hD2 hLip2 z
  have hpiece : ∀ n m, ∀ u ∈ Set.Ioc (gridT t n m : ℝ) (gridT t n (m + 1)), Φ n u = f n m u := by
    intro n m u hu
    have h2 : (0 : ℝ) < 2 ^ n := by positivity
    have hc : ⌈u * 2 ^ n / t⌉₊ = m + 1 := by
      rw [Nat.ceil_eq_iff (by omega), Nat.add_sub_cancel]
      rw [gridT_coe, gridT_coe] at hu
      constructor
      · rw [lt_div_iff₀ ht']
        have := hu.1
        rw [div_lt_iff₀ h2] at this
        push_cast
        linarith
      · rw [div_le_iff₀ ht']
        have := hu.2
        rw [le_div_iff₀ h2] at this
        push_cast at this ⊢
        linarith
    simp only [hΦ, hf, hc]
  have hII : ∀ n m, IntervalIntegrable (Φ n) volume (gridT t n m) (gridT t n (m + 1)) := by
    intro n m
    refine ((hfc n m).intervalIntegrable _ _).congr_ae ?_
    rw [Set.uIoc_of_le (NNReal.coe_le_coe.mpr (gridT_mono (Nat.le_succ m)))]
    exact (ae_restrict_mem measurableSet_Ioc).mono fun u hu ↦ (hpiece n m u hu).symm
  refine aestronglyMeasurable_of_tendsto_ae atTop (f := Φ) (fun n ↦ ?_) ?_
  · have := IntervalIntegrable.trans_iterate (a := fun k ↦ (gridT t n k : ℝ))
      (n := 2 ^ n) (fun k _ ↦ hII n k)
    simp only [gridT_pow] at this
    rw [show ((gridT t n 0 : ℝ≥0) : ℝ) = 0 by simp [gridT]] at this
    exact this.def'.aestronglyMeasurable
  · filter_upwards [ae_restrict_mem measurableSet_uIoc] with u hu
    rw [Set.uIoc_of_le ht'.le] at hu
    have hu0 : 0 < u.toNNReal := Real.toNNReal_pos.mpr hu.1
    refine tendsto_integral_of_dominated_convergence (fun _ ↦ 2 * C)
      (fun n ↦ ((aemeasurable_indicator_stayUpTo hB hQm z t n _).mul
        (hΔc.measurable.comp_aemeasurable (hBu _))).aestronglyMeasurable)
      (integrable_const _) (fun n ↦ ae_of_all _ fun ω ↦ ?_) ?_
    · rw [Real.norm_eq_abs, abs_mul]
      calc _ ≤ 1 * (2 * C) := mul_le_mul (abs_indicator_one_le _ _) (hΔb _) (abs_nonneg _)
            zero_le_one
        _ = 2 * C := one_mul _
    · filter_upwards [hB.cont] with ω hc
      refine Tendsto.mul_const _ (tendsto_indicator_grid hc hQ ht hu0 (fun n ω' hω' j hj ↦ ?_)
        (fun n j hj hω ↦ hω j ?_))
      · refine hω' _ ?_
        have := Nat.lt_ceil.mp hj
        rw [lt_div_iff₀ ht'] at this
        rw [← NNReal.coe_le_coe, gridT_coe, Real.coe_toNNReal _ hu.1.le,
          div_le_iff₀ (by positivity)]
        linarith
      · rw [Nat.lt_ceil, lt_div_iff₀ ht']
        rw [← NNReal.coe_lt_coe, gridT_coe, Real.coe_toNNReal _ hu.1.le,
          div_lt_iff₀ (by positivity)] at hj
        linarith

/-- **The heat identity for an open set**, tested against `g ∈ C_c^∞(U)`. -/
theorem open_identity (hB : IsPlanarBM B P) {U : Set ℂ} (hU : IsOpen U) {g : ℂ → ℝ}
    (hg : g ∈ QuantumZipper.zeroSpace U) (z : ℂ) {t : ℝ≥0} (ht : 0 < t) :
    ∫ ω, (stayAll U B z t).indicator 1 ω * g (z + B t ω) ∂P - g z =
      1 / 2 * ∫ u in (0 : ℝ)..t,
        ∫ ω, (stayAll U B z u.toNNReal).indicator 1 ω * Δ g (z + B u.toNNReal ω) ∂P := by
  have := hB.gauss.isProbabilityMeasure
  obtain ⟨hgs, hgc, hgU⟩ := hg
  obtain ⟨C, hC, h0, h1, h2, hL2⟩ := exists_bounds hgs hgc
  have hg3 : ContDiff ℝ 3 g := hgs.of_le (by simp)
  have ht' : (0 : ℝ) < t := by exact_mod_cast ht
  have hΔb := abs_lap_le h2
  have hΔc : Continuous (Δ g) := (lipschitz_lap hC hL2).continuous
  have hBu : ∀ u : ℝ≥0, AEMeasurable (fun ω ↦ z + B u ω) P := fun u ↦
    aemeasurable_const.add (aemeasurable_B hB u)
  have hev := eventually_subset_innerSet hgc hU hgU
  have hid : ∀ᶠ k : ℕ in atTop,
      ∫ ω, (stayAll (innerSet U k) B z t).indicator 1 ω * g (z + B t ω) ∂P =
        g z + 1 / 2 * ∫ u in (0 : ℝ)..t, ∫ ω, (stayAll (innerSet U k) B z u.toNNReal).indicator 1 ω *
          Δ g (z + B u.toNNReal ω) ∂P := by
    filter_upwards [hev] with k hk
    have hgQ : ∀ x ∉ innerSet U k, g x = 0 := fun x hx ↦
      image_eq_zero_of_notMem_tsupport (fun h ↦ hx (hk h))
    rw [← closed_identity hB (isClosed_innerSet U k) hgQ hg3 hC h0 h1 h2 hL2 z ht]
    ring
  have hL : Tendsto (fun k : ℕ ↦ ∫ ω, (stayAll (innerSet U k) B z t).indicator 1 ω *
      g (z + B t ω) ∂P) atTop (𝓝 (∫ ω, (stayAll U B z t).indicator 1 ω * g (z + B t ω) ∂P)) := by
    refine tendsto_integral_of_dominated_convergence (fun _ ↦ C)
      (fun k ↦ (aestronglyMeasurable_indicator_stayAll hB (isClosed_innerSet U k) z ht).mul
        (hgs.continuous.measurable.comp_aemeasurable (hBu t)).aestronglyMeasurable)
      (integrable_const _) (fun k ↦ ae_of_all _ fun ω ↦ ?_) ?_
    · rw [Real.norm_eq_abs, abs_mul]
      calc _ ≤ 1 * C := mul_le_mul (abs_indicator_one_le _ _) (h0 _) (abs_nonneg _) zero_le_one
        _ = C := one_mul C
    · filter_upwards [hB.cont] with ω hc
      exact (tendsto_indicator_inner hc hU z t).mul_const _
  have hR : Tendsto (fun k : ℕ ↦ ∫ u in (0 : ℝ)..t, ∫ ω,
      (stayAll (innerSet U k) B z u.toNNReal).indicator 1 ω * Δ g (z + B u.toNNReal ω) ∂P) atTop
      (𝓝 (∫ u in (0 : ℝ)..t, ∫ ω, (stayAll U B z u.toNNReal).indicator 1 ω *
        Δ g (z + B u.toNNReal ω) ∂P)) := by
    refine intervalIntegral.tendsto_integral_filter_of_dominated_convergence (fun _ ↦ 2 * C)
      (Eventually.of_forall fun k ↦ aesm_closed_rhs hB (isClosed_innerSet U k) hC h2 hL2 z ht)
      (Eventually.of_forall fun k ↦ ae_of_all _ fun u _ ↦ ?_)
      intervalIntegrable_const (ae_of_all _ fun u hu ↦ ?_)
    · rw [Real.norm_eq_abs]
      refine abs_integral_le_of_abs_le fun ω ↦ ?_
      rw [abs_mul]
      calc _ ≤ 1 * (2 * C) := mul_le_mul (abs_indicator_one_le _ _) (hΔb _) (abs_nonneg _)
            zero_le_one
        _ = 2 * C := one_mul _
    · rw [Set.uIoc_of_le ht'.le] at hu
      have hu0 : 0 < u.toNNReal := Real.toNNReal_pos.mpr hu.1
      refine tendsto_integral_of_dominated_convergence (fun _ ↦ 2 * C)
        (fun k ↦ (aestronglyMeasurable_indicator_stayAll hB (isClosed_innerSet U k) z hu0).mul
          (hΔc.measurable.comp_aemeasurable (hBu _)).aestronglyMeasurable)
        (integrable_const _) (fun k ↦ ae_of_all _ fun ω ↦ ?_) ?_
      · rw [Real.norm_eq_abs, abs_mul]
        calc _ ≤ 1 * (2 * C) := mul_le_mul (abs_indicator_one_le _ _) (hΔb _) (abs_nonneg _)
              zero_le_one
          _ = 2 * C := one_mul _
      · filter_upwards [hB.cont] with ω hc
        exact (tendsto_indicator_inner hc hU z _).mul_const _
  have hR' := (hR.const_mul (1 / 2)).const_add (g z)
  have := tendsto_nhds_unique hL (hR'.congr' (hid.mono fun k hk ↦ hk.symm))
  linarith

end HeatA
end ZBM
end CONF
end LQGMetric
