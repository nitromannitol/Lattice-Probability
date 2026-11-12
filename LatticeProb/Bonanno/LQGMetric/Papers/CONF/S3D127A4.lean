/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.CONF.S3D127A4 at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.CONF.S3D127A3
import LatticeProb.Bonanno.LQGMetric.Field.KilledHeatSqOpen

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# D127 N1, part 4: the dyadic limit for a closed set (P-127A)

For a closed `Q`, `g ∈ C³` (bounded derivatives) vanishing off `Q` and `t > 0`:

  `E[g(z + B_t); z + B_s ∈ Q ∀ s ≤ t] − g(z) = ½ ∫₀ᵗ E[Δg(z + B_u); z + B_s ∈ Q ∀ s ≤ u] du`
  (`HeatA.closed_identity`),

from `HeatA.grid_identity` by letting the mesh `t/2ⁿ → 0` (dominated convergence in `ω` and in
`u`). Since `Q` is closed and the paths are continuous, "in `Q` at the grid times" decreases to
"in `Q` at all times" (`HeatA.tendsto_indicator_grid`); this replaces the square-specific
`KilledHeatSq.stayGrid_ae_eq` of the square proof (KilledHeatSqLim/SqOpen). Own elementary
assembly (DEC-127 N1).
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

lemma gridT_coe (t : ℝ≥0) (n j : ℕ) : (gridT t n j : ℝ) = j * t / 2 ^ n := by
  simp [gridT]

lemma tendsto_mesh (t : ℝ≥0) : Tendsto (fun n : ℕ ↦ (t : ℝ) / 2 ^ n) atTop (𝓝 0) := by
  have h := (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2)
    (by norm_num)).const_mul (t : ℝ)
  rw [mul_zero] at h
  refine h.congr fun n ↦ ?_
  rw [one_div, inv_pow, div_eq_mul_inv]

/-- A point of the path outside the closed set `Q` is seen on all fine enough grids. -/
lemma eventually_exists_grid_notMem {F : ℝ≥0 → ℂ} (hF : Continuous F) {Q : Set ℂ}
    (hQ : IsClosed Q) {t u s : ℝ≥0} (ht : 0 < t) (hu : 0 < u) (hsu : s ≤ u) (hs : F s ∉ Q) :
    ∀ᶠ n in atTop, ∃ j : ℕ, gridT t n j < u ∧ F (gridT t n j) ∉ Q := by
  obtain ⟨δ, hδ, hball⟩ := Metric.isOpen_iff.mp (hQ.isOpen_compl.preimage hF) s hs
  have ht' : (0 : ℝ) < t := by exact_mod_cast ht
  filter_upwards [(tendsto_mesh t).eventually (gt_mem_nhds hδ)] with n hn
  rcases eq_or_lt_of_le (show (0 : ℝ≥0) ≤ s from zero_le) with h0 | hpos
  · subst h0
    refine ⟨0, by simpa [gridT] using hu, ?_⟩
    rw [show gridT t n 0 = 0 by simp [gridT]]
    exact hs
  · have hs' : (0 : ℝ) < s := by exact_mod_cast hpos
    set x : ℝ := s * 2 ^ n / t with hx
    have hx0 : 0 < x := by positivity
    set j := ⌈x⌉₊ - 1 with hj
    have hj1 : 1 ≤ ⌈x⌉₊ := Nat.one_le_iff_ne_zero.mpr (Nat.ceil_pos.mpr hx0).ne'
    have hjc : (j : ℝ) = ⌈x⌉₊ - 1 := by rw [hj, Nat.cast_sub hj1]; simp
    have hlt : (j : ℝ) < x := by rw [hjc]; linarith [Nat.ceil_lt_add_one hx0.le]
    have hge : x - 1 ≤ j := by rw [hjc]; linarith [Nat.le_ceil x]
    have h2 : (0 : ℝ) < 2 ^ n := by positivity
    have hgs : (gridT t n j : ℝ) < s := by
      rw [gridT_coe, div_lt_iff₀ h2]
      rw [hx, lt_div_iff₀ ht'] at hlt
      linarith
    have hgs2 : (s : ℝ) - t / 2 ^ n ≤ gridT t n j := by
      rw [gridT_coe, sub_le_iff_le_add, ← add_div, le_div_iff₀ h2]
      rw [hx, sub_le_iff_le_add, div_le_iff₀ ht'] at hge
      nlinarith
    refine ⟨j, lt_of_lt_of_le (by exact_mod_cast hgs) hsu, hball ?_⟩
    rw [Metric.mem_ball, NNReal.dist_eq, abs_lt]
    constructor <;> linarith

/-- The grid staying events converge to the continuous-time staying event. -/
lemma tendsto_indicator_grid {ω : Ω} (hc : Continuous fun s ↦ B s ω) {Q : Set ℂ}
    (hQ : IsClosed Q) {z : ℂ} {t u : ℝ≥0} (ht : 0 < t) (hu : 0 < u) {E : ℕ → Set Ω}
    (h1 : ∀ n, stayAll Q B z u ⊆ E n)
    (h2 : ∀ n j, gridT t n j < u → ω ∈ E n → z + B (gridT t n j) ω ∈ Q) :
    Tendsto (fun n ↦ (E n).indicator (1 : Ω → ℝ) ω) atTop
      (𝓝 ((stayAll Q B z u).indicator 1 ω)) := by
  by_cases hω : ω ∈ stayAll Q B z u
  · simp only [Set.indicator_of_mem hω, Set.indicator_of_mem (h1 _ hω)]
    exact tendsto_const_nhds
  · rw [Set.indicator_of_notMem hω]
    simp only [stayAll, Set.mem_ofPred_eq, not_forall] at hω
    obtain ⟨s, hsu, hs⟩ := hω
    have hev := eventually_exists_grid_notMem (continuous_const.add hc) hQ ht hu hsu hs
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [hev] with n ⟨j, hj, hjQ⟩
    rw [Set.indicator_of_notMem (fun h ↦ hjQ (h2 n j hj h))]

/-- Hölder continuity of `u ↦ E[ξ Δg(z + B_u)]` (as in `dynkin_past`). -/
lemma continuous_expect_lap (hB : IsPlanarBM B P) {ξ : Ω → ℝ} (hξm : AEStronglyMeasurable ξ P)
    (hξb : ∀ ω, |ξ ω| ≤ 1) {g : ℂ → ℝ} {C : ℝ} (hC : 0 ≤ C)
    (hD2 : ∀ x, ‖iteratedFDeriv ℝ 2 g x‖ ≤ C)
    (hLip2 : ∀ x y, ‖iteratedFDeriv ℝ 2 g x - iteratedFDeriv ℝ 2 g y‖ ≤ C * ‖x - y‖) (z : ℂ) :
    Continuous fun u : ℝ ↦ ∫ ω, ξ ω * Δ g (z + B u.toNNReal ω) ∂P := by
  set K := 2 * C * (2 * QuantumZipper.gaussianAbsMoment 1) with hK
  have hK0 : 0 ≤ K := by have := QuantumZipper.gaussianAbsMoment_nonneg 1; positivity
  set f : ℝ → ℝ := fun u ↦ ∫ ω, ξ ω * Δ g (z + B u.toNNReal ω) ∂P with hf
  have hΔc : Continuous (Δ g) := (lipschitz_lap hC hLip2).continuous
  have hfb : ∀ u v : ℝ, u ≤ v → |f v - f u| ≤ K * Real.sqrt (v - u) := by
    intro u v huv
    have hv : v.toNNReal = u.toNNReal + (v.toNNReal - u.toNNReal) :=
      (add_tsub_cancel_of_le (Real.toNNReal_le_toNNReal huv)).symm
    have h1 := abs_integral_sub_le hB hξm hξb hΔc (abs_lap_le hD2) (abs_lap_sub_le hLip2) z
      u.toNNReal (v.toNNReal - u.toNNReal)
    rw [← hv] at h1
    refine h1.trans (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt (toNNReal_sub_le huv)) hK0)
  rw [Metric.continuous_iff]
  intro b ε hε
  refine ⟨(ε / (K + 1)) ^ 2, by positivity, fun a hab ↦ ?_⟩
  rw [Real.dist_eq] at hab ⊢
  have hsq : Real.sqrt |a - b| < ε / (K + 1) := by
    rw [show ε / (K + 1) = Real.sqrt ((ε / (K + 1)) ^ 2) from
      (Real.sqrt_sq (by positivity)).symm]
    exact Real.sqrt_lt_sqrt (abs_nonneg _) hab
  have hle : |f a - f b| ≤ K * Real.sqrt |a - b| := by
    rcases le_total a b with h | h
    · rw [abs_sub_comm, abs_sub_comm a b, abs_of_nonneg (sub_nonneg.mpr h)]
      exact hfb a b h
    · rw [abs_of_nonneg (sub_nonneg.mpr h)]
      exact hfb b a h
  calc |f a - f b| ≤ K * Real.sqrt |a - b| := hle
    _ ≤ K * (ε / (K + 1)) := mul_le_mul_of_nonneg_left hsq.le hK0
    _ < ε := by
        rw [mul_div_assoc', div_lt_iff₀ (by positivity)]
        nlinarith

lemma aemeasurable_indicator_stayUpTo (hB : IsPlanarBM B P) {Q : Set ℂ} (hQ : MeasurableSet Q)
    (z : ℂ) (t : ℝ≥0) (n M : ℕ) :
    AEMeasurable (fun ω ↦ (stayUpTo Q B z t n M).indicator (1 : Ω → ℝ) ω) P := by
  have e : (fun ω ↦ (stayUpTo Q B z t n M).indicator (1 : Ω → ℝ) ω) =
      fun ω ↦ 1 - ∑ m ∈ Finset.range M, (exitAt Q B z t n m).indicator 1 ω :=
    funext fun ω ↦ indicator_stayUpTo_eq _ z t n _ ω
  rw [e]
  exact aemeasurable_const.sub (Finset.aemeasurable_fun_sum _ fun m _ ↦
    aemeasurable_indicator_exitAt hB hQ z t n m)

lemma abs_integral_le_of_abs_le [IsProbabilityMeasure P] {f : Ω → ℝ} {c : ℝ}
    (h : ∀ ω, |f ω| ≤ c) : |∫ ω, f ω ∂P| ≤ c := by
  have := norm_integral_le_of_norm_le_const (μ := P) (f := f) (C := c)
    (ae_of_all _ fun ω ↦ by rw [Real.norm_eq_abs]; exact h ω)
  simpa [Real.norm_eq_abs] using this

lemma lt_pow_of_gridT_lt {t : ℝ≥0} {n j : ℕ} (h : gridT t n j < t) : j < 2 ^ n := by
  by_contra hj
  push Not at hj
  have h' := gridT_mono (t := t) (n := n) hj
  rw [gridT_pow] at h'
  exact absurd h (not_lt.mpr h')

/-- **The heat identity for a closed set** (dyadic limit of `grid_identity`). -/
theorem closed_identity (hB : IsPlanarBM B P) {Q : Set ℂ} (hQ : IsClosed Q)
    {g : ℂ → ℝ} (hgQ : ∀ x ∉ Q, g x = 0) (hg : ContDiff ℝ 3 g) {C : ℝ} (hC : 0 ≤ C)
    (hg0 : ∀ x, |g x| ≤ C) (hD1 : ∀ x, ‖fderiv ℝ g x‖ ≤ C)
    (hD2 : ∀ x, ‖iteratedFDeriv ℝ 2 g x‖ ≤ C)
    (hLip2 : ∀ x y, ‖iteratedFDeriv ℝ 2 g x - iteratedFDeriv ℝ 2 g y‖ ≤ C * ‖x - y‖)
    (z : ℂ) {t : ℝ≥0} (ht : 0 < t) :
    ∫ ω, (stayAll Q B z t).indicator 1 ω * g (z + B t ω) ∂P - g z =
      1 / 2 * ∫ u in (0 : ℝ)..t,
        ∫ ω, (stayAll Q B z u.toNNReal).indicator 1 ω * Δ g (z + B u.toNNReal ω) ∂P := by
  have := hB.gauss.isProbabilityMeasure
  have hQm := hQ.measurableSet
  have ht' : (0 : ℝ) < t := by exact_mod_cast ht
  have hΔb := abs_lap_le hD2
  have hΔc : Continuous (Δ g) := (lipschitz_lap hC hLip2).continuous
  have hBu : ∀ u : ℝ≥0, AEMeasurable (fun ω ↦ z + B u ω) P := fun u ↦
    aemeasurable_const.add (aemeasurable_B hB u)
  -- left side
  have hL : Tendsto (fun n ↦ ∫ ω, (stayUpTo Q B z t n (2 ^ n + 1)).indicator 1 ω *
      g (z + B t ω) ∂P) atTop
      (𝓝 (∫ ω, (stayAll Q B z t).indicator 1 ω * g (z + B t ω) ∂P)) := by
    refine tendsto_integral_of_dominated_convergence (fun _ ↦ C)
      (fun n ↦ ((aemeasurable_indicator_stayUpTo hB hQm z t n _).mul
        (hg.continuous.measurable.comp_aemeasurable (hBu t))).aestronglyMeasurable)
      (integrable_const _) (fun n ↦ ae_of_all _ fun ω ↦ ?_) ?_
    · rw [Real.norm_eq_abs, abs_mul]
      calc _ ≤ 1 * C := mul_le_mul (abs_indicator_one_le _ _) (hg0 _) (abs_nonneg _) zero_le_one
        _ = C := one_mul C
    · filter_upwards [hB.cont] with ω hc
      refine Tendsto.mul_const _ (tendsto_indicator_grid hc hQ ht ht
        (fun n ω' hω' j hj ↦ hω' _ (gridT_le (by omega))) (fun n j hj hω ↦ ?_))
      exact hω j (by have := lt_pow_of_gridT_lt hj; omega)
  -- right side
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
  have hsum : ∀ n, ∑ m ∈ Finset.range (2 ^ n), ∫ u in (gridT t n m : ℝ)..(gridT t n (m + 1)),
      f n m u = ∫ u in (0 : ℝ)..t, Φ n u := by
    intro n
    have e : ∀ m, ∫ u in (gridT t n m : ℝ)..(gridT t n (m + 1)), f n m u =
        ∫ u in (gridT t n m : ℝ)..(gridT t n (m + 1)), Φ n u := fun m ↦ by
      refine intervalIntegral.integral_congr_ae (ae_of_all _ fun u hu ↦ ?_)
      rw [Set.uIoc_of_le (NNReal.coe_le_coe.mpr (gridT_mono (Nat.le_succ m)))] at hu
      exact (hpiece n m u hu).symm
    simp_rw [e]
    rw [intervalIntegral.sum_integral_adjacent_intervals (a := fun k ↦ (gridT t n k : ℝ))
      (fun k _ ↦ hII n k)]
    simp [gridT_pow, gridT]
  have hR : Tendsto (fun n ↦ ∫ u in (0 : ℝ)..t, Φ n u) atTop
      (𝓝 (∫ u in (0 : ℝ)..t, ∫ ω, (stayAll Q B z u.toNNReal).indicator 1 ω *
        Δ g (z + B u.toNNReal ω) ∂P)) := by
    refine intervalIntegral.tendsto_integral_filter_of_dominated_convergence (fun _ ↦ 2 * C)
      (Eventually.of_forall fun n ↦ ?_) (Eventually.of_forall fun n ↦ ae_of_all _ fun u _ ↦ ?_)
      intervalIntegrable_const (ae_of_all _ fun u hu ↦ ?_)
    · have := IntervalIntegrable.trans_iterate (a := fun k ↦ (gridT t n k : ℝ))
        (n := 2 ^ n) (fun k _ ↦ hII n k)
      simp only [gridT_pow] at this
      rw [show ((gridT t n 0 : ℝ≥0) : ℝ) = 0 by simp [gridT]] at this
      exact this.def'.aestronglyMeasurable
    · rw [Real.norm_eq_abs]
      refine abs_integral_le_of_abs_le fun ω ↦ ?_
      rw [abs_mul]
      calc _ ≤ 1 * (2 * C) := mul_le_mul (abs_indicator_one_le _ _) (hΔb _) (abs_nonneg _)
            zero_le_one
        _ = 2 * C := one_mul _
    · rw [Set.uIoc_of_le ht'.le] at hu
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
          rw [← NNReal.coe_le_coe, gridT_coe, Real.coe_toNNReal _ hu.1.le, div_le_iff₀ (by positivity)]
          linarith
        · rw [Nat.lt_ceil, lt_div_iff₀ ht']
          rw [← NNReal.coe_lt_coe, gridT_coe, Real.coe_toNNReal _ hu.1.le,
            div_lt_iff₀ (by positivity)] at hj
          linarith
  have hgrid : ∀ n, ∫ ω, (stayUpTo Q B z t n (2 ^ n + 1)).indicator 1 ω * g (z + B t ω) ∂P =
      g z + 1 / 2 * ∫ u in (0 : ℝ)..t, Φ n u := by
    intro n
    rw [← hsum n, ← grid_identity hB hQm hgQ hg hC hg0 hD1 hD2 hLip2 z t n]
    ring
  simp only [hgrid] at hL
  have hR' := (hR.const_mul (1 / 2)).const_add (g z)
  have := tendsto_nhds_unique hL hR'
  linarith

end HeatA
end ZBM
end CONF
end LQGMetric
