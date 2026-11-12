/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.CONF.S3D127A3 at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.CONF.S3D127A2

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# D127 N1, part 3: the grid-time telescoping identity (P-127A)

For a measurable `Q ⊆ ℂ` and `g ∈ C³` (bounded derivatives) vanishing off `Q`, and grid times
`t_m = m t / 2ⁿ`:

  `E[g(z + B_t); z + B_{t_j} ∈ Q ∀ j ≤ 2ⁿ] − g(z)
     = ½ ∑_{m < 2ⁿ} ∫_{t_m}^{t_{m+1}} E[Δg(z + B_u); z + B_{t_j} ∈ Q ∀ j ≤ m] du`
  (`HeatA.grid_identity`).

This is the scheme of `KilledHeatSq.integral_stayUpTo_sqMode` (KilledHeatSqStop) with
`HeatA.dynkin_past` in place of the sine-mode martingale; the exit terms vanish exactly because
`g = 0` off `Q` (DEC-127 N1). Own elementary assembly.
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

/-- In `Q` at the coordinates `0, …, m` of a coordinate vector. -/
def staySet (Q : Set ℂ) (z : ℂ) (m : ℕ) : Set (Bool × ℕ → ℝ) :=
  {y | ∀ j ≤ m, z + toC (fun b ↦ y (b, j)) ∈ Q}

lemma measurableSet_staySet {Q : Set ℂ} (hQ : MeasurableSet Q) (z : ℂ) (m : ℕ) :
    MeasurableSet (staySet Q z m) := by
  have e : staySet Q z m = ⋂ j : ℕ, ⋂ (_ : j ≤ m), {y | z + toC (fun b ↦ y (b, j)) ∈ Q} := by
    ext y; simp [staySet]
  rw [e]
  exact MeasurableSet.iInter fun j ↦ MeasurableSet.iInter fun _ ↦
    (measurable_const.add (measurable_toC_slice j)) hQ

lemma indicator_staySet_pastVec (Q : Set ℂ) (z : ℂ) (t : ℝ≥0) (n m : ℕ) (ω : Ω) :
    (staySet Q z m).indicator (1 : (Bool × ℕ → ℝ) → ℝ)
        (pastVec B (fun j ↦ gridT t n (min j m)) ω) =
      (stayUpTo Q B z t n (m + 1)).indicator 1 ω := by
  have hc : ∀ j, toC (fun b ↦ pastVec B (fun j ↦ gridT t n (min j m)) ω (b, j)) =
      B (gridT t n (min j m)) ω := fun j ↦ toC_coordProc B _ ω
  have hiff : pastVec B (fun j ↦ gridT t n (min j m)) ω ∈ staySet Q z m ↔
      ω ∈ stayUpTo Q B z t n (m + 1) := by
    simp only [staySet, Set.mem_setOf_eq, hc, stayUpTo]
    constructor
    · intro h1 j hj
      simpa [min_eq_left (Nat.lt_succ_iff.mp hj)] using h1 j (Nat.lt_succ_iff.mp hj)
    · intro h1 j hj
      simpa [min_eq_left hj] using h1 j (Nat.lt_succ_iff.mpr hj)
  by_cases h : ω ∈ stayUpTo Q B z t n (m + 1)
  · simp [Set.indicator_of_mem h, Set.indicator_of_mem (hiff.mpr h)]
  · rw [Set.indicator_of_notMem h, Set.indicator_of_notMem (fun h' ↦ h (hiff.mp h'))]

/-- **Grid telescoping** (exit terms vanish since `g = 0` off `Q`). -/
theorem grid_identity (hB : IsPlanarBM B P) {Q : Set ℂ} (hQ : MeasurableSet Q)
    {g : ℂ → ℝ} (hgQ : ∀ x ∉ Q, g x = 0) (hg : ContDiff ℝ 3 g) {C : ℝ} (hC : 0 ≤ C)
    (hg0 : ∀ x, |g x| ≤ C) (hD1 : ∀ x, ‖fderiv ℝ g x‖ ≤ C)
    (hD2 : ∀ x, ‖iteratedFDeriv ℝ 2 g x‖ ≤ C)
    (hLip2 : ∀ x y, ‖iteratedFDeriv ℝ 2 g x - iteratedFDeriv ℝ 2 g y‖ ≤ C * ‖x - y‖)
    (z : ℂ) (t : ℝ≥0) (n : ℕ) :
    ∫ ω, (stayUpTo Q B z t n (2 ^ n + 1)).indicator 1 ω * g (z + B t ω) ∂P - g z =
      1 / 2 * ∑ m ∈ Finset.range (2 ^ n), ∫ u in (gridT t n m : ℝ)..(gridT t n (m + 1)),
        ∫ ω, (stayUpTo Q B z t n (m + 1)).indicator 1 ω * Δ g (z + B u.toNNReal ω) ∂P := by
  have := hB.gauss.isProbabilityMeasure
  set c : ℕ → ℝ := fun m ↦
    ∫ ω, (stayUpTo Q B z t n (m + 1)).indicator 1 ω * g (z + B (gridT t n m) ω) ∂P with hc
  -- one step
  have hstep : ∀ m, c (m + 1) - c m = 1 / 2 * ∫ u in (gridT t n m : ℝ)..(gridT t n (m + 1)),
      ∫ ω, (stayUpTo Q B z t n (m + 1)).indicator 1 ω * Δ g (z + B u.toNNReal ω) ∂P := by
    intro m
    have hd := dynkin_past hB (r := fun j ↦ gridT t n (min j m)) (s := gridT t n m)
      (t := gridT t n (m + 1)) (fun j ↦ gridT_mono (min_le_right j m))
      (gridT_mono (Nat.le_succ m)) (measurable_one.indicator (measurableSet_staySet hQ z m))
      (fun y ↦ abs_indicator_one_le _ y) hg hC hg0 hD1 hD2 hLip2 z
    simp only [indicator_staySet_pastVec] at hd
    rw [← hd]
    congr 1
    refine integral_congr_ae (ae_of_all _ fun ω ↦ ?_)
    by_cases hx : z + B (gridT t n (m + 1)) ω ∈ Q
    · by_cases hs : ω ∈ stayUpTo Q B z t n (m + 1)
      · have hs2 : ω ∈ stayUpTo Q B z t n (m + 1 + 1) := fun j hj ↦ by
          rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj | rfl
          · exact hs j hj
          · exact hx
        simp [Set.indicator_of_mem hs, Set.indicator_of_mem hs2]
      · have hs2 : ω ∉ stayUpTo Q B z t n (m + 1 + 1) := fun h' ↦ hs fun j hj ↦ h' j (by omega)
        simp [Set.indicator_of_notMem hs, Set.indicator_of_notMem hs2]
    · simp [hgQ _ hx]
  have htel : c (2 ^ n) - c 0 = ∑ m ∈ Finset.range (2 ^ n), (c (m + 1) - c m) :=
    (Finset.sum_range_sub c (2 ^ n)).symm
  have hc0 : c 0 = g z := by
    simp only [hc]
    rw [integral_congr_ae (g := fun _ ↦ g z)]
    · simp
    · filter_upwards [ae_zero hB] with ω hω
      have h0 : gridT t n 0 = 0 := by simp [gridT]
      by_cases hz : z ∈ Q
      · have hs : ω ∈ stayUpTo Q B z t n (0 + 1) := fun j hj ↦ by
          rw [show j = 0 by omega, h0, hω, add_zero]; exact hz
        simp [Set.indicator_of_mem hs, h0, hω]
      · have hs : ω ∉ stayUpTo Q B z t n (0 + 1) := fun h' ↦ by
          have := h' 0 (by omega)
          rw [h0, hω, add_zero] at this
          exact hz this
        simp [Set.indicator_of_notMem hs, hgQ z hz]
  have hcN : c (2 ^ n) = ∫ ω, (stayUpTo Q B z t n (2 ^ n + 1)).indicator 1 ω * g (z + B t ω) ∂P := by
    simp only [hc, gridT_pow]
  rw [← hcN, ← hc0, htel, Finset.mul_sum]
  exact Finset.sum_congr rfl fun m _ ↦ hstep m

end HeatA
end ZBM
end CONF
end LQGMetric
