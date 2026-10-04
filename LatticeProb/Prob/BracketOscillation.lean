/-
# Pathwise dyadic oscillation of a continuous process

The pathwise input of the bracket-convergence reduction (`scratch/pk/dds-stage1-report.md`): for a
continuous process `M` on the compact `[0, T]`, the dyadic mesh oscillation

  `osc M T n ω = sup_{k < 2ⁿ} |M ((2k+1) T / 2ⁿ⁺¹) ω - M (k T / 2ⁿ) ω|`

tends to `0` as `n → ∞`.  This is uniform continuity of the path on the compact interval `[0, T]`
applied to the dyadic increments, whose length is `T / 2ⁿ⁺¹ → 0`.

Proved here: the arithmetic of the dyadic points, the basic bounds on `osc`, and the pathwise
convergence `tendsto_osc`.  Nothing here uses a measure.
-/
import Mathlib

open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal Topology

noncomputable section

namespace LatticeProb

variable {Ω : Type*}

/-- The dyadic grid point `k T / 2ⁿ` of `[0, T]`. -/
def dyadicPoint (T : ℝ≥0) (n k : ℕ) : ℝ≥0 := T * ((k : ℝ≥0) / 2 ^ n)

/-- The **dyadic mesh oscillation**: the largest change of `M` over one increment of the mesh
`2⁻ⁿ⁺¹` of `[0, T]`, read on the left endpoint of a mesh-`2⁻ⁿ` interval. -/
def osc (M : ℝ≥0 → Ω → ℝ) (T : ℝ≥0) (n : ℕ) (ω : Ω) : ℝ :=
  (Finset.range (2 ^ n)).sup' ⟨0, Finset.mem_range.mpr (by positivity)⟩
    (fun k => |M (dyadicPoint T (n + 1) (2 * k + 1)) ω - M (dyadicPoint T n k) ω|)

/-! ### Basic bounds on `osc` -/

theorem le_osc (M : ℝ≥0 → Ω → ℝ) (T : ℝ≥0) (n : ℕ) (ω : Ω) (k : ℕ)
    (hk : k ∈ Finset.range (2 ^ n)) :
    |M (dyadicPoint T (n + 1) (2 * k + 1)) ω - M (dyadicPoint T n k) ω| ≤ osc M T n ω :=
  Finset.le_sup' (s := Finset.range (2 ^ n))
    (f := fun k => |M (dyadicPoint T (n + 1) (2 * k + 1)) ω - M (dyadicPoint T n k) ω|) hk

theorem osc_nonneg (M : ℝ≥0 → Ω → ℝ) (T : ℝ≥0) (n : ℕ) (ω : Ω) : 0 ≤ osc M T n ω :=
  le_trans (abs_nonneg _) (le_osc M T n ω 0 (Finset.mem_range.mpr (by positivity)))

theorem osc_le (M : ℝ≥0 → Ω → ℝ) (T : ℝ≥0) (n : ℕ) (ω : Ω) (K : ℝ)
    (hK : ∀ t, |M t ω| ≤ K) : osc M T n ω ≤ 2 * K := by
  refine Finset.sup'_le (s := Finset.range (2 ^ n)) _ _ (fun k hk => ?_)
  calc |M (dyadicPoint T (n + 1) (2 * k + 1)) ω - M (dyadicPoint T n k) ω|
      ≤ |M (dyadicPoint T (n + 1) (2 * k + 1)) ω| + |M (dyadicPoint T n k) ω| := abs_sub _ _
    _ ≤ K + K := add_le_add (hK _) (hK _)
    _ = 2 * K := by ring

/-! ### The dyadic points -/

theorem dyadicPoint_nonneg (T : ℝ≥0) (n k : ℕ) : 0 ≤ dyadicPoint T n k := by
  simp [dyadicPoint]

theorem dyadicPoint_zero_time (n k : ℕ) : dyadicPoint (0 : ℝ≥0) n k = 0 := by
  simp [dyadicPoint]

/-- A level-`n` dyadic point lies in the interval. -/
theorem dyadicPoint_le_T (T : ℝ≥0) (n k : ℕ) (hk : k < 2 ^ n) : dyadicPoint T n k ≤ T := by
  unfold dyadicPoint
  have h : (k : ℝ≥0) / 2 ^ n ≤ 1 := by
    rw [div_le_one (by positivity)]
    exact_mod_cast hk.le
  calc T * ((k : ℝ≥0) / 2 ^ n) ≤ T * 1 := mul_le_mul_of_nonneg_left h (by positivity)
    _ = T := mul_one T

/-- The midpoint of a refined increment lies in the interval. -/
theorem dyadicPoint_mid_le_T (T : ℝ≥0) (n k : ℕ) (hk : k < 2 ^ n) :
    dyadicPoint T (n + 1) (2 * k + 1) ≤ T := by
  unfold dyadicPoint
  have h : ((2 * k + 1 : ℕ) : ℝ≥0) / 2 ^ (n + 1) ≤ 1 := by
    rw [div_le_one (by positivity)]
    have : (2 * k + 1 : ℕ) ≤ 2 ^ (n + 1) := by rw [pow_succ]; omega
    exact_mod_cast this
  calc T * (((2 * k + 1 : ℕ) : ℝ≥0) / 2 ^ (n + 1)) ≤ T * 1 :=
        mul_le_mul_of_nonneg_left h (by positivity)
    _ = T := mul_one T

/-- The left endpoint of a refined increment precedes its midpoint. -/
theorem dyadicPoint_le_mid (T : ℝ≥0) (n j : ℕ) :
    dyadicPoint T n j ≤ dyadicPoint T (n + 1) (2 * j + 1) := by
  unfold dyadicPoint
  rw [pow_succ]
  have h2 : (0 : ℝ≥0) < 2 ^ n := pow_pos two_pos n
  have h : (j : ℝ≥0) / 2 ^ n ≤ ((2 * j + 1 : ℕ) : ℝ≥0) / (2 ^ n * 2) := by
    rw [div_le_div_iff₀ h2 (by positivity)]
    push_cast
    nlinarith
  exact mul_le_mul_of_nonneg_left h (by positivity)

/-- The length of a refined increment is the mesh width `T / 2ⁿ⁺¹`. -/
theorem dyadicPoint_sub_mid (T : ℝ≥0) (n k : ℕ) :
    dyadicPoint T (n + 1) (2 * k + 1) - dyadicPoint T n k = T / 2 ^ (n + 1) := by
  have hxy := dyadicPoint_le_mid T n k
  apply NNReal.coe_injective
  rw [NNReal.coe_sub hxy]
  unfold dyadicPoint
  push_cast
  rw [pow_succ]
  field_simp
  ring

/-- The distance between the endpoints of a refined increment is `T / 2ⁿ⁺¹`. -/
theorem dist_dyadicPoint_mid (T : ℝ≥0) (n k : ℕ) :
    dist (dyadicPoint T n k) (dyadicPoint T (n + 1) (2 * k + 1)) = T / 2 ^ (n + 1) := by
  rw [NNReal.dist_eq]
  have hxy := dyadicPoint_le_mid T n k
  have hle : ((dyadicPoint T n k : ℝ) ≤ (dyadicPoint T (n + 1) (2 * k + 1) : ℝ)) := by
    exact_mod_cast hxy
  rw [abs_of_nonpos (sub_nonpos.mpr hle), neg_sub]
  exact_mod_cast dyadicPoint_sub_mid T n k

/-- At `T = 0` all dyadic increments vanish. -/
theorem osc_zero_time (M : ℝ≥0 → Ω → ℝ) (n : ℕ) (ω : Ω) : osc M 0 n ω = 0 := by
  refine le_antisymm ?_ (osc_nonneg M 0 n ω)
  refine Finset.sup'_le (s := Finset.range (2 ^ n)) _ _ (fun k hk => ?_)
  simp [dyadicPoint]

/-! ### The pathwise convergence -/

/-- **The dyadic oscillation of a continuous path vanishes.**  For a continuous path
`t ↦ M t ω` on the compact `[0, T]`, uniform continuity makes every increment of the mesh
`2⁻ⁿ⁺¹` (which has length `T / 2ⁿ⁺¹ → 0`) smaller than `ε` for large `n`, hence so does the
supremum `osc M T n ω`. -/
theorem tendsto_osc (M : ℝ≥0 → Ω → ℝ) (T : ℝ≥0) (ω : Ω)
    (hcont : Continuous fun t : ℝ≥0 => M t ω) :
    Tendsto (fun n => osc M T n ω) atTop (𝓝 0) := by
  rcases eq_or_ne T 0 with rfl | hT
  · simp only [osc_zero_time]
    exact tendsto_const_nhds
  · have huc : UniformContinuousOn (fun t : ℝ≥0 => M t ω) (Set.Icc 0 T) :=
      isCompact_Icc.uniformContinuousOn_of_continuous hcont.continuousOn
    rw [Metric.tendsto_atTop]
    intro ε hε
    have hε2 : 0 < ε / 2 := by linarith
    obtain ⟨δ, hδpos, hδ⟩ := (Metric.uniformContinuousOn_iff.mp huc) (ε / 2) hε2
    have htend : Tendsto (fun N : ℕ => (T : ℝ) / 2 ^ (N + 1)) atTop (𝓝 0) := by
      have hbase : Tendsto (fun N : ℕ => ((2 : ℝ))⁻¹ ^ (N + 1)) atTop (𝓝 0) :=
        (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)).comp
          (Filter.tendsto_add_atTop_nat 1)
      have h2 : Tendsto (fun N : ℕ => (T : ℝ) * (2 : ℝ)⁻¹ ^ (N + 1)) atTop (𝓝 ((T : ℝ) * 0)) :=
        tendsto_const_nhds.mul hbase
      simpa only [mul_zero, div_eq_mul_inv, inv_pow] using h2
    obtain ⟨N, hN⟩ := (htend.eventually (Iio_mem_nhds hδpos)).exists
    refine ⟨N, fun n hn => ?_⟩
    have hstep : osc M T n ω ≤ ε / 2 := by
      refine Finset.sup'_le (s := Finset.range (2 ^ n)) _ _ (fun k hk => ?_)
      have hkT : k < 2 ^ n := Finset.mem_range.mp hk
      have hx : dyadicPoint T n k ∈ Set.Icc 0 T :=
        ⟨dyadicPoint_nonneg T n k, dyadicPoint_le_T T n k hkT⟩
      have hy : dyadicPoint T (n + 1) (2 * k + 1) ∈ Set.Icc 0 T :=
        ⟨dyadicPoint_nonneg T (n + 1) (2 * k + 1), dyadicPoint_mid_le_T T n k hkT⟩
      have hdistlt : dist (dyadicPoint T n k) (dyadicPoint T (n + 1) (2 * k + 1)) < δ := by
        rw [dist_dyadicPoint_mid]
        have hle : T / 2 ^ (n + 1) ≤ T / 2 ^ (N + 1) := by
          refine div_le_div_of_nonneg_left (by positivity : (0 : ℝ≥0) ≤ T) (by positivity) ?_
          exact pow_le_pow_right₀ (by norm_num) (by omega)
        have hleR : ((T / 2 ^ (n + 1) : ℝ≥0) : ℝ) ≤ (T : ℝ) / 2 ^ (N + 1) := by
          have h1 : ((T / 2 ^ (n + 1) : ℝ≥0) : ℝ) ≤ ((T / 2 ^ (N + 1) : ℝ≥0) : ℝ) := by
            exact_mod_cast hle
          have h2 : ((T / 2 ^ (N + 1) : ℝ≥0) : ℝ) = (T : ℝ) / 2 ^ (N + 1) := by
            push_cast
            ring
          linarith
        exact lt_of_le_of_lt hleR hN
      have := hδ _ hx _ hy hdistlt
      rw [Real.dist_eq, abs_sub_comm] at this
      exact this.le
    rw [Real.dist_eq, sub_zero, abs_of_nonneg (osc_nonneg M T n ω)]
    linarith

end LatticeProb
