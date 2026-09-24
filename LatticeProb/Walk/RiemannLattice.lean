/-
A multi-dimensional Riemann-sum-to-integral limit: for a continuous compactly supported
function `f : (Fin d → ℝ) → ℝ`, the discrete lattice sum `∑_y f(y/R)` over `y : Site d`,
scaled by the mesh volume `R^{-d}`, converges to `∫ f` as `R → ∞`.

This is a classical, purely deterministic real-analysis fact (a Riemann sum for a continuous
compactly supported function converges to its integral as the mesh `1/R → 0`), with no
probabilistic content, proved here from scratch since no general form of it is available in
Mathlib.

Route: a continuous compactly supported `f` vanishes outside a fixed sup-norm ball
(`exists_norm_bound_of_hasCompactSupport`), so both the lattice sum and the "grid function"
`gridFn f R x := f(⌊Rx⌋/R)` reduce to finitely many terms; the grid function's integral equals
the lattice sum exactly, by decomposing `ℝ^d` into the finitely many `1/R`-side cubes
`⌊Rx⌋ = y` the support meets (`integral_gridFn_eq_latticeSum`); and the grid function converges
to `f` pointwise, dominated by a fixed integrable bound, so dominated convergence
(`MeasureTheory.tendsto_integral_filter_of_dominated_convergence`, the countably-generated-filter
form, applies directly to `Filter.atTop` on `ℝ`) gives the limit
(`tendsto_latticeSum_mul_rpow`).

Useful for any scaling-limit argument needing a lattice-sum-to-integral limit, for instance
identifying the limiting variance of a discrete weighted sum with the integral of the square of
a continuum test function.

Moved from Parking-Sharpness (`Parking/Support/RiemannLattice.lean`).
-/
import LatticeProb.ParticleHoleLemmas
import Mathlib

open MeasureTheory Filter Topology
open scoped ENNReal

noncomputable section

namespace LatticeProb.Walk

variable {d : ℕ}

/-- **A continuous compactly supported function vanishes outside a fixed sup-norm ball.** -/
theorem exists_norm_bound_of_hasCompactSupport {f : (Fin d → ℝ) → ℝ}
    (hfs : HasCompactSupport f) :
    ∃ B : ℝ, 0 < B ∧ ∀ x : Fin d → ℝ, f x ≠ 0 → ‖x‖ ≤ B := by
  obtain ⟨R, hR⟩ := (Metric.isBounded_iff_subset_closedBall (0 : Fin d → ℝ)).mp hfs.isBounded
  refine ⟨max R 1, lt_of_lt_of_le one_pos (le_max_right _ _), fun x hx => ?_⟩
  have hmem : x ∈ Metric.closedBall (0 : Fin d → ℝ) R := hR (subset_tsupport f hx)
  have hle : ‖x‖ ≤ R := by
    have := hmem
    rw [Metric.mem_closedBall, dist_eq_norm, sub_zero] at this
    exact this
  exact hle.trans (le_max_left _ _)

/-- **The finite box, indexed to a bound `B` and a scale `R`, containing every site `y` with
`f(y/R) ≠ 0` once `f` vanishes outside the sup-norm ball of radius `B`.** -/
def sceneryBox (d : ℕ) (B R : ℝ) : Finset (Site d) :=
  LatticeProb.boxFinset (0 : Site d) ⌈B * R⌉₊

/-- Every lattice point weighing nonzero in the scaled sum lies in the scenery box. -/
theorem mem_sceneryBox_of_ne_zero {f : (Fin d → ℝ) → ℝ} {B : ℝ} (hB : 0 < B)
    (hbound : ∀ x : Fin d → ℝ, f x ≠ 0 → ‖x‖ ≤ B) {R : ℝ} (hR : 1 ≤ R)
    {y : Site d} (hy : f (fun i => (y i : ℝ) / R) ≠ 0) :
    y ∈ sceneryBox d B R := by
  have hRpos : 0 < R := lt_of_lt_of_le one_pos hR
  have hnorm : ‖(fun i => (y i : ℝ) / R)‖ ≤ B := hbound _ hy
  have hcoord : ∀ i, |(y i : ℝ) / R| ≤ B := by
    intro i
    have h := (pi_norm_le_iff_of_nonneg hB.le).mp hnorm i
    simpa [Real.norm_eq_abs, abs_div, abs_of_pos hRpos] using h
  rw [sceneryBox, LatticeProb.mem_boxFinset_iff]
  intro i
  have h1 : |(y i : ℝ)| ≤ B * R := by
    have h2 := hcoord i
    rw [abs_div, abs_of_pos hRpos, div_le_iff₀ hRpos] at h2
    exact h2
  have h3 : (|y i| : ℝ) ≤ (⌈B * R⌉₊ : ℝ) := by
    calc (|y i| : ℝ) = |(y i : ℝ)| := by norm_cast
      _ ≤ B * R := h1
      _ ≤ (⌈B * R⌉₊ : ℝ) := Nat.le_ceil _
  have h4 : |y i| ≤ (⌈B * R⌉₊ : ℤ) := by exact_mod_cast h3
  simpa [sub_zero] using h4

/-- **`tsum` of the scenery weight over `Site d` reduces to the finite box.** -/
theorem tsum_eq_sceneryBox_sum {f : (Fin d → ℝ) → ℝ} {B : ℝ} (hB : 0 < B)
    (hbound : ∀ x : Fin d → ℝ, f x ≠ 0 → ‖x‖ ≤ B) {R : ℝ} (hR : 1 ≤ R) :
    ∑' y : Site d, f (fun i => (y i : ℝ) / R) = ∑ y ∈ sceneryBox d B R, f (fun i => (y i : ℝ) / R) := by
  apply tsum_eq_sum
  intro y hy
  by_contra hne
  exact hy (mem_sceneryBox_of_ne_zero hB hbound hR hne)

/-! ### The exact Riemann sum, as the integral of a grid function -/

/-- **A continuous compactly supported function is bounded.** -/
theorem exists_norm_le_of_hasCompactSupport {f : (Fin d → ℝ) → ℝ} (hfc : Continuous f)
    (hfs : HasCompactSupport f) : ∃ M : ℝ, 0 ≤ M ∧ ∀ x, |f x| ≤ M := by
  obtain ⟨B, hB, hbound⟩ := exists_norm_bound_of_hasCompactSupport hfs
  have hcpt : IsCompact (Metric.closedBall (0 : Fin d → ℝ) B) := isCompact_closedBall _ _
  have hne : (Metric.closedBall (0 : Fin d → ℝ) B).Nonempty := ⟨0, by simp [hB.le]⟩
  obtain ⟨x0, hx0mem, hx0max⟩ := hcpt.exists_isMaxOn hne hfc.abs.continuousOn
  refine ⟨|f x0|, abs_nonneg _, fun x => ?_⟩
  by_cases hx : f x = 0
  · simp [hx, abs_nonneg]
  · exact hx0max (Metric.mem_closedBall.mpr (by
      have := hbound x hx
      simpa [dist_eq_norm] using this))

/-- The `1/R`-mesh cube of `Site d` centred at the lattice point `y`. -/
def latticeCube (d : ℕ) (y : Site d) (R : ℝ) : Set (Fin d → ℝ) :=
  Set.pi Set.univ (fun i => Set.Ico ((y i : ℝ) / R) ((y i + 1 : ℝ) / R))

/-- The `1/R`-mesh grid function: `f` read at the lattice point below `x`. -/
def gridFn {d : ℕ} (f : (Fin d → ℝ) → ℝ) (R : ℝ) (x : Fin d → ℝ) : ℝ :=
  f (fun i => (⌊R * x i⌋ : ℝ) / R)

/-- A point lies in the mesh cube at `y` exactly when the scaled floor of every coordinate
equals `y`. -/
theorem mem_latticeCube_iff {y : Site d} {R : ℝ} (hR : 0 < R) (x : Fin d → ℝ) :
    x ∈ latticeCube d y R ↔ ∀ i, ⌊R * x i⌋ = y i := by
  simp only [latticeCube, Set.mem_pi, Set.mem_univ, forall_true_left, Set.mem_Ico]
  constructor
  · intro h i
    obtain ⟨h1, h2⟩ := h i
    rw [div_le_iff₀ hR] at h1
    rw [lt_div_iff₀ hR] at h2
    rw [Int.floor_eq_iff]
    constructor
    · linarith [h1]
    · linarith [h2]
  · intro h i
    have hfl := h i
    rw [Int.floor_eq_iff] at hfl
    obtain ⟨h1, h2⟩ := hfl
    constructor
    · rw [div_le_iff₀ hR]; linarith
    · rw [lt_div_iff₀ hR]; linarith

/-- Every mesh cube is measurable. -/
theorem latticeCube_measurableSet (y : Site d) (R : ℝ) :
    MeasurableSet (latticeCube d y R) :=
  MeasurableSet.univ_pi fun _ => measurableSet_Ico

/-- The volume of a mesh cube is the `d`-th power of the mesh size. -/
theorem volume_latticeCube (y : Site d) {R : ℝ} (hR : 0 < R) :
    volume (latticeCube d y R) = (ENNReal.ofReal (1 / R)) ^ d := by
  have hrw : (volume : Measure (Fin d → ℝ)) = Measure.pi fun _ : Fin d => (volume : Measure ℝ) :=
    volume_pi
  rw [latticeCube, hrw, Measure.pi_pi]
  have hterm : ∀ i : Fin d, volume (Set.Ico ((y i : ℝ) / R) ((y i + 1 : ℝ) / R))
      = ENNReal.ofReal (1 / R) := by
    intro i
    rw [Real.volume_Ico]
    congr 1
    field_simp
    ring
  simp_rw [hterm]
  rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]

/-- The grid function is exactly the sum of the scenery weights over the mesh cubes. -/
theorem gridFn_eq_sum_indicator {f : (Fin d → ℝ) → ℝ} {B : ℝ} (hB : 0 < B)
    (hbound : ∀ x : Fin d → ℝ, f x ≠ 0 → ‖x‖ ≤ B) {R : ℝ} (hR : 1 ≤ R) (x : Fin d → ℝ) :
    gridFn f R x = ∑ y ∈ sceneryBox d B R,
      (latticeCube d y R).indicator (fun _ => f (fun i => (y i : ℝ) / R)) x := by
  have hRpos : 0 < R := lt_of_lt_of_le one_pos hR
  set y0 : Site d := fun i => ⌊R * x i⌋ with hy0
  have hmemy0 : x ∈ latticeCube d y0 R := (mem_latticeCube_iff hRpos x).mpr (fun i => rfl)
  have hsingle : ∀ y ∈ sceneryBox d B R,
      (latticeCube d y R).indicator (fun _ => f (fun i => (y i : ℝ) / R)) x
        = if y = y0 then f (fun i => (y0 i : ℝ) / R) else 0 := by
    intro y _
    by_cases hyy0 : y = y0
    · subst hyy0
      rw [Set.indicator_of_mem hmemy0, if_pos rfl]
    · rw [if_neg hyy0]
      rw [Set.indicator_of_notMem]
      intro hxmem
      apply hyy0
      have h1 := (mem_latticeCube_iff hRpos x).mp hxmem
      funext i
      simp only [hy0]
      exact (h1 i).symm
  rw [Finset.sum_congr rfl hsingle]
  by_cases hy0mem : y0 ∈ sceneryBox d B R
  · rw [Finset.sum_ite_eq' (sceneryBox d B R) y0 (fun _ => f (fun i => (y0 i : ℝ) / R))]
    rw [if_pos hy0mem]
    rfl
  · rw [Finset.sum_ite_eq' (sceneryBox d B R) y0 (fun _ => f (fun i => (y0 i : ℝ) / R))]
    rw [if_neg hy0mem]
    show f (fun i => ((y0 i : ℝ)) / R) = 0
    by_contra hne
    exact hy0mem (mem_sceneryBox_of_ne_zero hB hbound hR hne)

/-- **The exact Riemann sum identity**: the integral of the grid function equals the discrete
lattice sum, scaled by the mesh volume `R^{-d}`. -/
theorem integral_gridFn_eq_latticeSum {f : (Fin d → ℝ) → ℝ} {B : ℝ} (hB : 0 < B)
    (hbound : ∀ x : Fin d → ℝ, f x ≠ 0 → ‖x‖ ≤ B) {R : ℝ} (hR : 1 ≤ R) :
    ∫ x, gridFn f R x ∂(volume : Measure (Fin d → ℝ))
      = (∑' y : Site d, f (fun i => (y i : ℝ) / R)) * (1 / R) ^ d := by
  have hRpos : 0 < R := lt_of_lt_of_le one_pos hR
  have hfun : (fun x => gridFn f R x) = fun x => ∑ y ∈ sceneryBox d B R,
      (latticeCube d y R).indicator (fun _ => f (fun i => (y i : ℝ) / R)) x :=
    funext fun x => gridFn_eq_sum_indicator hB hbound hR x
  rw [hfun]
  rw [integral_finsetSum]
  · have hterm : ∀ y ∈ sceneryBox d B R,
        ∫ x, (latticeCube d y R).indicator (fun _ => f (fun i => (y i : ℝ) / R)) x ∂volume
          = f (fun i => (y i : ℝ) / R) * (1 / R) ^ d := by
      intro y _
      rw [MeasureTheory.integral_indicator (latticeCube_measurableSet y R)]
      rw [MeasureTheory.setIntegral_const]
      rw [Measure.real, volume_latticeCube y hRpos]
      rw [ENNReal.toReal_pow, ENNReal.toReal_ofReal (by positivity)]
      rw [smul_eq_mul]
      ring
    rw [Finset.sum_congr rfl hterm, ← Finset.sum_mul]
    rw [tsum_eq_sceneryBox_sum hB hbound hR]
  · intro y _
    refine (integrable_indicator_iff (latticeCube_measurableSet y R)).mpr ?_
    refine integrableOn_const ?_
    rw [volume_latticeCube y hRpos]
    exact ENNReal.pow_ne_top ENNReal.ofReal_ne_top

/-- **The one-dimensional floor-grid approximation error is at most the mesh size `1/R`.** -/
theorem abs_floor_mul_div_sub_le {R : ℝ} (hR : 0 < R) (z : ℝ) :
    |(⌊R * z⌋ : ℝ) / R - z| ≤ 1 / R := by
  have h1 : (⌊R * z⌋ : ℝ) ≤ R * z := Int.floor_le _
  have h2 : R * z < (⌊R * z⌋ : ℝ) + 1 := Int.lt_floor_add_one _
  have hRne : R ≠ 0 := ne_of_gt hR
  have heq : (⌊R * z⌋ : ℝ) / R - z = ((⌊R * z⌋ : ℝ) - R * z) / R := by
    field_simp
  rw [heq, abs_div, abs_of_pos hR]
  gcongr
  rw [abs_le]
  constructor <;> linarith

/-- **`gridFn f R x` converges to `f x` pointwise as `R → ∞`.** -/
theorem tendsto_gridFn {f : (Fin d → ℝ) → ℝ} (hfc : Continuous f) (x : Fin d → ℝ) :
    Tendsto (fun R : ℝ => gridFn f R x) atTop (𝓝 (f x)) := by
  have hcoord : Tendsto (fun R : ℝ => fun i : Fin d => (⌊R * x i⌋ : ℝ) / R) atTop (𝓝 x) := by
    rw [tendsto_pi_nhds]
    intro i
    apply tendsto_iff_dist_tendsto_zero.mpr
    have hbnd : ∀ᶠ R : ℝ in atTop, dist ((⌊R * x i⌋ : ℝ) / R) (x i) ≤ 1 / R := by
      filter_upwards [eventually_gt_atTop (0:ℝ)] with R hR
      rw [Real.dist_eq]
      exact abs_floor_mul_div_sub_le hR (x i)
    have hinv : Tendsto (fun R : ℝ => (1:ℝ) / R) atTop (𝓝 0) := by
      simpa [one_div] using tendsto_inv_atTop_zero (𝕜 := ℝ)
    exact squeeze_zero' (Eventually.of_forall fun R => dist_nonneg) hbnd hinv
  exact hfc.continuousAt.tendsto.comp hcoord

/-- **`gridFn f R` is dominated by a fixed integrable function, for `R ≥ 1`.** -/
theorem eventually_abs_gridFn_le {f : (Fin d → ℝ) → ℝ} {B : ℝ} (_hB : 0 < B)
    (hbound : ∀ x : Fin d → ℝ, f x ≠ 0 → ‖x‖ ≤ B) {M : ℝ} (hM0 : 0 ≤ M) (hM : ∀ x, |f x| ≤ M) :
    ∀ᶠ R : ℝ in atTop, ∀ x : Fin d → ℝ,
      ‖gridFn f R x‖ ≤ M * (Metric.closedBall (0 : Fin d → ℝ) (B + 1)).indicator (fun _ => (1:ℝ)) x := by
  filter_upwards [eventually_ge_atTop (1:ℝ)] with R hR x
  have hRpos : (0:ℝ) < R := lt_of_lt_of_le one_pos hR
  by_cases hx0 : gridFn f R x = 0
  · rw [hx0]
    simp only [norm_zero]
    exact mul_nonneg hM0 (Set.indicator_nonneg (fun _ _ => zero_le_one) x)
  · set p : Fin d → ℝ := fun i => (⌊R * x i⌋ : ℝ) / R with hp
    have hfne : f p ≠ 0 := hx0
    have hn : ‖p‖ ≤ B := hbound p hfne
    have hcoorddiff : ∀ i, |p i - x i| ≤ 1 / R := by
      intro i
      rw [hp]
      exact abs_floor_mul_div_sub_le hRpos (x i)
    have hdiff : ‖p - x‖ ≤ 1 / R := by
      rw [pi_norm_le_iff_of_nonneg (by positivity)]
      intro i
      simpa [Real.norm_eq_abs] using hcoorddiff i
    have hdiffle1 : ‖p - x‖ ≤ 1 := hdiff.trans (by
      rw [div_le_one hRpos]; exact hR)
    have hxle : ‖x‖ ≤ B + 1 := by
      have hxeq : x = p - (p - x) := by abel
      calc ‖x‖ = ‖p - (p - x)‖ := by rw [← hxeq]
        _ ≤ ‖p‖ + ‖p - x‖ := norm_sub_le _ _
        _ ≤ B + 1 := add_le_add hn hdiffle1
    rw [Set.indicator_of_mem (Metric.mem_closedBall.mpr (by simpa [dist_eq_norm] using hxle))]
    rw [gridFn]
    show ‖f p‖ ≤ M * 1
    rw [mul_one, Real.norm_eq_abs]
    exact hM p

/-- **The multi-dimensional Riemann sum converges to the integral.**  For `f` continuous with
compact support, the discrete lattice sum `∑_y f(y/R)`, scaled by the mesh volume `R^{-d}`,
converges to `∫ f` as `R → ∞`. -/
theorem tendsto_latticeSum_mul_rpow {f : (Fin d → ℝ) → ℝ} (hfc : Continuous f)
    (hfs : HasCompactSupport f) :
    Tendsto (fun R : ℝ => (∑' y : Site d, f (fun i => (y i : ℝ) / R)) * (1 / R) ^ d) atTop
      (𝓝 (∫ x, f x ∂(volume : Measure (Fin d → ℝ)))) := by
  obtain ⟨B, hB, hbound⟩ := exists_norm_bound_of_hasCompactSupport hfs
  obtain ⟨M, hM0, hM⟩ := exists_norm_le_of_hasCompactSupport hfc hfs
  have hident : (fun R : ℝ => (∑' y : Site d, f (fun i => (y i : ℝ) / R)) * (1 / R) ^ d)
      =ᶠ[atTop] (fun R : ℝ => ∫ x, gridFn f R x ∂(volume : Measure (Fin d → ℝ))) := by
    filter_upwards [eventually_ge_atTop (1:ℝ)] with R hR
    exact (integral_gridFn_eq_latticeSum hB hbound hR).symm
  refine Tendsto.congr' hident.symm ?_
  have hgridMeas : ∀ R : ℝ, Measurable (gridFn f R) := by
    intro R
    apply hfc.measurable.comp
    apply measurable_pi_lambda
    intro i
    exact ((measurable_of_countable (fun k : ℤ => (k : ℝ))).comp
      (Int.measurable_floor.comp
        (measurable_const.mul (measurable_pi_apply i)))).div_const R
  refine tendsto_integral_filter_of_dominated_convergence
    (fun x => M * (Metric.closedBall (0 : Fin d → ℝ) (B + 1)).indicator (fun _ => (1:ℝ)) x)
    (Eventually.of_forall fun R => (hgridMeas R).aestronglyMeasurable)
    ?_ ?_ ?_
  · filter_upwards [eventually_abs_gridFn_le hB hbound hM0 hM] with R hR
    exact Eventually.of_forall hR
  · refine Integrable.const_mul ?_ M
    refine (integrable_indicator_iff measurableSet_closedBall).mpr ?_
    exact integrableOn_const (isCompact_closedBall (0 : Fin d → ℝ) (B + 1)).measure_lt_top.ne
  · exact Eventually.of_forall fun x => tendsto_gridFn hfc x

end LatticeProb.Walk
