import LatticeProb.LQG.RecentredSquareMaximalMoment
import LatticeProb.LQG.RecentredSquareGeometry
import LatticeProb.Bonanno.MatedCRTHarmonic.GMCFacts.OuterMoment
import LatticeProb.LQG.RecentredSquareCountableSupFiniteness

/-! # Spatial dependence of recentred square approximations -/

open MeasureTheory Set
open scoped ENNReal
open QuantumZipper
open MatedCRTHarmonic.GMCFacts LQGMetric.DGMC LQGMetric.DGMC.Neg3

namespace LatticeProb.LQG

/-- Recentering multiplies an approximation on a fixed measurable set by the
exponential of the circle average at the center. -/
theorem lqgApprox_recentred_eq_mul {Ω : Type*} (H : ℝ → ℂ → Ω → ℝ)
    (ω : Ω) (γ : ℝ) {ε r : ℝ}
    (z : ℂ) {S : Set ℂ} (hS : MeasurableSet S) :
    lqgApprox γ (fun s w => H (ε * s) w ω - H ε z ω) (r / ε) S =
      ENNReal.ofReal (Real.exp (-γ * H ε z ω)) *
        lqgApprox γ (fun s w => H (ε * s) w ω) (r / ε) S := by
  rw [lqgApprox, lqgApprox, withDensity_apply _ hS, withDensity_apply _ hS]
  rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  apply lintegral_congr
  intro w
  rw [← ENNReal.ofReal_mul (Real.exp_nonneg _)]
  congr 1
  have he : Real.exp (γ * (H (ε * (r / ε)) w ω - H ε z ω)) =
      Real.exp (-γ * H ε z ω) * Real.exp (γ * H (ε * (r / ε)) w ω) := by
    rw [← Real.exp_add]
    congr 1
    ring
  rw [he]
  ring

/-- For each fixed measurable set the recentred approximation is continuous
in the recentering point whenever the circle averages are spatially continuous. -/
theorem continuous_lqgApprox_recentred_fixed_set {Ω : Type*}
    [MeasurableSpace Ω] {P : Measure Ω} {H : ℝ → ℂ → Ω → ℝ}
    (hH : LQGDimension.IsGFFCircleAverage H P) (ω : Ω) (γ : ℝ)
    {ε r : ℝ} (hε : 0 < ε) {S : Set ℂ} (hS : MeasurableSet S)
    (hfinite : lqgApprox γ (fun s w => H (ε * s) w ω) (r / ε) S ≠ ⊤) :
    Continuous (fun z => lqgApprox γ (fun s w => H (ε * s) w ω - H ε z ω)
      (r / ε) S) := by
  simp_rw [lqgApprox_recentred_eq_mul H ω γ _ hS]
  apply (ENNReal.continuous_mul_const hfinite).comp
  exact ENNReal.continuous_ofReal.comp (Real.continuous_exp.comp
    (continuous_const.mul (hH.continuous ε hε ω)))

/-- A bounded set has finite approximation mass for the same field. -/
theorem lqgApprox_rescaled_apply_ne_top_of_isBounded {Ω : Type*}
    [MeasurableSpace Ω] {P : Measure Ω} {H : ℝ → ℂ → Ω → ℝ}
    (hH : LQGDimension.IsGFFCircleAverage H P) (ω : Ω) (γ : ℝ)
    {ε r : ℝ} (hε : 0 < ε) (hr : 0 < r) {S : Set ℂ}
    (hS : Bornology.IsBounded S) :
    lqgApprox γ (fun s w => H (ε * s) w ω) (r / ε) S ≠ ⊤ := by
  have hc : Continuous (fun w => H (ε * (r / ε)) w ω) := by
    rw [mul_div_cancel₀ r hε.ne']
    exact hH.continuous r hr ω
  let : IsLocallyFiniteMeasure (lqgApprox γ (fun s w => H (ε * s) w ω) (r / ε)) := by
    unfold lqgApprox
    exact IsLocallyFiniteMeasure.withDensity_ofReal
      (continuous_const.mul (Real.continuous_exp.comp (continuous_const.mul hc)))
  exact hS.measure_lt_top.ne

/-- The same approximation on a fixed bounded measurable set is continuous
in the recentering point. -/
theorem continuous_lqgApprox_recentred_of_isBounded {Ω : Type*}
    [MeasurableSpace Ω] {P : Measure Ω} {H : ℝ → ℂ → Ω → ℝ}
    (hH : LQGDimension.IsGFFCircleAverage H P) (ω : Ω) (γ : ℝ)
    {ε r : ℝ} (hε : 0 < ε) (hr : 0 < r) {S : Set ℂ}
    (hS : MeasurableSet S) (hbounded : Bornology.IsBounded S) :
    Continuous (fun z => lqgApprox γ (fun s w => H (ε * s) w ω - H ε z ω)
      (r / ε) S) :=
  continuous_lqgApprox_recentred_fixed_set hH ω γ hε hS
    (lqgApprox_rescaled_apply_ne_top_of_isBounded hH ω γ hε hr hbounded)

/-- A set containing a centered square bounds its normalized recentred mass. -/
theorem normalized_recentred_square_mass_le_of_subset {Ω : Type*}
    (H : ℝ → ℂ → Ω → ℝ) (γ : ℝ) (z : ℂ) (m k : ℕ) (ω : Ω)
    {S : Set ℂ} (hS : MeasurableSet S)
    (hsub : sqQ (sqCorner z (radius m)) m ⊆ S) :
    normalizedRecentredSquareMass H γ z m k ω ≤
      ENNReal.ofReal ((2 * radius m)⁻¹ ^ 2) *
        (ENNReal.ofReal (Real.exp (-γ * H (2 * radius m) z ω)) *
          lqgApprox γ (fun s w => H (2 * radius m * s) w ω)
            (radius (m + k) / (2 * radius m)) S) := by
  unfold normalizedRecentredSquareMass
  gcongr
  calc
    _ ≤ lqgApprox γ (fun s w => H (2 * radius m * s) w ω -
        H (2 * radius m) z ω) (radius (m + k) / (2 * radius m)) S := measure_mono hsub
    _ = _ := lqgApprox_recentred_eq_mul H ω γ z hS

/-- On a compact set of centers, every fixed level of the normalized
recentred square approximation is bounded simultaneously. -/
theorem exists_compact_bound_normalized_recentred_square_mass {Ω : Type*}
    [MeasurableSpace Ω] {P : Measure Ω} {H : ℝ → ℂ → Ω → ℝ}
    (hH : LQGDimension.IsGFFCircleAverage H P) (ω : Ω) (γ : ℝ)
    (K : Set ℂ) (hK : IsCompact K) (m k : ℕ) :
    ∃ C : ℝ≥0∞, C < ⊤ ∧ ∀ z ∈ K,
      normalizedRecentredSquareMass H γ z m k ω ≤ C := by
  obtain ⟨R, hR⟩ := Metric.isBounded_iff_subset_ball (0 : ℂ) |>.1 hK.isBounded
  let S : Set ℂ := Metric.closedBall 0 (R + radius m)
  have hS : MeasurableSet S := Metric.isClosed_closedBall.measurableSet
  have hsub : ∀ z ∈ K, sqQ (sqCorner z (radius m)) m ⊆ S := by
    intro z hz w hw
    have hz' : ‖z‖ < R := by simpa [Metric.mem_ball, dist_zero_right] using hR hz
    have hw' := norm_sub_le_of_mem_centred_sqQ z m hw
    show w ∈ Metric.closedBall 0 (R + radius m)
    rw [Metric.mem_closedBall, dist_zero_right]
    calc
      ‖w‖ = ‖(w - z) + z‖ := by rw [sub_add_cancel]
      _ ≤ ‖w - z‖ + ‖z‖ := norm_add_le _ _
      _ ≤ R + radius m := by linarith
  have hε : 0 < 2 * radius m := mul_pos (by norm_num) (radius_pos m)
  have hr : 0 < radius (m + k) := radius_pos _
  obtain ⟨B, hB⟩ := hK.bddAbove_image
    ((Real.continuous_exp.comp (continuous_const.mul (hH.continuous _ hε ω))).continuousOn)
  let M := lqgApprox γ (fun s w => H (2 * radius m * s) w ω)
    (radius (m + k) / (2 * radius m)) S
  have hM : M ≠ ⊤ := lqgApprox_rescaled_apply_ne_top_of_isBounded hH ω γ hε hr
    Metric.isBounded_closedBall
  refine ⟨ENNReal.ofReal ((2 * radius m)⁻¹ ^ 2) * (ENNReal.ofReal B * M),
    lt_top_iff_ne_top.mpr (ENNReal.mul_ne_top ENNReal.ofReal_ne_top
      (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hM)), ?_⟩
  intro z hz
  refine (normalized_recentred_square_mass_le_of_subset H γ z m k ω hS (hsub z hz)).trans ?_
  gcongr
  exact hB ⟨z, hz, rfl⟩

/-- Finitely many levels admit one bound over every center in a compact set. -/
theorem exists_compact_finset_bound_normalized_recentred_square_mass {Ω : Type*}
    [MeasurableSpace Ω] {P : Measure Ω} {H : ℝ → ℂ → Ω → ℝ}
    (hH : LQGDimension.IsGFFCircleAverage H P) (ω : Ω) (γ : ℝ)
    (K : Set ℂ) (hK : IsCompact K) (m : ℕ) (T : Finset ℕ) :
    ∃ C : ℝ≥0∞, C < ⊤ ∧ ∀ z ∈ K, ∀ k ∈ T,
      normalizedRecentredSquareMass H γ z m k ω ≤ C := by
  classical
  choose C hC using fun k => exists_compact_bound_normalized_recentred_square_mass hH ω γ K hK m k
  refine ⟨T.sup C, (Finset.sup_lt_iff bot_lt_top).2 (fun k _ => (hC k).1), ?_⟩
  intro z hz k hk
  exact ((hC k).2 z hz).trans (Finset.le_sup (f := C) hk)

/-- A disk at a dyadic scale is covered by sixteen squares of that scale. -/
theorem ball_subset_iUnion_sqQ (z : ℂ) (m : ℕ) :
    Metric.ball z (2 * radius m) ⊆
      ⋃ c ∈ corners16, sqQ (z + radius m • c) m := by
  intro w hw
  have hr : 0 < radius m := radius_pos m
  let u : ℂ := (radius m)⁻¹ • (w - z)
  have hu : u ∈ Metric.ball (0 : ℂ) 2 := by
    rw [Metric.mem_ball, dist_zero_right]
    rw [Metric.mem_ball, dist_eq_norm] at hw
    dsimp only [u]
    rw [norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hr]
    apply (inv_mul_lt_iff₀ hr).2
    linarith
  obtain ⟨c, hc, hmem⟩ := Set.mem_iUnion₂.mp (ball_two_subset_corners16 hu)
  apply Set.mem_iUnion₂.mpr
  refine ⟨c, hc, ?_⟩
  have hc0 : u - c ∈ cell0 := by
    simpa only [sqQ, QuantumZipper.radius, pow_zero, inv_one, one_smul, mem_ofPred_eq] using hmem
  change (radius m)⁻¹ • (w - (z + radius m • c)) ∈ cell0
  convert hc0 using 1
  simp only [u, sub_add_eq_sub_sub, smul_sub, smul_smul, inv_mul_cancel₀ hr.ne', one_smul]

/-- Every centered square of a fixed scale over a compact set is covered by
one finite family of squares of that scale. -/
theorem exists_finset_sqQ_cover_compact (K : Set ℂ) (hK : IsCompact K) (m : ℕ) :
    ∃ A : Finset ℂ, ∀ z ∈ K, sqQ (sqCorner z (radius m)) m ⊆
      ⋃ a ∈ A, sqQ a m := by
  classical
  have hr : 0 < radius m := radius_pos m
  obtain ⟨T, hT⟩ := hK.elim_finite_subcover (fun z : ℂ => Metric.ball z (radius m))
    (fun _ => Metric.isOpen_ball) (by
      intro z hz
      exact Set.mem_iUnion.mpr ⟨z, Metric.mem_ball_self hr⟩)
  refine ⟨T.biUnion (fun x => corners16.image fun c => x + radius m • c), ?_⟩
  intro z hz w hw
  obtain ⟨x, hx, hzx⟩ := Set.mem_iUnion₂.mp (hT hz)
  have hzx' : ‖z - x‖ < radius m := by simpa [Metric.mem_ball, dist_eq_norm] using hzx
  have hwz := norm_sub_le_of_mem_centred_sqQ z m hw
  have hwx : w ∈ Metric.ball x (2 * radius m) := by
    rw [Metric.mem_ball, dist_eq_norm]
    calc
      ‖w - x‖ = ‖(w - z) + (z - x)‖ := by congr 1; abel
      _ ≤ ‖w - z‖ + ‖z - x‖ := norm_add_le _ _
      _ < 2 * radius m := by linarith
  obtain ⟨c, hc, hwc⟩ := Set.mem_iUnion₂.mp (ball_subset_iUnion_sqQ x m hwx)
  apply Set.mem_iUnion₂.mpr
  refine ⟨x + radius m • c, ?_, hwc⟩
  exact Finset.mem_biUnion.mpr ⟨x, hx, Finset.mem_image.mpr ⟨c, hc, rfl⟩⟩

/-- Changing the center multiplies the approximation by the exponential of
the difference of the two circle averages. -/
theorem lqgApprox_recentred_eq_mul_recentred {Ω : Type*} (H : ℝ → ℂ → Ω → ℝ)
    (ω : Ω) (γ : ℝ) {ε r : ℝ} (z v : ℂ) {S : Set ℂ} (hS : MeasurableSet S) :
    lqgApprox γ (fun s w => H (ε * s) w ω - H ε z ω) (r / ε) S =
      ENNReal.ofReal (Real.exp (γ * (H ε v ω - H ε z ω))) *
        lqgApprox γ (fun s w => H (ε * s) w ω - H ε v ω) (r / ε) S := by
  rw [lqgApprox, lqgApprox, withDensity_apply _ hS, withDensity_apply _ hS]
  rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  apply lintegral_congr
  intro w
  rw [← ENNReal.ofReal_mul (Real.exp_nonneg _)]
  congr 1
  have he : Real.exp (γ * (H (ε * (r / ε)) w ω - H ε z ω)) =
      Real.exp (γ * (H ε v ω - H ε z ω)) *
        Real.exp (γ * (H (ε * (r / ε)) w ω - H ε v ω)) := by
    rw [← Real.exp_add]
    congr 1
    ring
  rw [he]
  ring

/-- A finite cover compares a moving square with fixed squares of the same
scale, using the same circle-average field at every level. -/
theorem normalized_recentred_square_mass_le_sum_of_cover {Ω : Type*}
    (H : ℝ → ℂ → Ω → ℝ) (γ : ℝ) (z : ℂ) (m k : ℕ) (ω : Ω)
    (A : Finset ℂ) (hcover : sqQ (sqCorner z (radius m)) m ⊆
      ⋃ a ∈ A, sqQ a m) :
    normalizedRecentredSquareMass H γ z m k ω ≤
      ∑ a ∈ A, ENNReal.ofReal (Real.exp (γ *
        (H (2 * radius m) (a + radius m • sqCentre) ω - H (2 * radius m) z ω))) *
        normalizedRecentredSquareMass H γ (a + radius m • sqCentre) m k ω := by
  let ε : ℝ := 2 * radius m
  let r : ℝ := radius (m + k)
  let α : ℝ≥0∞ := ENNReal.ofReal (ε⁻¹ ^ 2)
  let μ := lqgApprox γ (fun s w => H (ε * s) w ω - H ε z ω) (r / ε)
  have hle : μ (sqQ (sqCorner z (radius m)) m) ≤ ∑ a ∈ A, μ (sqQ a m) :=
    (measure_mono hcover).trans (measure_biUnion_finset_le A (fun a => sqQ a m))
  change α * μ (sqQ (sqCorner z (radius m)) m) ≤ _
  calc
    _ ≤ α * ∑ a ∈ A, μ (sqQ a m) := by gcongr
    _ = _ := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro a ha
      have heq : sqCorner (a + radius m • sqCentre) (radius m) = a := by simp [sqCorner]
      change α * lqgApprox γ (fun s w => H (ε * s) w ω - H ε z ω) (r / ε) (sqQ a m) = _
      rw [lqgApprox_recentred_eq_mul_recentred H ω γ z (a + radius m • sqCentre)
        (measurableSet_sqQ a m)]
      unfold normalizedRecentredSquareMass
      rw [heq]
      change α * (_ * _) = _ * (α * _)
      exact mul_left_comm _ _ _

/-- Almost surely, the masses at all approximation levels are uniformly
bounded over a compact set of centers, simultaneously for every scale. -/
theorem ae_exists_compact_bound_iSup_normalized_recentred_square_mass
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {H : ℝ → ℂ → Ω → ℝ}
    (hH : LQGDimension.IsGFFCircleAverage H P)
    (hHm : ∀ r z, Measurable (H r z)) {γ p q : ℝ}
    (hγ : 0 < γ) (hγ2 : γ < 2) (hp : 1 < p) (hpq : p < q)
    (hq : q < 4 / γ ^ 2) (K : Set ℂ) (hK : IsCompact K) :
    ∀ᵐ ω ∂P, ∀ m, ∃ C : ℝ≥0∞, C < ⊤ ∧ ∀ z ∈ K, ∀ k,
      normalizedRecentredSquareMass H γ z m k ω ≤ C := by
  classical
  apply ae_all_iff.mpr
  intro m
  obtain ⟨A, hA⟩ := exists_finset_sqQ_cover_compact K hK m
  let v : ℂ → ℂ := fun a => a + radius m • sqCentre
  let D : Set ℂ := v '' (A : Set ℂ)
  have hD : D.Countable := A.finite_toSet.countable.image v
  filter_upwards [ae_iSup_normalized_recentred_square_mass_ne_top_of_countable
    hH hHm hγ hγ2 hp hpq hq D hD] with ω hω
  have hε : 0 < 2 * radius m := mul_pos (by norm_num) (radius_pos m)
  obtain ⟨B, hB⟩ := hK.bddAbove_image
    ((Real.continuous_exp.comp (continuous_const.mul (hH.continuous _ hε ω))).continuousOn)
  let F : ℂ → ℝ≥0∞ := fun a =>
    ENNReal.ofReal (Real.exp (γ * H (2 * radius m) (v a) ω)) * ENNReal.ofReal B *
      (⨆ k, normalizedRecentredSquareMass H γ (v a) m k ω)
  have hF : ∀ a ∈ A, F a ≠ ⊤ := by
    intro a ha
    apply ENNReal.mul_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top)
    exact hω (v a) ⟨a, ha, rfl⟩ m
  refine ⟨∑ a ∈ A, F a, lt_top_iff_ne_top.mpr (ENNReal.sum_ne_top.mpr hF), ?_⟩
  intro z hz k
  refine (normalized_recentred_square_mass_le_sum_of_cover H γ z m k ω A (hA z hz)).trans ?_
  apply Finset.sum_le_sum
  intro a ha
  have hexp : Real.exp (γ * (H (2 * radius m) (v a) ω - H (2 * radius m) z ω)) ≤
      Real.exp (γ * H (2 * radius m) (v a) ω) * B := by
    have heq : γ * (H (2 * radius m) (v a) ω - H (2 * radius m) z ω) =
        γ * H (2 * radius m) (v a) ω + -γ * H (2 * radius m) z ω := by ring
    rw [heq, Real.exp_add]
    exact mul_le_mul_of_nonneg_left (hB ⟨z, hz, rfl⟩) (Real.exp_nonneg _)
  have hc := ENNReal.ofReal_le_ofReal hexp
  rw [ENNReal.ofReal_mul (Real.exp_nonneg _)] at hc
  change _ * normalizedRecentredSquareMass H γ (v a) m k ω ≤ F a
  dsimp only [F]
  exact mul_le_mul' hc (le_iSup (fun k => normalizedRecentredSquareMass H γ (v a) m k ω) k)

end LatticeProb.LQG
