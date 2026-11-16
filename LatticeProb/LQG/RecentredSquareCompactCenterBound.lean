import LatticeProb.LQG.RecentredSquareMaximalMoment
import LatticeProb.LQG.CircleIncrementTripleIndependence
import LatticeProb.LQG.LQGOnePieceScaling
import LatticeProb.LQG.RecentredSquareGeometry
import LatticeProb.Bonanno.MatedCRTHarmonic.GMCFacts.OuterMoment
import LatticeProb.LQG.RecentredSquareCountableSupFiniteness
import LatticeProb.LQG.LQGBallMassRatioUniform

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

/-- The centered squares over a bounded disk admit a cover whose cardinality
is bounded in terms of the disk radius and the dyadic scale. -/
theorem exists_finset_sqQ_cover_ball (R : ℝ) (hR : 0 < R) (m : ℕ) :
    ∃ A : Finset ℂ, (A.card : ℝ) ≤
        (corners16.card : ℝ) * (4 * R / radius m + 1) ^ 2 ∧
      ∀ z ∈ Metric.ball (0 : ℂ) R, sqQ (sqCorner z (radius m)) m ⊆
        ⋃ a ∈ A, sqQ a m := by
  classical
  have hr : 0 < radius m := radius_pos m
  obtain ⟨G, hGcard, hGcov⟩ := LQGBallMassRatioUniform.exists_ball_grid hR hr
  let A := G.biUnion (fun x => corners16.image fun c => x + radius m • c)
  refine ⟨A, ?_, ?_⟩
  · have hc : A.card ≤ G.card * corners16.card := by
      calc
        A.card ≤ ∑ x ∈ G, (corners16.image fun c => x + radius m • c).card :=
          Finset.card_biUnion_le
        _ ≤ ∑ _x ∈ G, corners16.card :=
          Finset.sum_le_sum fun _ _ => Finset.card_image_le
        _ = G.card * corners16.card := by simp
    have hc' : (A.card : ℝ) ≤ (G.card : ℝ) * (corners16.card : ℝ) := by exact_mod_cast hc
    calc
      (A.card : ℝ) ≤ (G.card : ℝ) * (corners16.card : ℝ) := hc'
      _ ≤ (corners16.card : ℝ) * (4 * R / radius m + 1) ^ 2 := by
        nlinarith [mul_nonneg (show (0 : ℝ) ≤ corners16.card by positivity)
          (sub_nonneg.mpr hGcard)]
  · intro z hz w hw
    obtain ⟨x, hx, hzx⟩ := hGcov z hz
    have hzx' : ‖z - x‖ < radius m := by simpa [dist_eq_norm] using hzx
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

/-- A bounded disk has a quantitative square cover in which each centered
square is covered by a uniformly bounded subfamily. -/
theorem exists_finset_sqQ_local_cover_ball (R : ℝ) (hR : 0 < R) (m : ℕ) :
    ∃ A : Finset ℂ, (A.card : ℝ) ≤
        (corners16.card : ℝ) * (4 * R / radius m + 1) ^ 2 ∧
      ∀ z ∈ Metric.ball (0 : ℂ) R, ∃ B : Finset ℂ,
        B ⊆ A ∧ B.card ≤ corners16.card ∧
          sqQ (sqCorner z (radius m)) m ⊆ ⋃ b ∈ B, sqQ b m := by
  classical
  have hr : 0 < radius m := radius_pos m
  obtain ⟨G, hGcard, hGcov⟩ := LQGBallMassRatioUniform.exists_ball_grid hR hr
  let A := G.biUnion (fun x => corners16.image fun c => x + radius m • c)
  refine ⟨A, ?_, ?_⟩
  · have hc : A.card ≤ G.card * corners16.card := by
      calc
        A.card ≤ ∑ x ∈ G, (corners16.image fun c => x + radius m • c).card :=
          Finset.card_biUnion_le
        _ ≤ ∑ _x ∈ G, corners16.card :=
          Finset.sum_le_sum fun _ _ => Finset.card_image_le
        _ = G.card * corners16.card := by simp
    have hc' : (A.card : ℝ) ≤ (G.card : ℝ) * (corners16.card : ℝ) := by exact_mod_cast hc
    calc
      (A.card : ℝ) ≤ (G.card : ℝ) * (corners16.card : ℝ) := hc'
      _ ≤ (corners16.card : ℝ) * (4 * R / radius m + 1) ^ 2 := by
        nlinarith [mul_nonneg (show (0 : ℝ) ≤ corners16.card by positivity)
          (sub_nonneg.mpr hGcard)]
  · intro z hz
    obtain ⟨x, hx, hzx⟩ := hGcov z hz
    refine ⟨corners16.image (fun c => x + radius m • c), ?_, Finset.card_image_le, ?_⟩
    · intro b hb
      exact Finset.mem_biUnion.mpr ⟨x, hx, hb⟩
    · intro w hw
      have hzx' : ‖z - x‖ < radius m := by simpa [dist_eq_norm] using hzx
      have hwz := norm_sub_le_of_mem_centred_sqQ z m hw
      have hwx : w ∈ Metric.ball x (2 * radius m) := by
        rw [Metric.mem_ball, dist_eq_norm]
        calc
          ‖w - x‖ = ‖(w - z) + (z - x)‖ := by congr 1; abel
          _ ≤ ‖w - z‖ + ‖z - x‖ := norm_add_le _ _
          _ < 2 * radius m := by linarith
      obtain ⟨c, hc, hwc⟩ := Set.mem_iUnion₂.mp (ball_subset_iUnion_sqQ x m hwx)
      exact Set.mem_iUnion₂.mpr ⟨x + radius m • c, Finset.mem_image.mpr ⟨c, hc, rfl⟩, hwc⟩

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

/-- A coarse circle increment is independent of the family of recentred
circle averages whose circles lie inside the smaller circle. -/
theorem indepFun_coarse_increment_recentred_family
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {H : ℝ → ℂ → Ω → ℝ}
    (hH : LQGDimension.IsGFFCircleAverage H P) {r : ℝ} (hr : 0 < r) (hr1 : r ≤ 1)
    (z : ℂ) :
    ProbabilityTheory.IndepFun (fun ω => H r z ω - H 1 z ω)
      (fun ω (a : {a : ℝ × ℂ // 0 < a.1 ∧ ‖a.2 - z‖ + a.1 ≤ r}) =>
        H a.1.1 a.1.2 ω - H r z ω) P := by
  classical
  let X : Set.Ioi (0 : ℝ) × ℂ → Ω → ℝ := fun a => H a.1 a.2
  have hX : ProbabilityTheory.IsGaussianProcess X P := hH.isGaussianProcess
  have hD : (fun ω => H r z ω - H 1 z ω) ∈ Submodule.span ℝ (Set.range X) :=
    LatticeProb.GaussIndep.fun_sub_mem_span_range X (⟨r, hr⟩, z) (⟨1, by norm_num⟩, z)
  have hB : ∀ a : {a : ℝ × ℂ // 0 < a.1 ∧ ‖a.2 - z‖ + a.1 ≤ r},
      (fun ω => H a.1.1 a.1.2 ω - H r z ω) ∈ Submodule.span ℝ (Set.range X) := by
    intro a
    exact LatticeProb.GaussIndep.fun_sub_mem_span_range X (⟨a.1.1, a.2.1⟩, a.1.2) (⟨r, hr⟩, z)
  apply LatticeProb.GaussIndep.indepFun_real_of_mem_span_of_covariance_eq_zero hX hD hB
  intro a
  have hinside1 : ‖a.1.2 - z‖ + a.1.1 ≤ (1 : ℝ) := le_trans a.2.2 hr1
  rw [covariance_increment_recentred hH hr (by norm_num) a.2.1 hr,
    LQGMetric.CircleAvg.circCov_comm hr a.2.1,
    LQGMetric.CircleAvg.circCov_comm (by norm_num) a.2.1,
    circCov_of_inside a.2.1 hr a.2.2,
    circCov_of_inside a.2.1 (by norm_num) hinside1,
    MatedCRTHarmonic.MoTPort.ConeArea6.circCov_same hr hr,
    MatedCRTHarmonic.MoTPort.ConeArea6.circCov_same (by norm_num) hr]
  simp [max_self, max_eq_right hr1]

/-- The coarse circle increment is independent of the maximal normalized
recentred mass on the centered square. -/
theorem indepFun_coarse_increment_iSup_normalized_recentred_square_mass
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {H : ℝ → ℂ → Ω → ℝ}
    (hH : LQGDimension.IsGFFCircleAverage H P) (γ : ℝ) (z : ℂ) (m : ℕ)
    (hm : 2 * radius m ≤ 1) :
    ProbabilityTheory.IndepFun (fun ω => H (2 * radius m) z ω - H 1 z ω)
      (fun ω => ⨆ k, normalizedRecentredSquareMass H γ z m k ω) P := by
  classical
  let ε := 2 * radius m
  have hε : 0 < ε := mul_pos (by norm_num) (radius_pos m)
  let A := {a : ℝ × ℂ // 0 < a.1 ∧ ‖a.2 - z‖ + a.1 ≤ ε}
  let Y : Ω → A → ℝ := fun ω a => H a.1.1 a.1.2 ω - H ε z ω
  have hind := indepFun_coarse_increment_recentred_family hH hε hm z
  have hcont0 : ∀ k ω, Continuous (fun w : ℂ => H (radius (m + k)) w ω) :=
    fun k ω => hH.continuous _ (radius_pos (m + k)) ω
  let 𝒢 : MeasurableSpace Ω := MeasurableSpace.comap Y MeasurableSpace.pi
  let S := sqQ (sqCorner z (radius m)) m
  have hS : MeasurableSet S := measurableSet_sqQ _ _
  have hfinite : IsFiniteMeasure (Measure.comap Subtype.val (volume : Measure ℂ) : Measure S) :=
    ⟨by rw [(MeasurableEmbedding.subtype_coe hS).comap_apply, Subtype.coe_image_univ]
        change volume (sqQ (sqCorner z (radius m)) m) < ⊤
        rw [volume_centred_sqQ]; exact ENNReal.ofReal_lt_top⟩
  let J (k : ℕ) (w : S) : A := ⟨(radius (m + k), w.1), radius_pos _,
    norm_add_radius_le_of_mem_centred_sqQ z (by dsimp [ε]; linarith [radius_pos m]) k w.2⟩
  have hY : ∀ k (w : S), Measurable[𝒢] (fun ω => Y ω (J k w)) := fun k w =>
    (measurable_pi_apply (J k w)).comp (comap_measurable Y)
  have hcont : ∀ k ω, Continuous (fun w : S => Y ω (J k w)) := by
    intro k ω
    exact ((hcont0 k ω).comp continuous_subtype_val).sub continuous_const
  have hM : ∀ k, Measurable[𝒢] (normalizedRecentredSquareMass H γ z m k) := by
    intro k
    let F : ℝ → ℝ≥0∞ := fun x => ENNReal.ofReal
      ((radius (m + k) / ε) ^ (γ ^ 2 / 2) * Real.exp (γ * x))
    have hF : Measurable F := Measurable.ennreal_ofReal (by fun_prop)
    have hI : Measurable[𝒢] (fun ω => ∫⁻ w : S, F (Y ω (J k w))
        ∂(Measure.comap Subtype.val (volume : Measure ℂ))) :=
      LatticeProb.measurable_lintegral_of_continuous _ (hcont k) (hY k) hF
    have heq : normalizedRecentredSquareMass H γ z m k = fun ω =>
        ENNReal.ofReal (ε⁻¹ ^ 2) * ∫⁻ w : S, F (Y ω (J k w))
          ∂(Measure.comap Subtype.val (volume : Measure ℂ)) := by
      funext ω
      unfold normalizedRecentredSquareMass lqgApprox
      rw [withDensity_apply _ hS, ← lintegral_subtype_comap hS]
      simp only [F, Y, J, ε, mul_div_cancel₀ _ hε.ne']
    rw [heq]
    exact hI.const_mul _
  exact ProbabilityTheory.indep_of_indep_of_le_right hind
    (measurable_iff_comap_le.1 (Measurable.iSup hM))

/-- The exponential moment of a coarse circle increment. -/
theorem lintegral_exp_coarse_circle_increment
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {H : ℝ → ℂ → Ω → ℝ}
    (hH : LQGDimension.IsGFFCircleAverage H P) {r : ℝ} (hr : 0 < r) (hr1 : r ≤ 1)
    (z : ℂ) (t : ℝ) :
    ∫⁻ ω, ENNReal.ofReal (Real.exp (t * (H r z ω - H 1 z ω))) ∂P =
      ENNReal.ofReal (r ^ (-(t ^ 2 / 2))) := by
  let : IsProbabilityMeasure P := hH.isProbabilityMeasure
  have hg : ProbabilityTheory.HasGaussianLaw (fun ω => H r z ω - H 1 z ω) P :=
    hH.isGaussianProcess.hasGaussianLaw_fun_sub (s := (⟨r, hr⟩, z)) (t := (⟨1, by norm_num⟩, z))
  have hmean : ∫ ω, (H r z ω - H 1 z ω) ∂P = 0 := by
    simpa using integral_recentred hH 1 (by norm_num) hr z z
  have hv : ProbabilityTheory.variance (fun ω => H r z ω - H 1 z ω) P = -Real.log r := by
    rw [← ProbabilityTheory.covariance_self hg.aemeasurable,
      cov_recentred hH (by norm_num) hr hr z z z,
      MatedCRTHarmonic.MoTPort.ConeArea6.circCov_same hr hr,
      MatedCRTHarmonic.MoTPort.ConeArea6.circCov_same hr (by norm_num),
      MatedCRTHarmonic.MoTPort.ConeArea6.circCov_same (by norm_num) hr,
      MatedCRTHarmonic.MoTPort.ConeArea6.circCov_same (by norm_num) (by norm_num)]
    simp [max_self, max_eq_left hr1, max_eq_right hr1]
  obtain ⟨hint, he⟩ := integral_exp_mul_of_hasGaussianLaw hg hmean t
  rw [← ofReal_integral_eq_lintegral_ofReal hint (Filter.Eventually.of_forall fun _ =>
    (Real.exp_pos _).le), he, hv, Real.rpow_def_of_pos hr]
  congr 1
  ring

/-- A joint moment bound for the coarse circle exponential and maximal
normalized square mass, uniform in the center and scale. -/
theorem exists_lintegral_exp_coarse_mul_iSup_square_rpow_le
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {H : ℝ → ℂ → Ω → ℝ}
    (hH : LQGDimension.IsGFFCircleAverage H P)
    (hHm : ∀ r z, Measurable (H r z)) {γ p q : ℝ}
    (hγ : 0 < γ) (hγ2 : γ < 2) (hp : 1 < p) (hpq : p < q)
    (hq : q < 4 / γ ^ 2) :
    ∃ C : ℝ≥0∞, C < ⊤ ∧ ∀ (z : ℂ) (m : ℕ), 2 * radius m ≤ 1 →
      (∫⁻ ω, ENNReal.ofReal (Real.exp ((p * γ) *
        (H (2 * radius m) z ω - H 1 z ω))) *
        (⨆ k, normalizedRecentredSquareMass H γ z m k ω) ^ p ∂P) ≤
      ENNReal.ofReal ((2 * radius m) ^ (-((p * γ) ^ 2 / 2))) * C := by
  obtain ⟨C, hC, hbound⟩ :=
    exists_lintegral_iSup_normalized_recentred_square_rpow_le hH hHm hγ hγ2 hp hpq hq
  refine ⟨C, hC, ?_⟩
  intro z m hm
  have hε : 0 < 2 * radius m := mul_pos (by norm_num) (radius_pos m)
  have hφ : Measurable (fun x : ℝ => ENNReal.ofReal (Real.exp ((p * γ) * x))) := by
    fun_prop
  have hf : AEMeasurable (fun ω => ENNReal.ofReal (Real.exp ((p * γ) *
      (H (2 * radius m) z ω - H 1 z ω)))) P :=
    (hφ.comp ((hHm (2 * radius m) z).sub (hHm 1 z))).aemeasurable
  have hg : AEMeasurable (fun ω => (⨆ k, normalizedRecentredSquareMass H γ z m k ω) ^ p) P := by
    apply AEMeasurable.pow_const
    apply AEMeasurable.iSup
    intro k
    exact ((measurable_recentred_square_mass hH hHm γ (2 * radius m) hε.ne' z m k).const_mul _).aemeasurable
  have hi := (indepFun_coarse_increment_iSup_normalized_recentred_square_mass hH γ z m hm).comp
    hφ (measurable_id.pow_const p)
  rw [ProbabilityTheory.lintegral_mul_eq_lintegral_mul_lintegral_of_indepFun'' hf hg hi,
    lintegral_exp_coarse_circle_increment hH hε hm z (p * γ)]
  exact mul_le_mul' le_rfl (hbound z m).1

/-- Rescaling and recentering express the original approximation on the same set. -/
theorem lqgApprox_eq_mul_recentred_rescaled {Ω : Type*}
    (H : ℝ → ℂ → Ω → ℝ) (ω : Ω) (γ : ℝ) {ε r : ℝ}
    (hε : 0 < ε) (hr : 0 < r) (z : ℂ) {S : Set ℂ} (hS : MeasurableSet S) :
    lqgApprox γ (fun s w => H s w ω) r S =
      ENNReal.ofReal (ε ^ (γ ^ 2 / 2) * Real.exp (γ * H ε z ω)) *
        lqgApprox γ (fun s w => H (ε * s) w ω - H ε z ω) (r / ε) S := by
  rw [lqgApprox, lqgApprox, withDensity_apply _ hS, withDensity_apply _ hS,
    ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  apply lintegral_congr
  intro w
  rw [← ENNReal.ofReal_mul (by positivity)]
  congr 1
  rw [mul_div_cancel₀ r hε.ne', Real.div_rpow hr.le hε.le,
    Real.rpow_def_of_pos hr, Real.rpow_def_of_pos hε]
  rw [← Real.exp_sub]
  simp only [← Real.exp_add]
  congr 1
  ring

/-- An uncentered square approximation is the normalized recentred square
mass multiplied by its exact scale and circle-average factors. -/
theorem lqgApprox_square_eq_mul_normalized_recentred_square_mass {Ω : Type*}
    (H : ℝ → ℂ → Ω → ℝ) (ω : Ω) (γ : ℝ) (z : ℂ) (m k : ℕ) :
    lqgApprox γ (fun s w => H s w ω) (radius (m + k))
        (sqQ (sqCorner z (radius m)) m) =
      ENNReal.ofReal ((2 * radius m) ^ (γ ^ 2 / 2) *
        Real.exp (γ * H (2 * radius m) z ω)) *
      (ENNReal.ofReal ((2 * radius m) ^ 2) * normalizedRecentredSquareMass H γ z m k ω) := by
  have hε : 0 < 2 * radius m := mul_pos (by norm_num) (radius_pos m)
  have hfactor : ENNReal.ofReal ((2 * radius m) ^ 2) *
      ENNReal.ofReal ((2 * radius m)⁻¹ ^ 2) = 1 := by
    rw [← ENNReal.ofReal_mul (sq_nonneg _), ← mul_pow, mul_inv_cancel₀ hε.ne', one_pow,
      ENNReal.ofReal_one]
  rw [normalizedRecentredSquareMass, ← mul_assoc (ENNReal.ofReal ((2 * radius m) ^ 2)),
    hfactor, one_mul]
  exact lqgApprox_eq_mul_recentred_rescaled H ω γ hε (radius_pos _) z (measurableSet_sqQ _ _)

/-- Removing the unit-circle factor leaves a coarse increment times the
normalized recentred square mass. -/
theorem tilted_lqgApprox_square_eq {Ω : Type*}
    (H : ℝ → ℂ → Ω → ℝ) (ω : Ω) (γ : ℝ) (z : ℂ) (m k : ℕ) :
    ENNReal.ofReal (Real.exp (-γ * H 1 z ω)) *
      lqgApprox γ (fun s w => H s w ω) (radius (m + k))
        (sqQ (sqCorner z (radius m)) m) =
      ENNReal.ofReal ((2 * radius m) ^ (γ ^ 2 / 2) * (2 * radius m) ^ 2) *
        (ENNReal.ofReal (Real.exp (γ * (H (2 * radius m) z ω - H 1 z ω))) *
          normalizedRecentredSquareMass H γ z m k ω) := by
  have hε : 0 < 2 * radius m := mul_pos (by norm_num) (radius_pos m)
  have hf : ENNReal.ofReal (Real.exp (-γ * H 1 z ω)) *
      ENNReal.ofReal ((2 * radius m) ^ (γ ^ 2 / 2) *
        Real.exp (γ * H (2 * radius m) z ω)) * ENNReal.ofReal ((2 * radius m) ^ 2) =
      ENNReal.ofReal ((2 * radius m) ^ (γ ^ 2 / 2) * (2 * radius m) ^ 2) *
        ENNReal.ofReal (Real.exp (γ * (H (2 * radius m) z ω - H 1 z ω))) := by
    rw [← ENNReal.ofReal_mul (Real.exp_nonneg _),
      ← ENNReal.ofReal_mul (mul_nonneg (Real.exp_nonneg _) (by positivity)),
      ← ENNReal.ofReal_mul (by positivity)]
    congr 1
    calc
      _ = ((2 * radius m) ^ (γ ^ 2 / 2) * (2 * radius m) ^ 2) *
          (Real.exp (-γ * H 1 z ω) * Real.exp (γ * H (2 * radius m) z ω)) := by ring
      _ = _ := by rw [← Real.exp_add]; congr 2; ring
  rw [lqgApprox_square_eq_mul_normalized_recentred_square_mass]
  simp only [← mul_assoc]
  rw [hf]

/-- The maximal tilted square mass has a uniform scale-dependent positive
moment bound. -/
theorem exists_lintegral_iSup_tilted_square_rpow_le
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {H : ℝ → ℂ → Ω → ℝ}
    (hH : LQGDimension.IsGFFCircleAverage H P)
    (hHm : ∀ r z, Measurable (H r z)) {γ p q : ℝ}
    (hγ : 0 < γ) (hγ2 : γ < 2) (hp : 1 < p) (hpq : p < q)
    (hq : q < 4 / γ ^ 2) :
    ∃ C : ℝ≥0∞, C < ⊤ ∧ ∀ (z : ℂ) (m : ℕ), 2 * radius m ≤ 1 →
      (∫⁻ ω, (⨆ k, ENNReal.ofReal (Real.exp (-γ * H 1 z ω)) *
        lqgApprox γ (fun s w => H s w ω) (radius (m + k))
          (sqQ (sqCorner z (radius m)) m)) ^ p ∂P) ≤
      ENNReal.ofReal ((2 * radius m) ^ (γ ^ 2 / 2) * (2 * radius m) ^ 2) ^ p *
        (ENNReal.ofReal ((2 * radius m) ^ (-((p * γ) ^ 2 / 2))) * C) := by
  obtain ⟨C, hC, hbound⟩ :=
    exists_lintegral_exp_coarse_mul_iSup_square_rpow_le hH hHm hγ hγ2 hp hpq hq
  refine ⟨C, hC, ?_⟩
  intro z m hm
  have hp0 : 0 ≤ p := by linarith
  have heq (ω : Ω) :
      (⨆ k, ENNReal.ofReal (Real.exp (-γ * H 1 z ω)) *
        lqgApprox γ (fun s w => H s w ω) (radius (m + k))
          (sqQ (sqCorner z (radius m)) m)) ^ p =
      ENNReal.ofReal ((2 * radius m) ^ (γ ^ 2 / 2) * (2 * radius m) ^ 2) ^ p *
        (ENNReal.ofReal (Real.exp ((p * γ) * (H (2 * radius m) z ω - H 1 z ω))) *
          (⨆ k, normalizedRecentredSquareMass H γ z m k ω) ^ p) := by
    simp_rw [tilted_lqgApprox_square_eq H ω γ z m, ← ENNReal.mul_iSup]
    rw [ENNReal.mul_rpow_of_nonneg _ _ hp0, ENNReal.mul_rpow_of_nonneg _ _ hp0,
      ENNReal.ofReal_rpow_of_nonneg (Real.exp_nonneg _) hp0, ← Real.exp_mul]
    congr 3
    ring
  simp_rw [heq, lintegral_const_mul' _ _
    (ENNReal.rpow_ne_top_of_nonneg hp0 ENNReal.ofReal_ne_top)]
  exact mul_le_mul' le_rfl (hbound z m hm)

/-- For every subcritical parameter there are admissible moments with a
strictly positive exponent after a two-dimensional union bound. -/
theorem exists_square_moment_exponents {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) :
    ∃ p q κ : ℝ, 1 < p ∧ p < q ∧ q < 4 / γ ^ 2 ∧ 0 < κ ∧
      2 + p * κ < 2 * p + γ ^ 2 * p / 2 - (p * γ) ^ 2 / 2 := by
  let p : ℝ := 2 / γ
  let q : ℝ := (p + 4 / γ ^ 2) / 2
  let κ : ℝ := (2 - γ) ^ 2 / (2 * γ * p)
  have hp : 1 < p := by dsimp [p]; rw [lt_div_iff₀ hγ]; linarith
  have hpq : p < 4 / γ ^ 2 := by
    dsimp [p]
    rw [div_lt_div_iff₀ hγ (sq_pos_of_pos hγ)]
    nlinarith
  have hκ : 0 < κ := by dsimp [κ]; positivity
  refine ⟨p, q, κ, hp, ?_, ?_, hκ, ?_⟩
  · dsimp [q]; linarith
  · dsimp [q]; linarith
  · have hmargin : 0 < (2 - γ) ^ 2 / γ := by positivity
    have heq : 2 * p + γ ^ 2 * p / 2 - (p * γ) ^ 2 / 2 - 2 =
        (2 - γ) ^ 2 / γ := by dsimp [p]; field_simp; ring
    have hk : p * κ = (2 - γ) ^ 2 / (2 * γ) := by
      dsimp [κ]; field_simp
    rw [hk]
    have : (2 - γ) ^ 2 / (2 * γ) = ((2 - γ) ^ 2 / γ) / 2 := by ring
    rw [this]
    linarith

end LatticeProb.LQG
