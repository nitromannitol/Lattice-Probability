import LatticeProb.LQG.CompactBallApproximantPower

/-! # Compact-center approximation bounds with a uniform exponent -/

open MeasureTheory Set
open scoped ENNReal
open QuantumZipper
open MatedCRTHarmonic.GMCFacts LQGMetric.DGMC LQGMetric.DGMC.Neg3

namespace LatticeProb.LQG

private theorem ae_eventually_finset_tilted_square_power_bound_fixed
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {H : ℝ → ℂ → Ω → ℝ}
    (hH : LQGDimension.IsGFFCircleAverage H P)
    (hHm : ∀ r z, Measurable (H r z)) {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2)
    {p q κ : ℝ} (hp : 1 < p) (hpq : p < q) (hq : q < 4 / γ ^ 2)
    (hexp : 2 + p * κ < 2 * p + γ ^ 2 * p / 2 - (p * γ) ^ 2 / 2)
    (S : ℕ → Finset ℂ) {A : ℝ≥0∞} (hA : A < ⊤)
    (hcard : ∀ m, ((S m).card : ℝ≥0∞) ≤ A * ENNReal.ofReal (radius m ^ (-2 : ℝ))) :
    ∀ᵐ ω ∂P, ∀ᶠ m in Filter.atTop,
      (S m).sup (fun z => ⨆ k, ENNReal.ofReal (Real.exp (-γ * H 1 z ω)) *
        lqgApprox γ (fun s w => H s w ω) (radius (m + 1 + k))
          (sqQ (sqCorner z (radius (m + 1))) (m + 1))) <
        ENNReal.ofReal (radius m ^ κ) := by
  obtain ⟨C, hC, htail⟩ := exists_measure_finset_sup_iSup_tilted_square_le hH hHm hγ hγ2 hp hpq hq
  let α : ℝ := 2 * p + γ ^ 2 * p / 2 - (p * γ) ^ 2 / 2
  have hδ : 0 < α - 2 - κ * p := by dsimp [α]; nlinarith
  have hscale (m : ℕ) : 2 * radius (m + 1) = radius m := by
    unfold radius
    rw [pow_succ]
    ring
  have hr1 (m : ℕ) : radius m ≤ 1 := by unfold radius; exact pow_le_one₀ (by norm_num) (by norm_num)
  let E : ℕ → Set Ω := fun m => {ω | ENNReal.ofReal (radius m ^ κ) ≤
    (S m).sup fun z => ⨆ k, ENNReal.ofReal (Real.exp (-γ * H 1 z ω)) *
      lqgApprox γ (fun s w => H s w ω) (radius (m + 1 + k))
        (sqQ (sqCorner z (radius (m + 1))) (m + 1))}
  have htail' (m : ℕ) : P (E m) ≤ (A * C) * ENNReal.ofReal (radius m ^ (α - 2 - κ * p)) := by
    have ht := htail (S m) (m + 1) (by rw [hscale]; exact hr1 m)
      (radius m ^ κ) (Real.rpow_pos_of_pos (radius_pos m) κ)
    rw [hscale] at ht
    calc
      P (E m) ≤ ((S m).card : ℝ≥0∞) *
          ((ENNReal.ofReal (radius m ^ α) * C) / ENNReal.ofReal ((radius m ^ κ) ^ p)) := ht
      _ ≤ (A * ENNReal.ofReal (radius m ^ (-2 : ℝ))) *
          ((ENNReal.ofReal (radius m ^ α) * C) / ENNReal.ofReal ((radius m ^ κ) ^ p)) :=
        mul_le_mul' (hcard m) le_rfl
      _ = (A * C) * ENNReal.ofReal (radius m ^ (α - 2 - κ * p)) := by
        rw [mul_assoc, square_grid_tail_factor_eq (radius_pos m) C]
        ring
  have hfin : (∑' m, P (E m)) ≠ ⊤ := by
    apply ne_top_of_le_ne_top _ (ENNReal.tsum_le_tsum htail')
    rw [ENNReal.tsum_mul_left]
    exact ENNReal.mul_ne_top (ENNReal.mul_ne_top hA.ne hC.ne) (tsum_ofReal_radius_rpow_ne_top hδ)
  filter_upwards [MeasureTheory.ae_eventually_notMem hfin] with ω hω
  filter_upwards [hω] with m hm
  exact lt_of_not_ge hm


private theorem ae_eventually_finset_coarse_unit_tilted_square_power_bound_fixed
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {H : ℝ → ℂ → Ω → ℝ}
    (hH : LQGDimension.IsGFFCircleAverage H P)
    (hHm : ∀ r z, Measurable (H r z)) {γ : ℝ} (hγ : 0 < γ)
    {p κ : ℝ} (hp : 1 < p)
    (hκ : 0 < κ) (hexp : 2 + p * κ < 2 * p + γ ^ 2 * p / 2 - (p * γ) ^ 2 / 2)
    (S : ℕ → Finset ℂ) {A : ℝ≥0∞} (hA : A < ⊤)
    (hcard : ∀ m, ((S m).card : ℝ≥0∞) ≤ A * ENNReal.ofReal (radius m ^ (-2 : ℝ))) :
    ∀ᵐ ω ∂P, ∀ᶠ m in Filter.atTop,
      (S m).sup (fun z => (Finset.range (m + 2)).sup fun n =>
        unitTiltedSquareMass H γ z (m + 1) n ω) < ENNReal.ofReal (radius m ^ κ) := by
  obtain ⟨C, hC, htail⟩ := exists_measure_finset_sup_coarse_unit_tilted_square_le hH hHm hγ hp
  let α : ℝ := 2 * p + γ ^ 2 * p / 2 - (p * γ) ^ 2 / 2
  have hp0 : 0 < p := by linarith
  have hα : 0 ≤ α := by dsimp [α]; nlinarith [mul_pos hp0 hκ]
  have hδ : 0 < α - 2 - κ * p := by dsimp [α]; nlinarith
  let E : ℕ → Set Ω := fun m => {ω | ENNReal.ofReal (radius m ^ κ) ≤
    (S m).sup fun z => (Finset.range (m + 2)).sup fun n =>
      unitTiltedSquareMass H γ z (m + 1) n ω}
  have htail' (m : ℕ) : P (E m) ≤ (A * C) * ENNReal.ofReal (radius m ^ (α - 2 - κ * p)) := by
    have ht := htail (S m) (m + 1) (radius m ^ κ) (Real.rpow_pos_of_pos (radius_pos m) κ)
    have hpow : ENNReal.ofReal (radius (m + 1) ^ α) ≤ ENNReal.ofReal (radius m ^ α) := by
      apply ENNReal.ofReal_le_ofReal
      exact Real.rpow_le_rpow (radius_pos (m + 1)).le
        (QuantumZipper.AreaExist.aradius_anti (by omega)) hα
    calc
      P (E m) ≤ ((S m).card : ℝ≥0∞) *
          ((ENNReal.ofReal (radius (m + 1) ^ α) * C) / ENNReal.ofReal ((radius m ^ κ) ^ p)) := ht
      _ ≤ (A * ENNReal.ofReal (radius m ^ (-2 : ℝ))) *
          ((ENNReal.ofReal (radius m ^ α) * C) / ENNReal.ofReal ((radius m ^ κ) ^ p)) :=
        mul_le_mul' (hcard m) (ENNReal.div_le_div_right (mul_le_mul' hpow le_rfl) _)
      _ = (A * C) * ENNReal.ofReal (radius m ^ (α - 2 - κ * p)) := by
        rw [mul_assoc, square_grid_tail_factor_eq (radius_pos m) C]
        ring
  have hfin : (∑' m, P (E m)) ≠ ⊤ := by
    apply ne_top_of_le_ne_top _ (ENNReal.tsum_le_tsum htail')
    rw [ENNReal.tsum_mul_left]
    exact ENNReal.mul_ne_top (ENNReal.mul_ne_top hA.ne hC.ne) (tsum_ofReal_radius_rpow_ne_top hδ)
  filter_upwards [MeasureTheory.ae_eventually_notMem hfin] with ω hω
  filter_upwards [hω] with m hm
  exact lt_of_not_ge hm



private theorem exists_bounded_square_covers_ae_eventually_tilted_power_fixed
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {H : ℝ → ℂ → Ω → ℝ}
    (hH : LQGDimension.IsGFFCircleAverage H P)
    (hHm : ∀ r z, Measurable (H r z)) {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2)
    {p q κ : ℝ} (hp : 1 < p) (hpq : p < q) (hq : q < 4 / γ ^ 2)
    (_hκ : 0 < κ) (hexp : 2 + p * κ < 2 * p + γ ^ 2 * p / 2 - (p * γ) ^ 2 / 2)
    (R : ℝ) (hR : 0 < R) :
    ∃ S : ℕ → Finset ℂ, (∀ m v, v ∈ S m → ‖v‖ ≤ R + 2) ∧
      (∀ m z, z ∈ Metric.ball (0 : ℂ) R → ∃ T : Finset ℂ,
        T ⊆ S m ∧ T.card ≤ corners16.card ∧
          sqQ (sqCorner z (radius (m + 1))) (m + 1) ⊆
            ⋃ v ∈ T, sqQ (sqCorner v (radius (m + 1))) (m + 1)) ∧
      ∀ᵐ ω ∂P, ∀ᶠ m in Filter.atTop,
        (S m).sup (fun z => ⨆ k, ENNReal.ofReal (Real.exp (-γ * H 1 z ω)) *
          lqgApprox γ (fun s w => H s w ω) (radius (m + 1 + k))
            (sqQ (sqCorner z (radius (m + 1))) (m + 1))) <
          ENNReal.ofReal (radius m ^ κ) := by
  classical
  choose S hS using fun m => exists_finset_bounded_centred_sqQ_local_cover_ball R hR (m + 1)
  refine ⟨S, fun m v hv => (hS m).2.1 v hv, fun m z hz => (hS m).2.2 z hz, ?_⟩
  let D : ℝ := (corners16.card : ℝ) * (8 * R + 1) ^ 2
  have hD : 0 ≤ D := by dsimp [D]; positivity
  apply ae_eventually_finset_tilted_square_power_bound_fixed hH hHm hγ hγ2 hp hpq hq hexp S
    (A := ENNReal.ofReal D) ENNReal.ofReal_lt_top
  intro m
  have hc : ((S m).card : ℝ) ≤ D * radius m ^ (-2 : ℝ) :=
    ((hS m).1).trans (square_cover_cardinal_scale_le R hR m)
  calc
    ((S m).card : ℝ≥0∞) = ENNReal.ofReal ((S m).card : ℝ) := by simp
    _ ≤ ENNReal.ofReal (D * radius m ^ (-2 : ℝ)) := ENNReal.ofReal_le_ofReal hc
    _ = _ := ENNReal.ofReal_mul hD


private theorem ae_exists_compact_center_fine_level_square_power_bound_fixed
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {H : ℝ → ℂ → Ω → ℝ}
    (hH : LQGDimension.IsGFFCircleAverage H P)
    (hHm : ∀ r z, Measurable (H r z)) {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2)
    {p q κ : ℝ} (hp : 1 < p) (hpq : p < q) (hq : q < 4 / γ ^ 2)
    (hκ : 0 < κ) (hexp : 2 + p * κ < 2 * p + γ ^ 2 * p / 2 - (p * γ) ^ 2 / 2)
    (R : ℝ) (hR : 0 < R) :
    ∀ᵐ ω ∂P, ∃ C : ℝ≥0∞, C < ⊤ ∧
      ∀ᶠ m in Filter.atTop, ∀ z ∈ Metric.ball (0 : ℂ) R, ∀ k,
        lqgApprox γ (fun s w => H s w ω) (radius (m + 1 + k))
          (sqQ (sqCorner z (radius (m + 1))) (m + 1)) ≤
            C * ENNReal.ofReal (radius m ^ κ) := by
  classical
  obtain ⟨S, hbounded, hcover, hevent⟩ :=
    exists_bounded_square_covers_ae_eventually_tilted_power_fixed hH hHm hγ hγ2 hp hpq hq hκ hexp R hR
  filter_upwards [hevent] with ω hω
  have hcompact : IsCompact (Metric.closedBall (0 : ℂ) (R + 2)) := isCompact_closedBall _ _
  obtain ⟨M, hM⟩ := hcompact.bddAbove_image
    ((Real.continuous_exp.comp (continuous_const.mul (hH.continuous 1 (by norm_num) ω))).continuousOn)
  let C : ℝ≥0∞ := (corners16.card : ℝ≥0∞) * ENNReal.ofReal M
  have hC : C < ⊤ := ENNReal.mul_lt_top (by simp) ENNReal.ofReal_lt_top
  refine ⟨C, hC, ?_⟩
  filter_upwards [hω] with m hm z hz k
  obtain ⟨T, hTS, hTcard, hTcover⟩ := hcover m z hz
  let μ := lqgApprox γ (fun s w => H s w ω) (radius (m + 1 + k))
  have hunit (v : ℂ) : ENNReal.ofReal (Real.exp (γ * H 1 v ω)) *
      ENNReal.ofReal (Real.exp (-γ * H 1 v ω)) = 1 := by
    rw [← ENNReal.ofReal_mul (Real.exp_nonneg _), ← Real.exp_add,
      show γ * H 1 v ω + -γ * H 1 v ω = 0 by ring, Real.exp_zero, ENNReal.ofReal_one]
  have hpoint (v : ℂ) (hv : v ∈ T) :
      μ (sqQ (sqCorner v (radius (m + 1))) (m + 1)) ≤
        ENNReal.ofReal M * ENNReal.ofReal (radius m ^ κ) := by
    have hvS := hTS hv
    have hvK : v ∈ Metric.closedBall (0 : ℂ) (R + 2) := by
      rw [Metric.mem_closedBall, dist_zero_right]
      exact hbounded m v hvS
    have hvM : ENNReal.ofReal (Real.exp (γ * H 1 v ω)) ≤ ENNReal.ofReal M :=
      ENNReal.ofReal_le_ofReal (hM ⟨v, hvK, rfl⟩)
    have htilt : ENNReal.ofReal (Real.exp (-γ * H 1 v ω)) *
        μ (sqQ (sqCorner v (radius (m + 1))) (m + 1)) ≤ ENNReal.ofReal (radius m ^ κ) := by
      calc
        _ ≤ ⨆ k, ENNReal.ofReal (Real.exp (-γ * H 1 v ω)) *
            lqgApprox γ (fun s w => H s w ω) (radius (m + 1 + k))
              (sqQ (sqCorner v (radius (m + 1))) (m + 1)) := le_iSup _ k
        _ ≤ (S m).sup (fun z => ⨆ k, ENNReal.ofReal (Real.exp (-γ * H 1 z ω)) *
            lqgApprox γ (fun s w => H s w ω) (radius (m + 1 + k))
              (sqQ (sqCorner z (radius (m + 1))) (m + 1))) :=
          Finset.le_sup (f := fun z => ⨆ j, ENNReal.ofReal (Real.exp (-γ * H 1 z ω)) *
            lqgApprox γ (fun s w => H s w ω) (radius (m + 1 + j))
              (sqQ (sqCorner z (radius (m + 1))) (m + 1))) hvS
        _ ≤ _ := hm.le
    calc
      _ = ENNReal.ofReal (Real.exp (γ * H 1 v ω)) *
          (ENNReal.ofReal (Real.exp (-γ * H 1 v ω)) *
            μ (sqQ (sqCorner v (radius (m + 1))) (m + 1))) := by
          rw [← mul_assoc, hunit, one_mul]
      _ ≤ _ := mul_le_mul' hvM htilt
  calc
    _ ≤ ∑ v ∈ T, μ (sqQ (sqCorner v (radius (m + 1))) (m + 1)) :=
      (measure_mono hTcover).trans (measure_biUnion_finset_le T _)
    _ ≤ ∑ _v ∈ T, ENNReal.ofReal M * ENNReal.ofReal (radius m ^ κ) :=
      Finset.sum_le_sum hpoint
    _ = (T.card : ℝ≥0∞) * (ENNReal.ofReal M * ENNReal.ofReal (radius m ^ κ)) := by simp
    _ ≤ _ := by
      have hc : (T.card : ℝ≥0∞) ≤ corners16.card := by exact_mod_cast hTcard
      dsimp [C]
      calc
        _ ≤ (corners16.card : ℝ≥0∞) * (ENNReal.ofReal M * ENNReal.ofReal (radius m ^ κ)) :=
          mul_le_mul' hc le_rfl
        _ = _ := by rw [mul_assoc]


private theorem exists_bounded_square_covers_ae_eventually_coarse_unit_tilted_power_fixed
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {H : ℝ → ℂ → Ω → ℝ}
    (hH : LQGDimension.IsGFFCircleAverage H P)
    (hHm : ∀ r z, Measurable (H r z)) {γ : ℝ} (hγ : 0 < γ) (_hγ2 : γ < 2)
    {p q κ : ℝ} (hp : 1 < p) (_hpq : p < q) (_hq : q < 4 / γ ^ 2)
    (hκ : 0 < κ) (hexp : 2 + p * κ < 2 * p + γ ^ 2 * p / 2 - (p * γ) ^ 2 / 2)
    (R : ℝ) (hR : 0 < R) :
    ∃ S : ℕ → Finset ℂ, (∀ m v, v ∈ S m → ‖v‖ ≤ R + 2) ∧
      (∀ m z, z ∈ Metric.ball (0 : ℂ) R → ∃ T : Finset ℂ,
        T ⊆ S m ∧ T.card ≤ corners16.card ∧
          sqQ (sqCorner z (radius (m + 1))) (m + 1) ⊆
            ⋃ v ∈ T, sqQ (sqCorner v (radius (m + 1))) (m + 1)) ∧
      ∀ᵐ ω ∂P, ∀ᶠ m in Filter.atTop,
        (S m).sup (fun z => (Finset.range (m + 2)).sup fun n =>
          unitTiltedSquareMass H γ z (m + 1) n ω) < ENNReal.ofReal (radius m ^ κ) := by
  classical
  choose S hS using fun m => exists_finset_bounded_centred_sqQ_local_cover_ball R hR (m + 1)
  refine ⟨S, fun m v hv => (hS m).2.1 v hv, fun m z hz => (hS m).2.2 z hz, ?_⟩
  let D : ℝ := (corners16.card : ℝ) * (8 * R + 1) ^ 2
  have hD : 0 ≤ D := by dsimp [D]; positivity
  apply ae_eventually_finset_coarse_unit_tilted_square_power_bound_fixed hH hHm hγ hp hκ hexp S
    (A := ENNReal.ofReal D) ENNReal.ofReal_lt_top
  intro m
  have hc : ((S m).card : ℝ) ≤ D * radius m ^ (-2 : ℝ) :=
    ((hS m).1).trans (square_cover_cardinal_scale_le R hR m)
  calc
    ((S m).card : ℝ≥0∞) = ENNReal.ofReal ((S m).card : ℝ) := by simp
    _ ≤ ENNReal.ofReal (D * radius m ^ (-2 : ℝ)) := ENNReal.ofReal_le_ofReal hc
    _ = _ := ENNReal.ofReal_mul hD


private theorem ae_exists_compact_center_coarse_level_square_power_bound_fixed
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {H : ℝ → ℂ → Ω → ℝ}
    (hH : LQGDimension.IsGFFCircleAverage H P)
    (hHm : ∀ r z, Measurable (H r z)) {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2)
    {p q κ : ℝ} (hp : 1 < p) (hpq : p < q) (hq : q < 4 / γ ^ 2)
    (hκ : 0 < κ) (hexp : 2 + p * κ < 2 * p + γ ^ 2 * p / 2 - (p * γ) ^ 2 / 2)
    (R : ℝ) (hR : 0 < R) :
    ∀ᵐ ω ∂P, ∃ C : ℝ≥0∞, C < ⊤ ∧
      ∀ᶠ m in Filter.atTop, ∀ z ∈ Metric.ball (0 : ℂ) R, ∀ n, n ≤ m + 1 →
        lqgApprox γ (fun s w => H s w ω) (radius n)
          (sqQ (sqCorner z (radius (m + 1))) (m + 1)) ≤
            C * ENNReal.ofReal (radius m ^ κ) := by
  classical
  obtain ⟨S, hbounded, hcover, hevent⟩ :=
    exists_bounded_square_covers_ae_eventually_coarse_unit_tilted_power_fixed hH hHm hγ hγ2 hp hpq hq hκ hexp R hR
  filter_upwards [hevent] with ω hω
  have hcompact : IsCompact (Metric.closedBall (0 : ℂ) (R + 3)) := isCompact_closedBall _ _
  obtain ⟨M, hM⟩ := hcompact.bddAbove_image
    ((Real.continuous_exp.comp (continuous_const.mul (hH.continuous 1 (by norm_num) ω))).continuousOn)
  let C : ℝ≥0∞ := (corners16.card : ℝ≥0∞) * ENNReal.ofReal M
  have hC : C < ⊤ := ENNReal.mul_lt_top (by simp) ENNReal.ofReal_lt_top
  refine ⟨C, hC, ?_⟩
  filter_upwards [hω] with m hm z hz n hn
  obtain ⟨T, hTS, hTcard, hTcover⟩ := hcover m z hz
  let μ := lqgApprox γ (fun s w => H s w ω) (radius n)
  have heq (w : ℂ) : ENNReal.ofReal (radius n ^ (γ ^ 2 / 2) * Real.exp (γ * H (radius n) w ω)) =
      ENNReal.ofReal (Real.exp (γ * H 1 w ω)) *
        ENNReal.ofReal (radius n ^ (γ ^ 2 / 2) * Real.exp (γ * (H (radius n) w ω - H 1 w ω))) := by
    rw [← ENNReal.ofReal_mul (Real.exp_nonneg _)]
    congr 1
    calc
      _ = radius n ^ (γ ^ 2 / 2) * (Real.exp (γ * H 1 w ω) *
          Real.exp (γ * (H (radius n) w ω - H 1 w ω))) := by
        rw [← Real.exp_add]
        congr 2
        ring
      _ = _ := by ring
  have hpoint (v : ℂ) (hv : v ∈ T) :
      μ (sqQ (sqCorner v (radius (m + 1))) (m + 1)) ≤
        ENNReal.ofReal M * ENNReal.ofReal (radius m ^ κ) := by
    have hvS := hTS hv
    have htilt : unitTiltedSquareMass H γ v (m + 1) n ω ≤ ENNReal.ofReal (radius m ^ κ) := by
      calc
        _ ≤ (Finset.range (m + 2)).sup (fun j => unitTiltedSquareMass H γ v (m + 1) j ω) :=
          Finset.le_sup (Finset.mem_range.mpr (by omega))
        _ ≤ (S m).sup (fun u => (Finset.range (m + 2)).sup fun j =>
            unitTiltedSquareMass H γ u (m + 1) j ω) :=
          Finset.le_sup (f := fun u => (Finset.range (m + 2)).sup fun j =>
            unitTiltedSquareMass H γ u (m + 1) j ω) hvS
        _ ≤ _ := hm.le
    have hμ : μ (sqQ (sqCorner v (radius (m + 1))) (m + 1)) ≤
        ENNReal.ofReal M * unitTiltedSquareMass H γ v (m + 1) n ω := by
      dsimp only [μ, unitTiltedSquareMass, lqgApprox]
      rw [withDensity_apply _ (measurableSet_sqQ _ _), ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
      apply setLIntegral_mono' (measurableSet_sqQ _ _)
      intro w hw
      have hwv := norm_sub_le_of_mem_centred_sqQ v (m + 1) hw
      have hr1 : radius (m + 1) ≤ 1 := by unfold radius; exact pow_le_one₀ (by norm_num) (by norm_num)
      have hwK : w ∈ Metric.closedBall (0 : ℂ) (R + 3) := by
        rw [Metric.mem_closedBall, dist_zero_right]
        have h1 := norm_sub_norm_le w v
        have h2 := hbounded m v hvS
        linarith
      rw [heq]
      exact mul_le_mul' (ENNReal.ofReal_le_ofReal (hM ⟨w, hwK, rfl⟩)) le_rfl
    exact hμ.trans (mul_le_mul' le_rfl htilt)
  calc
    _ ≤ ∑ v ∈ T, μ (sqQ (sqCorner v (radius (m + 1))) (m + 1)) :=
      (measure_mono hTcover).trans (measure_biUnion_finset_le T _)
    _ ≤ ∑ _v ∈ T, ENNReal.ofReal M * ENNReal.ofReal (radius m ^ κ) := Finset.sum_le_sum hpoint
    _ = (T.card : ℝ≥0∞) * (ENNReal.ofReal M * ENNReal.ofReal (radius m ^ κ)) := by simp
    _ ≤ _ := by
      have hc : (T.card : ℝ≥0∞) ≤ corners16.card := by exact_mod_cast hTcard
      dsimp [C]
      calc
        _ ≤ (corners16.card : ℝ≥0∞) * (ENNReal.ofReal M * ENNReal.ofReal (radius m ^ κ)) :=
          mul_le_mul' hc le_rfl
        _ = _ := by rw [mul_assoc]



private theorem ae_exists_compact_center_square_power_bound_fixed
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {H : ℝ → ℂ → Ω → ℝ}
    (hH : LQGDimension.IsGFFCircleAverage H P)
    (hHm : ∀ r z, Measurable (H r z)) {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2)
    {p₀ q₀ κ : ℝ} (hp₀ : 1 < p₀) (hpq₀ : p₀ < q₀) (hq₀ : q₀ < 4 / γ ^ 2)
    (hκ : 0 < κ) (hexp : 2 + p₀ * κ < 2 * p₀ + γ ^ 2 * p₀ / 2 - (p₀ * γ) ^ 2 / 2)
    (R : ℝ) (hR : 0 < R) :
    ∀ᵐ ω ∂P, ∃ C : ℝ≥0∞, C < ⊤ ∧
      ∀ᶠ m in Filter.atTop, ∀ z ∈ Metric.ball (0 : ℂ) R, ∀ n,
        lqgApprox γ (fun s w => H s w ω) (radius n)
          (sqQ (sqCorner z (radius (m + 1))) (m + 1)) ≤
            C * ENNReal.ofReal (radius m ^ κ) := by
  have hf := ae_exists_compact_center_fine_level_square_power_bound_fixed hH hHm hγ hγ2 hp₀ hpq₀ hq₀ hκ hexp R hR
  have hc := ae_exists_compact_center_coarse_level_square_power_bound_fixed hH hHm hγ hγ2 hp₀ hpq₀ hq₀ hκ hexp R hR
  filter_upwards [hf, hc] with ω hf hc
  obtain ⟨Cf, hCf, hf⟩ := hf
  obtain ⟨Cc, hCc, hc⟩ := hc
  refine ⟨Cf + Cc, ENNReal.add_lt_top.mpr ⟨hCf, hCc⟩, ?_⟩
  filter_upwards [hf, hc] with m hf hc z hz n
  by_cases hn : n ≤ m + 1
  · exact (hc z hz n hn).trans (mul_le_mul' (le_add_left le_rfl) le_rfl)
  · obtain ⟨k, rfl⟩ : ∃ k, n = m + 1 + k := ⟨n - (m + 1), by omega⟩
    exact (hf z hz k).trans (mul_le_mul' (le_add_right le_rfl) le_rfl)


private theorem ae_exists_compact_center_recentred_and_square_power_bounds_fixed
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {H : ℝ → ℂ → Ω → ℝ}
    (hH : LQGDimension.IsGFFCircleAverage H P)
    (hHm : ∀ r z, Measurable (H r z)) {γ p q : ℝ}
    (hγ : 0 < γ) (hγ2 : γ < 2) (hp : 1 < p) (hpq : p < q)
    (hq : q < 4 / γ ^ 2)
    {p₀ q₀ κ : ℝ} (hp₀ : 1 < p₀) (hpq₀ : p₀ < q₀) (hq₀ : q₀ < 4 / γ ^ 2)
    (hκ : 0 < κ) (hexp : 2 + p₀ * κ < 2 * p₀ + γ ^ 2 * p₀ / 2 - (p₀ * γ) ^ 2 / 2)
    (K : Set ℂ) (hK : IsCompact K) :
    ∀ᵐ ω ∂P,
      (∀ m, ∃ A : ℝ≥0∞, A < ⊤ ∧ ∀ z ∈ K, ∀ k,
        normalizedRecentredSquareMass H γ z m k ω ≤ A) ∧
      ∃ C : ℝ≥0∞, C < ⊤ ∧ ∀ᶠ m in Filter.atTop, ∀ z ∈ K, ∀ n,
        lqgApprox γ (fun s w => H s w ω) (radius n)
          (sqQ (sqCorner z (radius (m + 1))) (m + 1)) ≤
            C * ENNReal.ofReal (radius m ^ κ) := by
  obtain ⟨R, hR⟩ := Metric.isBounded_iff_subset_ball (0 : ℂ) |>.1 hK.isBounded
  let R' := max R 1 + 1
  have hR' : 0 < R' := by dsimp [R']; linarith [le_max_right R (1 : ℝ)]
  have hK' : K ⊆ Metric.ball (0 : ℂ) R' :=
    hR.trans (Metric.ball_subset_ball (by dsimp [R']; linarith [le_max_left R (1 : ℝ)]))
  have hevent := ae_exists_compact_center_square_power_bound_fixed hH hHm hγ hγ2 hp₀ hpq₀ hq₀ hκ hexp R' hR'
  filter_upwards [ae_exists_compact_bound_iSup_normalized_recentred_square_mass
    hH hHm hγ hγ2 hp hpq hq K hK, hevent] with ω hnorm hpow
  refine ⟨hnorm, ?_⟩
  obtain ⟨C, hC, hCevent⟩ := hpow
  refine ⟨C, hC, ?_⟩
  filter_upwards [hCevent] with m hm z hz n
  exact hm z (hK' hz) n


private theorem ae_exists_compact_center_recentred_and_all_scale_square_power_bounds_fixed
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {H : ℝ → ℂ → Ω → ℝ}
    (hH : LQGDimension.IsGFFCircleAverage H P)
    (hHm : ∀ r z, Measurable (H r z)) {γ p q : ℝ}
    (hγ : 0 < γ) (hγ2 : γ < 2) (hp : 1 < p) (hpq : p < q)
    (hq : q < 4 / γ ^ 2)
    {p₀ q₀ κ : ℝ} (hp₀ : 1 < p₀) (hpq₀ : p₀ < q₀) (hq₀ : q₀ < 4 / γ ^ 2)
    (hκ : 0 < κ) (hexp : 2 + p₀ * κ < 2 * p₀ + γ ^ 2 * p₀ / 2 - (p₀ * γ) ^ 2 / 2)
    (K : Set ℂ) (hK : IsCompact K) :
    ∀ᵐ ω ∂P,
      (∀ m, ∃ A : ℝ≥0∞, A < ⊤ ∧ ∀ z ∈ K, ∀ k,
        normalizedRecentredSquareMass H γ z m k ω ≤ A) ∧
      ∃ C : ℝ≥0∞, C < ⊤ ∧ ∀ m, ∀ z ∈ K, ∀ n,
        lqgApprox γ (fun s w => H s w ω) (radius n)
          (sqQ (sqCorner z (radius (m + 1))) (m + 1)) ≤
            C * ENNReal.ofReal (radius m ^ κ) := by
  classical
  have hevent := ae_exists_compact_center_recentred_and_square_power_bounds_fixed
    hH hHm hγ hγ2 hp hpq hq hp₀ hpq₀ hq₀ hκ hexp K hK
  filter_upwards [hevent, ae_exists_compact_center_all_level_square_bound
    hH hHm hγ hγ2 hp hpq hq K hK] with ω hevent hfixed
  obtain ⟨hnorm, C₀, hC₀, hCevent⟩ := hevent
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp hCevent
  choose A hA hbound using hfixed
  let X : ℕ → ℝ≥0∞ := fun m => ENNReal.ofReal (radius m ^ κ)
  have hX0 (m : ℕ) : X m ≠ 0 := (ENNReal.ofReal_pos.mpr (Real.rpow_pos_of_pos (radius_pos m) κ)).ne'
  have hXt (m : ℕ) : X m ≠ ⊤ := ENNReal.ofReal_ne_top
  let D : ℝ≥0∞ := ∑ m ∈ Finset.range N, A (m + 1) * (X m)⁻¹
  have hD : D ≠ ⊤ := ENNReal.sum_ne_top.mpr (fun m _ =>
    ENNReal.mul_ne_top (hA (m + 1)).ne (ENNReal.inv_ne_top.mpr (hX0 m)))
  refine ⟨hnorm, C₀ + D, ENNReal.add_lt_top.mpr ⟨hC₀, lt_top_iff_ne_top.mpr hD⟩, ?_⟩
  intro m z hz n
  by_cases hm : N ≤ m
  · exact (hN m hm z hz n).trans (mul_le_mul' (le_add_right le_rfl) le_rfl)
  · have hmem : m ∈ Finset.range N := Finset.mem_range.mpr (by omega)
    have hsum : A (m + 1) * (X m)⁻¹ ≤ D := by
      dsimp [D]
      exact Finset.single_le_sum (f := fun j => A (j + 1) * (X j)⁻¹) (fun _ _ => by positivity) hmem
    calc
      _ ≤ A (m + 1) := hbound (m + 1) z hz n
      _ = (A (m + 1) * (X m)⁻¹) * X m := by rw [mul_assoc, ENNReal.inv_mul_cancel (hX0 m) (hXt m), mul_one]
      _ ≤ (C₀ + D) * X m := mul_le_mul' (hsum.trans le_add_self) le_rfl


private theorem ae_exists_compact_center_recentred_and_square_scale_power_bounds_fixed
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {H : ℝ → ℂ → Ω → ℝ}
    (hH : LQGDimension.IsGFFCircleAverage H P)
    (hHm : ∀ r z, Measurable (H r z)) {γ p q : ℝ}
    (hγ : 0 < γ) (hγ2 : γ < 2) (hp : 1 < p) (hpq : p < q)
    (hq : q < 4 / γ ^ 2)
    {p₀ q₀ κ : ℝ} (hp₀ : 1 < p₀) (hpq₀ : p₀ < q₀) (hq₀ : q₀ < 4 / γ ^ 2)
    (hκ : 0 < κ) (hexp : 2 + p₀ * κ < 2 * p₀ + γ ^ 2 * p₀ / 2 - (p₀ * γ) ^ 2 / 2)
    (K : Set ℂ) (hK : IsCompact K) :
    ∀ᵐ ω ∂P,
      (∀ m, ∃ A : ℝ≥0∞, A < ⊤ ∧ ∀ z ∈ K, ∀ k,
        normalizedRecentredSquareMass H γ z m k ω ≤ A) ∧
      ∃ C : ℝ≥0∞, C < ⊤ ∧ ∀ m, ∀ z ∈ K, ∀ n,
        lqgApprox γ (fun s w => H s w ω) (radius n)
          (sqQ (sqCorner z (radius m)) m) ≤ C * ENNReal.ofReal (radius m ^ κ) := by
  have hevent := ae_exists_compact_center_recentred_and_all_scale_square_power_bounds_fixed
    hH hHm hγ hγ2 hp hpq hq hp₀ hpq₀ hq₀ hκ hexp K hK
  filter_upwards [hevent, ae_exists_compact_center_all_level_square_bound
    hH hHm hγ hγ2 hp hpq hq K hK] with ω hevent hfixed
  obtain ⟨hnorm, C, hC, hbound⟩ := hevent
  obtain ⟨A, hA, hA_bound⟩ := hfixed 0
  let D := A + C * ENNReal.ofReal ((2 : ℝ) ^ κ)
  have hD : D < ⊤ := ENNReal.add_lt_top.mpr ⟨hA, ENNReal.mul_lt_top hC ENNReal.ofReal_lt_top⟩
  refine ⟨hnorm, D, hD, ?_⟩
  intro m z hz n
  cases m with
  | zero =>
    have hb := hA_bound z hz n
    have hle : A ≤ D := le_add_right le_rfl
    simpa [QuantumZipper.radius] using hb.trans hle
  | succ m =>
    have hscale : radius m = 2 * radius (m + 1) := by unfold radius; rw [pow_succ]; ring
    have hr : ENNReal.ofReal (radius m ^ κ) =
        ENNReal.ofReal ((2 : ℝ) ^ κ) * ENNReal.ofReal (radius (m + 1) ^ κ) := by
      rw [hscale, Real.mul_rpow (by norm_num) (radius_pos _).le, ENNReal.ofReal_mul (by positivity)]
    have hb := hbound m z hz n
    rw [hr] at hb
    calc
      _ ≤ C * (ENNReal.ofReal ((2 : ℝ) ^ κ) * ENNReal.ofReal (radius (m + 1) ^ κ)) := hb
      _ = (C * ENNReal.ofReal ((2 : ℝ) ^ κ)) * ENNReal.ofReal (radius (m + 1) ^ κ) := by rw [mul_assoc]
      _ ≤ D * ENNReal.ofReal (radius (m + 1) ^ κ) := mul_le_mul' le_add_self le_rfl


private theorem ae_exists_compact_center_ball_approximant_power_bound_fixed
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {H : ℝ → ℂ → Ω → ℝ}
    (hH : LQGDimension.IsGFFCircleAverage H P)
    (hHm : ∀ r z, Measurable (H r z)) {γ p q : ℝ}
    (hγ : 0 < γ) (hγ2 : γ < 2) (hp : 1 < p) (hpq : p < q)
    (hq : q < 4 / γ ^ 2)
    {p₀ q₀ κ : ℝ} (hp₀ : 1 < p₀) (hpq₀ : p₀ < q₀) (hq₀ : q₀ < 4 / γ ^ 2)
    (hκ : 0 < κ) (hexp : 2 + p₀ * κ < 2 * p₀ + γ ^ 2 * p₀ / 2 - (p₀ * γ) ^ 2 / 2)
    (K : Set ℂ) (hK : IsCompact K) :
    ∀ᵐ ω ∂P, ∃ C : ℝ≥0∞, C < ⊤ ∧
      ∀ z ∈ K, ∀ r : ℝ, 0 < r → r ≤ 1 → ∀ n,
        lqgApprox γ (fun s w => H s w ω) (radius n) (Metric.ball z r) ≤
          C * ENNReal.ofReal (r ^ κ) := by
  classical
  obtain ⟨R, hR⟩ := Metric.isBounded_iff_subset_ball (0 : ℂ) |>.1 hK.isBounded
  have hevent := ae_exists_compact_center_recentred_and_square_scale_power_bounds_fixed
    hH hHm hγ hγ2 hp hpq hq hp₀ hpq₀ hq₀ hκ hexp (Metric.closedBall 0 (R + 4)) (isCompact_closedBall 0 (R + 4))
  filter_upwards [hevent] with ω hevent
  obtain ⟨_, C, hC, hbound⟩ := hevent
  refine ⟨(corners16.card : ℝ≥0∞) * C * ENNReal.ofReal ((2 : ℝ) ^ κ),
    ENNReal.mul_lt_top (ENNReal.mul_lt_top (by simp) hC) ENNReal.ofReal_lt_top, ?_⟩
  intro z hz r hr hr1 n
  obtain ⟨m, hm1, hm2⟩ := exists_nat_pow_near_of_lt_one hr hr1
    (by norm_num : (0 : ℝ) < 2⁻¹) (by norm_num)
  have hm1' : radius (m + 1) < r := hm1
  have hm2' : r ≤ radius m := hm2
  have hmhalf : radius m ≤ 2 * r := by
    have heq : radius m = 2 * radius (m + 1) := by unfold radius; rw [pow_succ]; ring
    linarith
  have hradius : radius m ≤ 1 := by
    unfold radius
    exact pow_le_one₀ (by norm_num) (by norm_num)
  have hzR : ‖z‖ < R := by simpa [Metric.mem_ball, dist_zero_right] using hR hz
  have hcentre : ∀ c ∈ corners16, (z + radius m • c) + radius m • sqCentre ∈
      Metric.closedBall (0 : ℂ) (R + 4) := by
    intro c hc
    have hsq : sqCentre ∈ unitSq := by
      norm_num [unitSq, sqCentre]
    have hc4 := mem_corners16_bound hc sqCentre hsq
    rw [Metric.mem_closedBall, dist_zero_right]
    have hnorm : ‖radius m • (c + sqCentre)‖ ≤ 4 := by
      rw [norm_smul, Real.norm_of_nonneg (radius_pos m).le]
      nlinarith [mul_nonneg (radius_pos m).le (sub_nonneg.mpr hc4)]
    have heq : z + radius m • c + radius m • sqCentre = z + radius m • (c + sqCentre) := by
      rw [smul_add, add_assoc]
    rw [heq]
    linarith [norm_add_le z (radius m • (c + sqCentre))]
  let μ := lqgApprox γ (fun s w => H s w ω) (radius n)
  have hcover : Metric.ball z r ⊆ ⋃ c ∈ corners16, sqQ (z + radius m • c) m :=
    (Metric.ball_subset_ball (by linarith [radius_pos m])).trans (ball_subset_iUnion_sqQ z m)
  have hscale : ENNReal.ofReal (radius m ^ κ) ≤
      ENNReal.ofReal ((2 : ℝ) ^ κ) * ENNReal.ofReal (r ^ κ) := by
    rw [← ENNReal.ofReal_mul (Real.rpow_nonneg (by norm_num) _),
      ← Real.mul_rpow (by norm_num) hr.le]
    exact ENNReal.ofReal_le_ofReal (Real.rpow_le_rpow (radius_pos m).le hmhalf hκ.le)
  calc
    μ (Metric.ball z r) ≤ ∑ c ∈ corners16, μ (sqQ (z + radius m • c) m) :=
      (measure_mono hcover).trans (measure_biUnion_finset_le corners16 _)
    _ ≤ ∑ _c ∈ corners16, C * ENNReal.ofReal (radius m ^ κ) := by
      apply Finset.sum_le_sum
      intro c hc
      have heq : sqCorner ((z + radius m • c) + radius m • sqCentre) (radius m) =
          z + radius m • c := by simp [sqCorner]
      simpa only [heq] using hbound m _ (hcentre c hc) n
    _ = (corners16.card : ℝ≥0∞) * (C * ENNReal.ofReal (radius m ^ κ)) := by simp
    _ ≤ (corners16.card : ℝ≥0∞) * (C *
        (ENNReal.ofReal ((2 : ℝ) ^ κ) * ENNReal.ofReal (r ^ κ))) := by gcongr
    _ = _ := by ring



/-- A single deterministic exponent and a single almost-sure event work for
all compact sets of centers and all dyadic approximations. -/
theorem ae_forall_compact_center_ball_approximant_power_bound
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {H : ℝ → ℂ → Ω → ℝ}
    (hH : LQGDimension.IsGFFCircleAverage H P)
    (hHm : ∀ r z, Measurable (H r z)) {γ p q : ℝ}
    (hγ : 0 < γ) (hγ2 : γ < 2) (hp : 1 < p) (hpq : p < q)
    (hq : q < 4 / γ ^ 2) :
    ∃ κ : ℝ, 0 < κ ∧ ∀ᵐ ω ∂P, ∀ K : Set ℂ, IsCompact K →
      ∃ C : ℝ≥0∞, C < ⊤ ∧ ∀ z ∈ K, ∀ r : ℝ, 0 < r → r ≤ 1 → ∀ n,
        lqgApprox γ (fun s w => H s w ω) (radius n) (Metric.ball z r) ≤
          C * ENNReal.ofReal (r ^ κ) := by
  obtain ⟨p₀, q₀, κ, hp₀, hpq₀, hq₀, hκ, hexp⟩ := exists_square_moment_exponents hγ hγ2
  refine ⟨κ, hκ, ?_⟩
  have hevent : ∀ j : ℕ, ∀ᵐ ω ∂P, ∃ C : ℝ≥0∞, C < ⊤ ∧
      ∀ z ∈ Metric.closedBall (0 : ℂ) (j : ℝ), ∀ r : ℝ, 0 < r → r ≤ 1 → ∀ n,
        lqgApprox γ (fun s w => H s w ω) (radius n) (Metric.ball z r) ≤
          C * ENNReal.ofReal (r ^ κ) := fun j =>
    ae_exists_compact_center_ball_approximant_power_bound_fixed
      hH hHm hγ hγ2 hp hpq hq hp₀ hpq₀ hq₀ hκ hexp _ (isCompact_closedBall _ _)
  filter_upwards [ae_all_iff.mpr hevent] with ω hω K hK
  obtain ⟨R, hR⟩ := Metric.isBounded_iff_subset_ball (0 : ℂ) |>.1 hK.isBounded
  obtain ⟨j, hj⟩ := exists_nat_gt R
  obtain ⟨C, hC, hbound⟩ := hω j
  refine ⟨C, hC, ?_⟩
  intro z hz r hr hr1 n
  apply hbound z _ r hr hr1 n
  exact Metric.ball_subset_closedBall ((Metric.ball_subset_ball hj.le) (hR hz))


/-- The same exponent gives the compact-center estimate on each compact set. -/
theorem exists_uniform_compact_center_ball_approximant_power_bound
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {H : ℝ → ℂ → Ω → ℝ}
    (hH : LQGDimension.IsGFFCircleAverage H P)
    (hHm : ∀ r z, Measurable (H r z)) {γ p q : ℝ}
    (hγ : 0 < γ) (hγ2 : γ < 2) (hp : 1 < p) (hpq : p < q)
    (hq : q < 4 / γ ^ 2) :
    ∃ κ : ℝ, 0 < κ ∧ ∀ K : Set ℂ, IsCompact K → ∀ᵐ ω ∂P,
      ∃ C : ℝ≥0∞, C < ⊤ ∧ ∀ z ∈ K, ∀ r : ℝ, 0 < r → r ≤ 1 → ∀ n,
        lqgApprox γ (fun s w => H s w ω) (radius n) (Metric.ball z r) ≤
          C * ENNReal.ofReal (r ^ κ) := by
  obtain ⟨κ, hκ, hevent⟩ :=
    ae_forall_compact_center_ball_approximant_power_bound hH hHm hγ hγ2 hp hpq hq
  refine ⟨κ, hκ, fun K hK => ?_⟩
  filter_upwards [hevent] with ω hω
  exact hω K hK

end LatticeProb.LQG
