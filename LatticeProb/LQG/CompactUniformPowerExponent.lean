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


end LatticeProb.LQG
