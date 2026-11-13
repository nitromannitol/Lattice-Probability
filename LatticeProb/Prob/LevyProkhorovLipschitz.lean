/-
Copyright (c) 2026. All rights reserved.
-/
import Mathlib

/-!
# Lipschitz maps and the Lévy–Prokhorov edistance

A measurable `K`-Lipschitz map with `K ≥ 1` multiplies the Lévy–Prokhorov edistance between two
measures by at most `K` when it pushes the measures forward:
`levyProkhorovEDist (μ.map f) (ν.map f) ≤ K * levyProkhorovEDist μ ν`.
For `K = 1` this is `levyProkhorovEDist_map_le_of_lipschitz_one`.
-/

open MeasureTheory Metric Set

open scoped ENNReal NNReal

noncomputable section

namespace LatticeProb

/-- A `K`-Lipschitz map sends the `r`-thickening of a preimage into the preimage of the
`K * r`-thickening. -/
private lemma thickening_preimage_subset_of_lipschitz
    {X Y : Type*} [PseudoEMetricSpace X] [PseudoEMetricSpace Y]
    {K : ℝ≥0} (hK : K ≠ 0) {f : X → Y} (hf : LipschitzWith K f) {r : ℝ} (S : Set Y) :
    thickening r (f ⁻¹' S) ⊆ f ⁻¹' thickening (K * r) S := by
  intro x hx
  obtain ⟨y, hy, hxy⟩ := (mem_thickening_iff_exists_edist_lt _ _).mp hx
  apply (mem_thickening_iff_exists_edist_lt _ _).mpr
  refine ⟨f y, hy, ?_⟩
  calc edist (f x) (f y) ≤ K * edist x y := hf x y
    _ < K * ENNReal.ofReal r :=
        (ENNReal.mul_lt_mul_iff_right (ENNReal.coe_ne_zero.2 hK) ENNReal.coe_ne_top).2 hxy
    _ = ENNReal.ofReal (K * r) := by
        rw [ENNReal.ofReal_mul K.coe_nonneg, ENNReal.ofReal_coe_nnreal]

/-- **A measurable `K`-Lipschitz map, `K ≥ 1`, multiplies the Lévy–Prokhorov edistance of the image
measures by at most `K`.** -/
theorem levyProkhorovEDist_map_le_of_lipschitz
    {X Y : Type*} [PseudoEMetricSpace X] [PseudoEMetricSpace Y]
    [MeasurableSpace X] [MeasurableSpace Y] [OpensMeasurableSpace Y]
    {K : ℝ≥0} (hK : 1 ≤ K) {f : X → Y} (hf : LipschitzWith K f) (hm : Measurable f)
    (μ ν : Measure X) :
    levyProkhorovEDist (μ.map f) (ν.map f) ≤ K * levyProkhorovEDist μ ν := by
  have hK0 : K ≠ 0 := (zero_lt_one.trans_le hK).ne'
  have hKe0 : (K : ℝ≥0∞) ≠ 0 := ENNReal.coe_ne_zero.2 hK0
  have hKe1 : (1 : ℝ≥0∞) ≤ K := by exact_mod_cast hK
  apply levyProkhorovEDist_le_of_forall
  intro ε S hε hεtop hS
  have hlt : levyProkhorovEDist μ ν < ε / K := by
    rw [ENNReal.lt_div_iff_mul_lt (Or.inl hKe0) (Or.inl ENNReal.coe_ne_top)]
    rwa [mul_comm]
  have hle : ε / K ≤ ε := by
    rw [ENNReal.div_le_iff_le_mul (Or.inl hKe0) (Or.inl ENNReal.coe_ne_top)]
    exact le_mul_of_one_le_right zero_le hKe1
  have hrad : (K : ℝ) * (ε / K).toReal = ε.toReal := by
    rw [ENNReal.toReal_div]
    have : (K : ℝ≥0∞).toReal = (K : ℝ) := by simp
    rw [this]
    have hKr : (K : ℝ) ≠ 0 := by exact_mod_cast hK0
    field_simp
  have hpre : thickening (ε / K).toReal (f ⁻¹' S) ⊆ f ⁻¹' thickening ε.toReal S := by
    have := thickening_preimage_subset_of_lipschitz hK0 hf (r := (ε / K).toReal) S
    rwa [hrad] at this
  constructor
  · rw [Measure.map_apply hm hS, Measure.map_apply hm isOpen_thickening.measurableSet]
    exact (left_measure_le_of_levyProkhorovEDist_lt hlt (hS.preimage hm)).trans
      (add_le_add (measure_mono hpre) hle)
  · rw [Measure.map_apply hm hS, Measure.map_apply hm isOpen_thickening.measurableSet]
    exact (right_measure_le_of_levyProkhorovEDist_lt hlt (hS.preimage hm)).trans
      (add_le_add (measure_mono hpre) hle)

end LatticeProb
