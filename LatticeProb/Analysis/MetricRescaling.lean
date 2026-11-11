import Mathlib

/-!
# Rescaling of intervals, distances and tightness

General forms of the dilation facts used in the rescaling of mated-CRT environments:

* the image of an interval under `s ↦ c X (b s)` is the `c`-multiple of the image of the
  rescaled interval under `X`;
* a real dilation `x ↦ R x` of the plane multiplies the extended distance by `R`, and the
  distance from `R x` to a set `s` is at least `R` times the distance from `x` to the
  dilated set `R⁻¹ s`;
* an almost-everywhere measurable real random variable under a finite measure is tight,
  so `P (M < R) → 0` as `M → ∞`.
-/

namespace LatticeProb.MetricRescaling

open MeasureTheory Filter Topology Set Metric
open scoped ENNReal

/-- The image of `[p, q]` under `s ↦ c X(b s)` is `c` times the image of `[b p, b q]` under `X`. -/
theorem image_Icc_rescale {b c : ℝ} (hb : 0 < b) (X X' : ℝ → ℝ) (hX : ∀ s, X' s = c * X (b * s))
    (p q : ℝ) :
    X' '' Icc p q = (fun y => c * y) '' (X '' Icc (b * p) (b * q)) := by
  ext y
  simp only [mem_image, mem_Icc]
  constructor
  · rintro ⟨s, ⟨h1, h2⟩, rfl⟩
    exact ⟨X (b * s), ⟨b * s, ⟨mul_le_mul_of_nonneg_left h1 hb.le, mul_le_mul_of_nonneg_left h2 hb.le⟩, rfl⟩,
      (hX s).symm⟩
  · rintro ⟨_, ⟨u, ⟨h1, h2⟩, rfl⟩, rfl⟩
    refine ⟨u / b, ⟨?_, ?_⟩, ?_⟩
    · rw [le_div_iff₀ hb, mul_comm]; exact h1
    · rw [div_le_iff₀ hb, mul_comm]; exact h2
    · rw [hX, mul_div_cancel₀ u hb.ne']

/-- The extended distance scales by a positive real factor: `edist (R x) (R w) = R edist x w`. -/
theorem edist_ofReal_mul {R : ℝ} (hR : 0 < R) (x w : ℂ) :
    edist ((R : ℂ) * x) ((R : ℂ) * w) = ENNReal.ofReal R * edist x w := by
  rw [edist_dist, edist_dist, dist_eq_norm, dist_eq_norm, ← mul_sub, norm_mul, Complex.norm_real,
    Real.norm_of_nonneg hR.le, ENNReal.ofReal_mul hR.le]

/-- Lower bound for the distance to a dilated set: if `R⁻¹ s ⊆ t` then `R dist(x, t) ≤ dist(R x, s)`. -/
theorem ofReal_mul_infEDist_le {R : ℝ} (hR : 0 < R) (x : ℂ) {s t : Set ℂ}
    (hst : ∀ y ∈ s, (R : ℂ)⁻¹ * y ∈ t) :
    ENNReal.ofReal R * infEDist x t ≤ infEDist ((R : ℂ) * x) s := by
  have hR' : (R : ℂ) ≠ 0 := by exact_mod_cast hR.ne'
  refine le_infEDist.2 fun y hy => ?_
  calc ENNReal.ofReal R * infEDist x t ≤ ENNReal.ofReal R * edist x ((R : ℂ)⁻¹ * y) :=
        mul_le_mul_of_nonneg_left (infEDist_le_edist_of_mem (hst y hy)) zero_le
    _ = edist ((R : ℂ) * x) y := by rw [← edist_ofReal_mul hR, mul_inv_cancel_left₀ hR']

/-- Cancellation of a positive real factor in `ℝ≥0∞`. -/
theorem le_of_ofReal_mul_le {R : ℝ} (hR : 0 < R) {a c : ℝ≥0∞}
    (h : ENNReal.ofReal R * a ≤ ENNReal.ofReal R * c) : a ≤ c := by
  have key : ∀ d : ℝ≥0∞, ENNReal.ofReal R⁻¹ * (ENNReal.ofReal R * d) = d := fun d => by
    rw [← mul_assoc, ← ENNReal.ofReal_mul (inv_nonneg.2 hR.le), inv_mul_cancel₀ hR.ne', ENNReal.ofReal_one,
      one_mul]
  calc a = ENNReal.ofReal R⁻¹ * (ENNReal.ofReal R * a) := (key a).symm
    _ ≤ ENNReal.ofReal R⁻¹ * (ENNReal.ofReal R * c) := mul_le_mul_of_nonneg_left h zero_le
    _ = c := key c

/-- `dist(R x, s) ≤ R dist(x, R⁻¹ s)` for real `R > 0`, with `R⁻¹ s = {z : R z ∈ s}`. -/
theorem infEDist_mul_le {R : ℝ} (hR : 0 < R) (x : ℂ) (s : Set ℂ) :
    infEDist ((R : ℂ) * x) s ≤ ENNReal.ofReal R * infEDist x {z | (R : ℂ) * z ∈ s} := by
  have hR' : (R : ℂ) ≠ 0 := by exact_mod_cast hR.ne'
  have h := ofReal_mul_infEDist_le (inv_pos.2 hR) ((R : ℂ) * x) (s := {z | (R : ℂ) * z ∈ s}) (t := s)
    (fun y hy => by simpa [Complex.ofReal_inv, inv_inv] using hy)
  rw [Complex.ofReal_inv, inv_mul_cancel_left₀ hR'] at h
  refine le_of_ofReal_mul_le (inv_pos.2 hR) ?_
  calc ENNReal.ofReal R⁻¹ * infEDist ((R : ℂ) * x) s ≤ infEDist x {z | (R : ℂ) * z ∈ s} := h
    _ = ENNReal.ofReal R⁻¹ * (ENNReal.ofReal R * infEDist x {z | (R : ℂ) * z ∈ s}) := by
      rw [← mul_assoc, ← ENNReal.ofReal_mul (inv_nonneg.2 hR.le), inv_mul_cancel₀ hR.ne', ENNReal.ofReal_one,
        one_mul]

/-- An almost-everywhere measurable real random variable under a finite measure is tight:
`P (M < R) → 0` as `M → ∞`. -/
theorem tendsto_measure_lt_atTop {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsFiniteMeasure P]
    {R : Ω → ℝ} (hR : AEMeasurable R P) : Tendsto (fun M : ℝ => P {ω | M < R ω}) atTop (𝓝 0) := by
  have h1 : ∀ M : ℝ, P {ω | M < R ω} = (P.map R) univ - (P.map R) (Iic M) := fun M => by
    rw [← measure_compl measurableSet_Iic (measure_ne_top _ _), compl_Iic,
      Measure.map_apply_of_aemeasurable hR measurableSet_Ioi]
    rfl
  simp only [h1]
  have h2 := ENNReal.Tendsto.sub tendsto_const_nhds (tendsto_measure_Iic_atTop (P.map R))
    (Or.inl (measure_ne_top (P.map R) univ))
  simpa using h2

end LatticeProb.MetricRescaling
