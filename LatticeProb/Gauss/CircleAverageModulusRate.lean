import LatticeProb.Gauss.CircleAverageModulus
import LatticeProb.Prob.KolmogorovModulusRate

/-!
# A quantitative modulus of the rescaled circle-average process on one box

For the whole-plane Gaussian free field `h` with circle averages `h_r(z)`, consider for a scale
`ε > 0` and a centre `z₀ ∈ ℂ` the rescaled process
`x ↦ h_{ε x₀}(z₀ + ε (x₁ + i x₂))` on the box `[1/2, 1] × [0, 1]²` (`circleRescaled`).
Its increments satisfy `E|X_x - X_y|^p ≤ E|Z|^p 12^{p/2} |x - y|^{p/2}` uniformly in `ε` and `z₀`,
and it is almost surely continuous on the box. The quantitative Kolmogorov–Chentsov estimate
`LatticeProb.measure_modulus_gt_le` (in dimension `3`, with exponent `q = p/2`) then gives, for every
level `N ≥ 1` and every `c ∈ (0, 1)` with `θ = 2^{3 - p/2} / c^p < 1`,

`P(∃ x, y in the box, |x - y| < 2^{-N}, |X_x - X_y| > 7 c^N / (1 - c)) ≤ C (N + 1)^3 θ^N`,

with a constant `C` depending only on `p` and `c` (not on the scale or on the centre).

## Main results

* `LatticeProb.Gauss.IsWholePlaneGFF.ae_continuousOn_circleRescaled`: almost sure continuity of the
  rescaled process on the box.
* `LatticeProb.Gauss.IsWholePlaneGFF.measure_circleRescaled_modulus_gt_le`: the rate above.
-/

open MeasureTheory ProbabilityTheory

namespace LatticeProb.Gauss

theorem circleBoxLower_le_circleBoxUpper : circleBoxLower ≤ circleBoxUpper := fun i => by
  fin_cases i <;> norm_num [circleBoxLower, circleBoxUpper]

namespace IsWholePlaneGFF

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {hC : Ω → (ℂ → ℝ) → ℝ}
  {hcirc : Ω → ℝ → ℂ → ℝ}

/-- Almost surely, the rescaled circle-average process `x ↦ h_{ε x₀}(z₀ + ε (x₁ + i x₂))` is
continuous on the box `[1/2, 1] × [0, 1]²`, for every scale `ε > 0` and every centre `z₀`. -/
theorem ae_continuousOn_circleRescaled (hh : IsWholePlaneGFF P hC hcirc) {ε : ℝ} (hε : 0 < ε)
    (z₀ : ℂ) :
    ∀ᵐ ω ∂P, ContinuousOn (fun x => circleRescaled hcirc ε z₀ x ω)
      (Set.Icc circleBoxLower circleBoxUpper) := by
  filter_upwards [hh.ae_continuousOn_circle] with ω hω
  have hcont : Continuous fun x : Fin 3 → ℝ =>
      ((ε * x 0, z₀ + (ε : ℂ) * ⟨x 1, x 2⟩) : ℝ × ℂ) := by
    simp_rw [Complex.mk_eq_add_mul_I]
    fun_prop
  refine hω.comp (f := fun x : Fin 3 → ℝ => ((ε * x 0, z₀ + (ε : ℂ) * ⟨x 1, x 2⟩) : ℝ × ℂ))
    hcont.continuousOn ?_
  intro x hx
  refine ⟨?_, Set.mem_univ _⟩
  have hx0 := le_coord_zero_of_mem_circleBox hx
  show 0 < ε * x 0
  have : (0 : ℝ) < x 0 := by linarith
  positivity

/-- **Per-box modulus rate of the rescaled circle averages.** For every scale `ε > 0`, every
centre `z₀`, every level `N ≥ 1`, and parameters `p > 0`, `c ∈ (0, 1)` with
`θ = 2^{3 - p/2} / c^p < 1`, the probability that the rescaled process
`x ↦ h_{ε x₀}(z₀ + ε (x₁ + i x₂))` has an increment larger than `7 c^N / (1 - c)` between two points
of the box `[1/2, 1] × [0, 1]²` at sup-distance less than `2^{-N}` is at most
`E|Z|^p 12^{p/2} · 3 · 3³ · S · (N + 1)³ θ^N`, with `S = ∑_j (j + 1)³ θ^j` and `Z` standard
Gaussian. The bound does not depend on `ε` or `z₀`. -/
theorem measure_circleRescaled_modulus_gt_le (hh : IsWholePlaneGFF P hC hcirc) {ε : ℝ}
    (hε : 0 < ε) (z₀ : ℂ) {p c : ℝ} (hp : 0 < p) (hc : 0 < c) (hc1 : c < 1)
    (hθ : (2 : ℝ) ^ ((3 : ℝ) - p / 2) / c ^ p < 1) {N : ℕ} (hN : 1 ≤ N) :
    P {ω | ∃ x ∈ Set.Icc circleBoxLower circleBoxUpper,
        ∃ y ∈ Set.Icc circleBoxLower circleBoxUpper, dist x y < 1 / 2 ^ N ∧
          7 * c ^ N / (1 - c) < |circleRescaled hcirc ε z₀ x ω - circleRescaled hcirc ε z₀ y ω|}
      ≤ ENNReal.ofReal ((∫ t, |t| ^ p ∂(gaussianReal 0 1)) * 12 ^ (p / 2) * 3 * 3 ^ 3 *
          (∑' j : ℕ, ((j : ℝ) + 1) ^ 3 * ((2 : ℝ) ^ ((3 : ℝ) - p / 2) / c ^ p) ^ j) *
          ((N : ℝ) + 1) ^ 3 * ((2 : ℝ) ^ ((3 : ℝ) - p / 2) / c ^ p) ^ N) := by
  have := hh.isProbabilityMeasure
  have hM : 0 ≤ (∫ t, |t| ^ p ∂(gaussianReal 0 1)) * (12 : ℝ) ^ (p / 2) :=
    mul_nonneg (integral_nonneg fun t => by positivity) (by positivity)
  have h := LatticeProb.measure_modulus_gt_le (k := 3) circleBoxLower_le_circleBoxUpper P
    (X := circleRescaled hcirc ε z₀) (hh.ae_continuousOn_circleRescaled hε z₀)
    (q := p / 2) (M := (∫ t, |t| ^ p ∂(gaussianReal 0 1)) * 12 ^ (p / 2)) hp
    (by positivity) hM hc hc1 (by simpa only [Nat.cast_ofNat] using hθ)
    (fun x hx y hy => integrable_abs_rpow_circleRescaled_sub hh hε z₀ hp.le hx hy)
    (fun x hx y hy => integral_abs_rpow_circleRescaled_sub_le hh hε z₀ hp.le hx hy)
    (R := 1) hN (fun x hx i => by simpa using abs_coord_le_one_of_mem_circleBox hx i)
  simp only [Nat.cast_ofNat] at h
  have h7 : (2 * (3 : ℝ) + 1) = 7 := by norm_num
  rw [h7] at h
  exact h

end IsWholePlaneGFF

end LatticeProb.Gauss
