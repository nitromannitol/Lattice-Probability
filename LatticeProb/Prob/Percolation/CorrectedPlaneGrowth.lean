import LatticeProb.Prob.Percolation.CorrectedPlaneConsumer

/-!
# Growth redundancy in the corrected-plane characterization

Uniform sublinear error from a coordinate slope bounds normalized component-ball L²
by a constant times the real radius. Consequently harmonicity and the slope tail alone
characterize the existing corrected-plane predicate on every actual open component.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace LatticeProb.Percolation

open Filter
open scoped BigOperators

noncomputable section

variable {d : ℕ} {ω : Configuration d}

/-- A uniform slope tail implies the literal subquadratic normalized L² limit,
without a harmonicity, infinitude, or probability assumption. -/
theorem componentL2Subpolynomial_one_of_slope_asymptotics (C : OpenComponent ω)
    (q : Fin d → ℝ) (u : C → ℝ) (hu : componentSlopeAsymptotics C q u) :
    componentL2Subpolynomial C 1 u := by
  obtain ⟨R₀, hR₀, htail⟩ := hu 1 zero_lt_one
  let M : ℝ := 1 + ∑ i, |q i|
  have hM : 0 ≤ M := by
    dsimp only [M]
    positivity
  apply squeeze_zero'
  · exact eventually_atTop.mpr ⟨0, fun R hR => componentL2_scaled_nonneg C 1 u hR⟩
  · refine eventually_atTop.mpr ⟨R₀, fun R hR => ?_⟩
    have hRp : 0 < R := hR₀.trans_le hR
    have hball : componentBallL2 C 0 R u ≤ M * R := by
      apply componentBallL2_le_of_abs_le C 0 R u (mul_nonneg hM hRp.le)
      intro x hx
      have hcoord (i : Fin d) : |(x.val i : ℝ)| ≤ R := by
        have hi := PiLp.norm_apply_le
          (latticeEuclideanEmbedding x.val - latticeEuclideanEmbedding (0 : Vertex d)) i
        change |(x.val i : ℝ) - ((0 : Vertex d) i : ℝ)| ≤
          ‖latticeEuclideanEmbedding x.val - latticeEuclideanEmbedding (0 : Vertex d)‖ at hi
        simp only [Pi.zero_apply, Int.cast_zero, sub_zero] at hi
        exact hi.trans (mem_componentEuclideanBall C 0 R x |>.mp hx).le
      have hslope : |componentSlope C q x| ≤ (∑ i, |q i|) * R := by
        calc
          |∑ i, q i * (x.val i : ℝ)| ≤ ∑ i, |q i * (x.val i : ℝ)| :=
            Finset.abs_sum_le_sum_abs _ _
          _ ≤ ∑ i, |q i| * R := by
            apply Finset.sum_le_sum
            intro i _
            rw [abs_mul]
            exact mul_le_mul_of_nonneg_left (hcoord i) (abs_nonneg _)
          _ = (∑ i, |q i|) * R := (Finset.sum_mul _ _ _).symm
      calc
        |u x| = |(u x - componentSlope C q x) + componentSlope C q x| := by
          rw [sub_add_cancel]
        _ ≤ |u x - componentSlope C q x| + |componentSlope C q x| := abs_add_le _ _
        _ ≤ 1 * R + (∑ i, |q i|) * R := add_le_add (htail R hR x hx) hslope
        _ = M * R := by dsimp only [M]; ring
    calc
      (R ^ (1 + 1))⁻¹ * componentBallL2 C 0 R u ≤
          (R ^ (1 + 1))⁻¹ * (M * R) :=
        mul_le_mul_of_nonneg_left hball (inv_nonneg.mpr (sq_nonneg R))
      _ = R⁻¹ * M := by field_simp; ring
  · simpa only [zero_mul] using (tendsto_inv_atTop_zero (𝕜 := ℝ)).mul_const M

/-- On every actual component the corrected-plane predicate is exactly harmonicity
and uniform sublinear error from the prescribed real slope. -/
theorem isCorrectedPlane_iff_harmonic_and_slope_asymptotics (C : OpenComponent ω)
    (q : Fin d → ℝ) (u : C → ℝ) :
    IsCorrectedPlane C q u ↔
      (∀ x, componentLaplacian C u x = 0) ∧ componentSlopeAsymptotics C q u := by
  constructor
  · rintro ⟨⟨hh, _⟩, hs⟩
    exact ⟨hh, hs⟩
  · rintro ⟨hh, hs⟩
    exact ⟨⟨hh, componentL2Subpolynomial_one_of_slope_asymptotics C q u hs⟩, hs⟩

/-- The full characterization applies to a nonconstant coordinate and the constant one
on the same actual infinite two-dimensional all-open component. -/
theorem allOpen_two_harmonic_slope_consumers :
    let C := uniqueInfiniteComponent (allOpen_hasUniqueInfiniteOpenComponent 2)
    (∃ u : C → ℝ, (∀ x, componentLaplacian C u x = 0) ∧
      componentSlopeAsymptotics C (Pi.single 0 1) u ∧ ∃ x y : C, u x ≠ u y) ∧
    (∀ x : C, componentLaplacian C (fun _ => 1) x = 0) ∧
      componentSlopeAsymptotics C 0 (fun _ => 1) := by
  dsimp only
  obtain ⟨u, hu, hn⟩ := allOpen_two_nonconstant_correctedPlane
  have hc := (isCorrectedPlane_iff_harmonic_and_slope_asymptotics _ _ _).mp hu
  have hk := (isCorrectedPlane_iff_harmonic_and_slope_asymptotics _ _ _).mp
    allOpen_two_isCorrectedPlane_const
  exact ⟨⟨u, hc.1, hc.2, hn⟩, hk⟩

end

end LatticeProb.Percolation
