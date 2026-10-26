import LatticeProb.Prob.Percolation.CorrectedPlaneGrowth

/-!
# Linear algebra of the corrected-plane relation

On each actual open component, sums and real scalar multiples preserve harmonicity
and the uniform slope tail at all sufficiently large real radii. These operations
act on the slope and function together, without selecting normalized correctors.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace LatticeProb.Percolation

open scoped BigOperators

noncomputable section

variable {d : ℕ} {ω : Configuration d}

/-- The literal coordinate slope is additive in its real vector argument. -/
theorem componentSlope_add (C : OpenComponent ω) (p q : Fin d → ℝ) (x : C) :
    componentSlope C (p + q) x = componentSlope C p x + componentSlope C q x := by
  simp only [componentSlope, Pi.add_apply, add_mul, Finset.sum_add_distrib]

/-- The literal coordinate slope commutes with every real scalar. -/
theorem componentSlope_smul (C : OpenComponent ω) (r : ℝ) (p : Fin d → ℝ) (x : C) :
    componentSlope C (r • p) x = r * componentSlope C p x := by
  simp only [componentSlope, Pi.smul_apply, smul_eq_mul, mul_assoc, Finset.mul_sum]

/-- Two uniform slope tails add on the same actual Euclidean component balls. -/
theorem componentSlopeAsymptotics_add (C : OpenComponent ω) {p q : Fin d → ℝ}
    {u v : C → ℝ} (hu : componentSlopeAsymptotics C p u)
    (hv : componentSlopeAsymptotics C q v) :
    componentSlopeAsymptotics C (p + q) (u + v) := by
  intro ε hε
  obtain ⟨a, ha, hu'⟩ := hu (ε / 2) (by positivity)
  obtain ⟨b, hb, hv'⟩ := hv (ε / 2) (by positivity)
  refine ⟨max a b, ha.trans_le (le_max_left _ _), ?_⟩
  intro R hR x hx
  have hux := hu' R ((le_max_left _ _).trans hR) x hx
  have hvx := hv' R ((le_max_right _ _).trans hR) x hx
  calc
    |(u + v) x - componentSlope C (p + q) x| =
        |(u x - componentSlope C p x) + (v x - componentSlope C q x)| := by
      rw [Pi.add_apply, componentSlope_add]
      congr 1
      ring
    _ ≤ |u x - componentSlope C p x| + |v x - componentSlope C q x| := abs_add_le _ _
    _ ≤ (ε / 2) * R + (ε / 2) * R := add_le_add hux hvx
    _ = ε * R := by ring

/-- Real scaling preserves the full uniform tail, including zero and negative scalars. -/
theorem componentSlopeAsymptotics_smul (C : OpenComponent ω) {p : Fin d → ℝ}
    {u : C → ℝ} (hu : componentSlopeAsymptotics C p u) (r : ℝ) :
    componentSlopeAsymptotics C (r • p) (r • u) := by
  intro ε hε
  have hden : 0 < |r| + 1 := by positivity
  have hδ : 0 < ε / (|r| + 1) := div_pos hε hden
  obtain ⟨a, ha, hu'⟩ := hu (ε / (|r| + 1)) hδ
  have hscale : |r| * (ε / (|r| + 1)) ≤ ε := by
    have heq := div_mul_cancel₀ ε hden.ne'
    nlinarith
  refine ⟨a, ha, ?_⟩
  intro R hR x hx
  calc
    |(r • u) x - componentSlope C (r • p) x| =
        |r| * |u x - componentSlope C p x| := by
      rw [Pi.smul_apply, smul_eq_mul, componentSlope_smul, ← mul_sub, abs_mul]
    _ ≤ |r| * ((ε / (|r| + 1)) * R) :=
      mul_le_mul_of_nonneg_left (hu' R hR x hx) (abs_nonneg r)
    _ = (|r| * (ε / (|r| + 1))) * R := by ring
    _ ≤ ε * R := mul_le_mul_of_nonneg_right hscale (ha.trans_le hR).le

/-- Corrected planes add with their prescribed slopes on every actual open component. -/
theorem isCorrectedPlane_add (C : OpenComponent ω) {p q : Fin d → ℝ}
    {u v : C → ℝ} (hu : IsCorrectedPlane C p u) (hv : IsCorrectedPlane C q v) :
    IsCorrectedPlane C (p + q) (u + v) := by
  obtain ⟨hhu, hsu⟩ := (isCorrectedPlane_iff_harmonic_and_slope_asymptotics C p u).mp hu
  obtain ⟨hhv, hsv⟩ := (isCorrectedPlane_iff_harmonic_and_slope_asymptotics C q v).mp hv
  apply (isCorrectedPlane_iff_harmonic_and_slope_asymptotics C _ _).mpr
  exact ⟨(component_harmonic_iff C _).mpr
    (Network.harmonic_add ((component_harmonic_iff C u).mp hhu)
      ((component_harmonic_iff C v).mp hhv)), componentSlopeAsymptotics_add C hsu hsv⟩

/-- Every real scalar multiplies both the slope and corrected plane, without normalization. -/
theorem isCorrectedPlane_smul (C : OpenComponent ω) {p : Fin d → ℝ}
    {u : C → ℝ} (hu : IsCorrectedPlane C p u) (r : ℝ) :
    IsCorrectedPlane C (r • p) (r • u) := by
  obtain ⟨hhu, hsu⟩ := (isCorrectedPlane_iff_harmonic_and_slope_asymptotics C p u).mp hu
  apply (isCorrectedPlane_iff_harmonic_and_slope_asymptotics C _ _).mpr
  exact ⟨(component_harmonic_iff C _).mpr
    (Network.harmonic_smul ((component_harmonic_iff C u).mp hhu) r),
    componentSlopeAsymptotics_smul C hsu r⟩

/-- Negating both arguments preserves the corrected-plane relation. -/
theorem isCorrectedPlane_neg (C : OpenComponent ω) {p : Fin d → ℝ}
    {u : C → ℝ} (hu : IsCorrectedPlane C p u) : IsCorrectedPlane C (-p) (-u) := by
  simpa only [neg_one_smul] using isCorrectedPlane_smul C hu (-1)

/-- Subtracting corrected planes subtracts their prescribed slopes. -/
theorem isCorrectedPlane_sub (C : OpenComponent ω) {p q : Fin d → ℝ}
    {u v : C → ℝ} (hu : IsCorrectedPlane C p u) (hv : IsCorrectedPlane C q v) :
    IsCorrectedPlane C (p - q) (u - v) := by
  simpa only [sub_eq_add_neg] using isCorrectedPlane_add C hu (isCorrectedPlane_neg C hv)

end

end LatticeProb.Percolation
