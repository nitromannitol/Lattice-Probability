import LatticeProb.LQG.LQGMetricInternalScaling

/-!
# Euclidean length metrics under homeomorphisms of the plane

For a homeomorphism `e` of `ℂ` and a function `D : ℂ → ℂ → ℝ`, write `D ∘ e` for `(u, v) ↦ D(e u, e v)`.
Paths are transported by `e`, so the internal metric of `D ∘ e` on the plane is the internal metric of `D`
between the images, and `D ∘ e` is a Euclidean length metric when `D` is one. The case of the affine maps
`u ↦ r u + z` (`r ≠ 0` real) is the one used for the coordinate change of an LQG metric.

## Main results

* `LatticeProb.LQG.internalMetric_univ_comp_homeomorph`: `D ∘ e(u, v; ℂ) = D(e u, e v; ℂ)`.
* `LatticeProb.LQG.IsEuclideanLengthMetric.comp_homeomorph`: `D ∘ e` is a Euclidean length metric.
* `LatticeProb.LQG.IsEuclideanLengthMetric.comp_affine`: `(u, v) ↦ D(r u + z, r v + z)` is a Euclidean length
  metric for real `r ≠ 0`.
-/

namespace LatticeProb.LQG

open Set
open scoped ENNReal

/-- The internal metric on the whole plane of `D ∘ e` is the internal metric of `D` between the images under
the homeomorphism `e`. -/
theorem internalMetric_univ_comp_homeomorph (D : ℂ → ℂ → ℝ) (e : ℂ ≃ₜ ℂ) (u v : ℂ) :
    internalMetric (fun x y => D (e x) (e y)) univ u v = internalMetric D univ (e u) (e v) := by
  have h := internalMetric_image_of_eq_mul (D := D) (D' := fun x y => D (e x) (e y)) e one_pos
    (fun x y => (one_mul _).symm) univ u v
  rw [image_univ_of_surjective e.surjective, ENNReal.ofReal_one, one_mul] at h
  exact h.symm

/-- The image of a Euclidean length metric under a homeomorphism `e` of the plane, `(u, v) ↦ D(e u, e v)`, is a
Euclidean length metric. -/
theorem IsEuclideanLengthMetric.comp_homeomorph {D : ℂ → ℂ → ℝ} (hD : IsEuclideanLengthMetric D)
    (e : ℂ ≃ₜ ℂ) : IsEuclideanLengthMetric fun u v => D (e u) (e v) where
  self_eq_zero z := hD.self_eq_zero (e z)
  eq_of_eq_zero z w h := e.injective (hD.eq_of_eq_zero _ _ h)
  symm z w := hD.symm _ _
  triangle x y z := hD.triangle _ _ _
  isOpen_iff U := by
    rw [← e.symm.isOpen_preimage, hD.isOpen_iff]
    constructor
    · intro h z hz
      obtain ⟨ε, hε, h'⟩ := h (e z) (by simpa using hz)
      exact ⟨ε, hε, fun w hw => by simpa using h' (e w) hw⟩
    · intro h z' hz'
      obtain ⟨ε, hε, h'⟩ := h (e.symm z') hz'
      exact ⟨ε, hε, fun w' hw' => h' (e.symm w') (by simpa using hw')⟩
  ofReal_eq_internalMetric z w := by
    rw [internalMetric_univ_comp_homeomorph, hD.ofReal_eq_internalMetric]

/-- The image of a Euclidean length metric under a real affine map `u ↦ r u + z`, `r ≠ 0`, is a Euclidean length
metric. -/
theorem IsEuclideanLengthMetric.comp_affine {D : ℂ → ℂ → ℝ} (hD : IsEuclideanLengthMetric D) {r : ℝ}
    (hr : r ≠ 0) (z : ℂ) : IsEuclideanLengthMetric fun u v => D (r * u + z) (r * v + z) :=
  hD.comp_homeomorph
    ((Homeomorph.mulLeft₀ (r : ℂ) (Complex.ofReal_ne_zero.mpr hr)).trans (Homeomorph.addRight z))

end LatticeProb.LQG
