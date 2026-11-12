/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module MatedCRTHarmonic.Planar.Topology.Jordan.Complex at commit fdb5cad; only the module paths of local imports are changed. -/
/- Provenance: ported from an earlier mating-of-trees formalization; only imports and namespace names were changed. -/
import LatticeProb.Bonanno.MatedCRTHarmonic.Planar.Topology.Jordan.Summary
import LatticeProb.Bonanno.LQGMetric.Complex.JordanMapCurve

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-! # The Jordan curve theorem in `ℂ`

The Jordan curve theorem for a Jordan curve `Γ ⊆ ℂ` in the sense of LQGMetric's
`LQGMetric.JordanMap.IsJordanCurve` (the image of the unit circle under a map continuous and
injective on it): `Γᶜ` is the disjoint union of a bounded and an unbounded component, each with
frontier `Γ`.

Obtained from the plane version `jordan_curve_components` (ported from rkirov/jordan_pick) by
transport along the linear isometry `Arcs.complexLIE : ℂ ≃ₗᵢ[ℝ] ℝ²` of the same port. The
transport is a short new bridge; it reuses the existing `IsJordanCurve` instead of introducing a
new notion of Jordan curve in `ℂ`.
-/

namespace MatedCRTHarmonic.Planar.Jordan

open Metric Set Function Bornology

/-- **Jordan curve theorem in `ℂ`.** For a Jordan curve `Γ ⊆ ℂ`, `Γᶜ` is the disjoint union of
the bounded component of `x₁` and the unbounded component of `x₀`, both with frontier `Γ`. -/
theorem jordan_curve_components_complex {Γ : Set ℂ} (hΓ : LQGMetric.JordanMap.IsJordanCurve Γ) :
    ∃ x₁ ∈ Γᶜ, ∃ x₀ ∈ Γᶜ,
      IsBounded (connectedComponentIn Γᶜ x₁) ∧
      ¬ IsBounded (connectedComponentIn Γᶜ x₀) ∧
      Disjoint (connectedComponentIn Γᶜ x₁) (connectedComponentIn Γᶜ x₀) ∧
      Γᶜ = connectedComponentIn Γᶜ x₁ ∪ connectedComponentIn Γᶜ x₀ ∧
      frontier (connectedComponentIn Γᶜ x₁) = Γ ∧
      frontier (connectedComponentIn Γᶜ x₀) = Γ := by
  obtain ⟨γ, hγc, hγi, rfl⟩ := hΓ
  set L := Arcs.complexLIE
  have hLs : ∀ p : sphere (0 : Plane) 1, L.symm p ∈ sphere (0 : ℂ) 1 := fun p => by
    rw [mem_sphere_zero_iff_norm, L.symm.norm_map, ← mem_sphere_zero_iff_norm]; exact p.2
  set r : sphere (0 : Plane) 1 → Plane := fun p => L (γ (L.symm p)) with hr
  have hcont : Continuous r :=
    L.continuous.comp (hγc.comp_continuous (L.symm.continuous.comp continuous_subtype_val) hLs)
  have hinj : Injective r := fun p q hpq =>
    Subtype.ext (L.symm.injective (hγi (hLs p) (hLs q) (L.injective hpq)))
  set h : Plane ≃ₜ ℂ := L.symm.toHomeomorph
  have hh : ⇑h = ⇑L.symm := rfl
  have hrange : h '' range r = γ '' sphere 0 1 := by
    ext z
    constructor
    · rintro ⟨_, ⟨p, rfl⟩, rfl⟩
      exact ⟨L.symm p, hLs p, by simp [hh, hr]⟩
    · rintro ⟨w, hw, rfl⟩
      refine ⟨L (γ w), ⟨⟨L w, ?_⟩, ?_⟩, by simp [hh]⟩
      · rw [mem_sphere_zero_iff_norm, L.norm_map, ← mem_sphere_zero_iff_norm]; exact hw
      · simp [hr]
  have hcompl : (γ '' sphere 0 1)ᶜ = h '' (range r)ᶜ := by
    rw [← hrange, image_compl_eq h.bijective]
  have hmem : ∀ y ∈ (range r)ᶜ, h y ∈ (γ '' sphere 0 1)ᶜ := fun y hy => by
    rw [hcompl]; exact mem_image_of_mem h hy
  have hcc : ∀ y ∈ (range r)ᶜ, connectedComponentIn (γ '' sphere 0 1)ᶜ (h y)
      = h '' connectedComponentIn (range r)ᶜ y := fun y hy => by
    rw [hcompl, h.image_connectedComponentIn hy]
  obtain ⟨y₁, hy₁, y₀, hy₀, hb, hu, hdisj, hunion, hfr₁, hfr₀⟩ :=
    jordan_curve_components r hcont hinj
  refine ⟨h y₁, hmem y₁ hy₁, h y₀, hmem y₀ hy₀, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hcc y₁ hy₁, hh]; exact L.symm.lipschitz.isBounded_image hb
  · rw [hcc y₀ hy₀, hh]
    exact fun hb' => hu ((L.symm.isometry.antilipschitzWith.isBounded_preimage hb').subset
      (subset_preimage_image _ _))
  · rw [hcc y₁ hy₁, hcc y₀ hy₀]; exact (disjoint_image_iff h.injective).mpr hdisj
  · rw [hcc y₁ hy₁, hcc y₀ hy₀, ← image_union, ← hunion, hcompl]
  · rw [hcc y₁ hy₁, ← h.image_frontier, hfr₁, hrange]
  · rw [hcc y₀ hy₀, ← h.image_frontier, hfr₀, hrange]

end MatedCRTHarmonic.Planar.Jordan
