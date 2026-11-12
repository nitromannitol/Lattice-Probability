/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module MatedCRTHarmonic.Planar.Topology.Jordan.Summary at commit fdb5cad; only the module paths of local imports are changed. -/
/- Provenance: ported from an earlier mating-of-trees formalization; only imports and namespace names were changed. -/
import LatticeProb.Bonanno.MatedCRTHarmonic.Planar.Topology.Jordan.Main

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-! # The Jordan curve theorem: the full statement in the plane

For a continuous injective `r : S¹ → ℝ²`, the complement of `J = range r` is the disjoint union of
two connected components, one bounded and one unbounded, and each has frontier `J`.

This packages results of the port of github.com/rkirov/jordan_pick (commit `b3c9b7cf`, file
`JordanPick/JordanCurve.lean`): `exists_unbounded_component`, `step_A_exists_bounded`,
`step_B_bounded_unique`, `unbounded_component_unique` and `component_boundary_eq`
(Maehara, Amer. Math. Monthly 91 (1984), Lemma 1 and the main construction), with Brouwer's
fixed point theorem `Brouwer.brouwerFPT` discharged. The assembly below is a short new
argument (the original only states `Nat.card … = 2`, see `jordan_curve`).
-/

namespace MatedCRTHarmonic.Planar.Jordan

open Metric Set Function Bornology

/-- **Jordan curve theorem (full form).** The complement of a Jordan curve `J = range r` in
`ℝ²` is the disjoint union of the bounded component of `x₁` and the unbounded component of
`x₀`, and both components have frontier `J`. -/
theorem jordan_curve_components (r : sphere (0 : Plane) 1 → Plane)
    (hcont : Continuous r) (hinj : Injective r) :
    ∃ x₁ ∈ (range r)ᶜ, ∃ x₀ ∈ (range r)ᶜ,
      IsBounded (connectedComponentIn (range r)ᶜ x₁) ∧
      ¬ IsBounded (connectedComponentIn (range r)ᶜ x₀) ∧
      Disjoint (connectedComponentIn (range r)ᶜ x₁) (connectedComponentIn (range r)ᶜ x₀) ∧
      (range r)ᶜ = connectedComponentIn (range r)ᶜ x₁ ∪ connectedComponentIn (range r)ᶜ x₀ ∧
      frontier (connectedComponentIn (range r)ᶜ x₁) = range r ∧
      frontier (connectedComponentIn (range r)ᶜ x₀) = range r := by
  have hbr : BrouwerFPT := Brouwer.brouwerFPT
  obtain ⟨x₀, hx₀S, hx₀u⟩ := exists_unbounded_component r hcont
  obtain ⟨x₁, hx₁S, hx₁b⟩ := step_A_exists_bounded hbr hcont hinj
  have hne : connectedComponentIn (range r)ᶜ x₁ ≠ connectedComponentIn (range r)ᶜ x₀ :=
    fun h => hx₀u (h ▸ hx₁b)
  refine ⟨x₁, hx₁S, x₀, hx₀S, hx₁b, hx₀u, ?_, ?_,
    component_boundary_eq hbr hcont hinj hx₁S ⟨x₀, hx₀S, hne.symm⟩,
    component_boundary_eq hbr hcont hinj hx₀S ⟨x₁, hx₁S, hne⟩⟩
  · exact Set.disjoint_left.mpr fun z hz₁ hz₀ =>
      hne ((connectedComponentIn_eq hz₁).trans (connectedComponentIn_eq hz₀).symm)
  · refine Subset.antisymm (fun z hz => ?_)
      (union_subset (connectedComponentIn_subset _ _) (connectedComponentIn_subset _ _))
    have hzz : z ∈ connectedComponentIn (range r)ᶜ z := mem_connectedComponentIn hz
    by_cases hzb : IsBounded (connectedComponentIn (range r)ᶜ z)
    · left
      rwa [step_B_bounded_unique hbr hcont hinj x₁ hx₁S z hz hx₁b hzb]
    · right
      rwa [unbounded_component_unique r hcont hx₀u hzb]

end MatedCRTHarmonic.Planar.Jordan
