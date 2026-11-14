import LatticeProb.Topology.LocalCurveIntervalDistanceBound

/-! # Local curve classes of unbounded continuous rays -/

set_option autoImplicit false

open scoped ENNReal

namespace LatticeProb

open UnboundedRayIntervalIntegrand UnboundedRayLocalDistance

/-- A continuous unbounded ray, endowed below with its local curve pseudometric. -/
structure LocalRay (d : ℕ) where
  ray : UnboundedRay d

namespace LocalRay

/-- The local curve distance defines an extended pseudometric. -/
@[instance_reducible] noncomputable def pseudoEMetricSpace (d : ℕ) :
    PseudoEMetricSpace (LocalRay d) where
  edist f g := localEDist f.ray g.ray
  edist_self f := localEDist_self f.ray
  edist_comm f g := localEDist_comm f.ray g.ray
  edist_triangle f g h := localEDist_triangle f.ray g.ray h.ray

/-- The local curve distance is finite. -/
noncomputable instance {d : ℕ} : PseudoMetricSpace (LocalRay d) :=
  @PseudoEMetricSpace.toPseudoMetricSpace _ (pseudoEMetricSpace d)
    (fun f g => localEDist_ne_top f.ray g.ray)

@[simp] theorem edist_eq_localEDist {d : ℕ} (f g : LocalRay d) :
    edist f g = localEDist f.ray g.ray := rfl

end LocalRay

/-- Unbounded continuous rays modulo zero local curve distance. -/
abbrev UnboundedRayCurveSpace (d : ℕ) := SeparationQuotient (LocalRay d)

namespace UnboundedRayCurveSpace

/-- The local curve class of an unbounded continuous ray. -/
noncomputable def project {d : ℕ} (f : UnboundedRay d) : UnboundedRayCurveSpace d :=
  SeparationQuotient.mk ⟨f⟩

@[simp] theorem edist_project {d : ℕ} (f g : UnboundedRay d) :
    edist (project f) (project g) = localEDist f g := rfl

theorem project_eq_project_iff {d : ℕ} (f g : UnboundedRay d) :
    project f = project g ↔ localEDist f g = 0 := by
  rw [project, project, SeparationQuotient.mk_eq_mk, EMetric.inseparable_iff]
  rfl

theorem surjective_project {d : ℕ} : Function.Surjective (project (d := d)) := by
  intro q
  obtain ⟨f, rfl⟩ := SeparationQuotient.surjective_mk q
  exact ⟨f.ray, by cases f; rfl⟩

end UnboundedRayCurveSpace
end LatticeProb
