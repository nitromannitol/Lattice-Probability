import LatticeProb.Topology.CurveSpace
import LatticeProb.Bonanno.BouRabeeGwynne.CurveSpace

/-! # Comparison of Fréchet curve spaces -/

set_option autoImplicit false
noncomputable section

open scoped unitInterval

namespace LatticeProb.CurveSpaceComparison

private def toSource {d : ℕ} : CurveSpace d → BouRabeeGwynne.CurveSpace d :=
  SeparationQuotient.lift
    (fun f : NormalizedCurve d => BouRabeeGwynne.CurveSpace.mk ⟨f.path⟩)
    (by
      intro f g h
      apply (BouRabeeGwynne.CurveSpace.mk_eq_mk_iff _ _).mpr
      exact EMetric.inseparable_iff.mp h)

private def fromSource {d : ℕ} : BouRabeeGwynne.CurveSpace d → CurveSpace d :=
  SeparationQuotient.lift
    (fun f : BouRabeeGwynne.NormalizedCurve d => CurveSpace.mk ⟨f.path⟩)
    (by
      intro f g h
      apply (CurveSpace.mk_eq_mk_iff _ _).mpr
      exact EMetric.inseparable_iff.mp h)

/-- The two presentations of Fréchet curve space are canonically isometric. -/
def isometryEquiv (d : ℕ) : CurveSpace d ≃ᵢ BouRabeeGwynne.CurveSpace d where
  toFun := toSource
  invFun := fromSource
  left_inv := by
    intro q
    obtain ⟨f, rfl⟩ := SeparationQuotient.surjective_mk q
    rfl
  right_inv := by
    intro q
    obtain ⟨f, rfl⟩ := SeparationQuotient.surjective_mk q
    rfl
  isometry_toFun := by
    intro x y
    obtain ⟨f, rfl⟩ := SeparationQuotient.surjective_mk x
    obtain ⟨g, rfl⟩ := SeparationQuotient.surjective_mk y
    rfl

/-- The isometry takes a path's class to the class of the same path. -/
@[simp] theorem isometryEquiv_project {d : ℕ}
    (f : C(unitInterval, EuclideanSpace ℝ (Fin d))) :
    isometryEquiv d (CurveSpace.project f) = BouRabeeGwynne.CurveSpace.project f := rfl

end LatticeProb.CurveSpaceComparison
end
