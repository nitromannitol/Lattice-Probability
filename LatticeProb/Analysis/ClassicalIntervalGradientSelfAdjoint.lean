import LatticeProb.Analysis.ClassicalIntervalSineSelfAdjoint

/-! # Self-adjoint interval gradient composition -/

set_option autoImplicit false

open MeasureTheory Set

namespace LatticeProb

noncomputable section

/-- The domain on which the closed interval gradient takes values in the
adjoint domain. -/
def classicalIntervalGradientCompositionDomain (a b : ℝ) :
    Submodule ℂ (Lp ℂ 2 (volume.restrict (Ioo a b))) :=
  (((classicalIntervalGradient a b).closure.adjoint.domain.comap
    (classicalIntervalGradient a b).closure.toFun).map
    (classicalIntervalGradient a b).closure.domain.subtype)

/-- The adjoint of the closed interval gradient composed with the gradient on
its natural domain. -/
def classicalIntervalGradientComposition (a b : ℝ) :
    (Lp ℂ 2 (volume.restrict (Ioo a b))) →ₗ.[ℂ]
      (Lp ℂ 2 (volume.restrict (Ioo a b))) := by
  let G := (classicalIntervalGradient a b).closure
  let D := classicalIntervalGradientCompositionDomain a b
  let R := G.domRestrict D
  have hR : ∀ u : R.domain, R u ∈ G.adjoint.domain := by
    intro u
    obtain ⟨v, hv, heq⟩ := u.property.1
    change G v ∈ G.adjoint.domain at hv
    have hu : (u : Lp ℂ 2 (volume.restrict (Ioo a b))) = v := heq.symm
    rw [LinearPMap.domRestrict_apply hu]
    exact hv
  exact G.adjoint.comp R hR

/-- The interval gradient composition has the graph of the adjoint of the
finite sine core. -/
theorem classicalIntervalGradientComposition_eq_sine_adjoint {a b : ℝ}
    (hab : a < b) :
    classicalIntervalGradientComposition a b =
      (show (Lp ℂ 2 (volume.restrict (Ioo a b))) →ₗ.[ℂ]
        (Lp ℂ 2 (volume.restrict (Ioo a b))) from
        ⟨_, orthonormalDiagonalCore (intervalSineHilbertBasis hab).orthonormal
          (fun n => (Real.pi * (n + 1 : ℕ) / (b - a)) ^ 2)⟩).adjoint := by
  apply LinearPMap.eq_of_eq_graph
  ext ⟨x, y⟩
  rw [intervalSine_adjoint_graph_iff hab]
  constructor
  · intro h
    obtain ⟨u, hu, hv⟩ := (LinearPMap.mem_graph_iff _).mp h
    refine ⟨⟨u, u.property.2⟩, ?_, ?_⟩
    · obtain ⟨v, hvg, heq⟩ := u.property.1
      change (classicalIntervalGradient a b).closure v ∈
        (classicalIntervalGradient a b).closure.adjoint.domain at hvg
      have : (⟨u, u.property.2⟩ : (classicalIntervalGradient a b).closure.domain) = v :=
        Subtype.ext heq.symm
      rw [this]
      exact hvg
    · exact Prod.ext hu hv
  · rintro ⟨u, hu, heq⟩
    have hD : (u : Lp ℂ 2 (volume.restrict (Ioo a b))) ∈
        classicalIntervalGradientCompositionDomain a b := ⟨u, hu, rfl⟩
    let v : (classicalIntervalGradientComposition a b).domain := ⟨u, hD, u.property⟩
    apply (LinearPMap.mem_graph_iff _).mpr
    exact ⟨v, (Prod.ext_iff.mp heq).1, (Prod.ext_iff.mp heq).2⟩

/-- The natural composition of the closed interval gradient with its adjoint
is self-adjoint. -/
theorem classicalIntervalGradientComposition_isSelfAdjoint {a b : ℝ} (hab : a < b) :
    IsSelfAdjoint (classicalIntervalGradientComposition a b) := by
  rw [classicalIntervalGradientComposition_eq_sine_adjoint hab]
  exact intervalSine_adjoint_isSelfAdjoint hab

end

end LatticeProb
