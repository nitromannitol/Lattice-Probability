import LatticeProb.Topology.CurveSpace

/-! # Lipschitz maps on finite curves -/

set_option autoImplicit false
noncomputable section

open scoped ENNReal NNReal unitInterval

namespace LatticeProb

namespace NormalizedCurve

/-- Apply a continuous spatial map to a parametrized curve. -/
def spatialMap {d e : ℕ} (F : C(EuclideanSpace ℝ (Fin d), EuclideanSpace ℝ (Fin e)))
    (f : NormalizedCurve d) : NormalizedCurve e := ⟨F.comp f.path⟩

/-- Spatial Lipschitz maps control the Fréchet distance of representatives. -/
theorem frechetEDist_spatialMap_le {d e : ℕ}
    (F : C(EuclideanSpace ℝ (Fin d), EuclideanSpace ℝ (Fin e)))
    {K : ℝ≥0} (hF : LipschitzWith K F) (f g : NormalizedCurve d) :
    frechetEDist (spatialMap F f) (spatialMap F g) ≤ (K : ℝ≥0∞) * frechetEDist f g := by
  have hc (t : TimeChange) : timeChangeCost (spatialMap F f) (spatialMap F g) t ≤
      (K : ℝ≥0∞) * timeChangeCost f g t := by
    apply iSup_le
    intro u
    exact (hF (f.path u) (g.path (t u))).trans
      (mul_le_mul_right (le_iSup (fun v : unitInterval =>
        edist (f.path v) (g.path (t v))) u) _)
  by_cases hK : K = 0
  · subst K
    simpa only [ENNReal.coe_zero, zero_mul, frechetEDist] using
      (le_trans (iInf_le (fun t => timeChangeCost (spatialMap F f) (spatialMap F g) t)
        (OrderIso.refl unitInterval)) (hc (OrderIso.refl unitInterval)))
  · simp only [frechetEDist]
    rw [ENNReal.mul_iInf_of_ne (by exact_mod_cast hK) ENNReal.coe_ne_top]
    apply le_iInf
    intro t
    exact (iInf_le _ t).trans (hc t)

end NormalizedCurve

namespace CurveSpace

/-- A Lipschitz spatial map acts on curves modulo zero Fréchet distance. -/
def spatialMap {d e : ℕ}
    (F : C(EuclideanSpace ℝ (Fin d), EuclideanSpace ℝ (Fin e)))
    {K : ℝ≥0} (hF : LipschitzWith K F) : CurveSpace d → CurveSpace e :=
  SeparationQuotient.lift (fun f => mk (NormalizedCurve.spatialMap F f)) (by
    intro f g h
    apply (mk_eq_mk_iff _ _).mpr
    have hzero : NormalizedCurve.frechetEDist f g = 0 := EMetric.inseparable_iff.mp h
    have hle : NormalizedCurve.frechetEDist (NormalizedCurve.spatialMap F f)
        (NormalizedCurve.spatialMap F g) ≤ 0 := by
      simpa only [hzero, mul_zero] using NormalizedCurve.frechetEDist_spatialMap_le F hF f g
    exact le_antisymm hle zero_le)

/-- The induced map has the same Lipschitz constant. -/
theorem spatialMap_lipschitz {d e : ℕ}
    (F : C(EuclideanSpace ℝ (Fin d), EuclideanSpace ℝ (Fin e)))
    {K : ℝ≥0} (hF : LipschitzWith K F) : LipschitzWith K (spatialMap F hF) := by
  intro x y
  obtain ⟨f, rfl⟩ := SeparationQuotient.surjective_mk x
  obtain ⟨g, rfl⟩ := SeparationQuotient.surjective_mk y
  exact NormalizedCurve.frechetEDist_spatialMap_le F hF f g

/-- Spatial maps commute with projection of a representative. -/
@[simp] theorem spatialMap_project {d e : ℕ}
    (F : C(EuclideanSpace ℝ (Fin d), EuclideanSpace ℝ (Fin e)))
    {K : ℝ≥0} (hF : LipschitzWith K F)
    (f : C(unitInterval, EuclideanSpace ℝ (Fin d))) :
    spatialMap F hF (project f) = project (F.comp f) := rfl

end CurveSpace
end LatticeProb
