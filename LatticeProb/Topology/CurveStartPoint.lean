import LatticeProb.Topology.CurveSpace

/-! # The initial point of a curve class

Increasing changes of time fix `0`, so the initial point of a normalized curve is controlled by
the Fréchet distance and descends to the curve space: it is a `1`-Lipschitz function of the
class. -/

set_option autoImplicit false

open scoped ENNReal unitInterval

namespace LatticeProb

namespace NormalizedCurve

/-- The initial spatial point of a normalized representative. -/
def startPoint {d : ℕ} (f : NormalizedCurve d) : EuclideanSpace ℝ (Fin d) := f.path 0

/-- Increasing changes of time preserve the initial point, so its distance is controlled. -/
lemma startPoint_edist_le {d : ℕ} (f g : NormalizedCurve d) :
    edist f.startPoint g.startPoint ≤ frechetEDist f g := by
  apply le_iInf
  intro e
  have he : e (0 : unitInterval) = 0 := e.map_bot
  simpa only [startPoint, timeChangeCost, he] using
    (le_iSup (fun t : unitInterval ↦ edist (f.path t) (g.path (e t))) (0 : unitInterval))

end NormalizedCurve

namespace CurveSpace

/-- The initial point is independent of the representative, including pauses. -/
noncomputable def startPoint {d : ℕ} : CurveSpace d → EuclideanSpace ℝ (Fin d) :=
  SeparationQuotient.lift NormalizedCurve.startPoint fun f g h ↦
    edist_eq_zero.mp <| le_antisymm
      ((NormalizedCurve.startPoint_edist_le f g).trans_eq (EMetric.inseparable_iff.mp h)) bot_le

@[simp] lemma startPoint_mk {d : ℕ} (f : NormalizedCurve d) :
    startPoint (mk f) = f.startPoint := rfl

/-- The initial point of the class of a path is its value at `0`. -/
@[simp] lemma startPoint_project {d : ℕ} (f : C(unitInterval, EuclideanSpace ℝ (Fin d))) :
    startPoint (project f) = f 0 := rfl

lemma startPoint_lipschitz {d : ℕ} : LipschitzWith 1 (startPoint (d := d)) := by
  intro x y
  obtain ⟨f, rfl⟩ := SeparationQuotient.surjective_mk x
  obtain ⟨g, rfl⟩ := SeparationQuotient.surjective_mk y
  change edist f.startPoint g.startPoint ≤ (1 : ℝ≥0∞) * NormalizedCurve.frechetEDist f g
  simpa only [one_mul] using NormalizedCurve.startPoint_edist_le f g

lemma continuous_startPoint {d : ℕ} : Continuous (startPoint (d := d)) :=
  startPoint_lipschitz.continuous

end CurveSpace

end LatticeProb
