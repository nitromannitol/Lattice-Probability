/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module BouRabeeGwynne.CurveSpace at commit fdb5cad; only the module paths of local imports are changed. -/
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Topology.ContinuousMap.Compact
import Mathlib.Topology.ContinuousMap.SecondCountableSpace
import Mathlib.Topology.Order.MonotoneContinuity
import Mathlib.Topology.UnitInterval
import Mathlib.Topology.MetricSpace.Basic

/-!
# Continuous curves modulo increasing changes of time

Every representative has domain `[0,1]`, including constant curves representing
zero-duration stopped paths. The distance is the actual infimum of supremal
spatial errors over increasing homeomorphisms. Its separation quotient, rather
than the quotient by exact time-change orbits, is the metric curve space.
-/

open scoped ENNReal unitInterval

namespace BouRabeeGwynne

/-- A continuous curve with its time interval normalized to `[0,1]`. -/
structure NormalizedCurve (d : ℕ) where
  path : C(unitInterval, EuclideanSpace ℝ (Fin d))

namespace NormalizedCurve

/-- Order automorphisms of the unit interval are precisely its increasing
homeomorphisms. Continuity follows from `OrderIso.toHomeomorph`. -/
abbrev TimeChange := unitInterval ≃o unitInterval

/-- Every increasing homeomorphism is among the time changes used below. -/
def TimeChange.ofHomeomorph (h : unitInterval ≃ₜ unitInterval)
    (hh : StrictMono h) : TimeChange :=
  { h.toEquiv with map_rel_iff' := hh.le_iff_le }

/-- Constant representatives include paths stopped at time zero. -/
def const {d : ℕ} (x : EuclideanSpace ℝ (Fin d)) : NormalizedCurve d :=
  ⟨ContinuousMap.const unitInterval x⟩

/-- Supremal spatial error after a fixed increasing homeomorphic time change. -/
noncomputable def timeChangeCost {d : ℕ} (f g : NormalizedCurve d)
    (e : TimeChange) : ℝ≥0∞ :=
  ⨆ t : unitInterval, edist (f.path t) (g.path (e t))

/-- The Fréchet extended pseudodistance, as an actual infimum over time changes. -/
noncomputable def frechetEDist {d : ℕ} (f g : NormalizedCurve d) : ℝ≥0∞ :=
  ⨅ e : TimeChange, timeChangeCost f g e

lemma timeChangeCost_refl {d : ℕ} (f g : NormalizedCurve d) :
    timeChangeCost f g (OrderIso.refl unitInterval) = edist f.path g.path := by
  rw [ContinuousMap.edist_eq_iSup]
  rfl

lemma timeChangeCost_symm {d : ℕ} (f g : NormalizedCurve d) (e : TimeChange) :
    timeChangeCost g f e.symm = timeChangeCost f g e := by
  apply le_antisymm
  · apply iSup_le
    intro t
    simpa only [timeChangeCost, e.apply_symm_apply, edist_comm] using
      (le_iSup (fun s : unitInterval ↦ edist (f.path s) (g.path (e s))) (e.symm t))
  · apply iSup_le
    intro t
    simpa only [timeChangeCost, e.symm_apply_apply, edist_comm] using
      (le_iSup (fun s : unitInterval ↦ edist (g.path s) (f.path (e.symm s))) (e t))

lemma timeChangeCost_triangle {d : ℕ} (f g h : NormalizedCurve d)
    (e e' : TimeChange) :
    timeChangeCost f h (e.trans e') ≤ timeChangeCost f g e + timeChangeCost g h e' := by
  apply iSup_le
  intro t
  exact (edist_triangle (f.path t) (g.path (e t)) (h.path (e' (e t)))).trans
    (add_le_add (le_iSup (fun s ↦ edist (f.path s) (g.path (e s))) t)
      (le_iSup (fun s ↦ edist (g.path s) (h.path (e' s))) (e t)))

@[simp] lemma frechetEDist_self {d : ℕ} (f : NormalizedCurve d) :
    frechetEDist f f = 0 := by
  apply le_antisymm _ bot_le
  calc
    frechetEDist f f ≤ timeChangeCost f f (OrderIso.refl unitInterval) := iInf_le _ _
    _ = 0 := by rw [timeChangeCost_refl, edist_self]

lemma frechetEDist_comm {d : ℕ} (f g : NormalizedCurve d) :
    frechetEDist f g = frechetEDist g f := by
  apply le_antisymm
  · apply le_iInf
    intro e
    exact (iInf_le _ e.symm).trans_eq (timeChangeCost_symm g f e)
  · apply le_iInf
    intro e
    exact (iInf_le _ e.symm).trans_eq (timeChangeCost_symm f g e)

lemma frechetEDist_triangle {d : ℕ} (f g h : NormalizedCurve d) :
    frechetEDist f h ≤ frechetEDist f g + frechetEDist g h := by
  apply ENNReal.le_iInf_add_iInf
  intro e e'
  exact (iInf_le _ (e.trans e')).trans (timeChangeCost_triangle f g h e e')

lemma frechetEDist_le_edist_path {d : ℕ} (f g : NormalizedCurve d) :
    frechetEDist f g ≤ edist f.path g.path :=
  (iInf_le _ (OrderIso.refl unitInterval)).trans_eq (timeChangeCost_refl f g)

lemma frechetEDist_ne_top {d : ℕ} (f g : NormalizedCurve d) :
    frechetEDist f g ≠ ⊤ :=
  ((frechetEDist_le_edist_path f g).trans_lt (edist_lt_top f.path g.path)).ne

/-- The pseudometric axioms have been proved for the actual infimum above. -/
@[instance_reducible] noncomputable def frechetPseudoEMetricSpace (d : ℕ) :
    PseudoEMetricSpace (NormalizedCurve d) where
  edist := frechetEDist
  edist_self := frechetEDist_self
  edist_comm := frechetEDist_comm
  edist_triangle := frechetEDist_triangle

/-- Finiteness follows by comparison with the ordinary uniform path metric. -/
noncomputable instance {d : ℕ} : PseudoMetricSpace (NormalizedCurve d) :=
  @PseudoEMetricSpace.toPseudoMetricSpace _ (frechetPseudoEMetricSpace d)
    (fun f g ↦ frechetEDist_ne_top f g)

@[simp] lemma edist_eq_frechetEDist {d : ℕ} (f g : NormalizedCurve d) :
    edist f g = frechetEDist f g := rfl

/-- Forget the uniform-path topology in favor of the Fréchet pseudometric. -/
def ofPath {d : ℕ} (f : C(unitInterval, EuclideanSpace ℝ (Fin d))) :
    NormalizedCurve d := ⟨f⟩

lemma ofPath_lipschitz {d : ℕ} : LipschitzWith 1 (ofPath (d := d)) := by
  intro f g
  simpa only [ENNReal.coe_one, one_mul, edist_eq_frechetEDist, ofPath] using
    frechetEDist_le_edist_path (ofPath f) (ofPath g)

instance {d : ℕ} : TopologicalSpace.SeparableSpace (NormalizedCurve d) := by
  have hs : Function.Surjective (ofPath (d := d)) := fun f ↦ ⟨f.path, rfl⟩
  exact hs.denseRange.separableSpace ofPath_lipschitz.continuous

/-- The terminal spatial point of a normalized representative. -/
def endPoint {d : ℕ} (f : NormalizedCurve d) : EuclideanSpace ℝ (Fin d) := f.path 1

/-- Increasing changes of time preserve the endpoint, so its distance is controlled. -/
lemma endpoint_edist_le {d : ℕ} (f g : NormalizedCurve d) :
    edist f.endPoint g.endPoint ≤ frechetEDist f g := by
  apply le_iInf
  intro e
  have he : e (1 : unitInterval) = 1 := e.map_top
  simpa only [endPoint, timeChangeCost, he] using
    (le_iSup (fun t : unitInterval ↦ edist (f.path t) (g.path (e t))) (1 : unitInterval))

lemma endPoint_lipschitz {d : ℕ} : LipschitzWith 1 (endPoint (d := d)) := by
  intro f g
  simpa only [ENNReal.coe_one, one_mul, edist_eq_frechetEDist] using
    endpoint_edist_le f g

end NormalizedCurve

/-- The metric space of curves modulo zero Fréchet distance. -/
abbrev CurveSpace (d : ℕ) := SeparationQuotient (NormalizedCurve d)

namespace CurveSpace

/-- Pass from a normalized representative to its metric curve class. -/
noncomputable def mk {d : ℕ} (f : NormalizedCurve d) : CurveSpace d :=
  SeparationQuotient.mk f

/-- The quotient metric is exactly the paper's infimum of supremal errors. -/
theorem edist_mk {d : ℕ} (f g : NormalizedCurve d) :
    edist (mk f) (mk g) =
      ⨅ e : NormalizedCurve.TimeChange,
        ⨆ t : unitInterval, edist (f.path t) (g.path (e t)) := rfl

theorem mk_eq_mk_iff {d : ℕ} (f g : NormalizedCurve d) :
    mk f = mk g ↔ NormalizedCurve.frechetEDist f g = 0 := by
  rw [mk, mk, SeparationQuotient.mk_eq_mk, EMetric.inseparable_iff]
  rfl

instance {d : ℕ} : TopologicalSpace.SeparableSpace (CurveSpace d) :=
  (SeparationQuotient.isQuotientMap_mk (X := NormalizedCurve d)).separableSpace

/-- Projection from ordinary continuous paths with their uniform metric. -/
noncomputable def project {d : ℕ} (f : C(unitInterval, EuclideanSpace ℝ (Fin d))) :
    CurveSpace d := mk (NormalizedCurve.ofPath f)

lemma project_lipschitz {d : ℕ} : LipschitzWith 1 (project (d := d)) := by
  intro f g
  change NormalizedCurve.frechetEDist (NormalizedCurve.ofPath f) (NormalizedCurve.ofPath g) ≤
    (1 : ℝ≥0∞) * edist f g
  simpa only [one_mul, NormalizedCurve.ofPath] using
    NormalizedCurve.frechetEDist_le_edist_path (NormalizedCurve.ofPath f)
      (NormalizedCurve.ofPath g)

lemma continuous_project {d : ℕ} : Continuous (project (d := d)) :=
  project_lipschitz.continuous

lemma surjective_project {d : ℕ} : Function.Surjective (project (d := d)) := by
  intro q
  obtain ⟨f, rfl⟩ := SeparationQuotient.surjective_mk q
  exact ⟨f.path, rfl⟩

/-- The terminal point is independent of the representative, including pauses. -/
noncomputable def endPoint {d : ℕ} : CurveSpace d → EuclideanSpace ℝ (Fin d) :=
  SeparationQuotient.lift NormalizedCurve.endPoint fun f g h ↦
    edist_eq_zero.mp <| le_antisymm
      ((NormalizedCurve.endpoint_edist_le f g).trans_eq (EMetric.inseparable_iff.mp h)) bot_le

@[simp] lemma endPoint_mk {d : ℕ} (f : NormalizedCurve d) :
    endPoint (mk f) = f.endPoint := rfl

lemma endPoint_lipschitz {d : ℕ} : LipschitzWith 1 (endPoint (d := d)) := by
  intro x y
  obtain ⟨f, rfl⟩ := SeparationQuotient.surjective_mk x
  obtain ⟨g, rfl⟩ := SeparationQuotient.surjective_mk y
  change edist f.endPoint g.endPoint ≤ (1 : ℝ≥0∞) * NormalizedCurve.frechetEDist f g
  simpa only [one_mul] using NormalizedCurve.endpoint_edist_le f g

lemma continuous_endPoint {d : ℕ} : Continuous (endPoint (d := d)) :=
  endPoint_lipschitz.continuous

end CurveSpace

end BouRabeeGwynne
