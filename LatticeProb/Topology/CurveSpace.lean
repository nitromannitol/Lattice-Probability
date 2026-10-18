/-
Adapted from Leonardo Bonanno’s formalizations:
https://github.com/leobon12/lean-formalizations
Source: BouRabeeGwynne/CurveSpace.lean and BouRabeeGwynne/CurvePauses.lean.
-/
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Topology.ContinuousMap.Compact
import Mathlib.Topology.ContinuousMap.SecondCountableSpace
import Mathlib.Topology.Order.MonotoneContinuity
import Mathlib.Topology.UnitInterval
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Topology.Order.ProjIcc
import Mathlib.Order.Hom.Set
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Continuous curves modulo increasing changes of time

Every representative has domain `[0,1]`, including constant curves representing
zero-duration stopped paths. The distance is the actual infimum of supremal
spatial errors over increasing homeomorphisms. Its separation quotient, rather
than the quotient by exact time-change orbits, is the metric curve space.
-/

open scoped ENNReal unitInterval

namespace LatticeProb

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

end LatticeProb


/-! Constant pauses do not change the actual Fréchet curve class. A continuous
nondecreasing time map is approximated by explicit strictly increasing
homeomorphisms; it is never assumed to be an allowed homeomorphism itself. -/

open Set
open scoped unitInterval ENNReal

namespace LatticeProb
namespace CurvePauses

variable (φ : C(unitInterval, unitInterval))

/-- Add a small strictly increasing part to the original nondecreasing clock. -/
noncomputable def blend (ε : ℝ) (hε : 0 ≤ ε) (hε1 : ε ≤ 1)
    (t : unitInterval) : unitInterval :=
  ⟨(1 - ε) * (φ t : ℝ) + ε * (t : ℝ),
    ⟨add_nonneg (mul_nonneg (sub_nonneg.mpr hε1) (φ t).property.1)
      (mul_nonneg hε t.property.1), by
      have h₁ := mul_le_mul_of_nonneg_left (φ t).property.2 (sub_nonneg.mpr hε1)
      have h₂ := mul_le_mul_of_nonneg_left t.property.2 hε
      nlinarith⟩⟩

lemma continuous_blend (ε : ℝ) (hε : 0 ≤ ε) (hε1 : ε ≤ 1) :
    Continuous (blend φ ε hε hε1) := by
  unfold blend
  fun_prop

lemma blend_strictMono (hmono : Monotone φ) (ε : ℝ) (hε : 0 < ε) (hε1 : ε ≤ 1) :
    StrictMono (blend φ ε hε.le hε1) := by
  intro s t hst
  change (1 - ε) * (φ s : ℝ) + ε * (s : ℝ) <
    (1 - ε) * (φ t : ℝ) + ε * (t : ℝ)
  exact add_lt_add_of_le_of_lt
    (mul_le_mul_of_nonneg_left (hmono hst.le) (sub_nonneg.mpr hε1))
    (mul_lt_mul_of_pos_left hst hε)

lemma blend_zero (hzero : φ 0 = 0) (ε : ℝ) (hε : 0 ≤ ε) (hε1 : ε ≤ 1) :
    blend φ ε hε hε1 0 = 0 := by
  apply Subtype.ext
  simp [blend, hzero]

lemma blend_one (hone : φ 1 = 1) (ε : ℝ) (hε : 0 ≤ ε) (hε1 : ε ≤ 1) :
    blend φ ε hε hε1 1 = 1 := by
  apply Subtype.ext
  simp [blend, hone]

lemma blend_surjective (hzero : φ 0 = 0) (hone : φ 1 = 1)
    (ε : ℝ) (hε : 0 ≤ ε) (hε1 : ε ≤ 1) :
    Function.Surjective (blend φ ε hε hε1) := by
  intro y
  apply intermediate_value_univ (0 : unitInterval) (1 : unitInterval)
    (continuous_blend φ ε hε hε1)
  rw [blend_zero φ hzero, blend_one φ hone]
  exact ⟨bot_le, le_top⟩

/-- An actual increasing order isomorphism, hence an allowed time homeomorphism. -/
noncomputable def blendTimeChange (hmono : Monotone φ) (hzero : φ 0 = 0) (hone : φ 1 = 1)
    (ε : ℝ) (hε : 0 < ε) (hε1 : ε ≤ 1) : unitInterval ≃o unitInterval :=
  StrictMono.orderIsoOfSurjective (blend φ ε hε.le hε1)
    (blend_strictMono φ hmono ε hε hε1) (blend_surjective φ hzero hone ε hε.le hε1)

lemma blend_dist_le (ε : ℝ) (hε : 0 ≤ ε) (hε1 : ε ≤ 1) (t : unitInterval) :
    dist (blend φ ε hε hε1 t) (φ t) ≤ ε := by
  change |(1 - ε) * (φ t : ℝ) + ε * (t : ℝ) - (φ t : ℝ)| ≤ ε
  have heq : (1 - ε) * (φ t : ℝ) + ε * (t : ℝ) - (φ t : ℝ) =
      ε * ((t : ℝ) - (φ t : ℝ)) := by ring
  rw [heq, abs_mul, abs_of_nonneg hε]
  have hd : |(t : ℝ) - (φ t : ℝ)| ≤ 1 := by
    rw [abs_le]
    constructor <;> linarith [t.property.1, t.property.2,
      (φ t).property.1, (φ t).property.2]
  exact (mul_le_mul_of_nonneg_left hd hε).trans_eq (mul_one ε)

end CurvePauses

/-- Continuous nondecreasing surjective clocks, including terminal pauses,
preserve the actual infimum-over-homeomorphisms Fréchet quotient. -/
theorem curveSpace_project_comp_monotone {d : ℕ}
    (f : C(unitInterval, EuclideanSpace ℝ (Fin d)))
    (φ : C(unitInterval, unitInterval)) (hmono : Monotone φ)
    (hzero : φ 0 = 0) (hone : φ 1 = 1) :
    CurveSpace.project (f.comp φ) = CurveSpace.project f := by
  apply dist_eq_zero.mp
  apply le_antisymm _ dist_nonneg
  apply le_of_forall_pos_le_add
  intro η hη
  obtain ⟨δ, hδ, huc⟩ := f.uniform_continuity η hη
  let ε : ℝ := min (δ / 2) (1 / 2)
  have hε : 0 < ε := lt_min (half_pos hδ) (by norm_num)
  have hε1 : ε ≤ 1 := (min_le_right _ _).trans (by norm_num)
  have hεδ : ε < δ := (min_le_left _ _).trans_lt (half_lt_self hδ)
  let e := CurvePauses.blendTimeChange φ hmono hzero hone ε hε hε1
  have hcost : NormalizedCurve.timeChangeCost
      (NormalizedCurve.ofPath (f.comp φ)) (NormalizedCurve.ofPath f) e ≤ ENNReal.ofReal η := by
    apply iSup_le
    intro t
    change edist (f (φ t)) (f (e t)) ≤ ENNReal.ofReal η
    rw [edist_dist]
    apply ENNReal.ofReal_le_ofReal
    apply (huc ?_).le
    have ht := CurvePauses.blend_dist_le φ ε hε.le hε1 t
    change dist (φ t) (CurvePauses.blend φ ε hε.le hε1 t) < δ
    rw [dist_comm]
    exact ht.trans_lt hεδ
  have hdist : edist (CurveSpace.project (f.comp φ)) (CurveSpace.project f) ≤
      ENNReal.ofReal η := (iInf_le _ e).trans hcost
  rw [edist_dist] at hdist
  have hr := (ENNReal.ofReal_le_ofReal_iff hη.le).mp hdist
  simpa only [zero_add] using hr

/-- The clamped clock `t ↦ projIcc 0 1 (t / a)`, defined for every real `a`.
For `0 < a ≤ 1`, it finishes at normalized time `a` and holds its endpoint.
At `a ≤ 0` it is the constant zero clock. -/
noncomputable def terminalPauseClock (a : ℝ) : C(unitInterval, unitInterval) :=
  ⟨fun t => projIcc 0 1 zero_le_one ((t : ℝ) / a), by fun_prop⟩

/-- Nonpositive parameters give the zero clock under the clamped formula. -/
lemma terminalPauseClock_of_nonpos {a : ℝ} (ha : a ≤ 0) :
    terminalPauseClock a = ContinuousMap.const unitInterval 0 := by
  apply ContinuousMap.ext
  intro t
  apply projIcc_eq_zero.mpr
  exact div_nonpos_of_nonneg_of_nonpos t.property.1 ha

lemma terminalPauseClock_monotone {a : ℝ} (ha : 0 < a) :
    Monotone (terminalPauseClock a) := by
  intro s t hst
  exact monotone_projIcc zero_le_one (div_le_div_of_nonneg_right hst ha.le)

@[simp] lemma terminalPauseClock_zero (a : ℝ) : terminalPauseClock a 0 = 0 := by
  simp [terminalPauseClock, projIcc_left]

lemma terminalPauseClock_one {a : ℝ} (ha : 0 < a) (ha1 : a ≤ 1) :
    terminalPauseClock a 1 = 1 := by
  apply projIcc_eq_one.mpr
  exact (one_le_div ha).mpr ha1

lemma terminalPauseClock_of_le {a : ℝ} (ha : 0 < a) (t : unitInterval)
    (ht : a ≤ (t : ℝ)) : terminalPauseClock a t = 1 := by
  apply projIcc_eq_one.mpr
  exact (one_le_div ha).mpr ht

/-- Adding a constant terminal segment leaves the genuine curve class unchanged. -/
theorem curveSpace_project_terminalPause {d : ℕ}
    (f : C(unitInterval, EuclideanSpace ℝ (Fin d))) {a : ℝ}
    (ha : 0 < a) (ha1 : a ≤ 1) :
    CurveSpace.project (f.comp (terminalPauseClock a)) = CurveSpace.project f :=
  curveSpace_project_comp_monotone f _ (terminalPauseClock_monotone ha)
    (terminalPauseClock_zero a) (terminalPauseClock_one ha ha1)

end LatticeProb

/-! ## Nonvacuity checks

Constant representatives exist in every dimension, including dimension zero.
The identity is an increasing homeomorphism and an endpoint-preserving monotone
clock. The last check uses a nonconstant segment and a genuine terminal pause.
-/
namespace LatticeProb

example (d : ℕ) : Nonempty (NormalizedCurve d) := ⟨NormalizedCurve.const 0⟩

example (d : ℕ) : Nonempty (CurveSpace d) := ⟨CurveSpace.mk (NormalizedCurve.const 0)⟩

example : StrictMono (Homeomorph.refl unitInterval) := fun _ _ h => h

example : Monotone (ContinuousMap.id unitInterval) ∧
    ContinuousMap.id unitInterval 0 = 0 ∧ ContinuousMap.id unitInterval 1 = 1 :=
  ⟨monotone_id, rfl, rfl⟩

example (d : ℕ) (f : C(unitInterval, EuclideanSpace ℝ (Fin d))) :
    CurveSpace.project (f.comp (ContinuousMap.id unitInterval)) = CurveSpace.project f :=
  curveSpace_project_comp_monotone f _ monotone_id rfl rfl

example : (0 : ℝ) < 1 / 2 ∧ (1 / 2 : ℝ) ≤ 1 := by norm_num

example : ∃ f : C(unitInterval, EuclideanSpace ℝ (Fin 1)),
    f 0 ≠ f 1 ∧ CurveSpace.project (f.comp (terminalPauseClock (1 / 2))) =
      CurveSpace.project f := by
  let f : C(unitInterval, EuclideanSpace ℝ (Fin 1)) :=
    ⟨fun t => (t : ℝ) • EuclideanSpace.single 0 1, by fun_prop⟩
  refine ⟨f, ?_, curveSpace_project_terminalPause f (by norm_num) (by norm_num)⟩
  intro h
  have hc := congrArg (fun x : EuclideanSpace ℝ (Fin 1) => x 0) h
  norm_num [f, PiLp.single_apply] at hc

end LatticeProb
