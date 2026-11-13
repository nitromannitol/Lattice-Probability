/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module ReflectedGMS.Process.AreaClockSimilarity at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.ReflectedGMS.Process.ReflectedWalkDilation
import LatticeProb.Bonanno.ReflectedGMS.Limit.DirectionalBracketLLNGates
import LatticeProb.Bonanno.ReflectedGMS.Spatial.ActualSpatialDensityBridge
import LatticeProb.Bonanno.ReflectedGMS.Temporal.TwoSidedRegenerationCoding
import LatticeProb.Bonanno.ReflectedGMS.Temporal.TrajectoryCoding
import LatticeProb.Bonanno.ReflectedGMS.Temporal.AnnealedTemporalTransport
import Mathlib.Probability.Kernel.MeasurableLIntegral
import LatticeProb.Bonanno.ReflectedGMS.Process.AreaClockFastSpeedOccupation
import LatticeProb.Bonanno.ReflectedGMS.Spatial.GoodEnvironmentSet
import LatticeProb.Bonanno.ReflectedGMS.Temporal.AreaClockCodingShift

/-!
# Similarity covariance of the area-clock path law

Let `e, e'` be environments related by a physical similarity of ratio `C = s > 0`
(`EnvironmentLaws.IsSimilarityRelabel s u hs e e' relabel`: the cells of `e'` are the images of
those of `e`, the conductances are unchanged).  Then the area-clock path law of `e'` from the
image cell is the image of the area-clock path law of `e` under the parabolic dilation

  `γ ↦ (t ↦ relabel(γ_{t / C²}))`

(`areaFamily_law_similarity`).  This is the mathematics behind the field
`ActualConditionalPathIntegral.DilationCoding.law_φ` (item T1 of the area-clock reversibility
handoff), proved at the raw path level `Trajectory (Vertex e.val)`, independent of any càdlàg
coding carrier.

## Proof

1. **Rates.**  Conductances, hence `π`, are unchanged (`ReflectedWalkDilation.pi_equiv`), and
   cell areas scale by `C²` (`ActualSpatialDensityBridge.cellArea_relabel`), so the area rate
   `π/a` of `e'` at `relabel v` is `C⁻²` times that of `e` at `v` (`areaRate_similarity`).
2. **The dilated walk is a reflected walk for `e'`.**  By
   `ReflectedWalkDilation.isReflectedWalk_dilateFamily` the process `relabel(X_{t/C²})` of the
   area family of `e` is a reflected walk on the cell graph of `e'` with rate
   `areaRate e ∘ relabel⁻¹ / C²`, which is `areaRate e'` by step 1
   (`isReflectedWalk_dilate_areaFamily`).
3. **Uniqueness in law.**  The area family of `e'` is a reflected walk with the same rate
   (`TwoSidedRegenerationCoding.isReflectedWalk_areaFamily`), so the two trajectory laws agree
   (`DirectionalBracketLLNGates.identDistrib_of_isReflectedWalk`, Gwynne–Sung Theorem 1.6
   uniqueness half at any positive rate).

## Inputs

The only hypotheses are the project's residual clock clause at the two environments,
`EnvironmentAreaClockAdmissible e` and `EnvironmentAreaClockAdmissible e'`: without them the
area family is not known to be a reflected walk at all.  Each holds for `ν`-a.e. environment
under (MTP) + (FE) (`AreaClockAdmissibleDischarge.ae_environmentAreaClockAdmissible`); it is
the gate `G` of `RegenerationKernel`.  For the label-coded and two-sided laws of
`TwoSidedRegenerationCoding` the corresponding hypotheses are `e ∈ G`, `e' ∈ G`.

The geometric sufficient condition `AreaClockFastSpeedOccupation.EnvironmentAreaClockGeometry`
(which is what the a.e. discharge actually proves) is similarity invariant
(`environmentAreaClockGeometry_of_similarity`), so `areaFamily_law_similarity_of_geometry`
needs ONE hypothesis, at `e` only.

## The shape `law_φ` needs

* `law_φ_of_codedTwoSidedLaw`: the `law_φ` equation for ANY two coded two-sided laws
  (`AreaClockCodingShift.CodedTwoSidedLaw`, the clause of `AreaClockTimeMTPWeld.IsCodedAreaClockLaw`)
  of `e` and `e'`, given an injective measurable continuous alphabet map `φ` with
  `φ ∘ code_e = code_{e'} ∘ Option.map relabel`.  No coding map is assumed; the equality is
  checked on rational-time point cylinders (`AreaClockCodingShift.ptCyls`), which determine a
  law on `CadlagPath S` for countable `S` (`TrajectoryCoding.CadlagPath.eq_of_map_ratEval_eq`).
* `law_φ_of_twoSidedCoding`: the same for a kernel `pathLaw` that is the image of the gated
  two-sided law `twoSidedSlotLaw G` under a coding map `code e : TwoSidedCoding → CadlagPath S`
  intertwining the raw dilation with `CadlagPath.parabolicDilate` almost surely (`hequiv`);
  `hequiv` holds for any coding that reads the two halves pointwise in time, because the raw
  dilation acts on both halves by the same `t ↦ t / C²` and commutes with time reversal.
-/

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal

namespace ReflectedGMS.AreaClockSimilarity

universe w

open Code EnvironmentLaws AreaClocks
open ReflectedWalk ReflectedWalk.Theorem16
open ReflectedGMS.ReflectedWalkDilation ReflectedGMS.EnvironmentWalkDataProducer
open ReflectedGMS.TwoSidedRegenerationCoding ReflectedGMS.TrajectoryCoding

/-- The parabolic time factor `C²` of a similarity of ratio `C = s`. -/
noncomputable def parabolicFactor (s : ℝ) : ℝ≥0 := ⟨s ^ 2, sq_nonneg s⟩

@[simp] theorem coe_parabolicFactor (s : ℝ) : (parabolicFactor s : ℝ) = s ^ 2 := rfl

theorem parabolicFactor_pos {s : ℝ} (hs : 0 < s) : 0 < parabolicFactor s :=
  NNReal.coe_pos.1 (pow_pos hs 2)

variable {s : ℝ} {u : Plane} {hs : 0 < s} {e e' : Env}
  {relabel : Vertex e.val ≃ Vertex e'.val}

/-! ## 1. The area rate scales by `C⁻²` -/

/-- **The area rate of the image environment** is the area rate of `e` divided by `C²`. -/
theorem areaRate_similarity (h : IsSimilarityRelabel s u hs e e' relabel)
    (x' : Vertex e'.val) :
    areaRate (decode e') x' = areaRate (decode e) (relabel.symm x') / (parabolicFactor s : ℝ) := by
  conv_lhs => rw [← relabel.apply_symm_apply x']
  unfold areaRate
  rw [ActualSpatialDensityBridge.cellArea_relabel h, pi_equiv relabel h.2, coe_parabolicFactor,
    mul_comm, ← div_div]

/-! ## 2. The dilated area clock of `e` is a reflected walk for `e'` -/

/-- **The time-dilated, relabelled area clock of `e` is a reflected walk on the cell graph of
`e'` at the area rate of `e'`.** -/
theorem isReflectedWalk_dilate_areaFamily (h : IsSimilarityRelabel s u hs e e' relabel)
    (he : EnvironmentAreaClockAdmissible e) :
    IsReflectedWalk (decode e').graph (areaRate (decode e'))
      (relabelMinimizer (energyMinimizer e) relabel h.2)
      (dilateFamily (areaFamily e) relabel (parabolicFactor s)) := by
  haveI := nontrivial_vertex e
  have hw := isReflectedWalk_dilateFamily relabel h.2 (areaRate_pos e)
    (isReflectedWalk_areaFamily e he) (parabolicFactor_pos hs)
  have hrate : (fun x' => areaRate (decode e) (relabel.symm x') / (parabolicFactor s : ℝ))
      = areaRate (decode e') :=
    funext fun x' => (areaRate_similarity h x').symm
  rwa [hrate] at hw

/-! ## 3. Similarity covariance of the path law -/

/-- **Similarity covariance of the area-clock path law (raw path level).**  For a physical
similarity of ratio `C = s` between admissible environments, the path law of the area clock of
`e'` from `relabel v` is the image of the path law of the area clock of `e` from `v` under the
parabolic dilation `γ ↦ (t ↦ relabel(γ_{t / C²}))`. -/
theorem areaFamily_law_similarity (h : IsSimilarityRelabel s u hs e e' relabel)
    (he : EnvironmentAreaClockAdmissible e) (he' : EnvironmentAreaClockAdmissible e')
    (v : Vertex e.val) :
    (areaFamily e').law (relabel v)
      = ((areaFamily e).law v).map (dilateTraj relabel (parabolicFactor s)) := by
  haveI := nontrivial_vertex e'
  have hid := DirectionalBracketLLNGates.identDistrib_of_isReflectedWalk (decode_connected e')
    (areaRate_pos e') (isReflectedWalk_areaFamily e' he')
    (isReflectedWalk_dilate_areaFamily h he) (relabel v)
  have h1 : (dilateFamily (areaFamily e) relabel (parabolicFactor s)).law (relabel v)
      = (areaFamily e').law (relabel v) := hid.map_eq
  rw [← h1, law_dilateFamily, relabel.symm_apply_apply]

/-! ## 4. The label coding and the two-sided coding -/

/-- The label coding intertwines the vertex dilation with the label dilation, for any label map
`lab` extending the relabelling on active labels. -/
theorem labelTraj_dilateTraj (lab : ℕ → ℕ) (hlab : ∀ v : Vertex e.val, lab v.val = (relabel v).val)
    (a : ℝ≥0) (γ : Trajectory (Vertex e.val)) :
    labelTraj (dilateTraj relabel a γ) = dilateTraj lab a (labelTraj γ) := by
  funext t
  simp only [labelTraj_apply, dilateTraj_apply]
  cases γ (a⁻¹ * t) with
  | none => rfl
  | some x => simp [hlab x]

/-- **Similarity covariance of the gated forward label law.** -/
theorem slotLaw_similarity {G : Set Env} (hGadm : ∀ e ∈ G, EnvironmentAreaClockAdmissible e)
    (h : IsSimilarityRelabel s u hs e e' relabel) (he : e ∈ G) (he' : e' ∈ G)
    (lab : ℕ → ℕ) (hlab : ∀ v : Vertex e.val, lab v.val = (relabel v).val) (v : Vertex e.val) :
    slotLaw G (relabel v).val e'
      = (slotLaw G v.val e).map (dilateTraj lab (parabolicFactor s)) := by
  rw [slotLaw_of_mem he' (relabel v).property, slotLaw_of_mem he v.property]
  have h1 : (areaFamily e').law ⟨(relabel v).val, (relabel v).property⟩
      = (areaFamily e').law (relabel v) := rfl
  rw [h1, areaFamily_law_similarity h (hGadm e he) (hGadm e' he') v,
    Measure.map_map measurable_labelTraj (measurable_dilateTraj _ _),
    Measure.map_map (measurable_dilateTraj _ _) measurable_labelTraj]
  congr 1
  funext γ
  exact labelTraj_dilateTraj lab hlab _ γ

/-! ## 5. The `law_φ` field of `DilationCoding`, conditional on a coding map -/

/-! ## 6. The geometric admissibility clause is similarity invariant -/

/-! ## 7. `law_φ` for coded two-sided laws (the `IsCodedAreaClockLaw` shape) -/

section Coded

open ReflectedGMS.AreaClockCodingShift ReflectedGMS.AreaClockRealTimeShift ReflectedGMS.TwoSided

variable {S : Type*} [TopologicalSpace S] [MeasurableSpace S] [BorelSpace S]
  [TopologicalSpace.PseudoMetrizableSpace S] [MeasurableSingletonClass S]

variable {W : Type w} [MeasurableSpace W] [MeasurableSingletonClass W] [Countable W]
  [Nontrivial W] [DecidableEq W]

end Coded

end ReflectedGMS.AreaClockSimilarity
