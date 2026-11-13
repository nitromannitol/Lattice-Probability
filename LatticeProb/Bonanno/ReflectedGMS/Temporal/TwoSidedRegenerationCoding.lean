/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module ReflectedGMS.Temporal.TwoSidedRegenerationCoding at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.ReflectedGMS.Recurrence.EnvironmentWalkDataProducer
import LatticeProb.Bonanno.ReflectedWalk.TransitionUniqueness
import Mathlib.MeasureTheory.Measure.Prod

/-!
# The two-sided coding and the fixed-environment two-sided laws (`p:lem:regeninvariant`, data)

The consumer of the regeneration lemma
(`Limit/BracketLLNDisintegratedWeld.ae_forall_bracket_limit_of_regenerativeInvariance_disintegrated`,
through `Temporal/RegenerativeInvarianceReduction.regenerativeInvariance_compProd_of_fiberwise`)
works on the annealed law `νenv ⊗ₘ κ` with `κ : Kernel Code.Env X` the fixed-environment
**two-sided** rooted laws `ℙ_H^{H_0}` of the manuscript (tex:1345), carried on ONE
environment-independent coding.  This module supplies the coding and the laws, environment by
environment; the kernel (measurable dependence on the environment) is
`Temporal/RegenerationKernel`.

## The coding

The manuscript's coding labels cells by their code slots and collapses every nonvertex state to
`∞` (tex:1345).  In this tree a trajectory with values in the vertices of the environment `e` is
`Trajectory (Vertex e.val)`; its label coding `labelTraj` sends `some v` to `some v.val` and
keeps `none`, so it lands in `Trajectory ℕ = ℝ≥0 → Option ℕ`, which does not depend on `e`.

`ℙ_H^v` has independent forward and time-reversed backward halves, each a copy of the process
from `v` (tex:1345).  The two-sided coding is therefore the pair
`TwoSidedCoding := Trajectory ℕ × Trajectory ℕ` — the forward half and the backward half read in
reversed time — with the product law of two copies of the forward label law
(`twoSidedSlotLaw`), exactly as `Temporal/TwoSidedStationaryLaw.twoSidedStartLaw` does on the
sample space.  Regularity subtypes of this coding (right-regularity for the random-time shifts,
left limits for the reversed half) are lifted later, by `RegenerationKernel.liftSubtype`.

## The laws

* `exhaustion e` — the standing exhaustion of the cell graph of `e`: one for which the area clock
  reaches every level-`0` index in finite time whenever such an exhaustion exists
  (`EnvironmentWalkDataProducer.EnvironmentAreaClockAdmissible`, the project's residual clock
  clause), an arbitrary one otherwise.  So `areaClockReaches_exhaustion` turns the project's
  `∃ D` clause into a statement at the canonical exhaustion at no cost.
* `areaFamily e` — the actual area-clock process family of `e` on that exhaustion
  (`Existence.processFamily`, rates `AreaClocks.areaRate`); its sample laws are the consumer's
  quenched laws `AreaClocks.areaSampleLaw (decode e) (exhaustion e) _ v` and its process is
  `AreaClocks.exponentialAreaPath` (`areaFamily_P`, `areaFamily_X`).  It is a reflected walk at
  every admissible environment (`isReflectedWalk_areaFamily`).
* `slotLaw G n e` — the forward label law of the walk from slot `n`, gated by an admissible set
  `G` of environments: the point mass at the cemetery path off `G` and at absent slots.  The gate
  is a parameter because the area family is a reflected walk only at admissible environments
  (a.e. under the annealed hypotheses, not everywhere), and the finite-dimensional recursion of
  `RegenerationKernel` needs the Markov property at every environment it is applied to.
* `twoSidedSlotLaw G n e` — the two-sided law from slot `n`; `rootedLaw G e` — at the root cell
  `rootLabel e` (the cell whose interior contains the origin, `RootDensities.rootAt`).

All are probability measures.  Nothing here is probabilistic beyond the product construction;
nothing here certifies `p:lem:regeninvariant`, `p:prop:timeergodic`, `p:lem:bracketlimit`,
`p:thm:areaclt` or either main theorem.
-/

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal

namespace ReflectedGMS.TwoSidedRegenerationCoding

open Code EnvironmentLaws AreaClocks RootDensities
open ReflectedWalk ReflectedWalk.Theorem16
open ReflectedGMS.EnvironmentWalkDataProducer

/-! ### The label coding of a trajectory -/

/-- The label coding of a trajectory: a vertex becomes its code slot, the cemetery `∞` stays
`none`.  The target `Trajectory ℕ` does not depend on the environment. -/
def labelTraj {r : RawCode} (x : Trajectory (Vertex r)) : Trajectory ℕ :=
  fun t => (x t).map Subtype.val

theorem labelTraj_apply {r : RawCode} (x : Trajectory (Vertex r)) (t : ℝ≥0) :
    labelTraj x t = (x t).map Subtype.val := rfl

theorem measurable_labelTraj {r : RawCode} : Measurable (labelTraj (r := r)) := by
  refine measurable_pi_iff.2 fun t => ?_
  have hmap : Measurable fun o : Option (Vertex r) => o.map Subtype.val :=
    fun _ _ => measurableSet_option _
  exact hmap.comp (measurable_pi_apply t)

/-- The cemetery path, the default value of the gated laws. -/
def cemetery : Trajectory ℕ := fun _ => none

/-! ### The canonical exhaustion and the area-clock family of an environment -/

/-- The standing exhaustion of the cell graph of `e`: one for which the area clock reaches every
level-`0` index in finite time when such an exhaustion exists
(`EnvironmentWalkDataProducer.EnvironmentAreaClockAdmissible`), and an arbitrary one otherwise
(`Existence.exists_exhaustion` at `decode_connected`). -/
noncomputable def exhaustion (e : Env) : (decode e).graph.Exhaustion := by
  classical
  letI := nontrivial_vertex e
  exact if h : ∃ D : (decode e).graph.Exhaustion,
      AreaClockReachesLevelZeroIndices e D (decode_connected e) then h.choose
    else Classical.choice (Existence.exists_exhaustion (decode_connected e))

/-- At an admissible environment the canonical exhaustion satisfies the clock clause. -/
theorem areaClockReaches_exhaustion (e : Env) (h : EnvironmentAreaClockAdmissible e) :
    letI := nontrivial_vertex e
    AreaClockReachesLevelZeroIndices e (exhaustion e) (decode_connected e) := by
  have := nontrivial_vertex e
  have h' : ∃ D : (decode e).graph.Exhaustion,
      AreaClockReachesLevelZeroIndices e D (decode_connected e) := h
  show AreaClockReachesLevelZeroIndices e (exhaustion e) (decode_connected e)
  unfold exhaustion
  rw [dite_eq_left h']
  exact h'.choose_spec

/-- The area-clock process family of `e` on the canonical exhaustion: the repository's actual
construction with the area rates `π(v)/a(v)`. -/
noncomputable def areaFamily (e : Env) : ProcessFamily (Vertex e.val) :=
  letI := nontrivial_vertex e
  Existence.processFamily (exhaustion e) (decode_connected e) (areaRate (decode e))

/-- **The area-clock family is a reflected walk at every admissible environment.** -/
theorem isReflectedWalk_areaFamily (e : Env) (h : EnvironmentAreaClockAdmissible e) :
    IsReflectedWalk (decode e).graph (areaRate (decode e)) (energyMinimizer e) (areaFamily e) := by
  have := nontrivial_vertex e
  exact isReflectedWalk_areaClock e (exhaustion e) (decode_connected e)
    (areaClockReaches_exhaustion e h)

/-! ### The forward label law from a slot -/

/-- The area-clock trajectory law of `e` started at slot `n`, read in the label coding and gated
by the admissible set `G`: the point mass at the cemetery path off `G` and at absent slots. -/
noncomputable def slotLaw (G : Set Env) (n : ℕ) (e : Env) : Measure (Trajectory ℕ) := by
  classical
  exact if h : e ∈ G ∧ (e.val.1 n).isSome then
    ((areaFamily e).law ⟨n, h.2⟩).map labelTraj
  else Measure.dirac cemetery

theorem slotLaw_of_mem {G : Set Env} {n : ℕ} {e : Env} (he : e ∈ G) (hn : (e.val.1 n).isSome) :
    slotLaw G n e = ((areaFamily e).law ⟨n, hn⟩).map labelTraj := by
  unfold slotLaw
  rw [dite_eq_left ⟨he, hn⟩]

theorem slotLaw_of_not {G : Set Env} {n : ℕ} {e : Env} (h : ¬ (e ∈ G ∧ (e.val.1 n).isSome)) :
    slotLaw G n e = Measure.dirac cemetery := by
  unfold slotLaw
  rw [dite_eq_right h]

instance slotLaw_isProbabilityMeasure (G : Set Env) (n : ℕ) (e : Env) :
    IsProbabilityMeasure (slotLaw G n e) := by
  unfold slotLaw
  split_ifs <;> infer_instance

/-- The forward label law is the image of the actual trajectory law, on the gate. -/
theorem slotLaw_apply_of_mem {G : Set Env} {n : ℕ} {e : Env} (he : e ∈ G)
    (hn : (e.val.1 n).isSome) {B : Set (Trajectory ℕ)} (hB : MeasurableSet B) :
    slotLaw G n e B = (areaFamily e).P ⟨n, hn⟩ ((areaFamily e).trajectory ⁻¹' (labelTraj ⁻¹' B)) := by
  rw [slotLaw_of_mem he hn, Measure.map_apply measurable_labelTraj hB, ProcessFamily.law,
    Measure.map_apply (areaFamily e).measurable_trajectory (measurable_labelTraj hB)]

/-! ### The two-sided coding and its laws -/

/-- **The two-sided coding**: the forward half and the backward half (read in reversed time),
both forward trajectories in the label coding. -/
abbrev TwoSidedCoding : Type := Trajectory ℕ × Trajectory ℕ

/-- The two-sided law from slot `n`: independent forward and backward copies of the forward
label law (tex:1345, "its forward and time-reversed backward halves are independent copies"). -/
noncomputable def twoSidedSlotLaw (G : Set Env) (n : ℕ) (e : Env) : Measure TwoSidedCoding :=
  (slotLaw G n e).prod (slotLaw G n e)

instance twoSidedSlotLaw_isProbabilityMeasure (G : Set Env) (n : ℕ) (e : Env) :
    IsProbabilityMeasure (twoSidedSlotLaw G n e) := by
  unfold twoSidedSlotLaw
  infer_instance

/-! ### The root -/

/-- The label of the root cell — the cell whose interior contains the origin
(`RootDensities.rootAt`); `0` on the boundary mask. -/
noncomputable def rootLabel (e : Env) : ℕ := (rootAt (decode e) 0).elim 0 Subtype.val

theorem rootLabel_of_some {e : Env} {v : Vertex e.val} (h : rootAt (decode e) 0 = some v) :
    rootLabel e = v.val := by
  rw [rootLabel, h]
  rfl

theorem rootLabel_of_none {e : Env} (h : rootAt (decode e) 0 = none) : rootLabel e = 0 := by
  rw [rootLabel, h]
  rfl

/-- **The rooted two-sided law of the environment**: `ℙ_H^{H_0}` in the label coding. -/
noncomputable def rootedLaw (G : Set Env) (e : Env) : Measure TwoSidedCoding :=
  twoSidedSlotLaw G (rootLabel e) e

instance rootedLaw_isProbabilityMeasure (G : Set Env) (e : Env) :
    IsProbabilityMeasure (rootedLaw G e) := by
  unfold rootedLaw
  infer_instance

end ReflectedGMS.TwoSidedRegenerationCoding
