/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module ReflectedGMS.Limit.CellRootedEncodingRepair at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.ReflectedGMS.Limit.FlowCodingFrontier

/-!
# The cell-rooted encoding removes the origin-rooted transport obstruction (core check)

`Limit/OriginRootedTransportObstruction.ae_rootedAt_reRootFlow_of_transport` shows that the
degree `-2` transport field at an ORIGIN-rooted law forces the re-rooting flow to keep the origin
in the walker's current cell for a.e. early time; at the bridge kernel and a translation-covariant
representative this is a lattice condition, false at non-lattice laws.

The manuscript (tex:1350, `p:lem:timeMTP`) states the temporal transport for the CELL-rooted
encoding: "we forget the absolute spatial origin and retain the distinguished current cell".  This
module checks the pointwise core of that repair (repair R2):

* `InteriorOffMask z`: a representative field whose values are interior points of their cells off
  the boundary mask.  Such points exist in every cell of every environment
  (`exists_interiorOffMask_point`), so the predicate is satisfiable by a (non-measurable) choice;
  the measurable, similarity-covariant witness is the incenter packet.
* `cellRoot ω := rootMap (fun _ => 0) ω`: the cell-rooted encoding of a configuration — the frame
  in which the walker's time-`0` position sits at the origin.  It intertwines the re-rooting flow
  with the PLAIN time shift (`reRootFlow_cellRoot`) and commutes with the scaling
  (`reScale_cellRoot`), and it is measurable.
* `rootedAt_reFrame_iff`: rootedness after a frame change reads `rootAt` at the new origin.
* **`rootedAt_reRootFlow_cellRoot_of_coupled`** (the statement that makes the obstruction
  disappear): at the cell-rooted encoding of a configuration coupled to an interior-off-mask
  representative, the flowed configuration is rooted at EVERY rational vertex time — the necessary
  condition of the obstruction theorem holds identically, not merely a.e., and for every
  environment law.  `displacement_mem_currentCell_cellRoot` is the geometric form.
* `ae_rootedAt_reRootFlow_cellRoot_flowKernel` / `ae_rootedAt_reRootFlow_cellRootedLaw`: the
  same at the bridge kernel `κF` and at the pushed-forward cell-rooted law
  `(ν ⊗ₘ κF).map cellRoot`, for an interior-off-mask `CellField`.

Nothing here constructs the covariant representative, certifies the transport field at the
cell-rooted law, `p:lem:timeMTP`, or either main theorem.
-/

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology

namespace ReflectedGMS.CellRootedEncodingRepair

open Code EnvironmentLaws EnvironmentFields RootDensities
open ReflectedGMS.EnvironmentWalkDataProducer ReflectedGMS.TwoSidedRegenerationCoding
open ReflectedGMS.TrajectoryCoding ReflectedGMS.TwoSidedRegenerationFlow
open ReflectedGMS.ActualMarkedBlockTransport ReflectedGMS.MarkedSimilarityActionLaws
open ReflectedGMS.CanonicalSimilarity
open ReflectedGMS.OriginRootedTransportObstruction ReflectedGMS.FlowCodingKernel
open ReflectedGMS.FlowCodingFrontier

/-! ### 1. Interior representatives off the boundary mask -/

/-- **An interior representative off the boundary mask**: at every active label the value is a
point of the cell that lies on no cell's frontier (hence in the cell's interior, and it is the
unique interior root of that point). -/
def InteriorOffMask (z : Env → ℕ → Plane) : Prop :=
  ∀ (e : Env) (n : ℕ) (hn : (e.val.1 n).isSome),
    z e n ∉ boundaryMask (decode e) ∧ z e n ∈ ((decode e).cell ⟨n, hn⟩ : Set Plane)

/-- A point of a cell off the mask is an interior root of that cell. -/
theorem rootAt_eq_some_of_offMask (e : Env) {n : ℕ} (hn : (e.val.1 n).isSome) {x : Plane}
    (hm : x ∉ boundaryMask (decode e)) (hc : x ∈ ((decode e).cell ⟨n, hn⟩ : Set Plane)) :
    rootAt (decode e) x = some ⟨n, hn⟩ := by
  rw [rootAt_eq_some_iff (decode e) (decode_geometry e)]
  refine ⟨hm, ?_⟩
  have hclosed : IsClosed ((decode e).cell ⟨n, hn⟩ : Set Plane) :=
    ((decode e).cell ⟨n, hn⟩).isCompact.isClosed
  -- the mask is the frontier union together with the uncovered set, so membership in the frontier
  -- part must be injected on the left
  have hnf : x ∉ frontier ((decode e).cell ⟨n, hn⟩ : Set Plane) := fun h =>
    hm (Set.mem_union_left _ (Set.mem_iUnion.2 ⟨⟨n, hn⟩, h⟩))
  rw [frontier, hclosed.closure_eq] at hnf
  show x ∈ interior ((decode e).cell ⟨n, hn⟩ : Set Plane)
  exact Classical.byContradiction fun hnot => hnf ⟨hc, hnot⟩

/-- The root at an interior-off-mask representative is its own label. -/
theorem rootAt_of_interiorOffMask {z : Env → ℕ → Plane} (hz : InteriorOffMask z) (e : Env)
    (n : ℕ) (hn : (e.val.1 n).isSome) :
    rootAt (decode e) (z e n) = some ⟨n, hn⟩ :=
  rootAt_eq_some_of_offMask e hn (hz e n hn).1 (hz e n hn).2

/-! ### 2. Rootedness after a frame change -/

/-! ### 3. The cell-rooted encoding of a configuration -/

/-- **The cell-rooted encoding**: the frame in which the walker's time-`0` position is the origin
(`rootMap` at the reference point `0`). -/
noncomputable def cellRoot : FlowSpace → FlowSpace := rootMap fun _ => 0

theorem cellRoot_eq_reFrame (ω : FlowSpace) : cellRoot ω = reFrame (ω.2.2.toFun 0) ω := by
  show reFrame (ω.2.2.toFun 0 - 0) ω = reFrame (ω.2.2.toFun 0) ω
  rw [sub_zero]

theorem measurable_cellRoot : Measurable cellRoot := by
  have h : Measurable (rootMap fun _ : Env => (0 : Plane)) := measurable_rootMap measurable_const
  exact h

/-- **The re-rooting flow on cell-rooted configurations is the plain time shift**, re-encoded:
`θΩ t ∘ cellRoot = cellRoot ∘ plainShift t`. -/
theorem reRootFlow_cellRoot (t : ℝ) (ω : FlowSpace) :
    reRootFlow t (cellRoot ω) = cellRoot (plainShift t ω) :=
  reRootFlow_rootMap _ t ω

/-- **The cell-rooted encoding commutes with the parabolic scaling.** -/
theorem reScale_cellRoot {C : ℝ} (hC : 0 < C) (ω : FlowSpace) :
    reScale C (cellRoot ω) = cellRoot (reScale C ω) := by
  show reScale C (rootMap (fun _ => 0) ω) = rootMap (fun _ => 0) (reScale C ω)
  exact reScale_rootMap (fun C hC e => (smul_zero C).symm) hC ω

/-! ### 4. The obstruction disappears at the cell-rooted encoding -/

/-! ### 5. At the bridge kernel and at the cell-rooted law -/

variable {z : CellField} {G : Set Env} {hG : MeasurableSet G}
  {hwalk : ∀ e ∈ G, EnvironmentAreaClockAdmissible e} {hext : ExtensionGate z G}

end ReflectedGMS.CellRootedEncodingRepair
