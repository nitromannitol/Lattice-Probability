/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module ReflectedGMS.Limit.OriginRootedTransportObstruction at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.ReflectedGMS.Temporal.TwoSidedRegenerationFlowGrid
import LatticeProb.Bonanno.ReflectedGMS.Temporal.ParabolicTemporalTransport
import LatticeProb.Bonanno.ReflectedGMS.Temporal.RegenerationKernel
import LatticeProb.Bonanno.ReflectedGMS.Spatial.ActualSpatialDensityBridge
import LatticeProb.Bonanno.ReflectedGMS.Corrector.MarkedBallEnergyGeometry

/-!
# The degree `-2` temporal transport forces the re-rooting flow to keep the origin in the
# walker's cell (a necessary condition for `hsys.transport` at an origin-rooted law)

The carrier-generic bracket-LLN weld (`Limit/DirectionalBracketLLNGates`) asks for
`hsys : ScaledRootChainSystem (ν ⊗ₘ κ) gridMeasure θ S blkFam sel` at the ORIGIN-rooted annealed law
`ν ⊗ₘ κ`: the environment keeps its absolute origin, and the gate `PathOriginRootedFibre` roots the
fibre at the origin cell `rootAt (decode e) 0`.  On the càdlàg carrier the flow is
`TwoSidedRegenerationFlow.reRootFlow`, which translates the environment by the displacement
`P t - P 0` of the position path.

This module proves, for EVERY law `Q` on `FlowSpace`:

* `ae_rootedAt_reRootFlow_of_transport`: if `Q ⊗ σ` satisfies the transport field
  `ParabolicTemporalTransport (Q.prod σ) gridFlow gridScaleFlow` and `Q`-a.s. the walker's time-`0`
  cell is the origin cell (`RootedAt`), then `Q`-a.s., for Lebesgue-a.e. `t` in the window
  `(0, |root cell|)`, the flowed configuration is again rooted.  The proof applies the transport
  identity to ONE explicit kernel (`exitKernel`: "rooted at the source time, not rooted at the
  target time, target within one root-cell area of the source"), which is measurable,
  time-shift covariant and of parabolic degree `-2`; its incoming side vanishes because the
  configuration is rooted at time `0`.
* `rootedAt_reRootFlow_iff`: the flowed configuration is rooted iff the displacement lies in the
  interior of the walker's CURRENT cell (`rootAt (decode e) (displacement ω t) = some (Y t)`).
* `ae_displacement_mem_currentCell_of_transport`: the combination.
* `rootAt_repDifference_of_coupled`: on the coupled set of a representative field `rep`
  (`TwoSidedRegenerationFlow.Coupled rep`), at a vertex time with current label `n` and root
  label `m`, the necessary condition reads `rootAt (decode e) (rep e n - rep e m) = some n`:
  the vector from the root cell's representative to the current cell's representative must
  land in the interior of the current cell.

## Consequence (argued, not checked)

For a translation-covariant representative (`RepTranslationCovariant`: the cell centroid, the
lexicographic minimum) this is the LATTICE condition `z(C) - z(R) ∈ int C` for every cell `C`
the walker visits from the root `R` during its first root-area of time — i.e. the origin's offset
inside `R` must be a valid offset inside every visited `C`.  It holds for the shifted unit-square
tiling (all cells are translates by the representative differences) and fails with positive
probability for every law whose neighbouring cells are not translates of the root cell along the
representative difference (the walker leaves the root cell at an exponential time and holds at
each neighbour for a positive time).  So `hsys.transport` at `ν ⊗ₘ κ` with `θΩ = reRootFlow` and
a position path coupled to a covariant representative is FALSE for non-lattice environment laws.
The manuscript avoids this by its cell-rooted encoding (tex:1350: "we forget the absolute spatial
origin and retain the distinguished current cell"), under which the transport field is stated
for functionals that do not see the origin.

Nothing here constructs a kernel, certifies `p:lem:timeMTP`, or either main theorem.
-/

set_option autoImplicit false

open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology

namespace ReflectedGMS.OriginRootedTransportObstruction

open Code EnvironmentLaws RootDensities
open ReflectedGMS.TrajectoryCoding ReflectedGMS.TwoSidedRegenerationFlow
open ReflectedGMS.TwoSidedRegenerationFlowGrid ReflectedGMS.ParabolicTransport
open ReflectedGMS.TemporalMassTransport ReflectedGMS.ScaledConditionalTemporalAveraging
open ReflectedGMS.ActualMarkedBlockTransport ReflectedGMS.MarkedSimilarityActionLaws
open ReflectedGMS.CanonicalSimilarity ReflectedGMS.DyadicApproximation

/-! ### 1. Rootedness of a configuration -/

/-- **The configuration is rooted**: the walker's time-`0` label is the origin cell of the
environment (the cell whose interior contains `0`, off the boundary mask). -/
def RootedAt (ω : FlowSpace) : Prop :=
  ∃ v : Vertex ω.1.val, rootAt (decode ω.1) 0 = some v ∧ ω.2.1.toFun 0 = ((v.val : ℕ) : ℕ∞)

theorem rootedAt_iff (ω : FlowSpace) :
    RootedAt ω ↔ (0 : Plane) ∉ boundaryMask (decode ω.1) ∧
      ω.2.1.toFun 0 = ((TwoSidedRegenerationCoding.rootLabel ω.1 : ℕ) : ℕ∞) := by
  constructor
  · rintro ⟨v, hv, hY⟩
    refine ⟨fun hm => ?_, ?_⟩
    · rw [rootAt_eq_none_of_mem_boundaryMask (decode ω.1) hm] at hv
      exact (Option.some_ne_none v).symm hv
    · rw [TwoSidedRegenerationCoding.rootLabel_of_some hv]
      exact hY
  · rintro ⟨hm, hY⟩
    obtain ⟨v, hv, -⟩ := rootAt_eq_some_of_not_mem_boundaryMask (decode ω.1)
      (decode_geometry ω.1) hm
    refine ⟨v, hv, ?_⟩
    rw [hY, TwoSidedRegenerationCoding.rootLabel_of_some hv]

theorem measurableSet_rootedAt : MeasurableSet {ω : FlowSpace | RootedAt ω} := by
  have hset : {ω : FlowSpace | RootedAt ω} =
      (Prod.fst ⁻¹' (MarkedRootedSpecificEnergyMeasurability.maskAt (fun e : Env => e))ᶜ) ∩
        {ω : FlowSpace | ω.2.1.toFun 0 =
          ((TwoSidedRegenerationCoding.rootLabel ω.1 : ℕ) : ℕ∞)} :=
    Set.ext fun ω => rootedAt_iff ω
  rw [hset]
  refine (measurable_fst ((MarkedRootedSpecificEnergyMeasurability.measurableSet_maskAt
    measurable_id).compl)).inter ?_
  have hY : Measurable fun ω : FlowSpace => ω.2.1.toFun 0 :=
    (CadlagPath.measurable_eval _).comp (measurable_fst.comp measurable_snd)
  have hR : Measurable fun ω : FlowSpace =>
      ((TwoSidedRegenerationCoding.rootLabel ω.1 : ℕ) : ℕ∞) :=
    (Measurable.of_discrete (f := (Nat.cast : ℕ → ℕ∞))).comp
      (RegenerationKernel.measurable_rootLabel.comp measurable_fst)
  exact measurableSet_eq_fun hY hR

/-- An injective label map lifts to an injective map of `ℕ∞`. -/
theorem liftLabel_injective {σ : ℕ → ℕ} (hσ : Function.Injective σ) :
    Function.Injective (liftLabel σ) := by
  intro x y hxy
  induction x using ENat.recTopCoe with
  | top =>
    induction y using ENat.recTopCoe with
    | top => rfl
    | coe m =>
      rw [liftLabel_top, liftLabel_natCast] at hxy
      exact absurd hxy.symm (ENat.natCast_ne_top _)
  | coe n =>
    induction y using ENat.recTopCoe with
    | top =>
      rw [liftLabel_top, liftLabel_natCast] at hxy
      exact absurd hxy (ENat.natCast_ne_top _)
    | coe m =>
      rw [liftLabel_natCast, liftLabel_natCast] at hxy
      have h : σ n = σ m := by exact_mod_cast hxy
      rw [hσ h]

/-- The image of an active label under the canonical label map is the canonical relabelling. -/
theorem simLabel_val {s : ℝ} {u : Plane} {hs : 0 < s} {e : Env} (v : Vertex e.val) :
    simLabel s u hs e v.val = (LabelBijectionProducer.similarityRelabel s u hs e v).val :=
  simLabel_of_isSome v.property

/-- **Rootedness after a similarity**: the similarity `z ↦ s • (z - u)` carries the cell containing
`u` in its interior to the cell containing the origin. -/
theorem rootedAt_similarity_iff {s : ℝ} {u : Plane} (hs : 0 < s) (e : Env) (y : ℕ∞) :
    (∃ v' : Vertex (similarityTargetEnv s u hs e).val,
        rootAt (decode (similarityTargetEnv s u hs e)) 0 = some v' ∧
          liftLabel (simLabel s u hs e) y = ((v'.val : ℕ) : ℕ∞)) ↔
      ∃ v : Vertex e.val, rootAt (decode e) u = some v ∧ y = ((v.val : ℕ) : ℕ∞) := by
  have h := LabelBijectionProducer.isSimilarityRelabel_similarityRelabel s u hs e
  have hroot := ActualSpatialDensityBridge.rootAt_similarity h u
  have h0 : positiveSimilarity s u u = 0 := by
    rw [positiveSimilarity_apply, sub_self, smul_zero]
  rw [h0] at hroot
  constructor
  · rintro ⟨v', hv', hy⟩
    rw [hroot] at hv'
    cases hru : rootAt (decode e) u with
    | none => rw [hru] at hv'; simp at hv'
    | some v =>
      rw [hru] at hv'
      have hvv : LabelBijectionProducer.similarityRelabel s u hs e v = v' := by
        simpa using hv'
      refine ⟨v, rfl, ?_⟩
      apply liftLabel_injective (simLabel_injective s u hs e)
      rw [hy, liftLabel_natCast, simLabel_val, hvv]
  · rintro ⟨v, hv, hy⟩
    refine ⟨LabelBijectionProducer.similarityRelabel s u hs e v, ?_, ?_⟩
    · rw [hroot, hv]
      rfl
    · rw [hy, liftLabel_natCast, simLabel_val]

/-! ### 2. The root-cell area as the covariant time scale -/

/-! ### 3. The test kernel -/

/-! ### 4. The necessary condition -/

end ReflectedGMS.OriginRootedTransportObstruction
