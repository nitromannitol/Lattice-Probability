import LatticeProb.Prob.Cadlag.HalfLine.Paths
import LatticeProb.Prob.JumpChain.Path
import LatticeProb.Prob.JumpChain.Position

/-!
# Continuous and jump-chain paths on the half-line

Continuous paths embed without changing their evaluations. Positive nonexplosive jump
histories give half-line càdlàg paths after any state map, with measurable evaluations
whenever the state map is measurable.
-/

namespace LatticeProb.Cadlag.HalfLine

open Set Filter
open scoped Topology

variable {S E : Type*} [TopologicalSpace E]

/-- Continuous half-line paths have their value as a left limit at every positive time. -/
theorem isCadlag_of_continuous {x : Time → E} (hx : Continuous x) : IsCadlag x :=
  ⟨fun _ => hx.continuousAt.continuousWithinAt,
    fun t _ => ⟨x t, hx.continuousAt.mono_left nhdsWithin_le_nhds⟩⟩

namespace D

/-- Regard a continuous half-line path as a càdlàg path with the same values. -/
def ofContinuous (x : C(Time, E)) : D E :=
  ⟨x, isCadlag_of_continuous x.continuous⟩

/-- The continuous-path inclusion preserves every evaluation. -/
@[simp] theorem ofContinuous_apply (x : C(Time, E)) (t : Time) :
    (ofContinuous x).1 t = x t := rfl

/-- The continuous-path inclusion is injective. -/
theorem ofContinuous_injective : Function.Injective (ofContinuous (E := E)) := by
  intro x y h
  apply ContinuousMap.ext
  intro t
  exact congrFun (congrArg Subtype.val h) t

/-- The existing constant half-line path, exposed in the path namespace. -/
abbrev const (a : E) : D E := HalfLine.const a

/-- A constant half-line path takes its defining value at every time. -/
@[simp] theorem const_apply (a : E) (t : Time) : (const a).1 t = a := rfl

/-- Including a continuous constant path gives the constant càdlàg path. -/
@[simp] theorem ofContinuous_const (a : E) :
    ofContinuous (ContinuousMap.const Time a) = const a := rfl

end D

/-- Every regular jump history is càdlàg after an arbitrary map of its states. -/
theorem isCadlag_position (h : JumpChain.RegularHistory S) (ι : S → E) :
    IsCadlag (fun t => ι (h.position t)) := by
  letI : TopologicalSpace S := ⊥
  letI : DiscreteTopology S := discreteTopology_bot S
  have hι : Continuous ι := continuous_of_discreteTopology
  constructor
  · intro t
    exact hι.continuousAt.comp_continuousWithinAt
      (h.continuousWithinAt_position_right t)
  · intro t _
    obtain ⟨z, hz⟩ := h.exists_leftLimit_position t
    exact ⟨ι z, (hι.tendsto z).comp hz⟩

end LatticeProb.Cadlag.HalfLine

namespace LatticeProb.JumpChain.RegularHistory

open Cadlag.HalfLine

variable {S E : Type*} [TopologicalSpace E]

/-- A regular jump history as a half-line càdlàg path after the given state map. -/
noncomputable def halfLinePath (ι : S → E) (h : RegularHistory S) : D E :=
  ⟨fun t => ι (h.position t), Cadlag.HalfLine.isCadlag_position h ι⟩

/-- The half-line path evaluates to the embedded position, including at clock rings. -/
@[simp] theorem halfLinePath_apply (ι : S → E) (h : RegularHistory S) (t : Time) :
    (halfLinePath ι h).1 t = ι (h.position t) := rfl

/-- Every half-line evaluation is measurable when the state map is measurable. -/
theorem measurable_halfLinePath_eval [MeasurableSpace S] [MeasurableSpace E]
    (ι : S → E) (hι : Measurable ι) (t : Time) :
    Measurable (fun h : RegularHistory S => (halfLinePath ι h).1 t) :=
  hι.comp (measurable_position t)

end LatticeProb.JumpChain.RegularHistory
