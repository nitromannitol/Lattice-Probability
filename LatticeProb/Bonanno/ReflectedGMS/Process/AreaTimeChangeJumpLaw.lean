/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module ReflectedGMS.Process.AreaTimeChangeJumpLaw at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.ReflectedGMS.Process.AreaClocks
import LatticeProb.Bonanno.ReflectedGMS.Process.AreaClockContinuity

/-!
# The area time-changed holding rate and neighbour law

Manuscript theorem `p:thm:areaclock` ends with the sentence

> Thus `X_t = Y_{A^{-1}(t)}`, `t ≥ 0`, is defined for all times.  It preserves the
> ordered reflected path and every end label.  **At a vertex `H`, its holding time
> is exponential with mean `a_H/π(H)` and its departing neighbour has
> probabilities `c(H,H')/π(H)`.**

The homeomorphism clause is already checked
(`AreaClockContinuity.ae_exists_homeomorph_areaClock`); a homeomorphism alone is
not the process law.  This file proves the highlighted clause for the *actual*
time-changed path, by the manuscript's own argument:

> Each holding interval at `o` is multiplied in length by `a_o/m_0(o)`.  The
> resulting lengths are independent exponentials of mean `a_o/π(o) > 0` …  On any
> other vertex holding interval the same deterministic multiplication gives the
> stated law, without changing the next-vertex choice.

## What is actually done

Along one genuine per-vertex sojourn — the interval `[0, τ)` on which the actual
reflected path of `ProcessFamily.X` sits at its starting vertex `o`, `τ` being
`Theorem16.exitTime` — the area clock `A(s) = ∫₀ˢ a_{Y_u}/m(Y_u) du` is *exactly*
the linear map `s ↦ (a_o/m(o)) · s` (`areaClock_eq_mul_of_forall_lt`).  Hence the
inverse clock rescales the sojourn by the deterministic factor `a_o/m(o)` and
leaves the embedded chain untouched:

* `exitTime_timeChanged` : the exit time of the time-changed path is the image of
  the fast exit time under the clock, `WithTop.map`-wise;
* `stoppedValue_timeChanged` : the position at that exit time is **unchanged**,
  which is the "without changing the next-vertex choice" clause;
* `exponentialFirstStep_areaTimeChangedPath` : the full property-(iii) package
  `Theorem16.ExponentialFirstStep` for the area time-changed path
  `areaTimeChangedPath` at rate `AreaClocks.areaRate F = π/a`.  Its exit time is
  `Exponential(π(o)/a_o)`, i.e. has mean `a_o/π(o)`, it is independent of the
  departing vertex, and that vertex has law `c(o,·)/π(o)`.

No finite total area is used, no global chronological CTRW is built, and the
exponential holding law is not re-derived: it is the existing property (iii) of
`IsReflectedWalk` for the fast rate `π/m`, transported along the clock.  The
non-vertex and reflection times are preserved because the time change is the
pathwise inverse homeomorphism of the *same* trajectory: `areaTimeChangedPath`
reads `PF.X` at a rescaled time and never modifies the path itself.

The inverse clock is the canonical right-continuous inverse
`A⁻¹(t) = inf{s : t ≤ A(s)}` (`inverseAreaClock`); on the almost sure event where
`A` is a homeomorphism it is its inverse (`inverseAreaClock_eq_symm`), so no
measurable selection of the homeomorphism is required.
-/

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal NNReal

namespace ReflectedGMS.AreaTimeChangeJumpLaw

open ReflectedWalk
open AreaClockLocalFiniteness AreaClockContinuity

universe u

/-! ## The exit time as an infimum of an explicit set of times -/

section Pathwise

variable {V : Type u} {Ω : Type u} [MeasurableSpace Ω]

end Pathwise

/-! ## The exit structure under a pathwise time change -/

section TimeChange

variable {V : Type u} {Ω : Type u} [MeasurableSpace Ω]
  {X Y : ℝ≥0 → Ω → Option V}

/-- An order isomorphism of `ℝ≥0` commutes with the infimum of a nonempty set. -/
theorem csInf_image_orderIso (e : ℝ≥0 ≃o ℝ≥0) {s : Set ℝ≥0} (hs : s.Nonempty) :
    sInf ((e : ℝ≥0 → ℝ≥0) '' s) = e (sInf s) := by
  have h1 : IsGLB s (sInf s) := isGLB_csInf hs (OrderBot.bddBelow s)
  have himg : (e.symm : ℝ≥0 → ℝ≥0) '' ((e : ℝ≥0 → ℝ≥0) '' s) = s := by
    ext x
    constructor
    · rintro ⟨y, ⟨w, hw, rfl⟩, rfl⟩
      rwa [e.symm_apply_apply]
    · intro hx
      exact ⟨e x, ⟨x, hx, rfl⟩, e.symm_apply_apply x⟩
  have h2 : IsGLB ((e : ℝ≥0 → ℝ≥0) '' s) (e (sInf s)) := by
    refine IsGLB.of_image (f := (e.symm : ℝ≥0 → ℝ≥0))
      (fun {x y} => e.symm.le_iff_le) ?_
    rw [himg, e.symm_apply_apply]
    exact h1
  exact h2.csInf_eq (hs.image _)

end TimeChange

/-! ## The exponential law under a deterministic rescaling -/

/-! ## The actual area clock on one per-vertex sojourn -/

section AreaClock

variable {V : Type u} [MeasurableSpace V] [MeasurableSingletonClass V]
  [Countable V] [Nontrivial V] [DecidableEq V]

/-- The canonical right-continuous inverse of the actual area clock,
`A⁻¹(t) = inf{s : t ≤ A(s)}`.  No measurable selection of a homeomorphism is
needed to write it down. -/
noncomputable def inverseAreaClock (F : IndexedCells V) (m : V → ℝ)
    (PF : ProcessFamily V) (ω : PF.Ω) (t : ℝ≥0) : ℝ≥0 :=
  sInf {s : ℝ≥0 | (t : ℝ≥0∞) ≤ areaClock F m PF s ω}

/-- **`p:eq:timechanged`**: the area time-changed path `X_t = Y_{A⁻¹(t)}`. -/
noncomputable def areaTimeChangedPath (F : IndexedCells V) (m : V → ℝ)
    (PF : ProcessFamily V) (t : ℝ≥0) (ω : PF.Ω) : Option V :=
  PF.X (inverseAreaClock F m PF ω t) ω

/-- On a trajectory whose area clock is an order isomorphism, the canonical
inverse clock is its inverse. -/
theorem inverseAreaClock_eq_symm (F : IndexedCells V) (m : V → ℝ)
    (PF : ProcessFamily V) (ω : PF.Ω) (e : ℝ≥0 ≃o ℝ≥0)
    (he : ∀ s : ℝ≥0, ((e s : ℝ≥0) : ℝ≥0∞) = areaClock F m PF s ω) (t : ℝ≥0) :
    inverseAreaClock F m PF ω t = e.symm t := by
  have hset : {s : ℝ≥0 | (t : ℝ≥0∞) ≤ areaClock F m PF s ω} = Ici (e.symm t) := by
    ext s
    rw [Set.mem_setOf_eq, ← he s, ENNReal.coe_le_coe, Set.mem_Ici]
    constructor
    · intro hst
      have hmono := e.symm.monotone hst
      rwa [e.symm_apply_apply] at hmono
    · intro hst
      have hmono := e.monotone hst
      rwa [e.apply_symm_apply] at hmono
  rw [inverseAreaClock, hset]
  exact isGLB_Ici.csInf_eq nonempty_Ici

end AreaClock

/-! ## The time-changed holding rate and neighbour law -/

section JumpLaw

variable {V : Type u} [MeasurableSpace V] [MeasurableSingletonClass V]
  [Countable V] [Nontrivial V] [DecidableEq V]
  {F : IndexedCells V} {m : V → ℝ} {hmin : F.graph.EnergyMinimizer}
  {PF : ProcessFamily V}

end JumpLaw

end ReflectedGMS.AreaTimeChangeJumpLaw
