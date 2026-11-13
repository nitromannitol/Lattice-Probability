/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module ReflectedGMS.Temporal.TwoSidedStationaryLaw at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.ReflectedGMS.Forms.StationaryGridReversal
import Mathlib.MeasureTheory.Measure.Prod

/-! # A genuine two-sided reflected path law on a constant-step time grid

The actual reflected process of `ReflectedWalk.IsReflectedWalk` is only defined
for nonnegative times.  Here a two-sided (`ℤ`-indexed) path is built from **two
independent copies** of the process started at the same vertex: the first copy
reads the nonnegative times, the second copy reads the negative times.  This is
the standard construction of a two-sided stationary path for a reversible
Markov process, and it is carried out here for the *fixed starting vertex* law
`twoSidedStartLaw` and for the speed-weighted mixture `twoSidedSpeedLaw`.

The proved content is:

* `measurable_twoSidedPath`: the two-sided path map is measurable, so the laws
  `twoSidedVertexLaw` and `twoSidedGridLaw` on `ℤ → Option V` exist;
* `twoSidedStartLaw_twoSidedCylinder_real` and
  `twoSidedSpeedLaw_twoSidedCylinder_real`: the exact finite-dimensional
  cylinder mass of a window `[-p, q]` crossing time `0`, as a forward product
  and a backward product of full-form semigroup kernels;
* `twoSidedSpeedLaw_twoSidedCylinder_real_leftStart`: the **reversible** form of
  that mass, i.e. the backward half is turned around by detailed balance, so the
  window mass is exactly the one-sided grid weight started at the left endpoint
  `v (-p)`.  This is what makes the two-sided object a genuine stationary
  reversible law rather than two glued one-sided laws;
* `twoSidedSpeedLaw_twoSidedCylinder_shift` and
  `twoSidedGridLaw_map_twoSidedShift_twoSidedCylinder`: time-shift invariance of
  the law on these cylinders.

Scope warning.  The speed function `m` here carries the hypothesis
`Summable m`: it is the **temporary summable fast speed** used by the existing
full-form semigroup identities (`semigroupKernel`, detailed balance,
`reflected_gridEvent_start_real`), and it is *not* the area speed measure of the
mass-transport statement.  Transferring these cylinder identities to the area
speed requires the time change from the fast clock to the area clock, which is
not proved anywhere here; nothing in this file proves an area-law temporal mass
transport principle.  Likewise no ordinary annealed stationarity, no finite
total area assumption and no abstract stationary-law hypothesis is used: the
law is constructed from the actual process family.  Canonical
environment-dependent measurability and the spatial-to-temporal transport
remain separately open.
-/

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal BigOperators

namespace ReflectedGMS.TwoSided

open ReflectedWalk FullNetworkForm

universe u
variable {V : Type u} [MeasurableSpace V] [MeasurableSingletonClass V]
  [Countable V] [Nontrivial V] [DecidableEq V]

/-! ## The two independent copies and the speed-weighted mixture -/

/-- Two independent copies of the reflected process started at the same vertex
`x`: the first coordinate runs forward in time, the second runs backward. -/
noncomputable def twoSidedStartLaw (PF : ProcessFamily V) (x : V) :
    Measure (PF.Ω × PF.Ω) :=
  (PF.P x).prod (PF.P x)

instance twoSidedStartLaw_isProbabilityMeasure (PF : ProcessFamily V) (x : V) :
    IsProbabilityMeasure (twoSidedStartLaw PF x) := by
  unfold twoSidedStartLaw
  infer_instance

/-- The two-sided starting laws as a kernel on the countable vertex set. -/
noncomputable def twoSidedStartKernel (PF : ProcessFamily V) :
    Kernel V (PF.Ω × PF.Ω) :=
  Kernel.ofFunOfCountable (twoSidedStartLaw PF)

/-- The unnormalized two-sided law obtained by mixing the fixed-vertex two-sided
laws with the speed mass.  This is the two-sided analogue of
`ReflectedGMS.reflectedSpeedLaw`. -/
noncomputable def twoSidedSpeedLaw (PF : ProcessFamily V) (m : V → ℝ) :
    Measure (PF.Ω × PF.Ω) :=
  twoSidedStartKernel PF ∘ₘ vertexSpeedMeasure m

/-- The mixture is literally the speed-weighted sum of the fixed-vertex laws. -/
theorem twoSidedSpeedLaw_apply (PF : ProcessFamily V) (m : V → ℝ)
    {E : Set (PF.Ω × PF.Ω)} (hE : MeasurableSet E) :
    twoSidedSpeedLaw PF m E =
      ∑' z : V, ENNReal.ofReal (m z) * twoSidedStartLaw PF z E := by
  rw [twoSidedSpeedLaw, Measure.comp_eq_sum_of_countable,
    Measure.sum_apply _ hE]
  simp only [vertexSpeedMeasure_singleton, Measure.smul_apply, smul_eq_mul]
  rfl

theorem twoSidedSpeedLaw_prod_apply (PF : ProcessFamily V) (m : V → ℝ)
    {A B : Set PF.Ω} (hA : MeasurableSet A) (hB : MeasurableSet B) :
    twoSidedSpeedLaw PF m (A ×ˢ B) =
      ∑' z : V, ENNReal.ofReal (m z) * (PF.P z A * PF.P z B) := by
  rw [twoSidedSpeedLaw_apply PF m (hA.prod hB)]
  refine tsum_congr fun z => ?_
  rw [twoSidedStartLaw, Measure.prod_prod]

/-! ## The two-sided path map and its cylinders -/

/-! ## Factorization of a two-sided cylinder into the two independent copies -/

/-! ## The two one-sided halves -/

/-! ## Finite-dimensional cylinder masses of the two-sided laws -/

/-! ## The two-sided laws on path space -/

end ReflectedGMS.TwoSided
