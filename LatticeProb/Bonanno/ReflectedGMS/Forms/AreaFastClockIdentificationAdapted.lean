/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module ReflectedGMS.Forms.AreaFastClockIdentificationAdapted at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.ReflectedGMS.Process.AreaClockContinuity
import LatticeProb.Bonanno.ReflectedGMS.Forms.VertexPotentialSupermartingale
import LatticeProb.Bonanno.ReflectedGMS.Forms.ProcessOccupationLaplace
import Mathlib.Probability.Martingale.Basic
import Mathlib.MeasureTheory.Integral.Prod

/-!
# An adapted version of the weighted occupation clock, and of the area clock

Step (b) of the bracket atom `CoordinateLocallySquareIntegrable` needs the area clock
`A_u = ∫₀^u (a/m)(Y_s) ds` of the *fast* walk to be measurable **at the horizon `u`**, so
that the level sets `{A_u ≥ t}` — which are the events `{h(t) ≤ u}` of the inverse clock —
lie in the fast filtration and `h(t)` is a stopping time.

Separate time and sample measurability does not give that: `areaClock F m PF u` is built from
`PF.X s` for *all* `s`, through `Real.toNNReal`, and the literal integrand is not a
measurable function of `(ω, s)` for the uncompleted natural filtration at `u`.  The repair is
the one already used in `Forms/PastOccupationAdapted` for discounted vertex occupations: cap
the process at the horizon **before** taking its canonical dyadic version.  The capped
process has time sections measurable at `u` (`measurable_cappedProcess_naturalFiltration`),
the dyadic version of a process with measurable sections is jointly measurable
(`measurable_uncurry_dyadicLimit`), and `Measurable.lintegral_prod_right'` finishes.

On the right-regular paths of the reflected walk the capped dyadic version agrees with the
path itself at every time strictly below the horizon, so the adapted version agrees almost
surely with the literal occupation clock at that horizon.

Nothing here is about the area clock in particular: `q` is an arbitrary nonnegative vertex
density, specialised at the end to `areaClockDensity F m`.  No `Summable` hypothesis appears.
-/

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal

namespace ReflectedGMS.AreaFastClockAdapted

open ReflectedWalk ReflectedWalk.Theorem16
open ReflectedGMS.PositiveOccupationClock ReflectedGMS.AreaClockLocalFiniteness

universe u

variable {V : Type u} [MeasurableSpace V] [MeasurableSingletonClass V]
  [Countable V] [Nontrivial V]

/-! ## The capped process -/

/-- The process stopped at a deterministic horizon. -/
def cappedProcess (PF : ProcessFamily V) (t : ℝ≥0) : ℝ≥0 → PF.Ω → Option V :=
  fun s ω => PF.X (min s t) ω

theorem measurable_cappedProcess_naturalFiltration (PF : ProcessFamily V) (t s : ℝ≥0) :
    Measurable[PF.naturalFiltration t] (cappedProcess PF t s) := by
  change Measurable[pastSigma PF.X t] (PF.X (min s t))
  intro A hA
  apply measurableSet_pastSigma_iff.mpr
  refine ⟨{p | p ⟨min s t, show min s t ≤ t from min_le_right _ _⟩ ∈ A}, ?_, rfl⟩
  exact hA.preimage (measurable_pi_apply _)

theorem dyadicLimit_cappedProcess_eq_of_lt (PF : ProcessFamily V) (t s : ℝ≥0) (ω : PF.Ω)
    (hω : RightRegularAt PF.X ω) (hst : s < t) :
    dyadicLimit (cappedProcess PF t) s ω = PF.X s ω := by
  have hε : 0 < t - s := tsub_pos_of_lt hst
  have hev : ∀ᶠ k in Filter.atTop, dyadicCeil k s < t := by
    filter_upwards [eventually_dyadicCeil_mem_Ico s hε] with k hk
    simpa [add_tsub_cancel_of_le hst.le] using hk.2
  have hversion : dyadicLimit (cappedProcess PF t) s ω = dyadicLimit PF.X s ω := by
    refine option_eq_of_forall_some_iff fun x => ?_
    rw [dyadicLimit_eq_some_iff, dyadicLimit_eq_some_iff]
    constructor
    · intro hx
      filter_upwards [hx, hev] with k hk hkt
      simpa [cappedProcess, min_eq_left hkt.le] using hk
    · intro hx
      filter_upwards [hx, hev] with k hk hkt
      simpa [cappedProcess, min_eq_left hkt.le] using hk
  rw [hversion, dyadicLimit_eq_of_rightRegular hω]

/-! ## The adapted occupation clock -/

/-- A canonical horizon-`t` measurable version of the weighted occupation clock on
`[0, t]`. -/
noncomputable def occupationVersion (PF : ProcessFamily V) (q : V → ℝ≥0∞) (t : ℝ≥0)
    (ω : PF.Ω) : ℝ≥0∞ :=
  ∫⁻ r in Icc (0 : ℝ) (t : ℝ),
    (dyadicLimit (cappedProcess PF t) (Real.toNNReal r) ω).elim 0 q

/-- **The adapted version is measurable in the uncompleted natural filtration at its
horizon.** -/
theorem measurable_occupationVersion (PF : ProcessFamily V) (q : V → ℝ≥0∞) (t : ℝ≥0) :
    Measurable[PF.naturalFiltration t] (occupationVersion PF q t) := by
  let H : PF.Ω → ℝ → ℝ≥0∞ := fun ω r ↦
    (Icc (0 : ℝ) (t : ℝ)).indicator
      (fun r ↦ (dyadicLimit (cappedProcess PF t) (Real.toNNReal r) ω).elim 0 q) r
  have hcap : ∀ s, Measurable[PF.naturalFiltration t] (cappedProcess PF t s) :=
    measurable_cappedProcess_naturalFiltration PF t
  have hjoint : @Measurable (PF.Ω × ℝ) ℝ≥0∞
      (MeasurableSpace.prod (PF.naturalFiltration t) Real.measurableSpace)
      inferInstance (Function.uncurry H) := by
    dsimp only [H]
    exact ((measurable_of_countable (fun p : Option V ↦ p.elim 0 q)).comp
      (measurable_swap_toNNReal (mΩ := PF.naturalFiltration t)
        (measurable_uncurry_dyadicLimit (mΩ := PF.naturalFiltration t) hcap))).indicator
          (measurable_snd measurableSet_Icc)
  letI : MeasurableSpace PF.Ω := PF.naturalFiltration t
  have hjoint' : Measurable (Function.uncurry H) := hjoint
  change Measurable fun ω ↦ ∫⁻ r in Icc (0 : ℝ) (t : ℝ),
    (dyadicLimit (cappedProcess PF t) (Real.toNNReal r) ω).elim 0 q
  simpa only [H, Function.uncurry_apply_pair,
    lintegral_indicator measurableSet_Icc] using
      hjoint'.lintegral_prod_right' (ν := (volume : Measure ℝ))

/-- **The adapted version agrees almost surely with the literal occupation clock.** -/
theorem occupationVersion_ae_eq {G : ConductanceGraph V} {w : V → ℝ}
    {hmin : G.EnergyMinimizer} {PF : ProcessFamily V}
    (h : IsReflectedWalk G w hmin PF) (q : V → ℝ≥0∞) (z : V) (t : ℝ≥0) :
    ∀ᵐ ω ∂PF.P z, occupationVersion PF q t ω = weightedOccupationClock q PF.X t ω := by
  filter_upwards [ae_rightRegularAt (h z).2.2.1 (h z).2.2.2.1] with ω hω
  have hne : ∀ᵐ r ∂(volume.restrict (Icc (0 : ℝ) (t : ℝ))), r ≠ (t : ℝ) := by
    refine ae_restrict_of_ae ?_
    filter_upwards [compl_mem_ae_iff.2 (measure_singleton (t : ℝ))] with r hr
    exact fun hh => hr (Set.mem_singleton_iff.2 hh)
  change (∫⁻ r in Icc (0 : ℝ) (t : ℝ),
      (dyadicLimit (cappedProcess PF t) (Real.toNNReal r) ω).elim 0 q)
    = ∫⁻ r in Icc (0 : ℝ) (t : ℝ), (PF.X (Real.toNNReal r) ω).elim 0 q
  refine lintegral_congr_ae ?_
  filter_upwards [self_mem_ae_restrict measurableSet_Icc, hne] with r hrI hrne
  have hrt : Real.toNNReal r < t := by
    rw [← NNReal.coe_lt_coe, Real.coe_toNNReal r hrI.1]
    exact lt_of_le_of_ne hrI.2 hrne
  rw [dyadicLimit_cappedProcess_eq_of_lt PF t (Real.toNNReal r) ω hω hrt]

/-! ## The area clock -/

/-- The horizon-`t` measurable version of the area clock. -/
noncomputable def areaClockVersion (F : IndexedCells V) (m : V → ℝ) (PF : ProcessFamily V)
    (t : ℝ≥0) (ω : PF.Ω) : ℝ≥0∞ :=
  occupationVersion PF (areaClockDensity F m) t ω

theorem measurable_areaClockVersion (F : IndexedCells V) (m : V → ℝ)
    (PF : ProcessFamily V) (t : ℝ≥0) :
    Measurable[PF.naturalFiltration t] (areaClockVersion F m PF t) :=
  measurable_occupationVersion PF (areaClockDensity F m) t

/-- **The area clock has a version measurable at its own horizon.** -/
theorem areaClockVersion_ae_eq {G : ConductanceGraph V} {w : V → ℝ}
    {hmin : G.EnergyMinimizer} {PF : ProcessFamily V}
    (h : IsReflectedWalk G w hmin PF) (F : IndexedCells V) (m : V → ℝ) (z : V) (t : ℝ≥0) :
    ∀ᵐ ω ∂PF.P z, areaClockVersion F m PF t ω = areaClock F m PF t ω :=
  occupationVersion_ae_eq h (areaClockDensity F m) z t

end ReflectedGMS.AreaFastClockAdapted
