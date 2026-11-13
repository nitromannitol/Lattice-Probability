/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module ReflectedGMS.Forms.AreaFastClockIdentificationStopping at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.ReflectedGMS.Forms.AreaFastClockIdentificationAdapted
import LatticeProb.Bonanno.ReflectedGMS.Process.AreaTimeChangeJumpLaw
import LatticeProb.Bonanno.ReflectedGMS.Forms.StoppedFormAssociationExitTime
import LatticeProb.Bonanno.ReflectedGMS.Limit.StoppedAdaptedness

/-!
# The clock `h` of the time change: monotone, finite, and a family of stopping times

This supplies the three structural inputs `hh`, `hmono`, `hfin` of the clock change
`Forms/StoppedFormAssociationOptionalSampling.martingale_stoppedValue_clock_of_bound_of_ae`,
for the manuscript's clock `h = A⁻¹` of `p:thm:martingale` ("time change a local martingale by
the inverses of the increasing adapted clock").

`A` is the **area clock of the fast walk**,
`A_u(ω) = ∫₀^u (cellArea/m)(Y_s(ω)) ds` (`AreaClockLocalFiniteness.areaClock`), and `h` is its
canonical right-continuous inverse `inverseAreaClock` — a formula, needing no measurable
selection.  Two obstacles have to be removed.

* **`hmono` and `hfin` are `∀ ω` statements**, not almost-sure ones, while `inverseAreaClock`
  is monotone only where the clock actually reaches every level (an `sInf` over an empty set
  collapses to `0`).  So `h` is *patched off the good event* `ClockGood`, on which the clock
  is an order isomorphism (`AreaClockContinuity.ae_exists_homeomorph_areaClock`, whose
  conclusion `ClockGood` reproduces verbatim); there it is `e.symm`
  (`AreaTimeChangeJumpLaw.inverseAreaClock_eq_symm`), and off it `h t = t`.  Patching changes
  `h` only on a null set, which the consumer's conclusion does not see.
* **`hh` needs `{h t ≤ u}` in the fast filtration at `u`.**  On the good event
  `h(t) ≤ u ↔ t ≤ A_u` (`inverseAreaClock_le_iff_of_good`), and `A_u` is a.s. equal to the
  horizon-`u` measurable version `areaClockVersion` of
  `Forms/AreaFastClockIdentificationAdapted`.  Since the completed natural filtration contains
  every null event, the two differences are absorbed.

The **pathwise** half of the identification — that the area path is the fast path read at
`h`, i.e. `areaTimeChangedPath = exponentialAreaPath` — is a separate statement; its chain-time
core is `Forms/AreaFastClockIdentificationOccupation`.  Nothing here asserts it, and nothing
here uses summability of a speed measure.
-/

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal NNReal

namespace ReflectedGMS.AreaFastClockStopping

open ReflectedWalk ReflectedWalk.Theorem16
open ReflectedGMS.AreaClockLocalFiniteness ReflectedGMS.AreaClockContinuity
open ReflectedGMS.AreaTimeChangeJumpLaw
open ReflectedGMS.AreaFastClockAdapted

universe u

variable {V : Type u} [MeasurableSpace V] [MeasurableSingletonClass V]
  [Countable V] [Nontrivial V] [DecidableEq V]

/-! ## The good event -/

/-- **The good event of the area clock**, the conclusion of
`AreaClockContinuity.ae_exists_homeomorph_areaClock` verbatim: the clock is a strictly
increasing homeomorphism of `[0,∞)` fixing `0`. -/
def ClockGood (F : IndexedCells V) (m : V → ℝ) (PF : ProcessFamily V) (ω : PF.Ω) : Prop :=
  ∃ e : ℝ≥0 ≃ₜ ℝ≥0, StrictMono e ∧ e 0 = 0 ∧
    ∀ t : ℝ≥0, ((e t : ℝ≥0) : ℝ≥0∞) = areaClock F m PF t ω

variable {F : IndexedCells V} {m : V → ℝ} {PF : ProcessFamily V} {ω : PF.Ω}

/-- The order isomorphism carried by a good path. -/
noncomputable def goodOrderIso (hω : ClockGood F m PF ω) : ℝ≥0 ≃o ℝ≥0 :=
  StrictMono.orderIsoOfSurjective (⇑hω.choose) hω.choose_spec.1 hω.choose.surjective

theorem goodOrderIso_apply (hω : ClockGood F m PF ω) (t : ℝ≥0) :
    ((goodOrderIso hω t : ℝ≥0) : ℝ≥0∞) = areaClock F m PF t ω := by
  have hcoe : (goodOrderIso hω) t = hω.choose t := by
    simp only [goodOrderIso, StrictMono.coe_orderIsoOfSurjective]
  rw [hcoe]
  exact hω.choose_spec.2.2 t

theorem inverseAreaClock_eq_symm_of_good (hω : ClockGood F m PF ω) (t : ℝ≥0) :
    inverseAreaClock F m PF ω t = (goodOrderIso hω).symm t :=
  inverseAreaClock_eq_symm F m PF ω (goodOrderIso hω) (goodOrderIso_apply hω) t

theorem monotone_inverseAreaClock_of_good (hω : ClockGood F m PF ω) :
    Monotone (inverseAreaClock F m PF ω) := by
  intro s t hst
  rw [inverseAreaClock_eq_symm_of_good hω, inverseAreaClock_eq_symm_of_good hω]
  exact (goodOrderIso hω).symm.monotone hst

/-- **The level sets of the inverse clock are the level sets of the clock.**  This is the
identity that turns `h t` into a stopping time. -/
theorem inverseAreaClock_le_iff_of_good (hω : ClockGood F m PF ω) (t v : ℝ≥0) :
    inverseAreaClock F m PF ω t ≤ v ↔ (t : ℝ≥0∞) ≤ areaClock F m PF v ω := by
  rw [inverseAreaClock_eq_symm_of_good hω, OrderIso.symm_apply_le, ← goodOrderIso_apply hω v]
  exact ENNReal.coe_le_coe.symm

/-! ## The patched clock -/

open Classical in
/-- **The clock `h` of the time change**, patched off the good event so that it is monotone
and finite at *every* sample. -/
noncomputable def fastClock (F : IndexedCells V) (m : V → ℝ) (PF : ProcessFamily V)
    (t : ℝ≥0) (ω : PF.Ω) : WithTop ℝ≥0 :=
  if ClockGood F m PF ω then ((inverseAreaClock F m PF ω t : ℝ≥0) : WithTop ℝ≥0)
  else ((t : ℝ≥0) : WithTop ℝ≥0)

theorem fastClock_of_good (hω : ClockGood F m PF ω) (t : ℝ≥0) :
    fastClock F m PF t ω = ((inverseAreaClock F m PF ω t : ℝ≥0) : WithTop ℝ≥0) := by
  unfold fastClock
  exact if_pos hω

theorem fastClock_of_not_good (hω : ¬ ClockGood F m PF ω) (t : ℝ≥0) :
    fastClock F m PF t ω = ((t : ℝ≥0) : WithTop ℝ≥0) := by
  unfold fastClock
  exact if_neg hω

/-- **`hfin`**: the clock is finite at every time and every sample. -/
theorem fastClock_ne_top (F : IndexedCells V) (m : V → ℝ) (PF : ProcessFamily V)
    (t : ℝ≥0) (ω : PF.Ω) : fastClock F m PF t ω ≠ ⊤ := by
  unfold fastClock
  split_ifs <;> exact WithTop.coe_ne_top

/-- **`hmono`**: the clock is monotone at every sample. -/
theorem monotone_fastClock (F : IndexedCells V) (m : V → ℝ) (PF : ProcessFamily V)
    (ω : PF.Ω) : Monotone (fun t => fastClock F m PF t ω) := by
  intro s t hst
  show fastClock F m PF s ω ≤ fastClock F m PF t ω
  by_cases hg : ClockGood F m PF ω
  · rw [fastClock_of_good hg, fastClock_of_good hg]
    exact WithTop.coe_le_coe.2 (monotone_inverseAreaClock_of_good hg hst)
  · rw [fastClock_of_not_good hg, fastClock_of_not_good hg]
    exact WithTop.coe_le_coe.2 hst

/-! ## The stopping-time property -/

/-- A set differing from a measurable one by two null sets is measurable, for a σ-algebra
containing the null events. -/
theorem measurableSet_of_null_diff {Ω' : Type*} {m' : MeasurableSpace Ω'} {Q : Measure Ω'}
    {𝔉 : MeasurableSpace Ω'} (hnull : ∀ S : Set Ω', Q S = 0 → MeasurableSet[𝔉] S)
    {A B : Set Ω'} (hB : MeasurableSet[𝔉] B)
    (h1 : Q (A \ B) = 0) (h2 : Q (B \ A) = 0) : MeasurableSet[𝔉] A := by
  have hAeq : A = (B \ (B \ A)) ∪ (A \ B) := by
    ext x
    by_cases hxB : x ∈ B <;> by_cases hxA : x ∈ A <;> simp [hxA, hxB]
  rw [hAeq]
  exact (hB.diff (hnull _ h2)).union (hnull _ h1)

section Stopping

variable {G : ConductanceGraph V} {w : V → ℝ} {hmin : G.EnergyMinimizer}

/-- **`hh`: each `h t` is an exact stopping time of the completed natural filtration of the
fast path.**  Only the almost-sure good event and the horizonwise measurable version of the
area clock are used. -/
theorem isStoppingTime_fastClock (F : IndexedCells V) (m : V → ℝ) {PF : ProcessFamily V}
    (h : IsReflectedWalk G w hmin PF) (z : V)
    {enc : Option V → ℕ} (henc : Function.Injective enc)
    (X' : ℝ≥0 → PF.Ω → ℕ) (hX'e : ∀ t ω, X' t ω = enc (PF.X t ω))
    (hX' : ∀ t, Measurable (X' t))
    (hgood : ∀ᵐ ω ∂PF.P z, ClockGood F m PF ω) (t : ℝ≥0) :
    IsStoppingTime (ProcessFiltration.completedNaturalFiltration (PF.P z) X' hX')
      (fastClock F m PF t) := by
  classical
  intro v
  set N : Set PF.Ω := {x : PF.Ω | ¬ ClockGood F m PF x} ∪
    {x : PF.Ω | areaClockVersion F m PF v x ≠ areaClock F m PF v x} with hNdef
  have hN : PF.P z N = 0 :=
    measure_union_null (ae_iff.1 hgood) (ae_iff.1 (areaClockVersion_ae_eq h F m z v))
  set B : Set PF.Ω := {x : PF.Ω | (t : ℝ≥0∞) ≤ areaClockVersion F m PF v x} with hBdef
  have hBmeas : MeasurableSet[ProcessFiltration.completedNaturalFiltration
      (PF.P z) X' hX' v] B := by
    have hle := StoppedFormAssociation.rightCont_naturalFiltration_le_completedNaturalFiltration
      (PF.P z) henc PF.X PF.measurable_X X' hX'e hX' v
    refine hle B (Filtration.le_rightCont _ v B ?_)
    exact measurable_areaClockVersion F m PF v measurableSet_Ici
  set A : Set PF.Ω := {x : PF.Ω | fastClock F m PF t x ≤ ((v : ℝ≥0) : WithTop ℝ≥0)} with hAdef
  have hAB : A \ B ⊆ N := by
    rintro x ⟨hxA, hxB⟩
    by_cases hg : ClockGood F m PF x
    · refine Or.inr ?_
      intro hveq
      refine hxB ?_
      show (t : ℝ≥0∞) ≤ areaClockVersion F m PF v x
      rw [hveq]
      refine (inverseAreaClock_le_iff_of_good hg t v).1 ?_
      have hxA' : ((inverseAreaClock F m PF x t : ℝ≥0) : WithTop ℝ≥0) ≤
          ((v : ℝ≥0) : WithTop ℝ≥0) := by
        rw [← fastClock_of_good hg t]
        exact hxA
      exact WithTop.coe_le_coe.1 hxA'
    · exact Or.inl hg
  have hBA : B \ A ⊆ N := by
    rintro x ⟨hxB, hxA⟩
    by_cases hg : ClockGood F m PF x
    · refine Or.inr ?_
      intro hveq
      refine hxA ?_
      show fastClock F m PF t x ≤ ((v : ℝ≥0) : WithTop ℝ≥0)
      rw [fastClock_of_good hg]
      refine WithTop.coe_le_coe.2 ((inverseAreaClock_le_iff_of_good hg t v).2 ?_)
      rw [← hveq]
      exact hxB
    · exact Or.inl hg
  refine measurableSet_of_null_diff
    (Q := (PF.P z).completion) (fun S hS => ?_) hBmeas ?_ ?_
  · exact ProcessFiltration.measurableSet_completedNaturalFiltration_of_null
      (PF.P z) X' hX' v S hS
  · exact (Measure.completion_apply (PF.P z) _).trans (measure_mono_null hAB hN)
  · exact (Measure.completion_apply (PF.P z) _).trans (measure_mono_null hBA hN)

end Stopping

end ReflectedGMS.AreaFastClockStopping
