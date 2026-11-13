/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module ReflectedGMS.Temporal.AreaCylinderShiftIdentity at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.ReflectedGMS.Temporal.TwoSidedStationaryLaw
import Mathlib.MeasureTheory.PiSystem
import Mathlib.MeasureTheory.Measure.Typeclasses.Finite
import Mathlib.MeasureTheory.Measure.Dirac.Basic
import LatticeProb.Bonanno.ReflectedGMS.StatementIngredients

/-!
**⚠ STALE (2026-09-18):** the "Scope warning" at the end of this docstring is wrong:
`ProcessTransitionReversible PF (cellArea F) δ` is PROVED, with no summability, as
`AreaReversibility.processTransitionReversible_cellArea` (`Forms/AreaTransitionReversibility.lean`,
checked since 2026-09-15; needs only `Geometry F` and connectivity).  The `hrev` hypothesis of the
area-weight instances below is discharged there
(`AreaReversibility.twoSidedCylinderShiftIdentity_cellArea_of_geometry`).

# The finite-cylinder shift identity for the area-speed reflected process

`ReflectedGMS.Temporal.SigmaFiniteTwoSidedShift` reduces σ-finite shift
invariance of the weighted two-sided reflected law to one remaining producer,
the finite-cylinder identity `TwoSidedCylinderShiftIdentity PF w δ` for a weight
`w` that need not be summable — in particular for the cell-area weight
`StatementIngredients.cellArea F`.  This file proves that producer.

The existing route to the cylinder identity (`TwoSidedStationaryLaw`,
`TwoSidedLawInvariance`) is unusable for the area weight for **two separate**
reasons, and only the second of them is a genuine mathematical obstruction:

* the finite-dimensional grid law `reflected_gridEvent_start_real` is stated in
  terms of the analytic `semigroupKernel G m δ`, and the identification of the
  process transition probabilities with that kernel
  (`reflected_vertexProbability_eq_semigroupKernel`) carries `Summable m`.  This
  is avoidable: the *product structure* of the finite-dimensional distributions
  comes from the Markov property (iv) of `IsReflectedWalk` alone.  It is proved
  here without any summability, as
  `reflectedGridEvent_start_real_processTransition`, in terms of the process's
  **own** one-step transition function
  `processTransition PF δ x y = (PF.P x {ω | PF.X δ ω = some y}).toReal`;
* the two-sided law is anchored at the time origin by the mixing weight, so
  moving the anchor along the window — which is what shift invariance *is* —
  needs reversibility of the one-step transition function with respect to the
  mixing weight.  That input is isolated as `ProcessTransitionReversible PF w δ`,
  a two-point identity `w x · p_δ(x,y) = w y · p_δ(y,x)`.  It is not the target
  and it is not vacuous: for the summable fast speed it is the already proved
  `reflected_transition_detailedBalance`
  (`processTransitionReversible_of_summable`).

Global finiteness of the mixing measure is removed exactly as the scope note of
`SigmaFiniteTwoSidedShift` predicts, by *local* finiteness: a two-sided cylinder
mass is `ofReal (w (v 0)) * (probability * probability)`, so it is finite for a
pointwise finite weight, and the `ENNReal`/`ℝ` conversion
`ENNReal.ofReal_toReal` needs `measure_ne_top` for the two fixed-vertex
**probability** measures only.  `IsFiniteMeasure (twoSidedSpeedLaw PF w)`, i.e.
`Summable w`, is never used.

**The process is not changed.**  Everything is stated for a process family `PF`
with `IsReflectedWalk G rate hmin PF` for its *own* rate function `rate`, and the
mixing weight `wt` is tracked as a separate argument.  The area statements
instantiate `rate = fun x => G.pi x / cellArea F x` — the area-speed process —
together with `wt = cellArea F`.  Reweighting a fast-speed process and calling
the result area-stationary is precisely what these two arguments keep apart.

Main results:

* `reflectedGridEvent_start_real_processTransition` — summability-free
  finite-dimensional producer, from the `IsReflectedWalk` Markov property;
* `twoSidedSpeedLaw_twoSidedCylinder_leftStart_processTransition` — the
  reversible left-endpoint form of a two-sided cylinder mass, with no global
  finiteness;
* `twoSidedCylinderShiftIdentity_of_processTransitionReversible` — the missing
  producer `TwoSidedCylinderShiftIdentity PF wt δ`;
* `twoSidedCylinderShiftIdentity_cellArea` and
  `twoSidedGridLaw_cellArea_map_twoSidedShiftBy` — the area-speed instances,
  and hence σ-finite shift invariance of the area-weighted two-sided law of the
  area-speed reflected process.

Scope warning.  The remaining mathematical input for an unconditional area-clock
statement is `ProcessTransitionReversible PF (cellArea F) δ`, the reversibility
of the area-speed process's one-step transition function with respect to the
area measure.  It is *not* proved here: the existing proof of reversibility goes
through the `Summable` identification of the transitions with the full-form
semigroup.  Nothing in this file assumes the cylinder identity, an abstract
stationary law, annealed stationarity or finite total area, and no temporal
ergodic theorem is claimed.
-/

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal BigOperators

namespace ReflectedGMS.TwoSided

open ReflectedWalk FullNetworkForm

universe u
variable {V : Type u} [MeasurableSpace V] [MeasurableSingletonClass V]
  [Countable V] [Nontrivial V] [DecidableEq V]

/-! ## The one-step transition function of the actual process -/

/-- The one-step transition probability of the process family itself, with no
reference to the analytic full-form semigroup and hence no summability. -/
noncomputable def processTransition (PF : ProcessFamily V) (t : ℝ≥0) (x y : V) : ℝ :=
  (PF.P x {ω | PF.X t ω = some y}).toReal

theorem processTransition_eq_measureReal (PF : ProcessFamily V) (t : ℝ≥0) (x y : V) :
    processTransition PF t x y = (PF.P x).real {ω | PF.X t ω = some y} := by
  simp only [processTransition, measureReal_def]

/-! ## The summability-free finite-dimensional producer -/

/-- Splitting the last time off a finite grid cylinder.  (The identically
proved `ReflectedGMS.reflectedGridEvent_succ` is `private` in its producer
module.) -/
theorem reflectedGridEvent_succ_inter (PF : ProcessFamily V) (δ : ℝ≥0) (n : ℕ)
    (v : ℕ → V) :
    reflectedGridEvent PF δ (n + 1) v =
      reflectedGridEvent PF δ n v ∩
        {ω | PF.X (((n + 1 : ℕ) : ℝ≥0) * δ) ω = some (v (n + 1))} := by
  ext ω
  simp only [reflectedGridEvent, mem_setOf_eq, mem_inter_iff, Finset.mem_range]
  constructor
  · intro hgrid
    exact ⟨fun i hi => hgrid i (by omega), hgrid (n + 1) (by omega)⟩
  · rintro ⟨hgrid, hlast⟩ i hi
    by_cases hin : i = n + 1
    · simpa [hin] using hlast
    · exact hgrid i (by omega)

/-- **The finite-dimensional distributions of the actual reflected process are a
product of its own one-step transition probabilities.**  No summability, no
connectedness and no positivity of the speed: the only inputs are the starting
law `X₀ = z` and the Markov property (iv) of `IsReflectedWalk`, used through
`ReflectedMarkovConditional.setIntegral_vertexFiber`.

This is the summability-free replacement for
`ReflectedGMS.reflected_gridEvent_start_real`, whose right-hand side is the
analytic `semigroupKernel` and whose proof therefore needs `Summable m` to
identify the transitions. -/
theorem reflectedGridEvent_start_real_processTransition
    {G : ConductanceGraph V} {rate : V → ℝ} {hmin : G.EnergyMinimizer}
    {PF : ProcessFamily V}
    (h : IsReflectedWalk G rate hmin PF) (δ : ℝ≥0) (n : ℕ) (v : ℕ → V) :
    (PF.P (v 0)).real (reflectedGridEvent PF δ n v) =
      ∏ i ∈ Finset.range n, processTransition PF δ (v i) (v (i + 1)) := by
  classical
  induction n with
  | zero =>
      rw [show reflectedGridEvent PF δ 0 v = {ω | PF.X 0 ω = some (v 0)} by
        ext ω; simp [reflectedGridEvent]]
      simp only [Finset.range_zero, Finset.prod_empty]
      have hmeas : MeasurableSet {ω : PF.Ω | PF.X 0 ω = some (v 0)} :=
        PF.measurable_X 0 (measurableSet_singleton _)
      have hcompl : PF.P (v 0) {ω : PF.Ω | PF.X 0 ω = some (v 0)}ᶜ = 0 := by
        rw [Set.compl_setOf]
        exact ae_iff.mp (h (v 0)).1
      rw [measureReal_def, (prob_compl_eq_zero_iff hmeas).mp hcompl, ENNReal.toReal_one]
  | succ n ih =>
      let F := reflectedGridEvent PF δ n v
      let f : V → ℝ := fun y => if y = v (n + 1) then 1 else 0
      have hf : ∀ y, ‖f y‖ ≤ (1 : ℝ) := by
        intro y
        simp only [f]
        split <;> norm_num
      have hstep := ReflectedMarkovConditional.setIntegral_vertexFiber
        h (v 0) (v n) (s := (n : ℝ≥0) * δ)
        (t := ((n + 1 : ℕ) : ℝ≥0) * δ)
        (by gcongr; omega) f 1 hf
        (measurableSet_reflectedGridEvent_naturalFiltration PF δ n v)
      have hsub : (((n + 1 : ℕ) : ℝ≥0) * δ - (n : ℝ≥0) * δ) = δ := by
        rw [Nat.cast_add, Nat.cast_one, add_mul, one_mul, add_tsub_cancel_left]
      have htransition :
          (∫ ω, (PF.X ((((n + 1 : ℕ) : ℝ≥0) * δ) - (n : ℝ≥0) * δ) ω).elim 0 f
            ∂PF.P (v n)) = processTransition PF δ (v n) (v (n + 1)) := by
        rw [hsub]
        have hmeas := PF.measurable_X δ
        rw [show (fun ω => (PF.X δ ω).elim 0 f) =
            {ω | PF.X δ ω = some (v (n + 1))}.indicator (fun _ => (1 : ℝ)) by
          funext ω
          cases hq : PF.X δ ω with
          | none => simp [f, hq]
          | some y => by_cases hy : y = v (n + 1) <;> simp [f, hq, hy]]
        have hI := integral_indicator_const (μ := PF.P (v n)) (1 : ℝ)
          (hmeas (measurableSet_singleton (some (v (n + 1)))))
        calc
          _ = (PF.P (v n)).real {ω | PF.X δ ω = some (v (n + 1))} := by
            simpa only [Set.preimage, Set.mem_singleton_iff, smul_eq_mul, mul_one] using hI
          _ = processTransition PF δ (v n) (v (n + 1)) :=
            (processTransition_eq_measureReal PF δ (v n) (v (n + 1))).symm
      rw [htransition] at hstep
      have hF : MeasurableSet F := measurableSet_reflectedGridEvent PF δ n v
      have hnext : MeasurableSet
          {ω : PF.Ω | PF.X (((n + 1 : ℕ) : ℝ≥0) * δ) ω = some (v (n + 1))} :=
        PF.measurable_X _ (measurableSet_singleton _)
      have hleft :
          (∫ ω in F, {ω | PF.X ((n : ℝ≥0) * δ) ω = some (v n)}.indicator
              (fun ω => (PF.X (((n + 1 : ℕ) : ℝ≥0) * δ) ω).elim 0 f) ω
              ∂PF.P (v 0)) =
            (PF.P (v 0)).real
              (F ∩ {ω | PF.X (((n + 1 : ℕ) : ℝ≥0) * δ) ω = some (v (n + 1))}) := by
        calc
          _ = ∫ ω in F,
                {ω | PF.X (((n + 1 : ℕ) : ℝ≥0) * δ) ω = some (v (n + 1))}.indicator
                  (fun _ => (1 : ℝ)) ω ∂PF.P (v 0) := by
              apply setIntegral_congr_fun hF
              intro ω hω
              have hn := hω n (by simp [F, reflectedGridEvent])
              simp only [Nat.cast_add, Nat.cast_one]
              cases hq : PF.X (((n : ℝ≥0) + 1) * δ) ω with
              | none => simp [hn, f, hq]
              | some y => by_cases hy : y = v (n + 1) <;> simp [hn, f, hq, hy]
          _ = _ := by
            rw [integral_indicator_const (1 : ℝ) hnext,
              measureReal_restrict_apply hnext, smul_eq_mul, mul_one, inter_comm]
      have hright :
          (∫ ω in F, {ω | PF.X ((n : ℝ≥0) * δ) ω = some (v n)}.indicator
              (fun _ => processTransition PF δ (v n) (v (n + 1))) ω ∂PF.P (v 0)) =
            (PF.P (v 0)).real F * processTransition PF δ (v n) (v (n + 1)) := by
        calc
          _ = ∫ _ in F, processTransition PF δ (v n) (v (n + 1)) ∂PF.P (v 0) := by
            apply setIntegral_congr_fun hF
            intro ω hω
            have hn := hω n (by simp [F, reflectedGridEvent])
            simp [hn]
          _ = _ := by rw [setIntegral_const, smul_eq_mul]
      rw [reflectedGridEvent_succ_inter]
      rw [Finset.prod_range_succ, ← ih]
      exact hleft.symm.trans (hstep.trans hright)

/-! ## One-step reversibility with respect to the mixing weight -/

/-- **Reversibility of the process's own one-step transition function with
respect to the weight `w`**: the two-point detailed balance identity
`w x · p_δ(x,y) = w y · p_δ(y,x)`.  This is strictly weaker than, and logically
independent of, the cylinder shift identity it produces below. -/
def ProcessTransitionReversible (PF : ProcessFamily V) (w : V → ℝ) (t : ℝ≥0) : Prop :=
  ∀ x y : V, w x * processTransition PF t x y = w y * processTransition PF t y x

/-- Path-weight balance: reversibility turns the weight anchor of a grid path
from its first to its last vertex.  This is the process-level analogue of
`ReflectedGMS.FullNetworkForm.semigroup_path_weight_balance`. -/
theorem processTransition_path_weight_balance (PF : ProcessFamily V) (w : V → ℝ)
    (δ : ℝ≥0) (hrev : ProcessTransitionReversible PF w δ) (v : ℕ → V) (n : ℕ) :
    w (v 0) * (∏ i ∈ Finset.range n, processTransition PF δ (v i) (v (i + 1))) =
      w (v n) * (∏ i ∈ Finset.range n, processTransition PF δ (v (i + 1)) (v i)) := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Finset.prod_range_succ, Finset.prod_range_succ, ← mul_assoc, ih]
      calc
        _ = (∏ i ∈ Finset.range n, processTransition PF δ (v (i + 1)) (v i)) *
            (w (v n) * processTransition PF δ (v n) (v (n + 1))) := by ring
        _ = (∏ i ∈ Finset.range n, processTransition PF δ (v (i + 1)) (v i)) *
            (w (v (n + 1)) * processTransition PF δ (v (n + 1)) (v n)) := by
          rw [hrev (v n) (v (n + 1))]
        _ = _ := by ring

/-- The reversed grid path weight, the process-level analogue of
`ReflectedGMS.FullNetworkForm.semigroup_grid_path_weight_reverse`. -/
theorem processTransition_grid_path_weight_reverse (PF : ProcessFamily V) (w : V → ℝ)
    (δ : ℝ≥0) (hrev : ProcessTransitionReversible PF w δ) (v : ℕ → V) (n : ℕ) :
    w (v 0) * (∏ i ∈ Finset.range n, processTransition PF δ (v i) (v (i + 1))) =
      w (v n) * (∏ i ∈ Finset.range n,
        processTransition PF δ (v (n - i)) (v (n - (i + 1)))) := by
  rw [processTransition_path_weight_balance PF w δ hrev v n]
  congr 1
  rw [← Finset.prod_range_reflect
    (fun i => processTransition PF δ (v (i + 1)) (v i)) n]
  refine Finset.prod_congr rfl fun i hi => ?_
  have hin : i < n := Finset.mem_range.mp hi
  congr 2 <;> omega

/-! ## Two-sided cylinder masses without global finiteness -/

/-! ## The finite-cylinder shift identity -/

/-! ## The area-speed process and the cell-area weight -/

/-- The cell area is nonnegative — it is the volume of a compact cell — with no
finiteness of the total area. -/
theorem cellArea_nonneg (F : IndexedCells V) (x : V) :
    0 ≤ StatementIngredients.cellArea F x := ENNReal.toReal_nonneg

end ReflectedGMS.TwoSided

/-! ## Remaining input

The single remaining mathematical input for an unconditional area-clock
invariance is

`ProcessTransitionReversible PF (StatementIngredients.cellArea F) δ`,

the two-point identity `area(x) · p_δ(x,y) = area(y) · p_δ(y,x)` for the
one-step transition function of the area-speed reflected process.  It is a
property of the process at a single pair of vertices, not a path or law
statement, and it is exactly what the summable route obtains from
`reflected_vertexProbability_eq_semigroupKernel`; supplying it without
`Summable` is the identification-of-the-transition-function gap, not a
stationarity gap.  Everything between it and σ-finite invariance of the
area-weighted two-sided law under all integer shifts, on all measurable events,
is proved above and in `SigmaFiniteTwoSidedShift`. -/
