/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module ReflectedGMS.Temporal.CadlagRegenerationCoding at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.ReflectedGMS.Temporal.CadlagRegenerationAbstract
import LatticeProb.Bonanno.ReflectedGMS.Temporal.ActualExcursionErgodicIdentification

/-!
# The regenerative coding of a reflected-walk trajectory

`Temporal/ActualExcursionErgodicIdentification` proves one-step whole-cycle regeneration for the
actual reflected walk on its sample space: the post-cycle path `futureAt X τ_v` has law
`PF.law v` and is independent of the cycle `killedPathAt X τ_v`.  To turn that into ergodicity
of the *cycle shift* one needs the shift as a measurable self-map of a path space.  On the raw
product space `Trajectory V = ℝ≥0 → Option V` it is not: a random-time shift needs the joint
evaluation `(x, t) ↦ x t`, which the product σ-algebra over an uncountable index does not make
measurable, and the set of regular paths is not measurable there either.

This module builds the carrier on which it is.

## The carrier

`IsRegenPath v x` bundles, for one trajectory `x`, exactly the pointwise regularity that the
actual process has almost surely:

* `regular` — properties (ii) and (R) of `IsReflectedWalk` at `x` (`RightRegularAt`);
* `start` — `x 0 = v`;
* `leaves`, `recurs` — `x` is off `v`, and at `v`, at arbitrarily large times;
* `dense` — the vertex times are dense (no interval is spent at `∞`).

Every clause is **invariant under the shift at the first return** (`isRegenPath_shiftRaw`), so
`RegenPath v = {x // IsRegenPath v x}` carries the cycle shift `regenShift v` and the cycle map
`regenCycle v` (the trajectory killed at its first return, valued in the right-regular
trajectories `RegTraj V`).

## Measurability

With the subtype σ-algebra of the cylinder σ-algebra:

* `measurable_retTime` — the first return time is measurable (it is the countable-dense
  hitting time `denseHitAfter` at every regular point);
* `measurable_regenShift` — the cycle shift is measurable (it is the right-limit trajectory
  `dyadicLimitFuture` at every regular point);
* `measurable_regenCycle` — the cycle map is measurable;
* `measurable_regTraj_eval` — on right-regular trajectories the evaluation `(c, t) ↦ c t` is
  **jointly** measurable.  This is the statement the raw product space lacks.
* `cycleLength` — a measurable functional of a cycle that returns the first return time:
  `cycleLength_regenCycle` (this is where `dense` is used: the return time is the supremum of
  the vertex times of the killed path).

## Why this is not `TrajectoryCoding.CadlagPath`

`CadlagPath` also asks for **left limits** (`IsCadlag`), and it is `ℝ`-indexed.  Left limits
are not part of the definition `IsReflectedWalk` (which gives right regularity (ii)+(R)); they
*are* proved almost surely, for positive rates, in `Forms/VertexIndicatorLeftLimits`
(`reflected_vertexIndicators_ae_tendsto_nhdsLT`: every vertex indicator has a left limit at
every `t > 0`, i.e. the path has left limits in the one-point compactification).  The forward
regeneration needs only right regularity — joint measurability is a right-limit statement — so
the carrier here is the right-regular, `ℝ≥0`-indexed coding.  The **two-sided** coding
(backward half read in reversed time) will need those left limits.  Nothing here is
probabilistic.
-/

set_option autoImplicit false

open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology

namespace ReflectedGMS.CadlagRegeneration

open ReflectedWalk ReflectedWalk.Theorem16
open ReflectedGMS.TargetReturnRecursion
open ReflectedGMS.Temporal.ActualExcursionErgodicIdentification

universe u

variable {V : Type u}

/-! ### Path functionals on trajectory space -/

/-- The coordinate process of trajectory space. -/
def coord : ℝ≥0 → Trajectory V → Option V := fun t x => x t

/-- The first complete return time to `v`, read off the trajectory. -/
noncomputable def retTime (v : V) : Trajectory V → WithTop ℝ≥0 := firstReturnTime coord v

/-- The trajectory shifted by a deterministic time. -/
def shiftBy (T : ℝ≥0) (x : Trajectory V) : Trajectory V := fun s => x (s + T)

/-- **The regenerative coding from `v`**: the pointwise regularity of an actual path. -/
structure IsRegenPath (v : V) (x : Trajectory V) : Prop where
  /-- Properties (ii) and (R) of `IsReflectedWalk`, at this trajectory. -/
  regular : RightRegularAt (coord (V := V)) x
  /-- The trajectory starts at `v`. -/
  start : x 0 = some v
  /-- The trajectory is off `v` at arbitrarily large times. -/
  leaves : ∀ T : ℝ≥0, ∃ t, T ≤ t ∧ x t ≠ some v
  /-- The trajectory is at `v` at arbitrarily large times. -/
  recurs : ∀ T : ℝ≥0, ∃ t, T ≤ t ∧ x t = some v
  /-- The vertex times are dense. -/
  dense : ∀ a b : ℝ≥0, a < b → ∃ s, a < s ∧ s < b ∧ x s ≠ none

theorem retTime_eq (v : V) (x : Trajectory V) :
    retTime v x = hitAfter coord (some '' (({v} : Finset V) : Set V))
      (exitAfter coord (fun _ => ((0 : ℝ≥0) : WithTop ℝ≥0))) x := rfl

theorem exitAfter_zero_eq (x : Trajectory V) :
    exitAfter coord (fun _ => ((0 : ℝ≥0) : WithTop ℝ≥0)) x
      = MeasureTheory.hittingAfter coord {s | s ≠ x 0} 0 x := rfl

/-- The exit from the starting vertex is finite, positive and attained off `v`. -/
theorem exists_exit {v : V} {x : Trajectory V} (hx : IsRegenPath v x) :
    ∃ e : ℝ≥0, MeasureTheory.hittingAfter coord {s | s ≠ x 0} 0 x = e ∧ 0 < e ∧
      x e ≠ some v := by
  obtain ⟨t, -, ht⟩ := hx.leaves 0
  have hmemt : coord t x ∈ {s : Option V | s ≠ x 0} := by
    show x t ≠ x 0
    rw [hx.start]
    exact ht
  have hle : MeasureTheory.hittingAfter coord {s | s ≠ x 0} 0 x ≤ t :=
    MeasureTheory.hittingAfter_le_of_mem bot_le hmemt
  have hadm : AdmissibleTarget {s : Option V | s ≠ x 0} := by
    rw [hx.start]
    exact admissibleTarget_ne v
  cases he : MeasureTheory.hittingAfter coord {s | s ≠ x 0} 0 x with
  | top =>
    rw [he] at hle
    exact absurd hle (WithTop.not_top_le_coe t)
  | coe e =>
    have hmem : coord e x ∈ {s : Option V | s ≠ x 0} :=
      mem_of_hittingAfter_eq_of_rightRegular hx.regular hadm he
    refine ⟨e, rfl, ?_, ?_⟩
    · rcases (bot_le : (0 : ℝ≥0) ≤ e).lt_or_eq with h | h
      · exact h
      · exfalso
        rw [← h] at hmem
        exact hmem rfl
    · have hmem' : x e ≠ x 0 := hmem
      rw [hx.start] at hmem'
      exact hmem'

/-- **The first return is finite, positive, and at `v`.** -/
theorem retTime_spec {v : V} {x : Trajectory V} (hx : IsRegenPath v x) :
    ∃ r : ℝ≥0, retTime v x = r ∧ 0 < r ∧ x r = some v := by
  obtain ⟨e, he, he0, -⟩ := exists_exit hx
  have hret : retTime v x =
      MeasureTheory.hittingAfter coord (some '' (({v} : Finset V) : Set V)) e x := by
    rw [retTime_eq]
    exact hitAfter_coe (by rw [exitAfter_zero_eq, he])
  obtain ⟨t, het, ht⟩ := hx.recurs e
  have hmemt : coord t x ∈ some '' (({v} : Finset V) : Set V) :=
    ⟨v, by simp, ht.symm⟩
  have hle : MeasureTheory.hittingAfter coord (some '' (({v} : Finset V) : Set V)) e x ≤ t :=
    MeasureTheory.hittingAfter_le_of_mem het hmemt
  cases hr : MeasureTheory.hittingAfter coord (some '' (({v} : Finset V) : Set V)) e x with
  | top =>
    rw [hr] at hle
    exact absurd hle (WithTop.not_top_le_coe t)
  | coe r =>
    have hmem : coord r x ∈ some '' (({v} : Finset V) : Set V) :=
      mem_of_hittingAfter_eq_of_rightRegular hx.regular (admissibleTarget_image {v}) hr
    obtain ⟨w, hw, hxw⟩ := hmem
    have hwv : w = v := by simpa using hw
    have her : e ≤ r := WithTop.coe_le_coe.1 (hr ▸ MeasureTheory.le_hittingAfter x)
    refine ⟨r, hret.trans hr, lt_of_lt_of_le he0 her, ?_⟩
    have hxr : x r = some w := hxw.symm
    rw [hxr, hwv]

/-! ### Invariance of the carrier under the shift at the first return -/

theorem regular_shiftBy {x : Trajectory V} (hx : RightRegularAt (coord (V := V)) x)
    (T : ℝ≥0) : RightRegularAt (coord (V := V)) (shiftBy T x) := by
  refine ⟨fun t ht => ?_, fun t ht y => ?_⟩
  · obtain ⟨ε, hε, hεs⟩ := hx.1 (t + T) ht
    refine ⟨ε, hε, fun s hs => ?_⟩
    have hmem : s + T ∈ Set.Ico (t + T) (t + T + ε) := by
      refine ⟨add_le_add hs.1 le_rfl, ?_⟩
      calc s + T < t + ε + T := add_lt_add_of_lt_of_le hs.2 le_rfl
        _ = t + T + ε := add_right_comm t ε T
    exact hεs (s + T) hmem
  · obtain ⟨ε, hε, hεs⟩ := hx.2 (t + T) ht y
    refine ⟨ε, hε, fun s hs => ?_⟩
    have hmem : s + T ∈ Set.Ioo (t + T) (t + T + ε) := by
      refine ⟨add_lt_add_of_lt_of_le hs.1 le_rfl, ?_⟩
      calc s + T < t + ε + T := add_lt_add_of_lt_of_le hs.2 le_rfl
        _ = t + T + ε := add_right_comm t ε T
    exact hεs (s + T) hmem

/-! ### The coded spaces, the cycle shift and the cycle map -/

/-- The right-regular trajectories, where complete cycles live. -/
abbrev RegTraj (V : Type u) : Type u := {c : Trajectory V // RightRegularAt (coord (V := V)) c}

/-! ### Measurability on the coded spaces -/

section Measurability

theorem measurable_subtype_coord {p : Trajectory V → Prop} (t : ℝ≥0) :
    Measurable fun x : {x : Trajectory V // p x} => x.1 t :=
  (measurable_pi_apply t).comp measurable_subtype_coe

variable [Countable V]

/-- **Joint measurability of the evaluation on right-regular trajectories.** -/
theorem measurable_regTraj_eval : Measurable fun p : RegTraj V × ℝ≥0 => p.1.1 p.2 := by
  let Xp : ℝ≥0 → RegTraj V × ℝ≥0 → Option V := fun t p => p.1.1 t
  have hXp : ∀ t, Measurable (Xp t) := fun t => (measurable_subtype_coord t).comp measurable_fst
  let τp : RegTraj V × ℝ≥0 → WithTop ℝ≥0 := fun p => ((p.2 : ℝ≥0) : WithTop ℝ≥0)
  have hτp : Measurable τp := measurable_coe_nnreal_ennreal.comp measurable_snd
  have heq : (fun p : RegTraj V × ℝ≥0 => p.1.1 p.2) = fun p => dyadicLimitFuture Xp τp p 0 := by
    funext p
    have h := futureAt_eq_dyadicLimitFuture (X := Xp) (τ := τp) (ω := p) p.1.2.1 p.1.2.2
    rw [← h]
    show p.1.1 p.2 = p.1.1 (0 + p.2)
    rw [zero_add]
  rw [heq]
  exact (measurable_pi_apply 0).comp (measurable_dyadicLimitFuture hXp hτp)

end Measurability

end ReflectedGMS.CadlagRegeneration
