import Mathlib
import LatticeProb.Prob.CrossingTimesClock4

/-!
# Measurability of the inverse crossing clock on path space

On the space `C(ℝ≥0, E)` of continuous paths, the inverse crossing clock
`y ↦ clockInv (crossClock m y) t` and the clock-read path `y ↦ clockPath m y t` are measurable for
every fixed `t`, and the set of paths whose crossing clock is finite, strictly increasing,
unbounded and zero at zero is measurable (these are countable conditions, checked on the dense set
of rational times).

* `measurable_clockInv`, `measurable_clockPath`;
* `GoodClock c` for a clock `c : ℝ≥0 → ℝ≥0∞`, and `measurableSet_goodClock`.
-/

open MeasureTheory Filter Topology
open scoped NNReal ENNReal

noncomputable section

namespace LatticeProb

section Measurability

variable {E : Type*} [MetricSpace E] [SecondCountableTopology E] [MeasurableSpace E] [BorelSpace E]

/-- The inverse crossing clock at a fixed time is a measurable function of a continuous path. -/
theorem measurable_clockInv (m : ℝ≥0∞) (t : ℝ≥0) :
    Measurable fun y : C(ℝ≥0, E) => clockInv (crossClock m (fun s => y s)) t := by
  refine measurable_of_Iio fun a => ?_
  obtain ⟨D, hDc, hDd⟩ := TopologicalSpace.exists_countable_dense ℝ≥0
  have key : (fun y : C(ℝ≥0, E) => clockInv (crossClock m (fun s => y s)) t) ⁻¹' Set.Iio a =
      ⋃ d ∈ D, {y : C(ℝ≥0, E) | (d : ℝ≥0∞) < a ∧ (t : ℝ≥0∞) ≤ crossClock m (fun s => y s) d} := by
    ext y
    simp only [Set.mem_preimage, Set.mem_Iio, Set.mem_iUnion, Set.mem_ofPred_eq, exists_prop,
      clockInv, iInf_lt_iff]
    constructor
    · rintro ⟨u, hu, hua⟩
      obtain ⟨r, hur, hra⟩ := ENNReal.lt_iff_exists_nnreal_btwn.1 hua
      obtain ⟨d, hdD, hd⟩ := hDd.exists_mem_open isOpen_Ioo
        (Set.nonempty_Ioo.2 (ENNReal.coe_lt_coe.1 hur))
      exact ⟨d, hdD, (ENNReal.coe_lt_coe.2 hd.2).trans hra,
        hu.trans (crossClock_mono m _ hd.1.le)⟩
    · rintro ⟨d, -, hda, htd⟩
      exact ⟨d, htd, hda⟩
  rw [key]
  refine MeasurableSet.biUnion hDc fun d _ => ?_
  exact (MeasurableSet.const _).inter (measurableSet_le measurable_const (measurable_crossClock m d))

/-- The path read in the time scale of its inverse clock, at a fixed time, is a measurable function
of a continuous path. -/
theorem measurable_clockPath (m : ℝ≥0∞) (t : ℝ≥0) :
    Measurable fun y : C(ℝ≥0, E) => clockPath m (fun s => y s) t := by
  have h1 : Measurable fun y : C(ℝ≥0, E) =>
      (clockInv (crossClock m (fun s => y s)) t).toNNReal := (measurable_clockInv m t).ennreal_toNNReal
  have h2 : Measurable fun p : C(ℝ≥0, E) × ℝ≥0 => p.1 p.2 := continuous_eval.measurable
  exact h2.comp (measurable_id.prodMk h1)

end Measurability

/-- The nonnegative real `max r 0` of a rational number: a countable dense set of times. -/
def ratTime (r : ℚ) : ℝ≥0 := Real.toNNReal r

theorem denseRange_ratTime : DenseRange ratTime :=
  (Function.Surjective.denseRange fun x : ℝ≥0 => ⟨(x : ℝ), by simp⟩ : DenseRange Real.toNNReal).comp
    Rat.denseRange_cast continuous_real_toNNReal

/-- A *good clock*: finite, strictly increasing, unbounded and zero at zero, expressed through the
rational times (for a nondecreasing `c` this is equivalent to the same properties for all times). -/
def GoodClock (c : ℝ≥0 → ℝ≥0∞) : Prop :=
  c 0 = 0 ∧ (∀ r : ℚ, c (ratTime r) < ⊤) ∧
    (∀ r r' : ℚ, ratTime r < ratTime r' → c (ratTime r) < c (ratTime r')) ∧
    ∀ n : ℕ, ∃ r : ℚ, (n : ℝ≥0∞) ≤ c (ratTime r)

section Measurability2

variable {E : Type*} [MetricSpace E] [SecondCountableTopology E] [MeasurableSpace E] [BorelSpace E]

/-- The set of paths with a good crossing clock is measurable. -/
theorem measurableSet_goodClock (m : ℝ≥0∞) :
    MeasurableSet {y : C(ℝ≥0, E) | GoodClock (crossClock m (fun s => y s))} := by
  have h : {y : C(ℝ≥0, E) | GoodClock (crossClock m (fun s => y s))} =
      {y | crossClock m (fun s => y s) 0 = 0} ∩ (⋂ r : ℚ, {y | crossClock m (fun s => y s) (ratTime r) < ⊤}) ∩
      (⋂ p : ℚ × ℚ, {y | ratTime p.1 < ratTime p.2 →
        crossClock m (fun s => y s) (ratTime p.1) < crossClock m (fun s => y s) (ratTime p.2)}) ∩
      ⋂ n : ℕ, ⋃ r : ℚ, {y | (n : ℝ≥0∞) ≤ crossClock m (fun s => y s) (ratTime r)} := by
    ext y
    simp only [Set.mem_ofPred_eq, Set.mem_inter_iff, Set.mem_iInter, Set.mem_iUnion, GoodClock,
      Prod.forall, and_assoc]
  rw [h]
  refine (((measurableSet_eq_fun (measurable_crossClock m 0) measurable_const).inter
    (MeasurableSet.iInter fun r => measurableSet_lt (measurable_crossClock m _) measurable_const)).inter
    (MeasurableSet.iInter fun p => ?_)).inter (MeasurableSet.iInter fun n => MeasurableSet.iUnion fun r =>
      measurableSet_le measurable_const (measurable_crossClock m _))
  exact (MeasurableSet.const _).imp (measurableSet_lt (measurable_crossClock m _) (measurable_crossClock m _))

end Measurability2

end LatticeProb
