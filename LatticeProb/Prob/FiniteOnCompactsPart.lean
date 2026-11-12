import Mathlib.MeasureTheory.Measure.GiryMonad
import Mathlib.MeasureTheory.Measure.Typeclasses.Finite
import Mathlib.Topology.Compactness.SigmaCompact

/-!
# The finite-on-compacts part of a measure, as a measurable map

On a weakly locally compact, σ-compact Hausdorff space `E`, fix the compact exhaustion `K = CompactExhaustion.choice E`.
For a measure `m` on `E`, its *finite-on-compacts part* is `m` itself if `m (K n) < ∞` for every `n`, and `0` otherwise.

* `isFiniteMeasureOnCompacts_finiteOnCompactsPart`: it is always finite on compact sets (every compact set lies in
  some `K n`);
* `finiteOnCompactsPart_eq_self`: it equals `m` when `m` is finite on compact sets (for instance a Radon measure);
* `measurable_finiteOnCompactsPart`: it is a measurable map on the space of measures (Giry σ-algebra).

So a measurable family of measures that are almost surely Radon agrees almost surely with a measurable family of
measures that are finite on compacts everywhere. This is the form in which measurability results stated for families
of measures finite on compacts apply to random Radon measures.
-/

open MeasureTheory Set

namespace LatticeProb

variable {E : Type*} [TopologicalSpace E] [MeasurableSpace E] [WeaklyLocallyCompactSpace E]
  [SigmaCompactSpace E]

open scoped Classical in
/-- The finite-on-compacts part of a measure: the measure itself if it is finite on every set of the compact
exhaustion `CompactExhaustion.choice E`, and `0` otherwise. -/
noncomputable def finiteOnCompactsPart (m : Measure E) : Measure E :=
  if ∀ n, m (CompactExhaustion.choice E n) < ⊤ then m else 0

/-- The finite-on-compacts part of a measure is finite on compact sets. -/
instance isFiniteMeasureOnCompacts_finiteOnCompactsPart (m : Measure E) :
    IsFiniteMeasureOnCompacts (finiteOnCompactsPart m) := by
  unfold finiteOnCompactsPart
  split_ifs with h
  · refine ⟨fun K hK => ?_⟩
    obtain ⟨n, hn⟩ := (CompactExhaustion.choice E).exists_superset_of_isCompact hK
    exact (measure_mono hn).trans_lt (h n)
  · infer_instance

/-- A measure that is finite on compact sets is its own finite-on-compacts part. -/
theorem finiteOnCompactsPart_eq_self (m : Measure E) [IsFiniteMeasureOnCompacts m] :
    finiteOnCompactsPart m = m := by
  have h : ∀ n, m (CompactExhaustion.choice E n) < ⊤ :=
    fun n => ((CompactExhaustion.choice E).isCompact n).measure_lt_top
  unfold finiteOnCompactsPart
  simp only [h, implies_true, ↓reduceIte]

/-- The finite-on-compacts part is a measurable map on the space of measures. -/
theorem measurable_finiteOnCompactsPart [OpensMeasurableSpace E] [T2Space E] :
    Measurable (finiteOnCompactsPart : Measure E → Measure E) := by
  have hS : MeasurableSet {m : Measure E | ∀ n, m (CompactExhaustion.choice E n) < ⊤} := by
    rw [ofPred_forall]
    exact MeasurableSet.iInter fun n => measurableSet_lt
      (Measure.measurable_coe ((CompactExhaustion.choice E).isCompact n).isClosed.measurableSet)
      measurable_const
  classical
  unfold finiteOnCompactsPart
  exact Measurable.ite hS measurable_id measurable_const

/-- The finite-on-compacts part of a measurable family of measures is a measurable family. -/
theorem measurable_finiteOnCompactsPart_comp [OpensMeasurableSpace E] [T2Space E] {X : Type*}
    [MeasurableSpace X] {μ : X → Measure E} (hμ : Measurable μ) :
    Measurable fun x => LatticeProb.finiteOnCompactsPart (μ x) :=
  measurable_finiteOnCompactsPart.comp hμ

end LatticeProb
