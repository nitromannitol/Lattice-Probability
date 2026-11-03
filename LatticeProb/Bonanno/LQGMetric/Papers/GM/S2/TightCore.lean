/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.GM.S2.TightCore at commit 31e7483; only the module paths of local imports are changed. -/
import Mathlib.MeasureTheory.Measure.Prokhorov
import Mathlib.MeasureTheory.Measure.Portmanteau
import Mathlib.Topology.Semicontinuity.Basic
import Mathlib.Topology.CompactOpen

/-!
# GM S2.4, abstract core: uniform smallness on a compact set of laws (task P2-TIGHT)

GM (arXiv:1905.00383v3, `uniqueness-final.tex` l. 449–452) and DFGPS (arXiv:1904.08021,
`T:370–374`) assert without proof that Axiom V "implies the tightness of various functionals".
Decision D-A3 (`decisions/DEC-A.md` (c)) splits the claim into S2.4a–e. The common step of
S2.4a and S2.4b is the following abstract fact, proved here.

* `upperSemicontinuous_measure_closed`: for a closed set `F`, `μ ↦ μ F` is upper semicontinuous
  on probability measures (Portmanteau, mathlib
  `ProbabilityMeasure.limsup_measure_closed_le_of_tendsto` with the filter `𝓝 μ`).
* `exists_measure_lt_of_isCompact_closure`: if `S` has compact closure (Prokhorov) and `C n` is a
  decreasing sequence of closed sets with `μ (⋂ C n) = 0` for every `μ ∈ closure S`, then for
  every `ε > 0` some `C n` has `ν (C n) < ε` for all `ν ∈ S` (a Dini-type argument: the closed
  sets `{μ ∈ closure S | ε ≤ μ (C n)}` decrease and have empty intersection, so by Cantor's
  intersection theorem one of them is empty).
* `exists_mem_iInter_of_not_mapsTo`: in `C(X, Y)`, if `d` fails `MapsTo d (A n) (U n)` for every
  `n` (compact `A n` decreasing, open `U n` increasing), then some `x ∈ ⋂ A n` has
  `d x ∉ U n` for all `n` (Cantor again).

This replaces the subsequence/Portmanteau argument of D-A3 by its compactness form (same
ingredients: Prokhorov, Portmanteau, closure property of Axiom V). Own argument (no source
proves S2.4); DEVIATIONS entry DA5.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open MeasureTheory Filter Topology Set
open scoped ENNReal

namespace LQGMetric
namespace GM
namespace Tight

section Abstract

variable {E : Type*} [TopologicalSpace E] [MeasurableSpace E] [OpensMeasurableSpace E]
  [HasOuterApproxClosed E]

/-- Portmanteau: `μ ↦ μ F` is upper semicontinuous for closed `F`. -/
theorem upperSemicontinuous_measure_closed {F : Set E} (hF : IsClosed F) :
    UpperSemicontinuous fun μ : ProbabilityMeasure E => (μ : Measure E) F := by
  intro μ y hy
  have := ProbabilityMeasure.limsup_measure_closed_le_of_tendsto (L := 𝓝 μ)
    (μs := fun ν => ν) tendsto_id hF
  exact eventually_lt_of_limsup_lt (lt_of_le_of_lt this hy)

/-- Uniform smallness of a decreasing sequence of closed sets over a relatively compact set of
laws, when the intersection is null for every limit law. -/
theorem exists_measure_lt_of_isCompact_closure {S : Set (ProbabilityMeasure E)}
    (hS : IsCompact (closure S)) {C : ℕ → Set E} (hC : ∀ n, IsClosed (C n)) (hCa : Antitone C)
    (h0 : ∀ μ ∈ closure S, (μ : Measure E) (⋂ n, C n) = 0) {ε : ℝ≥0∞} (hε : 0 < ε) :
    ∃ n, ∀ μ ∈ S, (μ : Measure E) (C n) < ε := by
  by_contra hcon
  push Not at hcon
  let T : ℕ → Set (ProbabilityMeasure E) := fun n =>
    closure S ∩ (fun μ : ProbabilityMeasure E => (μ : Measure E) (C n)) ⁻¹' Ici ε
  have hTc : ∀ n, IsClosed (T n) := fun n =>
    isClosed_closure.inter ((upperSemicontinuous_measure_closed (hC n)).isClosed_preimage ε)
  obtain ⟨μ, hμ⟩ := IsCompact.nonempty_iInter_of_sequence_nonempty_isCompact_isClosed T
    (fun n => inter_subset_inter_right _ fun ν (hν : ε ≤ _) =>
      (show ε ≤ (ν : Measure E) (C n) from hν.trans (measure_mono (hCa n.le_succ))))
    (fun n => by
      obtain ⟨ν, hν, h⟩ := hcon n
      exact ⟨ν, subset_closure hν, h⟩)
    (hS.of_isClosed_subset (hTc 0) inter_subset_left) hTc
  rw [mem_iInter] at hμ
  have h1 : (μ : Measure E) (⋂ n, C n) = ⨅ n, (μ : Measure E) (C n) :=
    hCa.measure_iInter (fun n => (hC n).measurableSet.nullMeasurableSet)
      ⟨0, measure_ne_top _ _⟩
  have h2 : ε ≤ (μ : Measure E) (⋂ n, C n) := by
    rw [h1]; exact le_iInf fun n => (hμ n).2
  rw [h0 μ (hμ 0).1] at h2
  exact (not_le.2 hε) h2

end Abstract

section MapsTo

variable {X Y : Type*} [TopologicalSpace X] [T2Space X] [TopologicalSpace Y]

omit [T2Space X] in
/-- `{d | ¬ MapsTo d A U}` is closed in the compact-open topology. -/
theorem isClosed_setOf_not_mapsTo {A : Set X} {U : Set Y} (hA : IsCompact A) (hU : IsOpen U) :
    IsClosed {d : C(X, Y) | ¬ MapsTo d A U} :=
  (ContinuousMap.isOpen_setOfPred_mapsTo hA hU).isClosed_compl

/-- Cantor: failing `MapsTo d (A n) (U n)` for all `n` yields a bad point of `⋂ A n`. -/
theorem exists_mem_iInter_of_not_mapsTo {A : ℕ → Set X} (hA : ∀ n, IsCompact (A n))
    (hAa : Antitone A) {U : ℕ → Set Y} (hU : ∀ n, IsOpen (U n)) (hUm : Monotone U)
    {d : C(X, Y)} (hd : ∀ n, ¬ MapsTo d (A n) (U n)) :
    ∃ x ∈ ⋂ n, A n, ∀ n, d x ∉ U n := by
  let t : ℕ → Set X := fun n => A n ∩ d ⁻¹' (U n)ᶜ
  have htc : ∀ n, IsClosed (t n) := fun n =>
    (hA n).isClosed.inter ((hU n).isClosed_compl.preimage d.continuous)
  obtain ⟨x, hx⟩ := IsCompact.nonempty_iInter_of_sequence_nonempty_isCompact_isClosed t
    (fun n => inter_subset_inter (hAa n.le_succ)
      (preimage_mono (compl_subset_compl.2 (hUm n.le_succ))))
    (fun n => by
      have := hd n
      simp only [MapsTo, not_forall] at this
      obtain ⟨x, hxA, hxU⟩ := this
      exact ⟨x, hxA, hxU⟩)
    ((hA 0).of_isClosed_subset (htc 0) inter_subset_left) htc
  rw [mem_iInter] at hx
  exact ⟨x, mem_iInter.2 fun n => (hx n).1, fun n => (hx n).2⟩

end MapsTo

end Tight
end GM
end LQGMetric
