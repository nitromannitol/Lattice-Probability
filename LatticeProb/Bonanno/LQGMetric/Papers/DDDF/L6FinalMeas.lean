/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DDDF.L6FinalMeas at commit fdb5cad; only the module paths of local imports are changed. -/
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
import Mathlib.MeasureTheory.Constructions.BorelSpace.Metrizable
import Mathlib.MeasureTheory.Measure.AEMeasurable
import Mathlib.Topology.Bases
import Mathlib.Analysis.Complex.Basic

/-!
# Measurable continuous versions

A field `Y` continuous on a set `K ⊆ ℂ` for every `ω` and a version of a measurable field `X`
on `K` can be modified on a null set so that it is moreover measurable in `ω` at each point
(`exists_measurable_version`): set it to `0` on a measurable null set containing the event where
`Y ≠ X` at some point of a countable dense subset of `K`; at the other points use continuity
(limits of measurable functions). Standard measure theory (own routine step).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology

namespace LQGMetric
namespace DDDF

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}

/-- **Measurable continuous version.** -/
theorem exists_measurable_version {K : Set ℂ} {Y X : ℂ → Ω → ℝ}
    (hYc : ∀ ω, ContinuousOn (fun x => Y x ω) K) (hX : ∀ x, Measurable (X x))
    (hYX : ∀ x ∈ K, Y x =ᵐ[P] X x) :
    ∃ Y' : ℂ → Ω → ℝ, (∀ ω, ContinuousOn (fun x => Y' x ω) K) ∧ (∀ x, Measurable (Y' x)) ∧
      (∀ᵐ ω ∂P, ∀ x ∈ K, Y' x ω = Y x ω) := by
  classical
  obtain ⟨D, hDc, hDK, hKD⟩ := TopologicalSpace.exists_countable_dense_subset K
  set Bad : Set Ω := {ω | ∃ q ∈ D, Y q ω ≠ X q ω}
  have hBad : P Bad = 0 := by
    have : Bad = ⋃ q ∈ D, {ω | Y q ω ≠ X q ω} := by ext ω; simp [Bad]
    rw [this]
    exact (measure_biUnion_null_iff hDc).2 fun q hq => ae_iff.1 (hYX q (hDK hq))
  set N := toMeasurable P Bad
  have hN : MeasurableSet N := measurableSet_toMeasurable P Bad
  have hN0 : P N = 0 := by rw [measure_toMeasurable]; exact hBad
  have hBN : Bad ⊆ N := subset_toMeasurable P Bad
  set Y' : ℂ → Ω → ℝ := fun x ω => if x ∈ K ∧ ω ∉ N then Y x ω else 0
  have hD' : ∀ q ∈ D, Y' q = Nᶜ.indicator (X q) := by
    intro q hq; funext ω
    by_cases hω : ω ∈ N
    · simp [Y', hω]
    · have hgood : Y q ω = X q ω := by
        by_contra hne; exact hω (hBN ⟨q, hq, hne⟩)
      simp [Y', hω, hDK hq, hgood]
  refine ⟨Y', fun ω => ?_, fun x => ?_, ?_⟩
  · by_cases hω : ω ∈ N
    · exact (continuousOn_const (c := (0 : ℝ))).congr fun x hx => by simp [Y', hω]
    · exact (hYc ω).congr fun x hx => by simp [Y', hω, hx]
  · by_cases hx : x ∈ K
    · obtain ⟨d, hdD, hdx⟩ := mem_closure_iff_seq_limit.1 (hKD hx)
      refine measurable_of_tendsto_metrizable (f := fun k => Y' (d k))
        (fun k => by rw [hD' _ (hdD k)]; exact (hX _).indicator hN.compl) ?_
      refine tendsto_pi_nhds.2 fun ω => ?_
      by_cases hω : ω ∈ N
      · simp only [Y', hω, not_true_eq_false, and_false, ite_false]; exact tendsto_const_nhds
      · have hdK : ∀ k, d k ∈ K := fun k => hDK (hdD k)
        simp only [Y', hω, not_false_eq_true, and_true, hdK, hx, ite_true]
        exact ((hYc ω) x hx).tendsto.comp (tendsto_nhdsWithin_iff.2 ⟨hdx, Eventually.of_forall hdK⟩)
    · have : Y' x = fun _ => 0 := by funext ω; simp [Y', hx]
      rw [this]; exact measurable_const
  · refine (measure_eq_zero_iff_ae_notMem.1 hN0).mono fun ω hω x hx => ?_
    simp [Y', hx, hω]

end DDDF
end LQGMetric
