/-
The real-parameter (filter) form of `CramerWold.lean`'s device, needed whenever the limit of
interest is an `R → ∞` limit over a real parameter rather than a sequence indexed by `ℕ`, while
Mathlib's own Lévy continuity theorem
(`MeasureTheory.ProbabilityMeasure.tendsto_of_tendsto_charFun`) and hence
`LatticeProb.Scaling.CramerWold.tendstoInDistribution_of_tendsto_charFun_linearCombination` are
stated only for `(ℕ, Filter.atTop)`, because the underlying tightness argument genuinely needs a
countable family of measures.

The fix is the standard one for a countably generated filter (`Filter.atTop` on `ℝ` is
countably generated because `ℝ` is Archimedean,
`Mathlib.Order.Filter.AtTopBot.Archimedean`): `Tendsto f l Z` is equivalent to
`Tendsto (f ∘ u) atTop Z` for every sequence `u : ℕ → ι` with `Tendsto u atTop l`
(`Filter.tendsto_of_seq_tendsto`). Composing the hypothesis with such a `u` reduces the general
filter statement to the ℕ-indexed one already proved, and gluing over all sequences gives the
general filter conclusion back. This is a mechanical filter reduction, stated once for an
arbitrary countably generated, nontrivial filter.

The companion fact `tendsto_integral_of_tendstoInDistribution` records that
`TendstoInDistribution` tested against a bounded continuous function is exactly weak
convergence of the pushed-forward expectations, for an arbitrary filter (Mathlib's own
`ProbabilityMeasure.tendsto_iff_forall_integral_tendsto`, applied to the `tendsto` field).

Moved from Parking-Sharpness.
-/
import LatticeProb.Prob.Scaling.CramerWold

open MeasureTheory Filter Topology
open scoped RealInnerProductSpace

noncomputable section
namespace LatticeProb.Scaling.CramerWold

/-- **Cramer-Wold, for an arbitrary countably generated, nontrivial filter.**  The real-parameter
form of `tendstoInDistribution_of_tendsto_charFun_linearCombination`, needed for `R : ℝ → atTop`
limits. -/
theorem tendstoInDistribution_of_tendsto_charFun_linearCombination_filter
    {ι : Type*} {l : Filter ι} [l.IsCountablyGenerated] [l.NeBot]
    {Ω : ι → Type*} [∀ i, MeasurableSpace (Ω i)] {Ω' : Type*} [MeasurableSpace Ω']
    {P : (i : ι) → Measure (Ω i)} [∀ i, IsProbabilityMeasure (P i)]
    {Q : Measure Ω'} [IsProbabilityMeasure Q]
    {m : ℕ} {X : (i : ι) → Ω i → Fin m → ℝ} {Z : Ω' → Fin m → ℝ}
    (hXm : ∀ i, Measurable (X i)) (hZm : Measurable Z)
    (hcomb : ∀ t : Fin m → ℝ,
      Tendsto (fun i => charFun ((P i).map (fun ω => ∑ k, t k * X i ω k)) 1) l
        (𝓝 (charFun (Q.map (fun ω => ∑ k, t k * Z ω k)) 1))) :
    TendstoInDistribution X l Z P Q := by
  refine { forall_aemeasurable := fun i => (hXm i).aemeasurable
           aemeasurable_limit := hZm.aemeasurable
           tendsto := ?_ }
  apply tendsto_of_seq_tendsto
  intro u hu
  have hcomb' : ∀ t : Fin m → ℝ,
      Tendsto (fun n : ℕ => charFun ((P (u n)).map (fun ω => ∑ k, t k * X (u n) ω k)) 1) atTop
        (𝓝 (charFun (Q.map (fun ω => ∑ k, t k * Z ω k)) 1)) :=
    fun t => (hcomb t).comp hu
  exact (tendstoInDistribution_of_tendsto_charFun_linearCombination
    (fun n => hXm (u n)) hZm hcomb').tendsto

/-- **`TendstoInDistribution` tested against a bounded continuous function is exactly weak
convergence of the pushed-forward expectations**, for an arbitrary filter (no countable
generation needed: this direction is Mathlib's own general-filter
`ProbabilityMeasure.tendsto_iff_forall_integral_tendsto`, applied to the `tendsto` field). -/
theorem tendsto_integral_of_tendstoInDistribution
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E]
    [TopologicalSpace.PseudoMetrizableSpace E] [BorelSpace E] [SecondCountableTopology E]
    {ι : Type*} {l : Filter ι}
    {Ω : ι → Type*} [∀ i, MeasurableSpace (Ω i)] {Ω' : Type*} [MeasurableSpace Ω']
    {P : (i : ι) → Measure (Ω i)} [∀ i, IsProbabilityMeasure (P i)]
    {Q : Measure Ω'} [IsProbabilityMeasure Q]
    {X : (i : ι) → Ω i → E} {Z : Ω' → E}
    (h : TendstoInDistribution X l Z P Q) (F : BoundedContinuousFunction E ℝ) :
    Tendsto (fun i => ∫ ω, F (X i ω) ∂(P i)) l (𝓝 (∫ ω, F (Z ω) ∂Q)) := by
  have hconv := h.tendsto
  rw [ProbabilityMeasure.tendsto_iff_forall_integral_tendsto] at hconv
  have hF := hconv F
  simp only [MeasureTheory.ProbabilityMeasure.coe_mk] at hF
  have heq1 : ∀ i, ∫ x, F x ∂((P i).map (X i)) = ∫ ω, F (X i ω) ∂(P i) := fun i =>
    integral_map (h.forall_aemeasurable i) F.continuous.aestronglyMeasurable
  have heq2 : ∫ x, F x ∂(Q.map Z) = ∫ ω, F (Z ω) ∂Q :=
    integral_map h.aemeasurable_limit F.continuous.aestronglyMeasurable
  simpa only [heq1, heq2] using hF

end LatticeProb.Scaling.CramerWold
end
