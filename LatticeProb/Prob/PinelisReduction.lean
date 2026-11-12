/-
# Transfer lemmas for the cumulative cross term

For partial sums `S i = ∑_{j=1}^{i} ξ_j` of martingale differences with predictable quadratic
variation increments `v (i+1) = E[ξ(i+1)² | F i]`, the cumulative cross term

  `B = ∑_{i<k} E[|S i|^{p-2} v (i+1)]`

may be read either in its `v`-form or in its `ξ²`-form.  This file proves the two facts behind
that change of form:

* `martingalePartialSum_stronglyMeasurable` — the **strongly-measurable transfer**: if each `ξ i` is
  `F i`-strongly-measurable then the partial sum `S i` is `F i`-strongly-measurable, hence so is
  `|S i|^{p-2}`;
* `crossTerm_pullOut` — the **pull-out identity** `E[|S i|^{p-2} v (i+1)] = E[|S i|^{p-2} ξ(i+1)²]`
  under that measurability and `v (i+1) =ᵐ E[ξ(i+1)² | F i]`, via `integral_rpow_mul_condExp_sq_eq`;
* `crossTerm_sum_pullOut` — the same identity summed over `i < k`.
-/
import LatticeProb.Prob.BernsteinInduction

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal

namespace LatticeProb

variable {Ω : Type*} {m₀ : MeasurableSpace Ω} {μ : @Measure Ω m₀}

/-- **The strongly-measurable transfer to the filtered partial-sum process.**  If each increment
`ξ i` is `F i`-strongly-measurable then the partial sum `S i = ∑_{j∈Icc 1 i} ξ j` is
`F i`-strongly-measurable. -/
theorem martingalePartialSum_stronglyMeasurable {F : Filtration ℕ m₀} {ξ : ℕ → Ω → ℝ}
    (hξ : ∀ i, StronglyMeasurable[F i] (ξ i)) (i : ℕ) :
    StronglyMeasurable[F i] (martingalePartialSum ξ i) := by
  unfold martingalePartialSum
  have h := Finset.stronglyMeasurable_sum (M := ℝ) (f := fun j : ℕ => ξ j)
    (Finset.Icc 1 i) fun j hj => by
      rw [Finset.mem_Icc] at hj
      exact (hξ j).mono (F.mono hj.2)
  rw [show (∑ j ∈ Finset.Icc 1 i, ξ j)
      = (fun ω => ∑ j ∈ Finset.Icc 1 i, ξ j ω) by funext ω; rw [Finset.sum_apply]] at h
  exact h

/-- **The pull-out identity for the cross term.**  Under the `F i`-strong measurability of
`|S i|^{p-2}` and `v (i+1) =ᵐ E[ξ(i+1)² | F i]`, the `v`-form of the cross term is the `ξ²`-form:
`E[|S i|^{p-2} v (i+1)] = E[|S i|^{p-2} ξ(i+1)²]`. -/
theorem crossTerm_pullOut [IsProbabilityMeasure μ] {m : MeasurableSpace Ω} {p : ℝ}
    {S : Ω → ℝ} {ξ v : Ω → ℝ}
    (hm : m ≤ m₀) (hS : StronglyMeasurable[m] fun ω => |S ω| ^ (p - 2))
    (hv : μ[fun ω => ξ ω ^ 2 | m] =ᵐ[μ] v)
    (hSξ2 : Integrable (fun ω => |S ω| ^ (p - 2) * ξ ω ^ 2) μ)
    (hξ2 : Integrable (fun ω => ξ ω ^ 2) μ) :
    ∫ ω, |S ω| ^ (p - 2) * v ω ∂μ = ∫ ω, |S ω| ^ (p - 2) * ξ ω ^ 2 ∂μ :=
  (integral_rpow_mul_condExp_sq_eq hm hS hv hSξ2 hξ2).symm

/-- **Summed pull-out.**  Under `F`-adaptation and `v (i+1) =ᵐ E[ξ(i+1)² | F i]`, the whole
cumulative cross term may be rewritten from its `v`-form to its `ξ²`-form. -/
theorem crossTerm_sum_pullOut [IsProbabilityMeasure μ] {p : ℝ} {F : Filtration ℕ m₀}
    {S ξ : ℕ → Ω → ℝ} {v : ℕ → Ω → ℝ}
    (hS : ∀ i, StronglyMeasurable[F i] (fun ω => |S i ω| ^ (p - 2)))
    (hv : ∀ i, μ[fun ω => ξ (i + 1) ω ^ 2 | F i] =ᵐ[μ] v (i + 1))
    (hSξ2 : ∀ i, Integrable (fun ω => |S i ω| ^ (p - 2) * ξ (i + 1) ω ^ 2) μ)
    (hξ2 : ∀ i, Integrable (fun ω => ξ (i + 1) ω ^ 2) μ) :
    ∀ k, (∑ i ∈ Finset.range k, (∫ ω, |S i ω| ^ (p - 2) * v (i + 1) ω ∂μ))
      = ∑ i ∈ Finset.range k, (∫ ω, |S i ω| ^ (p - 2) * ξ (i + 1) ω ^ 2 ∂μ) := by
  intro k
  refine Finset.sum_congr rfl fun i _ => ?_
  exact crossTerm_pullOut (F.le i) (hS i) (hv i) (hSξ2 i) (hξ2 i)

end LatticeProb
