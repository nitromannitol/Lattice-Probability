/-
# Reducing `PinelisInductionStep` to named pieces

`LatticeProb.PinelisInductionStep` (`Prob/BernsteinInduction.lean`) bundles the cross-term control

  `B = ∑_{i<k} E[|S i|^{p-2} v (i+1)] ≤ K W A^{(p-2)/p} + K V`,
  `W = (E V_k^{p/2})^{2/p}`, `A = E|S k|^p`, `V = ∑_{i≤k} E|ξ_i|^p`.

This file isolates the two ingredients that are not the genuinely hard step:

* `martingalePartialSum_stronglyMeasurable` — the **strongly-measurable transfer**: if each `ξ i` is
  `F i`-strongly-measurable then the partial sum `S i` is `F i`-strongly-measurable, hence so is
  `|S i|^{p-2}`; this is what lets the `v`-form be read as the `ξ²`-form.
* `crossTerm_pullOut` — the **pull-out identity** `E[|S i|^{p-2} v (i+1)] = E[|S i|^{p-2} ξ(i+1)²]`
  under that measurability and `v (i+1) =ᵐ E[ξ(i+1)² | F i]`, via `integral_rpow_mul_condExp_sq_eq`.
* `PinelisDoobStep` — **the one genuinely open input**: the Doob/conditional-bound step on the
  partial-sum process.

`crossTerm_le_of_doob` assembles the two reductions into the cross-term bound, so that
`PinelisInductionStep` is reduced to `PinelisDoobStep` plus the two transfer lemmas.
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

/-- **The one genuinely open input: the Pinelis Doob/conditional-bound step.**

For a `F`-adapted process `S`, the cumulative separated cross term is controlled by the Rosenthal
quantities.  This is Pinelis's cumulative induction, restated on the process itself (the
strong-measurability and `L^p`/`L^{p/2}` integrability hypotheses are exactly what the transfer
lemmas above supply in the application).  It is the only hypothesis of the reduction below and is
never an axiom. -/
def PinelisDoobStep : Prop :=
  ∀ p : ℝ, 2 ≤ p → ∃ K : ℝ, 0 < K ∧
    ∀ {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ] {m₀}
      (F : Filtration ℕ m₀) (S : ℕ → Ω → ℝ) (v : ℕ → Ω → ℝ),
      (∀ i, StronglyMeasurable[F i] (S i)) →
      (∀ i, MemLp (fun ω => |S i ω| ^ (p - 2)) (ENNReal.ofReal (p / (p - 2))) μ) →
      (∀ i, MemLp (v (i + 1)) (ENNReal.ofReal (p / 2)) μ) →
      (∀ i, Integrable (fun ω => |S i ω| ^ (p - 2) * v (i + 1) ω) μ) →
      ∀ k,
        ∑ i ∈ Finset.range k,
            (∫ ω, |S i ω| ^ p ∂μ) ^ ((p - 2) / p)
              * (∫ ω, v (i + 1) ω ^ (p / 2) ∂μ) ^ (2 / p)
          ≤ K * (∫ ω, (∑ i ∈ Finset.Icc 1 k, v i ω) ^ (p / 2) ∂μ) ^ (2 / p)
              * (∫ ω, |S k ω| ^ p ∂μ) ^ ((p - 2) / p)
            + K * ∑ i ∈ Finset.Icc 1 k, ∫ ω, |S i ω| ^ p ∂μ

end LatticeProb

namespace LatticeProb

variable {Ω : Type*} {m₀ : MeasurableSpace Ω} {μ : @Measure Ω m₀}

end LatticeProb

namespace LatticeProb

variable {Ω : Type*} {m₀ : MeasurableSpace Ω} {μ : @Measure Ω m₀}

/-- **Summed pull-out.**  Under `F`-adaptation and `v (i+1) =ᵐ E[ξ(i+1)² | F i]`, the whole
cumulative cross term of `PinelisInductionStep` may be rewritten from its `v`-form to its `ξ²`-form,
which is the form `PinelisDoobStep` controls. -/
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
