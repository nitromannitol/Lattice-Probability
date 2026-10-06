/-
# Raw-factorial producer, part two: per-term extraction and exponent summability

`LatticeProb.condExp_exp_le_of_momentSeries` (`Prob/BernsteinFactorialProducer.lean`) turns a
per-increment bound `E[|X|^q | m] ≤ (q!/2) a^{q-2} v` into the conditional-exponential bound whose
exponent is the increment's own moment series `∑_{q≥2} (λ^q/q!) E[|X|^q | m]`.  To run it
from the
`Parking` clause-2 hypothesis — which bounds the **sum** `∑_i E[|ξ_i|^q | F_{i-1}]`, not each
increment — two further pieces are needed, and both are supplied here:

* the **per-term extraction**: a term of a non-negative sum is at most the sum, so the frozen
  bound on `∑_i E[|ξ_i|^q | F_{i-1}]` gives each
  `E[|ξ_j|^q | F_{j-1}] ≤ (q!/2) a^{q-2} v` a.s.;
* the **exponent-series summability and value**: the geometric majorant
  `∑_{q≥2} (λ^q/q!) ((q!/2) a^{q-2} v) = λ²v/(2(1-aλ))`, which is exactly the `hg` input of
  `condExp_exp_le_of_momentSeries` and the bound that makes `∑_i d_λ(i)` finite.

The admissible-λ domain is `0 ≤ λ`, `λ a < 1`; the empty-horizon and `λ = 0` cases are then
immediate (an empty sum is `0`; `λ = 0` gives the exponent `0` and the bound `1`).

No new `Prop`; no new external input; no false Pinelis input; not imported by the root.
-/
import LatticeProb.Prob.BernsteinFactorialProducer

open MeasureTheory ProbabilityTheory Filter Finset
open scoped NNReal ENNReal

namespace LatticeProb

variable {Ω : Type*} {m₀ : MeasurableSpace Ω} {μ : @Measure Ω m₀}

/-- **A term of a non-negative sum is at most the sum.** -/
private theorem le_of_sum_le_of_nonneg {ι : Type*} {s : Finset ι} {f : ι → ℝ} {B : ℝ}
    (hnn : ∀ i ∈ s, 0 ≤ f i) (h : ∑ i ∈ s, f i ≤ B) {j : ι} (hj : j ∈ s) :
    f j ≤ B :=
  (Finset.single_le_sum hnn hj).trans h

/-- **Per-term extraction from the raw sum bound.**  If every conditional absolute moment is
non-negative and the frozen sum bound `∑_{i∈s} E[|ξ_i|^q | m] ≤ B q` holds a.s., then each
increment obeys `E[|ξ_j|^q | m] ≤ B q` a.s.  This is how the clause-2 sum hypothesis feeds the
per-increment producer. -/
theorem factorialMoment_term_le [IsProbabilityMeasure μ] {s : Finset ℕ}
    {M : ℕ → Ω → ℝ} {B : ℕ → ℝ}
    {q : ℕ}
    (hnn : ∀ᵐ ω ∂μ, ∀ i ∈ s, 0 ≤ M i ω)
    (hsum : ∀ᵐ ω ∂μ, ∑ i ∈ s, M i ω ≤ B q) {j : ℕ} (hj : j ∈ s) :
    M j ≤ᵐ[μ] fun _ => B q := by
  filter_upwards [hnn, hsum] with ω hnnω hsumω
  exact le_of_sum_le_of_nonneg hnnω hsumω hj

/-- **Summability of the Bernstein tail majorant.**  For admissible `λ` (`0 ≤ λ`,
`λ a < 1`) the
series `∑_{q≥2} (λ^q/q!) ((q!/2) a^{q-2} v)` converges. -/
theorem summable_bernsteinTail {a v lam : ℝ} (ha : 0 < a) (hlam : 0 ≤ lam)
    (hlam_a : lam * a < 1) :
    Summable (fun q : ℕ => lam ^ (q + 2) / (Nat.factorial (q + 2) : ℝ)
      * ((Nat.factorial (q + 2) : ℝ) / 2 * a ^ q * v)) := by
  have hcongr : (fun q : ℕ => lam ^ (q + 2) / (Nat.factorial (q + 2) : ℝ)
      * ((Nat.factorial (q + 2) : ℝ) / 2 * a ^ q * v))
      = fun q : ℕ => (lam ^ 2 * v / 2) * (lam * a) ^ q := by
    funext q
    have hf : (Nat.factorial (q + 2) : ℝ) ≠ 0 := by positivity
    field_simp
    ring
  rw [hcongr]
  exact (summable_geometric_of_lt_one (mul_nonneg hlam ha.le) hlam_a).mul_left _

/-- **Value of the Bernstein tail exponent.**  For admissible `λ`,
  `∑_{q≥2} (λ^q/q!) ((q!/2) a^{q-2} v) = λ²v/(2(1-aλ))`. -/
theorem tsum_bernsteinTail_eq {a v lam : ℝ} (ha : 0 < a) (hlam : 0 ≤ lam)
    (hlam_a : lam * a < 1) :
    ∑' q : ℕ, lam ^ (q + 2) / (Nat.factorial (q + 2) : ℝ)
        * ((Nat.factorial (q + 2) : ℝ) / 2 * a ^ q * v)
      = lam ^ 2 * v / (2 * (1 - a * lam)) := by
  have hcongr : (fun q : ℕ => lam ^ (q + 2) / (Nat.factorial (q + 2) : ℝ)
      * ((Nat.factorial (q + 2) : ℝ) / 2 * a ^ q * v))
      = fun q : ℕ => (lam ^ 2 * v / 2) * (lam * a) ^ q := by
    funext q
    have hf : (Nat.factorial (q + 2) : ℝ) ≠ 0 := by positivity
    field_simp
    ring
  rw [hcongr, tsum_mul_left, tsum_geometric_of_lt_one (mul_nonneg hlam ha.le) hlam_a]
  have hne : (1 : ℝ) - lam * a ≠ 0 := by linarith
  field_simp

/-- **Summability of the per-increment exponent series.**  If the increment's conditional absolute
moments obey the per-term Bernstein factorial bound for `q ≥ 2`, then the exponent series
`q ↦ (λ^q/q!) E[|X|^q | m]` (zeroed at `q < 2`) is summable for admissible `λ`.  This is exactly
the `hg` input of `condExp_exp_le_of_momentSeries`. -/
theorem summable_expMomentSeries {M : ℕ → ℝ} {a v lam : ℝ} (ha : 0 < a)
    (hlam : 0 ≤ lam) (hlam_a : lam * a < 1)
    (hMnn : ∀ q : ℕ, 0 ≤ M q)
    (hM : ∀ q : ℕ, 2 ≤ q → M q ≤ (Nat.factorial q : ℝ) / 2 * a ^ (q - 2) * v) :
    Summable (fun q : ℕ => if q < 2 then 0
      else (lam ^ q / (Nat.factorial q : ℝ)) * M q) := by
  refine (summable_nat_add_iff 2).mp ?_
  change Summable (fun q : ℕ => if q + 2 < 2 then 0
      else (lam ^ (q + 2) / (Nat.factorial (q + 2) : ℝ)) * M (q + 2))
  have hiff : (fun q : ℕ => if q + 2 < 2 then 0
      else (lam ^ (q + 2) / (Nat.factorial (q + 2) : ℝ)) * M (q + 2))
      = fun q : ℕ => (lam ^ (q + 2) / (Nat.factorial (q + 2) : ℝ)) * M (q + 2) := by
    funext q
    rw [if_neg (by omega : ¬ (q + 2 < 2))]
  rw [hiff]
  have hmaj := summable_bernsteinTail (v := v) ha hlam hlam_a
  refine hmaj.of_nonneg_of_le (fun q => ?_) (fun q => ?_)
  · exact mul_nonneg (by positivity) (hMnn (q + 2))
  · have hle := hM (q + 2) (by omega)
    rw [show (q + 2) - 2 = q from by omega] at hle
    exact mul_le_mul_of_nonneg_left hle (by positivity)

end LatticeProb
