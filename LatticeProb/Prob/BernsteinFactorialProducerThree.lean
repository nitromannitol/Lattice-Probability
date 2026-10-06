/-
# Raw-factorial producer, part three: the exponent-sum interchange and majorant value

`LatticeProb.summable_expMomentSeries` (`Prob/BernsteinFactorialProducerTwo.lean`) makes each
per-increment exponent series `d_λ(i) = ∑_{q≥2} (λ^q/q!) E[|ξ_i|^q | m]` summable.  To run
the
super-martingale consumer the exponents must be **added over the increments**, and the raw
factorial bound only controls `∑_i E[|ξ_i|^q | m]` for each fixed `q`.  This file supplies
the two
remaining analytical pieces, both pointwise (the caller applies them a.s.):

* the **finite-sum / `tsum` interchange** `∑_{i∈s} ∑_q g i q = ∑_q ∑_{i∈s} g i q`;
* the **identification of the majorant series**:
  `∑_{q≥2} (λ^q/q!) ((q!/2) a^{q-2} v) = λ²v/(2(1-aλ))`, for admissible `λ`
  (`0 ≤ λ`, `λa < 1`).

Together they give `∑_{i∈s} d_λ(i) ≤ λ²v/(2(1-aλ))`, the `hD_le` input of the consumer.
The
empty-horizon case is `s = ∅` (sum `0`), and `λ = 0` is inside the statement (exponent `0`).

No new `Prop`; no new external input; no false Pinelis input; not imported by the root.
-/
import LatticeProb.Prob.BernsteinFactorialProducerTwo

open MeasureTheory ProbabilityTheory Filter Finset
open scoped NNReal ENNReal

namespace LatticeProb

variable {Ω : Type*} {m₀ : MeasurableSpace Ω} {μ : @Measure Ω m₀}

/-- A term of a non-negative sum is at most the sum. -/
private theorem le_of_sum_le_of_nonneg {ι : Type*} {s : Finset ι} {f : ι → ℝ} {B : ℝ}
    (hnn : ∀ i ∈ s, 0 ≤ f i) (h : ∑ i ∈ s, f i ≤ B) {j : ι} (hj : j ∈ s) :
    f j ≤ B :=
  (Finset.single_le_sum hnn hj).trans h

/-- A finite sum of summable sequences is summable. -/
private theorem summable_finset_sum {ι : Type*} {s : Finset ι} {g : ι → ℕ → ℝ}
    (hs : ∀ i ∈ s, Summable (g i)) : Summable (fun q => ∑ i ∈ s, g i q) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
      have ha' := hs a (Finset.mem_insert_self a s)
      have hs' : ∀ i ∈ s, Summable (g i) := fun i hi => hs i (Finset.mem_insert_of_mem hi)
      have hcomb := (ih hs').add ha'
      have hcongr : (fun q => (∑ i ∈ s, g i q) + g a q)
          = fun q => ∑ i ∈ insert a s, g i q := by
        funext q
        rw [Finset.sum_insert ha]
        ring
      rwa [hcongr] at hcomb

/-- **Finite-sum / `tsum` interchange.**  For a finite index set `s` and summable sequences
`g i`, `∑_{i∈s} ∑_q g i q = ∑_q ∑_{i∈s} g i q`. -/
theorem sum_tsum_eq_tsum_sum {ι : Type*} {s : Finset ι} {g : ι → ℕ → ℝ}
    (hs : ∀ i ∈ s, Summable (g i)) :
    ∑ i ∈ s, (∑' q, g i q) = ∑' q, ∑ i ∈ s, g i q := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
      have ha' := hs a (Finset.mem_insert_self a s)
      have hs' : ∀ i ∈ s, Summable (g i) := fun i hi => hs i (Finset.mem_insert_of_mem hi)
      have hsum' : Summable (fun q => ∑ i ∈ s, g i q) := summable_finset_sum hs'
      calc ∑ i ∈ insert a s, (∑' q, g i q)
          = (∑' q, g a q) + ∑ i ∈ s, (∑' q, g i q) := by rw [Finset.sum_insert ha]
        _ = (∑' q, g a q) + ∑' q, ∑ i ∈ s, g i q := by rw [ih hs']
        _ = ∑' q, (g a q + ∑ i ∈ s, g i q) := (Summable.tsum_add ha' hsum').symm
        _ = ∑' q, ∑ i ∈ insert a s, g i q := by
              congr 1
              funext q
              rw [Finset.sum_insert ha]

/-- **Summability of the Bernstein majorant series** (zeroed at `q < 2`). -/
theorem summable_bernsteinMajorant {a v lam : ℝ} (ha : 0 < a) (hlam : 0 ≤ lam)
    (hlam_a : lam * a < 1) :
    Summable (fun q : ℕ => if q < 2 then 0
      else (lam ^ q / (Nat.factorial q : ℝ))
        * ((Nat.factorial q : ℝ) / 2 * a ^ (q - 2) * v)) := by
  have htail := summable_bernsteinTail (v := v) ha hlam hlam_a
  refine (summable_nat_add_iff 2).mp ?_
  have hiff : (fun n : ℕ => if n + 2 < 2 then 0
      else (lam ^ (n + 2) / (Nat.factorial (n + 2) : ℝ))
        * ((Nat.factorial (n + 2) : ℝ) / 2 * a ^ (n + 2 - 2) * v))
      = fun n : ℕ => lam ^ (n + 2) / (Nat.factorial (n + 2) : ℝ)
          * ((Nat.factorial (n + 2) : ℝ) / 2 * a ^ n * v) := by
    funext n
    rw [if_neg (by omega : ¬ (n + 2 < 2)), (by omega : n + 2 - 2 = n)]
  rw [hiff]
  exact htail

/-- **Value of the Bernstein majorant series.**  For admissible `λ`,
  `∑_{q≥2} (λ^q/q!) ((q!/2) a^{q-2} v) = λ²v/(2(1-aλ))`. -/
theorem tsum_bernsteinMajorant_eq {a v lam : ℝ} (ha : 0 < a) (hlam : 0 ≤ lam)
    (hlam_a : lam * a < 1) :
    ∑' q : ℕ, (if q < 2 then 0
        else (lam ^ q / (Nat.factorial q : ℝ)) * ((Nat.factorial q : ℝ) / 2 * a ^ (q - 2) * v))
      = lam ^ 2 * v / (2 * (1 - a * lam)) := by
  have hs := summable_bernsteinMajorant (v := v) ha hlam hlam_a
  have hsplit := hs.tsum_eq_zero_add
  rw [hsplit, ((summable_nat_add_iff 1).mpr hs).tsum_eq_zero_add]
  have h0 : (if (0 : ℕ) < 2 then 0
      else (lam ^ 0 / (Nat.factorial 0 : ℝ))
        * ((Nat.factorial 0 : ℝ) / 2 * a ^ (0 - 2) * v)) = 0 := by
    simp
  have h1 : (if (1 : ℕ) < 2 then 0
      else (lam ^ 1 / (Nat.factorial 1 : ℝ))
        * ((Nat.factorial 1 : ℝ) / 2 * a ^ (1 - 2) * v)) = 0 := by
    simp
  rw [h0, h1, zero_add, zero_add]
  have hiff : (fun n : ℕ => if n + 1 + 1 < 2 then 0
      else (lam ^ (n + 1 + 1) / (Nat.factorial (n + 1 + 1) : ℝ))
        * ((Nat.factorial (n + 1 + 1) : ℝ) / 2 * a ^ (n + 1 + 1 - 2) * v))
      = fun n : ℕ => lam ^ (n + 2) / (Nat.factorial (n + 2) : ℝ)
          * ((Nat.factorial (n + 2) : ℝ) / 2 * a ^ n * v) := by
    funext n
    rw [if_neg (by omega : ¬ (n + 1 + 1 < 2)), (by omega : n + 1 + 1 - 2 = n),
      (by omega : n + 1 + 1 = n + 2)]
  rw [hiff, tsum_bernsteinTail_eq (v := v) ha hlam hlam_a]

/-- **The exponent-sum bound.**  For a finite set of increments whose conditional absolute moments
obey the raw factorial bound `∑_{i∈s} E[|ξ_i|^q|m] ≤ (q!/2) a^{q-2} v` for every
`q ≥ 2`, the
per-increment exponents satisfy `∑_{i∈s} d_λ(i) ≤ λ²v/(2(1-λa))` for admissible `λ`.
This is the
`hD_le` input of `LatticeProb.mgf_sum_le_of_random_condMgf`. -/
theorem sum_expMomentSeries_le {s : Finset ℕ} {M : ℕ → ℕ → ℝ} {a v lam : ℝ}
    (ha : 0 < a)
    (hlam : 0 ≤ lam) (hlam_a : lam * a < 1)
    (hMnn : ∀ i ∈ s, ∀ q, 0 ≤ M i q)
    (hq : ∀ q, 2 ≤ q → ∑ i ∈ s, M i q ≤ (Nat.factorial q : ℝ) / 2 * a ^ (q - 2) * v) :
    ∑ i ∈ s, (∑' q : ℕ, if q < 2 then 0
        else (lam ^ q / (Nat.factorial q : ℝ)) * M i q)
      ≤ lam ^ 2 * v / (2 * (1 - a * lam)) := by
  classical
  have hper : ∀ i ∈ s, ∀ q, 2 ≤ q →
      M i q ≤ (Nat.factorial q : ℝ) / 2 * a ^ (q - 2) * v := fun i hi q hq2 =>
    le_of_sum_le_of_nonneg (fun j hj => hMnn j hj q) (hq q hq2) hi
  have hsumm : ∀ i ∈ s, Summable (fun q : ℕ => if q < 2 then 0
      else (lam ^ q / (Nat.factorial q : ℝ)) * M i q) := fun i hi =>
    summable_expMomentSeries (M := M i) ha hlam hlam_a (fun q => hMnn i hi q)
      (fun q hq2 => hper i hi q hq2)
  rw [sum_tsum_eq_tsum_sum hsumm]
  have hle : (∑' q : ℕ, ∑ i ∈ s, (if q < 2 then 0
        else (lam ^ q / (Nat.factorial q : ℝ)) * M i q))
      ≤ ∑' q : ℕ, (if q < 2 then 0
        else (lam ^ q / (Nat.factorial q : ℝ))
          * ((Nat.factorial q : ℝ) / 2 * a ^ (q - 2) * v)) := by
    refine Summable.tsum_le_tsum ?_ (summable_finset_sum hsumm)
      (summable_bernsteinMajorant (v := v) ha hlam hlam_a)
    intro q
    by_cases hq2 : q < 2
    · simp [hq2]
    · simp only [if_neg hq2]
      calc ∑ i ∈ s, (lam ^ q / (Nat.factorial q : ℝ)) * M i q
          = (lam ^ q / (Nat.factorial q : ℝ)) * ∑ i ∈ s, M i q := by rw [Finset.mul_sum]
        _ ≤ (lam ^ q / (Nat.factorial q : ℝ))
              * ((Nat.factorial q : ℝ) / 2 * a ^ (q - 2) * v) :=
            mul_le_mul_of_nonneg_left (hq q (by omega)) (by positivity)
  exact hle.trans_eq (tsum_bernsteinMajorant_eq (v := v) ha hlam hlam_a)

end LatticeProb
