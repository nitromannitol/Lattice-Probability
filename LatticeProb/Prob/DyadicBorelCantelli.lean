import Mathlib.MeasureTheory.OuterMeasure.BorelCantelli
import Mathlib.MeasureTheory.Measure.MeasureSpaceDef

/-!
# Borel-Cantelli for events indexed by dyadic squares

If for each scale `n` the exceptional sets `(E n i j)ᶜ`, indexed by the `4ⁿ` dyadic squares
`(i, j)` with `i, j < 2ⁿ`, all have measure at most `p n`, and `∑ₙ 4ⁿ p n < ∞`, then almost surely
all the events `E n i j` hold simultaneously for all large enough `n`.  The proof is a union bound
over the `4ⁿ` squares of one scale followed by the first Borel-Cantelli lemma.
-/

open MeasureTheory Filter
open scoped ENNReal

namespace LatticeProb

/-- **Borel-Cantelli over dyadic squares.** Let `E n i j` be events with
`μ (E n i j)ᶜ ≤ p n` for all `i, j < 2ⁿ` and `∑ₙ 4ⁿ p n ≠ ∞`.  Then almost surely there is `N` with
`ω ∈ E n i j` for all `n ≥ N` and all `i, j < 2ⁿ`. -/
theorem ae_eventually_forall_dyadic_of_tsum {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (E : ℕ → ℕ → ℕ → Set Ω) (p : ℕ → ℝ≥0∞)
    (hp : ∀ n i j, i < 2 ^ n → j < 2 ^ n → μ (E n i j)ᶜ ≤ p n)
    (hsum : ∑' n, 4 ^ n * p n ≠ ⊤) :
    ∀ᵐ ω ∂μ, ∃ N, ∀ n ≥ N, ∀ i j, i < 2 ^ n → j < 2 ^ n → ω ∈ E n i j := by
  set B : ℕ → Set Ω := fun n =>
    ⋃ i ∈ Finset.range (2 ^ n), ⋃ j ∈ Finset.range (2 ^ n), (E n i j)ᶜ with hB
  have hBn : ∀ n, μ (B n) ≤ 4 ^ n * p n := by
    intro n
    calc μ (B n)
        ≤ ∑ i ∈ Finset.range (2 ^ n), μ (⋃ j ∈ Finset.range (2 ^ n), (E n i j)ᶜ) :=
          measure_biUnion_finset_le _ _
      _ ≤ ∑ i ∈ Finset.range (2 ^ n), ∑ j ∈ Finset.range (2 ^ n), μ ((E n i j)ᶜ) :=
          Finset.sum_le_sum fun i _ => measure_biUnion_finset_le _ _
      _ ≤ ∑ i ∈ Finset.range (2 ^ n), ∑ j ∈ Finset.range (2 ^ n), p n :=
          Finset.sum_le_sum fun i hi => Finset.sum_le_sum fun j hj =>
            hp n i j (Finset.mem_range.1 hi) (Finset.mem_range.1 hj)
      _ = 4 ^ n * p n := by
          simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
          push_cast
          rw [← mul_assoc, ← mul_pow]
          norm_num
  have hfin : ∑' n, μ (B n) ≠ ⊤ :=
    ne_top_of_le_ne_top hsum (ENNReal.tsum_le_tsum hBn)
  filter_upwards [ae_eventually_notMem hfin] with ω hω
  obtain ⟨N, hN⟩ := eventually_atTop.1 hω
  refine ⟨N, fun n hn i j hi hj => ?_⟩
  by_contra hcon
  refine hN n hn ?_
  simp only [hB, Set.mem_iUnion]
  exact ⟨i, Finset.mem_range.2 hi, j, Finset.mem_range.2 hj, hcon⟩

end LatticeProb
