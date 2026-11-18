import Mathlib

/-!
# Infinitely many successes of trials with a uniform conditional failure bound

Let `𝓖 j` be a nondecreasing sequence of σ-algebras and let the `j`-th trial `S j` be decided by
time `j + 1`, i.e. `S j ∈ 𝓖 (j + 1)`. Suppose that, whatever happened up to time `j`, the `j`-th
trial fails with probability at most `q < 1`:
`μ (E ∩ (S j)ᶜ) ≤ q μ E` for every `E ∈ 𝓖 j`.
Then `n` consecutive trials all fail with probability at most `q ^ n`, and almost surely
infinitely many trials succeed. This is the form in which the strong Markov property at a
sequence of stopping times `σ j` (with `σ j + 1 ≤ σ (j + 1)`) delivers a success bound that
is uniform in the starting point, and no conditional expectations are needed.

For a nondecreasing `F` whose increments over the disjoint intervals `[σ j, σ j + 1]` exceed a
fixed `c > 0` infinitely often, `F t → ∞`
(`LatticeProb.tendsto_atTop_of_frequently_lt_increment`).

## Main results

* `LatticeProb.measure_iInter_range_compl_le_pow`: the geometric bound for `n` consecutive
  failures.
* `LatticeProb.ae_frequently_mem_of_measure_inter_compl_le`: almost surely infinitely many
  successes.
* `LatticeProb.tendsto_atTop_of_frequently_lt_increment`: divergence of a nondecreasing function
  with infinitely many increments above `c` along separated times.
-/

open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology

namespace LatticeProb

variable {Ω : Type*} {m : MeasurableSpace Ω} {μ : Measure Ω}

/-- **Geometric bound.** If the `j`-th trial `S j ∈ 𝓖 (j + 1)` fails with conditional
probability at most `q` given `𝓖 j`, in the sense `μ (E ∩ (S j)ᶜ) ≤ q μ E` for `E ∈ 𝓖 j`, then
the `n` consecutive trials `S J, …, S (J + n - 1)` all fail with probability at most
`q ^ n μ univ`. -/
theorem measure_iInter_range_compl_le_pow (𝓖 : ℕ → MeasurableSpace Ω) (h𝓖 : Monotone 𝓖)
    {S : ℕ → Set Ω} (hS : ∀ j, MeasurableSet[𝓖 (j + 1)] (S j)) {q : ℝ≥0∞}
    (htrial : ∀ j E, MeasurableSet[𝓖 j] E → μ (E ∩ (S j)ᶜ) ≤ q * μ E) (J n : ℕ) :
    μ (⋂ i ∈ Finset.range n, (S (J + i))ᶜ) ≤ q ^ n * μ univ := by
  have key : ∀ n : ℕ, MeasurableSet[𝓖 (J + n)] (⋂ i ∈ Finset.range n, (S (J + i))ᶜ) ∧
      μ (⋂ i ∈ Finset.range n, (S (J + i))ᶜ) ≤ q ^ n * μ univ := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      have heq : (⋂ i ∈ Finset.range (n + 1), (S (J + i))ᶜ) =
          (⋂ i ∈ Finset.range n, (S (J + i))ᶜ) ∩ (S (J + n))ᶜ := by
        rw [Finset.range_add_one, Finset.set_biInter_insert, Set.inter_comm]
      rw [heq]
      refine ⟨?_, ?_⟩
      · exact (h𝓖 (Nat.le_succ (J + n)) _ ih.1).inter (hS (J + n)).compl
      · calc μ ((⋂ i ∈ Finset.range n, (S (J + i))ᶜ) ∩ (S (J + n))ᶜ)
            ≤ q * μ (⋂ i ∈ Finset.range n, (S (J + i))ᶜ) := htrial (J + n) _ ih.1
          _ ≤ q * (q ^ n * μ univ) := by gcongr; exact ih.2
          _ = q ^ (n + 1) * μ univ := by ring
  exact (key n).2

/-- **Infinitely many successes.** If the `j`-th trial `S j ∈ 𝓖 (j + 1)` fails with conditional
probability at most `q < 1` given `𝓖 j` (`μ (E ∩ (S j)ᶜ) ≤ q μ E` for `E ∈ 𝓖 j`), then almost
surely infinitely many trials succeed. -/
theorem ae_frequently_mem_of_measure_inter_compl_le [IsFiniteMeasure μ]
    (𝓖 : ℕ → MeasurableSpace Ω) (h𝓖 : Monotone 𝓖) {S : ℕ → Set Ω}
    (hS : ∀ j, MeasurableSet[𝓖 (j + 1)] (S j)) {q : ℝ≥0∞} (hq : q < 1)
    (htrial : ∀ j E, MeasurableSet[𝓖 j] E → μ (E ∩ (S j)ᶜ) ≤ q * μ E) :
    ∀ᵐ ω ∂μ, ∃ᶠ j in atTop, ω ∈ S j := by
  have hlim : Tendsto (fun n : ℕ => q ^ n * μ univ) atTop (𝓝 0) := by
    have := ENNReal.Tendsto.mul_const (ENNReal.tendsto_pow_atTop_nhds_zero_of_lt_one hq)
      (Or.inr (measure_ne_top μ univ))
    rwa [zero_mul] at this
  have hJ : ∀ J, μ (⋂ i, (S (J + i))ᶜ) = 0 := by
    intro J
    refine le_antisymm (ge_of_tendsto' hlim fun n => ?_) zero_le
    refine (measure_mono fun ω hω => ?_).trans
      (measure_iInter_range_compl_le_pow 𝓖 h𝓖 hS htrial J n)
    exact mem_iInter₂.2 fun i _ => mem_iInter.1 hω i
  rw [ae_iff]
  refine measure_mono_null (fun ω hω => ?_) (measure_iUnion_null hJ)
  obtain ⟨J, hJ'⟩ := eventually_atTop.1 (Filter.not_frequently.1 hω)
  exact mem_iUnion.2 ⟨J, mem_iInter.2 fun i => hJ' (J + i) (Nat.le_add_right J i)⟩

/-- **Divergence from infinitely many separated increments.** Let `F` be nondecreasing and let
the times `σ j` satisfy `σ j + 1 ≤ σ (j + 1)`. If `F (σ j + 1) - F (σ j) > c > 0` for
infinitely many `j`, then `F t → ∞` as `t → ∞`. -/
theorem tendsto_atTop_of_frequently_lt_increment {F : ℝ≥0 → ℝ} (hF : Monotone F)
    {σ : ℕ → ℝ≥0} (hσ : ∀ j, σ j + 1 ≤ σ (j + 1)) {c : ℝ} (hc : 0 < c)
    (hfreq : ∃ᶠ j in atTop, c < F (σ j + 1) - F (σ j)) :
    Tendsto F atTop atTop := by
  have hσm : Monotone σ :=
    monotone_nat_of_le_succ fun j => le_trans (le_add_of_nonneg_right zero_le_one) (hσ j)
  have hstep : ∀ n : ℕ, ∃ J, F (σ 0) + n * c ≤ F (σ J) := by
    intro n
    induction n with
    | zero => exact ⟨0, by simp⟩
    | succ n ih =>
      obtain ⟨J, hJ⟩ := ih
      obtain ⟨j, hjJ, hj⟩ := (frequently_atTop.1 hfreq) J
      refine ⟨j + 1, ?_⟩
      have h1 : F (σ J) ≤ F (σ j) := hF (hσm hjJ)
      have h2 : F (σ j + 1) ≤ F (σ (j + 1)) := hF (hσ j)
      push_cast
      linarith
  refine tendsto_atTop_atTop_of_monotone hF fun b => ?_
  obtain ⟨n, hn⟩ := exists_nat_ge ((b - F (σ 0)) / c)
  obtain ⟨J, hJ⟩ := hstep n
  refine ⟨σ J, ?_⟩
  have : b - F (σ 0) ≤ n * c := by rwa [div_le_iff₀ hc] at hn
  linarith

end LatticeProb
