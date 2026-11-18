import Mathlib

/-!
# From "almost surely eventually along every sequence" to a bound at every small scale

Let `M ε` be a family of **measurable** sets indexed by a scale `ε > 0`. If, for every sequence
`e n → 0` of positive scales, almost every `ω` lies in `M (e n)` for all large `n`, then for every
`θ > 0` there is `ε₀ > 0` with `P (M ε)ᶜ ≤ θ` for all `ε < ε₀` (a reverse Fatou argument along
a bad sequence).

Measurability of the sets `M ε` cannot be dropped: for non-measurable families (for instance
`M e := (V e)ᶜ` for a partition of `[0,1]` into continuum many sets of full outer measure) the
hypothesis holds while every `P (M ε)ᶜ` is `1`.
-/

open MeasureTheory Filter Topology
open scoped ENNReal

namespace LatticeProb

/-- **Reverse Fatou along a bad sequence.** If the measurable events `M ε` hold almost surely
eventually along every positive sequence tending to `0`, then their complements have probability at
most `θ` for all sufficiently small `ε`. -/
theorem exists_eps_measure_compl_le_of_ae_eventually {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsFiniteMeasure P] (M : ℝ → Set Ω)
    (hM : ∀ ε, 0 < ε → MeasurableSet (M ε))
    (h : ∀ e : ℕ → ℝ, (∀ n, 0 < e n) → Tendsto e atTop (𝓝 0) →
      ∀ᵐ ω ∂P, ∀ᶠ n in atTop, ω ∈ M (e n))
    {θ : ℝ} (hθ : 0 < θ) :
    ∃ ε₀ > 0, ∀ ε, 0 < ε → ε < ε₀ → P (M ε)ᶜ ≤ ENNReal.ofReal θ := by
  by_contra hcon
  push Not at hcon
  choose e he0 he1 hePM using fun n : ℕ => hcon (1 / ((n : ℝ) + 1)) (by positivity)
  have hetend : Tendsto e atTop (𝓝 0) :=
    squeeze_zero (fun n => (he0 n).le) (fun n => (he1 n).le) tendsto_one_div_add_atTop_nhds_zero_nat
  set B : ℕ → Set Ω := fun n => ⋃ k ≥ n, (M (e k))ᶜ with hB
  have hBmeas : ∀ n, MeasurableSet (B n) := fun n =>
    MeasurableSet.biUnion (Set.to_countable _) fun k _ => (hM _ (he0 k)).compl
  have hBanti : Antitone B := by
    intro m n hmn x hx
    simp only [hB, Set.mem_iUnion] at hx ⊢
    obtain ⟨k, hk, hx⟩ := hx
    exact ⟨k, hmn.trans hk, hx⟩
  have hlim : Tendsto (P ∘ B) atTop (𝓝 (P (⋂ n, B n))) :=
    tendsto_measure_iInter_atTop (fun n => (hBmeas n).nullMeasurableSet) hBanti
      ⟨0, measure_ne_top P _⟩
  have hnull : P (⋂ n, B n) = 0 := by
    refine measure_mono_null ?_ (ae_iff.1 (h e he0 hetend))
    intro ω hω
    simp only [Set.mem_iInter, hB, Set.mem_iUnion] at hω
    show ¬ ∀ᶠ n in atTop, ω ∈ M (e n)
    rw [not_eventually, frequently_atTop]
    intro n
    obtain ⟨k, hk, hωk⟩ := hω n
    exact ⟨k, hk, hωk⟩
  rw [hnull] at hlim
  obtain ⟨n, hn⟩ := (hlim.eventually (gt_mem_nhds (ENNReal.ofReal_pos.2 hθ))).exists
  have hsub : (M (e n))ᶜ ⊆ B n := fun x hx => by
    simp only [hB, Set.mem_iUnion]
    exact ⟨n, le_refl n, hx⟩
  exact absurd (lt_of_lt_of_le (hePM n) (measure_mono hsub)) (not_lt.2 hn.le)

end LatticeProb
