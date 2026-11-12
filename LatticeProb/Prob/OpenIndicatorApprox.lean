import Mathlib

/-!
# Monotone continuous approximation of the indicator of an increasing union of open sets

For an increasing sequence `U n` of open subsets of a pseudo-metric space there are continuous functions
`f n : X → [0, 1]`, increasing in `n`, with `f n` vanishing outside `U n` and `f n x → 1_{⋃ U n} x` for
every `x`.  They are `f n x = min 1 ((n + 1) dist (x, (U n)ᶜ))`.

## Main statement

* `LatticeProb.exists_monotone_continuous_tendsto_indicator_iUnion`.
-/

open Filter Topology Metric Set

namespace LatticeProb

/-- Monotone continuous functions with values in `[0, 1]`, supported in `U n`, converging pointwise to the
indicator of `⋃ n, U n`, for an increasing sequence `U n` of open subsets of a pseudo-metric space. -/
theorem exists_monotone_continuous_tendsto_indicator_iUnion {X : Type*} [PseudoMetricSpace X]
    (U : ℕ → Set X) (hU : ∀ n, IsOpen (U n)) (hmono : Monotone U) :
    ∃ f : ℕ → X → ℝ, (∀ n, Continuous (f n)) ∧ (∀ n x, 0 ≤ f n x ∧ f n x ≤ 1) ∧
      (∀ n x, f n x ≠ 0 → x ∈ U n) ∧ (∀ x, Monotone fun n => f n x) ∧
      ∀ x, Tendsto (fun n => f n x) atTop (𝓝 ((⋃ n, U n).indicator (1 : X → ℝ) x)) := by
  classical
  let f : ℕ → X → ℝ := fun n x =>
    if (U n)ᶜ.Nonempty then min 1 (((n : ℝ) + 1) * infDist x (U n)ᶜ) else 1
  have hfp : ∀ n x, (U n)ᶜ.Nonempty → f n x = min 1 (((n : ℝ) + 1) * infDist x (U n)ᶜ) :=
    fun n x h => by simp [f, h]
  have hfe : ∀ n x, ¬ (U n)ᶜ.Nonempty → f n x = 1 := fun n x h => by simp [f, h]
  have hemp : ∀ n, ¬ (U n)ᶜ.Nonempty → U n = univ := fun n h => by
    rwa [not_nonempty_iff_eq_empty, compl_empty_iff] at h
  have hbd : ∀ n x, 0 ≤ f n x ∧ f n x ≤ 1 := fun n x => by
    by_cases h : (U n)ᶜ.Nonempty
    · rw [hfp n x h]
      exact ⟨le_min zero_le_one (mul_nonneg (by positivity) infDist_nonneg), min_le_left _ _⟩
    · rw [hfe n x h]; exact ⟨zero_le_one, le_rfl⟩
  have hsupp : ∀ n x, f n x ≠ 0 → x ∈ U n := fun n x hx => by
    by_cases h : (U n)ᶜ.Nonempty
    · by_contra hxU
      rw [hfp n x h, infDist_zero_of_mem (show x ∈ (U n)ᶜ from hxU), mul_zero] at hx
      exact hx (min_eq_right zero_le_one)
    · rw [hemp n h]; exact mem_univ x
  refine ⟨f, fun n => ?_, hbd, hsupp, fun x => ?_, fun x => ?_⟩
  · by_cases h : (U n)ᶜ.Nonempty
    · have : f n = fun x => min 1 (((n : ℝ) + 1) * infDist x (U n)ᶜ) := funext fun x => hfp n x h
      rw [this]
      exact continuous_const.min (continuous_const.mul (continuous_infDist_pt _))
    · have : f n = fun _ => 1 := funext fun x => hfe n x h
      rw [this]; exact continuous_const
  · refine monotone_nat_of_le_succ fun n => ?_
    by_cases h : (U n)ᶜ.Nonempty
    · by_cases h' : (U (n + 1))ᶜ.Nonempty
      · rw [hfp n x h, hfp (n + 1) x h']
        have hd : infDist x (U n)ᶜ ≤ infDist x (U (n + 1))ᶜ :=
          infDist_le_infDist_of_subset (compl_subset_compl.2 (hmono (Nat.le_succ n))) h'
        push_cast
        exact min_le_min le_rfl (mul_le_mul (by linarith) hd infDist_nonneg (by positivity))
      · rw [hfe (n + 1) x h']; exact (hbd n x).2
    · have h1 := hemp n h
      have h' : ¬ (U (n + 1))ᶜ.Nonempty := fun hh => h (by
        obtain ⟨y, hy⟩ := hh
        exact ⟨y, fun hyU => hy (hmono (Nat.le_succ n) hyU)⟩)
      rw [hfe n x h, hfe (n + 1) x h']
  · by_cases hx : x ∈ ⋃ n, U n
    · rw [indicator_of_mem hx, Pi.one_apply]
      obtain ⟨N, hN⟩ := mem_iUnion.1 hx
      by_cases hNe : (U N)ᶜ.Nonempty
      · have hpos : 0 < infDist x (U N)ᶜ :=
          ((hU N).isClosed_compl.notMem_iff_infDist_pos hNe).1 (fun hh => hh hN)
        obtain ⟨n0, hn0⟩ := exists_nat_ge (1 / infDist x (U N)ᶜ)
        refine tendsto_atTop_of_eventually_const (i₀ := max N n0) fun n hn => ?_
        by_cases h : (U n)ᶜ.Nonempty
        · rw [hfp n x h]
          have hd : infDist x (U N)ᶜ ≤ infDist x (U n)ᶜ :=
            infDist_le_infDist_of_subset (compl_subset_compl.2 (hmono ((le_max_left _ _).trans hn))) h
          have hn1 : (n0 : ℝ) ≤ n := Nat.cast_le.2 ((le_max_right _ _).trans hn)
          have : 1 ≤ ((n : ℝ) + 1) * infDist x (U n)ᶜ := by
            calc (1 : ℝ) = (1 / infDist x (U N)ᶜ) * infDist x (U N)ᶜ := by field_simp
              _ ≤ ((n : ℝ) + 1) * infDist x (U N)ᶜ :=
                mul_le_mul_of_nonneg_right (by linarith) hpos.le
              _ ≤ ((n : ℝ) + 1) * infDist x (U n)ᶜ := mul_le_mul_of_nonneg_left hd (by positivity)
          exact min_eq_left this
        · exact hfe n x h
      · exact tendsto_atTop_of_eventually_const (i₀ := N) fun n hn => hfe n x fun h => hNe
          (by obtain ⟨y, hy⟩ := h; exact ⟨y, fun hyU => hy (hmono hn hyU)⟩)
    · rw [indicator_of_notMem hx]
      refine tendsto_const_nhds.congr fun n => ?_
      by_contra hne
      exact hx (mem_iUnion.2 ⟨n, hsupp n x (Ne.symm hne)⟩)

end LatticeProb
