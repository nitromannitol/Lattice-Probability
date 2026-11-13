import Mathlib

/-!
# Integrals against measures on `ℝ≥0` converge when the distribution functions converge

Let `μ k` and `ν` be finite measures on `ℝ≥0` and `T ≥ 0`. If `μ k (Iic t) → ν (Iic t)` for every `t ∈ [0, T]`, then
`∫_{[0, T]} h dμ k → ∫_{[0, T]} h dν` for every function `h` continuous on `[0, T]` (the Helly-Bray theorem on a
compact interval). The convergence of the distribution functions is assumed at every point of `[0, T]`, including
`0`, so no continuity of the limit distribution function is needed. The proof approximates `h` uniformly on `[0, T]`
by the step function `t ↦ h (⌈t / Δ⌉₊ Δ)` on a grid of mesh `Δ = T / N`, whose integrals are finite combinations of
the masses `μ (Iic (j Δ)) - μ (Iic ((j - 1) Δ))`.

A typical use: `μ k` is the Stieltjes measure of a nondecreasing clock `F_k` and `ν` that of a clock `Φ` with
`F_k → Φ` pointwise on `[0, T]`; then `∫_{[0,T]} g(b_u) dF_k(u) → ∫_{[0,T]} g(b_u) dΦ(u)` for every path `b` and every
continuous `g`.

## Main results

* `Icc_inter_ceil_div_eq`: the cells `{t ∈ [0, N Δ] : ⌈t / Δ⌉₊ = j}` of the grid of mesh `Δ`;
* `tendsto_setIntegral_Icc_of_tendsto_measureReal_Iic`: the convergence of the integrals.
-/

namespace LatticeProb.Prob

open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal

/-- The cells of the grid of mesh `Δ` on `[0, N Δ]`: the points `t` with `⌈t / Δ⌉₊ = j` form `{0}` for `j = 0` and
the interval `((j - 1) Δ, j Δ]` for `1 ≤ j ≤ N`, written as a difference of half-lines. -/
theorem Icc_inter_ceil_div_eq (Δ : ℝ≥0) (N j : ℕ) (hj : j ≤ N) :
    Icc 0 ((N : ℝ≥0) * Δ) ∩ {t | ⌈t / Δ⌉₊ = j} =
      if j = 0 then Iic 0 else Iic ((j : ℝ≥0) * Δ) \ Iic (((j - 1 : ℕ) : ℝ≥0) * Δ) := by
  rcases eq_or_ne Δ 0 with rfl | hΔ
  · split_ifs with hj0
    · subst hj0
      ext t
      simp
    · ext t
      simp [Ne.symm hj0]
  · have hΔ' : 0 < Δ := pos_iff_ne_zero.2 hΔ
    split_ifs with hj0
    · subst hj0
      ext t
      simp only [mem_inter_iff, mem_Icc, Set.mem_ofPred_eq, mem_Iic, Nat.ceil_eq_zero, nonpos_iff_eq_zero,
        div_eq_zero_iff, hΔ, or_false, zero_le, true_and]
      exact ⟨fun h => h.2, fun h => ⟨h ▸ zero_le, h⟩⟩
    · have hjN : (j : ℝ≥0) * Δ ≤ (N : ℝ≥0) * Δ :=
        mul_le_mul_of_nonneg_right (by exact_mod_cast hj) zero_le
      ext t
      simp only [mem_inter_iff, mem_Icc, Set.mem_ofPred_eq, Set.mem_sdiff, mem_Iic, not_le, Nat.ceil_eq_iff hj0]
      rw [lt_div_iff₀ hΔ', div_le_iff₀ hΔ']
      exact ⟨fun ⟨_, h1, h2⟩ => ⟨h2, h1⟩, fun ⟨h2, h1⟩ => ⟨⟨zero_le, h2.trans hjN⟩, h1, h2⟩⟩

/-- **Convergence of integrals from the convergence of the distribution functions on a compact interval.** Let
`μ k` and `ν` be finite measures on `ℝ≥0` with `μ k (Iic t) → ν (Iic t)` for every `t ≤ T`. Then
`∫_{[0, T]} h dμ k → ∫_{[0, T]} h dν` for every `h` continuous on `[0, T]`. -/
theorem tendsto_setIntegral_Icc_of_tendsto_measureReal_Iic {μ : ℕ → Measure ℝ≥0} {ν : Measure ℝ≥0}
    [∀ k, IsFiniteMeasure (μ k)] [IsFiniteMeasure ν] {T : ℝ≥0}
    (hcdf : ∀ t ≤ T, Tendsto (fun k => (μ k).real (Iic t)) atTop (𝓝 (ν.real (Iic t))))
    {h : ℝ≥0 → ℝ} (hh : ContinuousOn h (Icc 0 T)) :
    Tendsto (fun k => ∫ t in Icc 0 T, h t ∂(μ k)) atTop (𝓝 (∫ t in Icc 0 T, h t ∂ν)) := by
  have hIT : Icc (0 : ℝ≥0) T = Iic T := by ext t; simp
  have huc : UniformContinuousOn h (Icc 0 T) := isCompact_Icc.uniformContinuousOn_of_continuous hh
  rw [hIT] at huc ⊢
  rw [Metric.tendsto_atTop]
  intro η hη
  -- a bound on the masses of `[0, T]`
  have hνT : 0 ≤ ν.real (Iic T) := measureReal_nonneg
  have hB : 0 < ν.real (Iic T) + 1 := by linarith
  obtain ⟨K₀, hK₀⟩ : ∃ K₀, ∀ k ≥ K₀, (μ k).real (Iic T) ≤ ν.real (Iic T) + 1 := by
    obtain ⟨K₀, hK₀⟩ := eventually_atTop.1 ((hcdf T le_rfl).eventually (gt_mem_nhds (lt_add_one _)))
    exact ⟨K₀, fun k hk => (hK₀ k hk).le⟩
  obtain ⟨ε', hε'⟩ : ∃ ε' : ℝ, ε' = η / (3 * (ν.real (Iic T) + 1)) := ⟨_, rfl⟩
  have hε'0 : 0 < ε' := by rw [hε']; positivity
  have hε'B : ε' * (ν.real (Iic T) + 1) = η / 3 := by
    rw [hε']; field_simp
  obtain ⟨δ, hδ, hδh⟩ := Metric.uniformContinuousOn_iff.1 huc ε' hε'0
  -- the grid of mesh `Δ = T / N < δ`
  obtain ⟨N, hN⟩ := exists_nat_gt ((T : ℝ) / δ)
  have hN0 : N ≠ 0 := by
    rintro rfl
    simp only [Nat.cast_zero] at hN
    linarith [div_nonneg T.coe_nonneg hδ.le]
  have hN' : (N : ℝ≥0) ≠ 0 := Nat.cast_ne_zero.2 hN0
  obtain ⟨Δ, hΔ⟩ : ∃ Δ : ℝ≥0, Δ = T / N := ⟨_, rfl⟩
  have hNΔ : (N : ℝ≥0) * Δ = T := by rw [hΔ]; field_simp
  have hΔδ : (Δ : ℝ) < δ := by
    have hNpos : (0 : ℝ) < N := Nat.cast_pos.2 (Nat.pos_of_ne_zero hN0)
    rw [hΔ, NNReal.coe_div, NNReal.coe_natCast, div_lt_iff₀ hNpos]
    rw [div_lt_iff₀ hδ] at hN
    linarith
  have hgridT : ∀ j : ℕ, j ≤ N → (j : ℝ≥0) * Δ ≤ T := fun j hj => by
    rw [← hNΔ]; exact mul_le_mul_of_nonneg_right (by exact_mod_cast hj) zero_le
  -- the grid point `⌈t / Δ⌉₊ Δ` of `t ∈ [0, T]`
  have hgrid : ∀ t ∈ Iic T, ⌈t / Δ⌉₊ ≤ N ∧ dist t ((⌈t / Δ⌉₊ : ℝ≥0) * Δ) < δ := by
    intro t ht
    rcases eq_or_ne Δ 0 with h0 | h0
    · have hT0 : T = 0 := by rw [← hNΔ, h0, mul_zero]
      have ht0 : t = 0 := le_antisymm (hT0 ▸ ht) zero_le
      simp [h0, ht0, hδ]
    · have hΔ0 : 0 < Δ := pos_iff_ne_zero.2 h0
      refine ⟨Nat.ceil_le.2 ?_, ?_⟩
      · rw [div_le_iff₀ hΔ0, hNΔ]
        exact ht
      · have h1 : t ≤ (⌈t / Δ⌉₊ : ℝ≥0) * Δ := (div_le_iff₀ hΔ0).1 (Nat.le_ceil _)
        have h2 : (⌈t / Δ⌉₊ : ℝ≥0) * Δ < t + Δ := by
          have h3 := Nat.ceil_lt_add_one ((zero_le : (0 : ℝ≥0) ≤ t / Δ))
          calc (⌈t / Δ⌉₊ : ℝ≥0) * Δ < (t / Δ + 1) * Δ := (mul_lt_mul_iff_left₀ hΔ0).2 h3
            _ = t + Δ := by rw [add_mul, div_mul_cancel₀ _ h0, one_mul]
        have h1' : (t : ℝ) ≤ (⌈t / Δ⌉₊ : ℝ) * Δ := by exact_mod_cast h1
        have h2' : (⌈t / Δ⌉₊ : ℝ) * Δ < t + Δ := by exact_mod_cast h2
        rw [NNReal.dist_eq, NNReal.coe_mul, NNReal.coe_natCast, abs_sub_lt_iff]
        constructor <;> linarith
  -- the step function
  have hmeasj : ∀ j : ℕ, MeasurableSet {t : ℝ≥0 | ⌈t / Δ⌉₊ = j} := fun j =>
    (measurable_id.div_const Δ).nat_ceil (measurableSet_singleton j)
  obtain ⟨S, hS⟩ : ∃ S : ℝ≥0 → ℝ, S = fun t => ∑ j ∈ Finset.range (N + 1),
      {t : ℝ≥0 | ⌈t / Δ⌉₊ = j}.indicator (fun _ => h ((j : ℝ≥0) * Δ)) t := ⟨_, rfl⟩
  have hSeq : ∀ t ∈ Iic T, S t = h ((⌈t / Δ⌉₊ : ℝ≥0) * Δ) := by
    intro t ht
    rw [hS]
    dsimp only
    rw [Finset.sum_eq_single ⌈t / Δ⌉₊]
    · exact Set.indicator_of_mem (by simp) _
    · intro j _ hj
      exact Set.indicator_of_notMem (show t ∉ {t : ℝ≥0 | ⌈t / Δ⌉₊ = j} from fun h' => hj (Eq.symm h')) _
    · intro hnot
      exact absurd (Finset.mem_range.2 (Nat.lt_succ_of_le (hgrid t ht).1)) hnot
  have hSint : ∀ (m : Measure ℝ≥0) [IsFiniteMeasure m], ∫ t in Iic T, S t ∂m =
      ∑ j ∈ Finset.range (N + 1), m.real (Iic T ∩ {t : ℝ≥0 | ⌈t / Δ⌉₊ = j}) * h ((j : ℝ≥0) * Δ) := by
    intro m _
    rw [hS]
    rw [integral_finsetSum _ (fun j _ => (integrable_const _).indicator (hmeasj j))]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [integral_indicator_const _ (hmeasj j), measureReal_restrict_apply (hmeasj j), smul_eq_mul,
      inter_comm]
  have hSintegrable : ∀ (m : Measure ℝ≥0) [IsFiniteMeasure m], IntegrableOn S (Iic T) m := by
    intro m _
    rw [hS]
    exact integrable_finsetSum _ (fun j _ => (integrable_const _).indicator (hmeasj j))
  -- convergence of the masses of the cells
  have hcell : ∀ j ∈ Finset.range (N + 1),
      Tendsto (fun k => (μ k).real (Iic T ∩ {t : ℝ≥0 | ⌈t / Δ⌉₊ = j})) atTop
        (𝓝 (ν.real (Iic T ∩ {t : ℝ≥0 | ⌈t / Δ⌉₊ = j}))) := by
    intro j hj
    have hjN : j ≤ N := Nat.lt_succ_iff.1 (Finset.mem_range.1 hj)
    have hset : Iic T ∩ {t : ℝ≥0 | ⌈t / Δ⌉₊ = j} =
        if j = 0 then Iic 0 else Iic ((j : ℝ≥0) * Δ) \ Iic (((j - 1 : ℕ) : ℝ≥0) * Δ) := by
      rw [← hIT, ← hNΔ]
      exact Icc_inter_ceil_div_eq Δ N j hjN
    rw [hset]
    split_ifs with hj0
    · exact hcdf 0 zero_le
    · have hsub : Iic (((j - 1 : ℕ) : ℝ≥0) * Δ) ⊆ Iic ((j : ℝ≥0) * Δ) :=
        Iic_subset_Iic.2 (mul_le_mul_of_nonneg_right (by exact_mod_cast Nat.sub_le j 1) zero_le)
      have hd : ∀ (m : Measure ℝ≥0) [IsFiniteMeasure m],
          m.real (Iic ((j : ℝ≥0) * Δ) \ Iic (((j - 1 : ℕ) : ℝ≥0) * Δ)) =
            m.real (Iic ((j : ℝ≥0) * Δ)) - m.real (Iic (((j - 1 : ℕ) : ℝ≥0) * Δ)) :=
        fun m _ => measureReal_sdiff hsub measurableSet_Iic
      have hfun : (fun k => (μ k).real (Iic ((j : ℝ≥0) * Δ) \ Iic (((j - 1 : ℕ) : ℝ≥0) * Δ))) =
          fun k => (μ k).real (Iic ((j : ℝ≥0) * Δ)) - (μ k).real (Iic (((j - 1 : ℕ) : ℝ≥0) * Δ)) :=
        funext fun k => hd (μ k)
      rw [hfun, hd ν]
      exact (hcdf _ (hgridT j hjN)).sub (hcdf _ (hgridT _ ((Nat.sub_le j 1).trans hjN)))
  have hSconv : Tendsto (fun k => ∫ t in Iic T, S t ∂(μ k)) atTop (𝓝 (∫ t in Iic T, S t ∂ν)) := by
    have hfun : (fun k => ∫ t in Iic T, S t ∂(μ k)) = fun k => ∑ j ∈ Finset.range (N + 1),
        (μ k).real (Iic T ∩ {t : ℝ≥0 | ⌈t / Δ⌉₊ = j}) * h ((j : ℝ≥0) * Δ) :=
      funext fun k => hSint (μ k)
    rw [hfun, hSint ν]
    exact tendsto_finsetSum _ fun j hj => (hcell j hj).mul_const _
  -- the step function is uniformly `ε'`-close to `h` on `[0, T]`
  have hhS : ∀ t ∈ Iic T, ‖h t - S t‖ ≤ ε' := by
    intro t ht
    rw [hSeq t ht, Real.norm_eq_abs, ← Real.dist_eq]
    exact (hδh t ht _ (hgridT _ (hgrid t ht).1) (hgrid t ht).2).le
  have hmI : ∀ (m : Measure ℝ≥0) [IsFiniteMeasure m],
      |∫ t in Iic T, h t ∂m - ∫ t in Iic T, S t ∂m| ≤ ε' * m.real (Iic T) := by
    intro m _
    have hhi : IntegrableOn h (Iic T) m := by
      rw [← hIT]
      exact hh.integrableOn_compact isCompact_Icc
    rw [← integral_sub hhi (hSintegrable m), ← Real.norm_eq_abs]
    exact norm_setIntegral_le_of_norm_le_const (measure_lt_top _ _) hhS
  obtain ⟨K₁, hK₁⟩ := Metric.tendsto_atTop.1 hSconv (η / 3) (by positivity)
  refine ⟨max K₀ K₁, fun k hk => ?_⟩
  have hk0 := hK₀ k (le_of_max_le_left hk)
  have hk1 := hK₁ k (le_of_max_le_right hk)
  rw [Real.dist_eq] at hk1 ⊢
  have e1 := abs_le.1 (hmI (μ k))
  have e2 := abs_le.1 (hmI ν)
  have e3 := abs_lt.1 hk1
  have b1 : ε' * (μ k).real (Iic T) ≤ η / 3 :=
    (mul_le_mul_of_nonneg_left hk0 hε'0.le).trans hε'B.le
  have b2 : ε' * ν.real (Iic T) ≤ η / 3 :=
    (mul_le_mul_of_nonneg_left (by linarith) hε'0.le).trans hε'B.le
  rw [abs_lt]
  constructor <;> linarith [e1.1, e1.2, e2.1, e2.2, e3.1, e3.2]

end LatticeProb.Prob
