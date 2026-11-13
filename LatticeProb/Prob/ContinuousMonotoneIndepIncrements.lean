import Mathlib
import LatticeProb.Prob.IndepLaplaceRatio

/-!
# A continuous nondecreasing process with independent increments has deterministic increments

Let `A : ℝ → Ω → ℝ` be a family of random variables such that, for every `ω`, `u ↦ A u ω` is
continuous and nondecreasing on `[s, t]`.  Suppose that for every `n` the increments of `A` over
the `n + 1` cells of the uniform partition of `[s, t]` are independent.  Then `A t - A s` is
almost surely constant.

The proof applies the second-moment bound `LatticeProb.mgf_sum_neg_two_le` to the increments of
the `n`-th partition: by uniform continuity of the paths, the probability that all increments are
at most `c` tends to `1`, and by independence this probability is at most `exp (-∑ P[Iₖ > c])`,
so `∑ₖ P[Iₖ > c] → 0`.  Hence `E e^{-2I} ≤ (E e^{-I})²` for `I = A t - A s`, so that the variance
of `e^{-I}` vanishes.

* `LatticeProb.cellPoint`, `LatticeProb.cellIncrement`: the uniform partition and its increments.
* `LatticeProb.tendsto_sum_measureReal_cellIncrement_gt`: `∑ₖ P[Iₖ > c] → 0`.
* `LatticeProb.ae_eq_const_of_monotone_continuous_indepIncrements`: the conclusion.
-/

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Filter Topology

namespace LatticeProb

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}

/-- The `j`-th point of the uniform partition of `[s, t]` into `n + 1` cells. -/
noncomputable def cellPoint (s t : ℝ) (n j : ℕ) : ℝ := s + (j : ℝ) * ((t - s) / ((n : ℝ) + 1))

/-- The increment of `A` over the `k`-th cell of the uniform partition of `[s, t]` into `n + 1`
cells. -/
noncomputable def cellIncrement (A : ℝ → Ω → ℝ) (s t : ℝ) (n k : ℕ) (ω : Ω) : ℝ :=
  A (cellPoint s t n (k + 1)) ω - A (cellPoint s t n k) ω

section cell

variable {A : ℝ → Ω → ℝ} {s t : ℝ}

theorem cellPoint_zero (n : ℕ) : cellPoint s t n 0 = s := by simp [cellPoint]

theorem cellPoint_last (n : ℕ) : cellPoint s t n (n + 1) = t := by
  have h : ((n : ℝ) + 1) ≠ 0 := by positivity
  unfold cellPoint
  push_cast
  field_simp
  ring

theorem cellPoint_mem (hst : s ≤ t) {n j : ℕ} (hj : j ≤ n + 1) :
    cellPoint s t n j ∈ Set.Icc s t := by
  have hh : 0 ≤ (t - s) / ((n : ℝ) + 1) := div_nonneg (sub_nonneg.2 hst) (by positivity)
  have hj' : (j : ℝ) ≤ (n : ℝ) + 1 := by exact_mod_cast hj
  have hnh : ((n : ℝ) + 1) * ((t - s) / ((n : ℝ) + 1)) = t - s := by
    have h : ((n : ℝ) + 1) ≠ 0 := by positivity
    field_simp
  refine ⟨?_, ?_⟩
  · unfold cellPoint
    have : 0 ≤ (j : ℝ) * ((t - s) / ((n : ℝ) + 1)) := by positivity
    linarith
  · unfold cellPoint
    have := mul_le_mul_of_nonneg_right hj' hh
    linarith

theorem cellPoint_le_succ (hst : s ≤ t) (n j : ℕ) : cellPoint s t n j ≤ cellPoint s t n (j + 1) := by
  have hh : 0 ≤ (t - s) / ((n : ℝ) + 1) := div_nonneg (sub_nonneg.2 hst) (by positivity)
  unfold cellPoint
  push_cast
  nlinarith

theorem cellPoint_succ_sub (n j : ℕ) :
    cellPoint s t n (j + 1) - cellPoint s t n j = (t - s) / ((n : ℝ) + 1) := by
  unfold cellPoint
  push_cast
  ring

theorem sum_cellIncrement (n : ℕ) (ω : Ω) :
    ∑ k : Fin (n + 1), cellIncrement A s t n k ω = A t ω - A s ω := by
  rw [Fin.sum_univ_eq_sum_range (fun k => cellIncrement A s t n k ω) (n + 1)]
  have h := Finset.sum_range_sub (fun k : ℕ => A (cellPoint s t n k) ω) (n + 1)
  rw [cellPoint_last, cellPoint_zero] at h
  exact h

theorem measurable_cellIncrement (hmeas : ∀ u, Measurable (A u)) (n k : ℕ) :
    Measurable (cellIncrement A s t n k) :=
  (hmeas _).sub (hmeas _)

theorem cellIncrement_nonneg (hst : s ≤ t)
    (hmono : ∀ ω, MonotoneOn (fun u => A u ω) (Set.Icc s t)) (n : ℕ) (k : Fin (n + 1)) (ω : Ω) :
    0 ≤ cellIncrement A s t n k ω := by
  unfold cellIncrement
  rw [sub_nonneg]
  exact hmono ω (cellPoint_mem hst (by omega)) (cellPoint_mem hst (by omega))
    (cellPoint_le_succ hst n k)

/-- By uniform continuity of the path on `[s, t]`, all increments over the `n`-th partition are
eventually at most `c`. -/
theorem eventually_cellIncrement_le (hst : s ≤ t)
    (hcont : ∀ ω, ContinuousOn (fun u => A u ω) (Set.Icc s t)) {c : ℝ} (hc : 0 < c) (ω : Ω) :
    ∀ᶠ n : ℕ in atTop, ∀ k : Fin (n + 1), cellIncrement A s t n k ω ≤ c := by
  have hu := (isCompact_Icc (a := s) (b := t)).uniformContinuousOn_of_continuous (hcont ω)
  rw [Metric.uniformContinuousOn_iff] at hu
  obtain ⟨δ, hδ, hδ'⟩ := hu c hc
  obtain ⟨N, hN⟩ := exists_nat_gt ((t - s) / δ)
  filter_upwards [eventually_ge_atTop N] with n hn k
  have hlt : (t - s) / ((n : ℝ) + 1) < δ := by
    rw [div_lt_iff₀ (by positivity)]
    rw [div_lt_iff₀ hδ] at hN
    have : (N : ℝ) ≤ n := by exact_mod_cast hn
    nlinarith
  have hh : 0 ≤ (t - s) / ((n : ℝ) + 1) := div_nonneg (sub_nonneg.2 hst) (by positivity)
  have hd : dist (cellPoint s t n (k + 1)) (cellPoint s t n k) < δ := by
    rw [Real.dist_eq, cellPoint_succ_sub, abs_of_nonneg hh]
    exact hlt
  have := hδ' _ (cellPoint_mem hst (by omega)) _ (cellPoint_mem hst (by omega)) hd
  rw [Real.dist_eq] at this
  exact (le_abs_self _).trans this.le

/-- By independence, the probability that all increments are at most `c` is at most
`exp (-∑ₖ P[Iₖ > c])`. -/
theorem measureReal_iInter_cellIncrement_le [IsProbabilityMeasure μ]
    (hmeas : ∀ u, Measurable (A u)) (n : ℕ)
    (hind : iIndepFun (fun k : Fin (n + 1) => cellIncrement A s t n k) μ) (c : ℝ) :
    μ.real (⋂ k : Fin (n + 1), {ω | cellIncrement A s t n k ω ≤ c}) ≤
      Real.exp (-∑ k : Fin (n + 1), μ.real {ω | c < cellIncrement A s t n k ω}) := by
  have h1 : μ (⋂ k : Fin (n + 1), {ω | cellIncrement A s t n k ω ≤ c}) =
      ∏ k : Fin (n + 1), μ {ω | cellIncrement A s t n k ω ≤ c} :=
    hind.meas_iInter (fun k => ⟨Set.Iic c, measurableSet_Iic, rfl⟩)
  have h2 : μ.real (⋂ k : Fin (n + 1), {ω | cellIncrement A s t n k ω ≤ c}) =
      ∏ k : Fin (n + 1), μ.real {ω | cellIncrement A s t n k ω ≤ c} := by
    simp only [measureReal_def]
    rw [h1, ENNReal.toReal_prod]
  have h3 : ∀ k : Fin (n + 1), μ.real {ω | cellIncrement A s t n k ω ≤ c} =
      1 - μ.real {ω | c < cellIncrement A s t n k ω} := by
    intro k
    have hm : MeasurableSet {ω | c < cellIncrement A s t n k ω} :=
      measurableSet_lt measurable_const (measurable_cellIncrement hmeas n k)
    have : {ω | cellIncrement A s t n k ω ≤ c} = {ω | c < cellIncrement A s t n k ω}ᶜ := by
      ext ω; simp
    rw [this, probReal_compl_eq_one_sub hm]
  rw [h2, ← Finset.sum_neg_distrib, Real.exp_sum]
  refine Finset.prod_le_prod₀ (fun k _ => measureReal_nonneg) (fun k _ => ?_)
  rw [h3 k]
  have := Real.add_one_le_exp (-μ.real {ω | c < cellIncrement A s t n k ω})
  linarith

/-- The sum of the tail probabilities of the increments tends to `0` along the uniform
partitions. -/
theorem tendsto_sum_measureReal_cellIncrement_gt [IsProbabilityMeasure μ] (hst : s ≤ t)
    (hmeas : ∀ u, Measurable (A u)) (hcont : ∀ ω, ContinuousOn (fun u => A u ω) (Set.Icc s t))
    (hind : ∀ n : ℕ, iIndepFun (fun k : Fin (n + 1) => cellIncrement A s t n k) μ)
    {c : ℝ} (hc : 0 < c) :
    Tendsto (fun n : ℕ => ∑ k : Fin (n + 1), μ.real {ω | c < cellIncrement A s t n k ω})
      atTop (𝓝 0) := by
  set E : ℕ → Set Ω := fun n => ⋂ k : Fin (n + 1), {ω | cellIncrement A s t n k ω ≤ c} with hE
  have hEm : ∀ n, MeasurableSet (E n) := fun n =>
    MeasurableSet.iInter fun k => measurableSet_le (measurable_cellIncrement hmeas n k)
      measurable_const
  have hlim : ∀ ω, ∀ᶠ n in atTop, ω ∈ E n ↔ ω ∈ (Set.univ : Set Ω) := by
    intro ω
    filter_upwards [eventually_cellIncrement_le hst hcont hc ω] with n hn
    simp only [hE, Set.mem_iInter, Set.mem_ofPred_eq, Set.mem_univ, iff_true]
    exact hn
  have h1 : Tendsto (fun n => μ (E n)) atTop (𝓝 (μ Set.univ)) :=
    tendsto_measure_of_tendsto_indicator_of_isFiniteMeasure atTop μ hEm hlim
  have h2 : Tendsto (fun n => μ.real (E n)) atTop (𝓝 1) := by
    have := (ENNReal.tendsto_toReal (measure_ne_top μ Set.univ)).comp h1
    simpa [measureReal_def, Function.comp_def] using this
  have h3 : Tendsto (fun n => -Real.log (μ.real (E n))) atTop (𝓝 0) := by
    have := ((Real.continuousAt_log one_ne_zero).tendsto.comp h2).neg
    simpa using this
  have hpos : ∀ᶠ n in atTop, 0 < μ.real (E n) := h2.eventually_const_lt one_pos
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds h3
    (Eventually.of_forall fun n => Finset.sum_nonneg fun k _ => measureReal_nonneg) ?_
  filter_upwards [hpos] with n hn
  have h4 := measureReal_iInter_cellIncrement_le hmeas n (hind n) c
  have h5 := Real.log_le_log hn h4
  rw [Real.log_exp] at h5
  linarith

end cell

section main

variable {A : ℝ → Ω → ℝ} {s t : ℝ}

/-- **A continuous nondecreasing process with independent increments has deterministic
increments.**  If, for every `ω`, `u ↦ A u ω` is continuous and nondecreasing on `[s, t]`, and for
every `n` the increments of `A` over the cells of the uniform partition of `[s, t]` into `n + 1`
cells are independent, then `A t - A s` is almost surely constant. -/
theorem ae_eq_const_of_monotone_continuous_indepIncrements [IsProbabilityMeasure μ]
    (hst : s ≤ t) (hmeas : ∀ u, Measurable (A u))
    (hcont : ∀ ω, ContinuousOn (fun u => A u ω) (Set.Icc s t))
    (hmono : ∀ ω, MonotoneOn (fun u => A u ω) (Set.Icc s t))
    (hind : ∀ n : ℕ, iIndepFun (fun k : Fin (n + 1) => cellIncrement A s t n k) μ) :
    ∃ c : ℝ, (fun ω => A t ω - A s ω) =ᵐ[μ] fun _ => c := by
  set X : Ω → ℝ := fun ω => A t ω - A s ω with hXdef
  have hXm : Measurable X := (hmeas t).sub (hmeas s)
  have hX0 : ∀ ω, 0 ≤ X ω := fun ω =>
    sub_nonneg.2 (hmono ω ⟨le_rfl, hst⟩ ⟨hst, le_rfl⟩ hst)
  have hS : ∀ n : ℕ, (∑ k : Fin (n + 1), cellIncrement A s t n k) = X := by
    intro n
    funext ω
    simp only [Finset.sum_apply]
    exact sum_cellIncrement n ω
  set L : ℝ := mgf X μ (-1) with hL
  have hLpos : 0 < L := mgf_pos (integrable_exp_mul_of_nonneg hXm hX0 (by norm_num))
  -- the bound for each `η`
  have hbound : ∀ η : ℝ, 0 < η → η < 1 → mgf X μ (-2) ≤
      L ^ 2 * Real.exp (L⁻¹ ^ 2 * (η * (-Real.log L))) := by
    intro η hη0 hη1
    have hc : 0 < -Real.log (1 - η) := by
      have : Real.log (1 - η) < 0 := Real.log_neg (by linarith) (by linarith)
      linarith
    have hn : ∀ n : ℕ, mgf X μ (-2) ≤ L ^ 2 * Real.exp (L⁻¹ ^ 2 * (η * (-Real.log L) +
        ∑ k : Fin (n + 1), μ.real {ω | -Real.log (1 - η) < cellIncrement A s t n k ω})) := by
      intro n
      have := mgf_sum_neg_two_le (μ := μ) (hind n)
        (fun k => measurable_cellIncrement hmeas n k)
        (fun k ω => cellIncrement_nonneg hst hmono n k ω) hη0 hη1
      rwa [hS n] at this
    have hsum := tendsto_sum_measureReal_cellIncrement_gt hst hmeas hcont hind hc
    have hg : Continuous fun x : ℝ =>
        L ^ 2 * Real.exp (L⁻¹ ^ 2 * (η * (-Real.log L) + x)) := by fun_prop
    have hlim := (hg.tendsto 0).comp hsum
    simpa using ge_of_tendsto' hlim hn
  have hu : Continuous fun η : ℝ => L ^ 2 * Real.exp (L⁻¹ ^ 2 * (η * (-Real.log L))) := by
    fun_prop
  have hlim0 : Tendsto (fun η : ℝ => L ^ 2 * Real.exp (L⁻¹ ^ 2 * (η * (-Real.log L))))
      (𝓝[>] 0) (𝓝 (L ^ 2)) := by
    have := (hu.tendsto 0).mono_left (nhdsWithin_le_nhds (s := Set.Ioi (0 : ℝ)))
    simpa using this
  have hmgf2 : mgf X μ (-2) ≤ L ^ 2 :=
    ge_of_tendsto hlim0 (by
      filter_upwards [Ioo_mem_nhdsGT (zero_lt_one : (0 : ℝ) < 1)] with η hη using
        hbound η hη.1 hη.2)
  -- variance of `exp (-X)` vanishes
  set Y : Ω → ℝ := fun ω => Real.exp (-X ω) with hY
  have hYm : Measurable Y := Real.measurable_exp.comp hXm.neg
  have hYle : ∀ ω, ‖Y ω‖ ≤ 1 := fun ω => by
    rw [hY, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    exact Real.exp_le_one_iff.2 (by linarith [hX0 ω])
  have hmem : MemLp Y 2 μ :=
    MemLp.of_bound hYm.aestronglyMeasurable 1 (Eventually.of_forall hYle)
  have hint1 : μ[Y] = L := by
    simp only [hL, mgf, hY, neg_one_mul]
  have hint2 : μ[Y ^ 2] = mgf X μ (-2) := by
    simp only [mgf, hY, Pi.pow_apply]
    congr 1
    funext ω
    rw [← Real.exp_nat_mul]
    congr 1
    push_cast
    ring
  have hvar : variance Y μ = 0 := by
    refine le_antisymm ?_ (variance_nonneg _ _)
    rw [variance_eq_sub hmem, hint1, hint2]
    linarith
  have hae := ae_eq_integral_of_variance_eq_zero hmem hvar
  refine ⟨-Real.log L, ?_⟩
  filter_upwards [hae] with ω hω
  rw [hint1] at hω
  have : -X ω = Real.log L := by
    rw [← hω, hY]
    simp only [Real.log_exp]
  simp only [hXdef] at this ⊢
  linarith

end main

end LatticeProb
