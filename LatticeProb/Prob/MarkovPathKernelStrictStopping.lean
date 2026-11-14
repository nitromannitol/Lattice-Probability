import Mathlib
import LatticeProb.Prob.MarkovPathKernelStrong

/-!
# The strong Markov property at a strict stopping time

A random time `σ : Ω → ℝ≥0∞` is a *strict stopping time* for a filtration `ℱ` indexed by `ℝ≥0` if
`{σ < u} ∈ ℱ u` for every `u`.  (Every stopping time is strict; the converse holds for
right-continuous filtrations.)  For every `δ > 0` the shifted time `σ + δ` is a stopping time.

For a continuous family of path laws `K` with the Markov property at every deterministic time, the
strong Markov property is known at stopping times of the filtration of stopped paths.  Here it is
extended to strict stopping times: apply it to `σ + 1/(n+1)` and let `n → ∞`, for bounded
continuous test functions, and then extend to bounded measurable test functions.
-/

open MeasureTheory Filter Topology ProbabilityTheory
open scoped BoundedContinuousFunction ENNReal NNReal

namespace LatticeProb

section Generic

variable {Ω : Type*} {m : MeasurableSpace Ω}

/-- If `σ` is a strict stopping time of a filtration indexed by `ℝ≥0`, then `σ + δ` is a stopping
time for every `δ > 0`. -/
theorem isStoppingTime_add_const_of_lt (ℱ : Filtration ℝ≥0 m) {σ : Ω → ℝ≥0∞}
    (hσ : ∀ u : ℝ≥0, MeasurableSet[ℱ u] {ω | σ ω < (u : ℝ≥0∞)}) {δ : ℝ≥0} (hδ : δ ≠ 0) :
    IsStoppingTime ℱ fun ω => σ ω + (δ : ℝ≥0∞) := by
  intro u
  change MeasurableSet[ℱ u] {ω | σ ω + (δ : ℝ≥0∞) ≤ (u : ℝ≥0∞)}
  by_cases hu : u < δ
  · have : {ω | σ ω + (δ : ℝ≥0∞) ≤ (u : ℝ≥0∞)} = ∅ := by
      ext ω
      simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, not_le]
      exact lt_of_lt_of_le (by exact_mod_cast hu) le_add_self
    rw [this]
    exact @MeasurableSet.empty Ω (ℱ u)
  · obtain ⟨v, rfl⟩ : ∃ v : ℝ≥0, u = v + δ := ⟨u - δ, (tsub_add_cancel_of_le (not_lt.1 hu)).symm⟩
    have hset : {ω | σ ω + (δ : ℝ≥0∞) ≤ ((v + δ : ℝ≥0) : ℝ≥0∞)} =
        ⋂ k : ℕ, {ω | σ ω < ((v + δ / ((k : ℝ≥0) + 1) : ℝ≥0) : ℝ≥0∞)} := by
      ext ω
      simp only [Set.mem_ofPred_eq, Set.mem_iInter]
      rw [ENNReal.coe_add, ENNReal.add_le_add_iff_right ENNReal.coe_ne_top]
      constructor
      · intro h k
        refine lt_of_le_of_lt h ?_
        rw [ENNReal.coe_lt_coe]
        exact lt_add_of_pos_right _ (by positivity)
      · intro h
        refine ENNReal.le_of_forall_pos_le_add fun ε hε _ => ?_
        obtain ⟨k, hk⟩ := exists_nat_gt (δ / ε)
        have hk' : δ / ((k : ℝ≥0) + 1) < ε := by
          rw [div_lt_iff₀ (by positivity)]
          rw [div_lt_iff₀ hε] at hk
          calc δ < k * ε := hk
            _ ≤ ε * ((k : ℝ≥0) + 1) := by
              rw [mul_comm]
              exact mul_le_mul_right (le_add_of_nonneg_right zero_le) _
        refine (h k).le.trans ?_
        rw [← ENNReal.coe_add, ENNReal.coe_le_coe]
        exact add_le_add_right hk'.le v
    rw [hset]
    refine MeasurableSet.iInter fun k => ?_
    refine ℱ.mono ?_ _ (hσ _)
    exact add_le_add_right (div_le_self zero_le (by simp)) v

end Generic

section Path

attribute [local instance] dUnifMetricSpace

variable {E : Type*} [MetricSpace E] [SecondCountableTopology E] [MeasurableSpace E] [BorelSpace E]
  [MeasurableSpace C(ℝ≥0, E)] [BorelSpace C(ℝ≥0, E)]

omit [SecondCountableTopology E] [MeasurableSpace E] [BorelSpace E] in
/-- A strict stopping time of the filtration of stopped paths is measurable. -/
theorem measurable_of_strictStopping {σ : C(ℝ≥0, E) → ℝ≥0∞}
    (hσ : ∀ u : ℝ≥0, MeasurableSet[(stoppedPathFiltration (E := E)) u] {x | σ x < (u : ℝ≥0∞)}) :
    Measurable σ := by
  have h1 := measurable_of_isStoppingTime_stoppedPath
    (isStoppingTime_add_const_of_lt (stoppedPathFiltration (E := E)) hσ (δ := 1) one_ne_zero)
  have h2 : σ = fun x => (σ x + ((1 : ℝ≥0) : ℝ≥0∞)) - 1 := by
    ext x
    simp
  rw [h2]
  exact h1.sub_const 1

/-- **The strong Markov property at a strict stopping time.**  If `K : E → Prob C(ℝ≥0, E)` is
continuous and `K z` has the Markov property at every deterministic time, then for every
`σ : C(ℝ≥0, E) → ℝ≥0∞` with `{σ < u}` determined by the path stopped at `u` for every `u`, almost
surely finite under `K z`, and every bounded measurable test function `g` on pairs of paths,
`∫ g (x (· ∧ σ), x (σ + ·)) d(K z) = ∫ ∫ g (x (· ∧ σ), w) d(K (x σ)) (w) d(K z)`. -/
theorem strongMarkov_of_strictStopping {K : E → ProbabilityMeasure C(ℝ≥0, E)}
    (hK : Continuous K) {z : E} (hM : ∀ t, MarkovAt K z t) {σ : C(ℝ≥0, E) → ℝ≥0∞}
    (hσ : ∀ u : ℝ≥0, MeasurableSet[(stoppedPathFiltration (E := E)) u] {x | σ x < (u : ℝ≥0∞)})
    (hfin : ∀ᵐ x ∂(K z : Measure C(ℝ≥0, E)), σ x < ⊤)
    {g : C(ℝ≥0, E) × C(ℝ≥0, E) → ℝ} (hg : Measurable g) {C : ℝ} (hC : ∀ p, ‖g p‖ ≤ C) :
    ∫ x, g (stopPath x (σ x).toNNReal, pathShift x (σ x).toNNReal)
        ∂(K z : Measure C(ℝ≥0, E)) =
      ∫ x, ∫ w, g (stopPath x (σ x).toNNReal, w) ∂(K (x (σ x).toNNReal) : Measure C(ℝ≥0, E))
        ∂(K z : Measure C(ℝ≥0, E)) := by
  have hσm : Measurable σ := measurable_of_strictStopping hσ
  refine integral_stopShift_eq_of_forall_boundedContinuous hK z
    (σ := fun x => (σ x).toNNReal) (ENNReal.measurable_toNNReal.comp hσm) (fun g => ?_) hg hC
  set δ : ℕ → ℝ≥0 := fun n => Real.toNNReal (1 / ((n : ℝ) + 1)) with hδdef
  have hδne : ∀ n, δ n ≠ 0 := fun n => by
    simp only [hδdef, ne_eq, Real.toNNReal_eq_zero, not_le]
    positivity
  have hδlim : Tendsto δ atTop (𝓝 0) := by
    have := (continuous_real_toNNReal.tendsto 0).comp tendsto_one_div_add_atTop_nhds_zero_nat
    simpa [hδdef, Function.comp_def] using this
  have hstop : ∀ n, IsStoppingTime (stoppedPathFiltration (E := E))
      fun x => σ x + (δ n : ℝ≥0∞) := fun n =>
    isStoppingTime_add_const_of_lt _ hσ (hδne n)
  have hdisc : ∀ n : ℕ,
      ∫ x, g (stopPath x (σ x + (δ n : ℝ≥0∞)).toNNReal, pathShift x (σ x + (δ n : ℝ≥0∞)).toNNReal)
          ∂(K z : Measure C(ℝ≥0, E)) =
        ∫ x, ∫ w, g (stopPath x (σ x + (δ n : ℝ≥0∞)).toNNReal, w)
          ∂(K (x (σ x + (δ n : ℝ≥0∞)).toNNReal) : Measure C(ℝ≥0, E))
          ∂(K z : Measure C(ℝ≥0, E)) := fun n =>
    strongMarkov_of_markovAt_of_ae_lt_top hK hM (hstop n)
      (hfin.mono fun x hx => ENNReal.add_lt_top.2 ⟨hx, ENNReal.coe_lt_top⟩)
      g.continuous.measurable (fun p => g.norm_coe_le_norm p)
  have hσn : ∀ n : ℕ, Measurable fun x : C(ℝ≥0, E) => (σ x + (δ n : ℝ≥0∞)).toNNReal := fun n =>
    ENNReal.measurable_toNNReal.comp (hσm.add_const _)
  have hev : Continuous fun q : C(ℝ≥0, E) × ℝ≥0 => q.1 q.2 := ContinuousEval.continuous_eval
  have hΦ : Continuous fun q : C(ℝ≥0, E) × ℝ≥0 =>
      ∫ w, g (stopPath q.1 q.2, w) ∂(K (q.1 q.2) : Measure C(ℝ≥0, E)) :=
    continuous_integral_of_continuous_measure (μ := fun q : C(ℝ≥0, E) × ℝ≥0 => K (q.1 q.2))
      (hK.comp hev)
      (G := fun p : C(ℝ≥0, E) × (C(ℝ≥0, E) × ℝ≥0) => g (stopPath p.2.1 p.2.2, p.1))
      (g.continuous.comp ((continuous_stopPath_uncurry.comp continuous_snd).prodMk continuous_fst))
      (C := ‖g‖) fun p => g.norm_coe_le_norm _
  have hΦb : ∀ q : C(ℝ≥0, E) × ℝ≥0,
      ‖∫ w, g (stopPath q.1 q.2, w) ∂(K (q.1 q.2) : Measure C(ℝ≥0, E))‖ ≤ ‖g‖ := fun q => by
    simpa using norm_integral_le_of_norm_le_const (μ := (K (q.1 q.2) : Measure C(ℝ≥0, E)))
      (f := fun w => g (stopPath q.1 q.2, w)) (C := ‖g‖)
      (Filter.Eventually.of_forall fun w => g.norm_coe_le_norm _)
  have hlim : ∀ x : C(ℝ≥0, E), σ x < ⊤ →
      Tendsto (fun n : ℕ => (x, (σ x + (δ n : ℝ≥0∞)).toNNReal)) atTop (𝓝 (x, (σ x).toNNReal)) := by
    intro x hx
    refine tendsto_const_nhds.prodMk_nhds ?_
    have : ∀ n : ℕ, (σ x + (δ n : ℝ≥0∞)).toNNReal = (σ x).toNNReal + δ n := fun n => by
      rw [ENNReal.toNNReal_add hx.ne ENNReal.coe_ne_top, ENNReal.toNNReal_coe]
    simp only [this]
    simpa using tendsto_const_nhds.add hδlim
  have hL : Tendsto (fun n : ℕ => ∫ x, g (stopPath x (σ x + (δ n : ℝ≥0∞)).toNNReal,
      pathShift x (σ x + (δ n : ℝ≥0∞)).toNNReal) ∂(K z : Measure C(ℝ≥0, E))) atTop
      (𝓝 (∫ x, g (stopPath x (σ x).toNNReal, pathShift x (σ x).toNNReal)
        ∂(K z : Measure C(ℝ≥0, E)))) := by
    refine tendsto_integral_of_dominated_convergence (fun _ => ‖g‖) (fun n => ?_)
      (integrable_const _) (fun n => Filter.Eventually.of_forall fun x => g.norm_coe_le_norm _)
      (hfin.mono fun x hx => ?_)
    · exact (g.continuous.measurable.comp
        ((continuous_stopPath_uncurry.measurable.comp (measurable_id.prodMk (hσn n))).prodMk
          (continuous_pathShift_uncurry.measurable.comp
            (measurable_id.prodMk (hσn n))))).aestronglyMeasurable
    · exact (g.continuous.continuousAt.tendsto).comp
        (((continuous_stopPath_uncurry.continuousAt.tendsto).comp (hlim x hx)).prodMk_nhds
          ((continuous_pathShift_uncurry.continuousAt.tendsto).comp (hlim x hx)))
  have hR : Tendsto (fun n : ℕ => ∫ x, ∫ w, g (stopPath x (σ x + (δ n : ℝ≥0∞)).toNNReal, w)
      ∂(K (x (σ x + (δ n : ℝ≥0∞)).toNNReal) : Measure C(ℝ≥0, E))
      ∂(K z : Measure C(ℝ≥0, E))) atTop
      (𝓝 (∫ x, ∫ w, g (stopPath x (σ x).toNNReal, w)
        ∂(K (x (σ x).toNNReal) : Measure C(ℝ≥0, E)) ∂(K z : Measure C(ℝ≥0, E)))) := by
    refine tendsto_integral_of_dominated_convergence (fun _ => ‖g‖) (fun n => ?_)
      (integrable_const _)
      (fun n => Filter.Eventually.of_forall fun x => hΦb (x, (σ x + (δ n : ℝ≥0∞)).toNNReal))
      (hfin.mono fun x hx => ?_)
    · exact (hΦ.measurable.comp (measurable_id.prodMk (hσn n))).aestronglyMeasurable
    · exact (hΦ.continuousAt.tendsto).comp (hlim x hx)
  exact tendsto_nhds_unique (hL.congr hdisc) hR

end Path

end LatticeProb
