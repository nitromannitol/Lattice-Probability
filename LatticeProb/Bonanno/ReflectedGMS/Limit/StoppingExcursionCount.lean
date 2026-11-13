/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module ReflectedGMS.Limit.StoppingExcursionCount at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.ReflectedGMS.Limit.StoppingIncrementProbability

set_option autoImplicit false
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology BigOperators

namespace ReflectedGMS.MartingaleLimit

variable {Ω : Type*} {m : MeasurableSpace Ω}

/-- The real-valued count of increments of size at least `ε` among the first
`r` successive stopping-time intervals. -/
noncomputable def largeStoppingIncrementCount
    (M : ℝ≥0 → Ω → ℝ) (σ : ℕ → Ω → WithTop ℝ≥0)
    (ε : ℝ) (r : ℕ) (ω : Ω) : ℝ :=
  ∑ k ∈ Finset.range r,
    ({ω | ε ≤ |stoppedValue M (σ (k + 1)) ω - stoppedValue M (σ k) ω|}.indicator
      (fun _ => (1 : ℝ))) ω

/-- Successive bounded stopping-time square increments sum exactly to the
expected compensator increment between the two endpoint stopping times. -/
theorem bounded_stopping_sq_increment_integral_sum
    {P : Measure Ω} [IsProbabilityMeasure P]
    {F : Filtration ℝ≥0 m} {M B : ℝ≥0 → Ω → ℝ}
    (hM : Martingale M F P)
    (hC : Martingale (fun t ω => M t ω * M t ω - B t ω) F P)
    (σ : ℕ → Ω → WithTop ℝ≥0)
    (hσ : ∀ k, IsStoppingTime F (σ k))
    (T : ℝ≥0) (hmono : ∀ k ω, σ k ω ≤ σ (k + 1) ω)
    (hT : ∀ k ω, σ k ω ≤ T)
    (hrM : ∀ᵐ ω ∂P, IsRightContinuous (fun t => M t ω))
    (hrC : ∀ᵐ ω ∂P,
      IsRightContinuous (fun t => M t ω * M t ω - B t ω))
    (h2T : MemLp (M T) 2 P) (r : ℕ) :
    (∀ k < r, Integrable (fun ω =>
      (stoppedValue M (σ (k + 1)) ω - stoppedValue M (σ k) ω) ^ 2) P) ∧
    Integrable (stoppedValue B (σ r) - stoppedValue B (σ 0)) P ∧
    (∑ k ∈ Finset.range r, ∫ ω,
      (stoppedValue M (σ (k + 1)) ω - stoppedValue M (σ k) ω) ^ 2 ∂P) =
      ∫ ω, stoppedValue B (σ r) ω - stoppedValue B (σ 0) ω ∂P := by
  have hpair (k : ℕ) := bounded_stopping_bracket_increment_integral
    hM hC (hσ k) (hσ (k + 1)) T (hmono k) (hT (k + 1)) hrM hrC h2T
  have htel (ω : Ω) :
      (∑ k ∈ Finset.range r,
        (stoppedValue B (σ (k + 1)) ω - stoppedValue B (σ k) ω)) =
        stoppedValue B (σ r) ω - stoppedValue B (σ 0) ω := by
    induction r with
    | zero => simp
    | succ r ihr =>
        rw [Finset.sum_range_succ, ihr]
        ring
  refine ⟨fun k hk => (hpair k).1, ?_, ?_⟩
  · have hsumB : Integrable (fun ω => ∑ k ∈ Finset.range r,
        (stoppedValue B (σ (k + 1)) ω - stoppedValue B (σ k) ω)) P :=
      integrable_finsetSum (Finset.range r) fun k hk => (hpair k).2.1
    refine hsumB.congr ?_
    filter_upwards [] with ω
    exact htel ω
  · calc
      _ = ∑ k ∈ Finset.range r,
          ∫ ω, stoppedValue B (σ (k + 1)) ω - stoppedValue B (σ k) ω ∂P := by
            apply Finset.sum_congr rfl
            intro k hk
            exact (hpair k).2.2
      _ = ∫ ω, ∑ k ∈ Finset.range r,
          (stoppedValue B (σ (k + 1)) ω - stoppedValue B (σ k) ω) ∂P := by
            rw [integral_finset_sum]
            intro k hk
            exact (hpair k).2.1
      _ = _ := integral_congr_ae (Eventually.of_forall htel)

/-- The expected number of successive stopping-time increments of size at least
`ε` is controlled by the expected compensator increment. -/
theorem large_stopping_increment_count_integrable_and_expectation_le
    {P : Measure Ω} [IsProbabilityMeasure P]
    {F : Filtration ℝ≥0 m} {M B : ℝ≥0 → Ω → ℝ}
    (hM : Martingale M F P)
    (hC : Martingale (fun t ω => M t ω * M t ω - B t ω) F P)
    (σ : ℕ → Ω → WithTop ℝ≥0)
    (hσ : ∀ k, IsStoppingTime F (σ k))
    (T : ℝ≥0) (hmono : ∀ k ω, σ k ω ≤ σ (k + 1) ω)
    (hT : ∀ k ω, σ k ω ≤ T)
    (hrM : ∀ᵐ ω ∂P, IsRightContinuous (fun t => M t ω))
    (hrC : ∀ᵐ ω ∂P,
      IsRightContinuous (fun t => M t ω * M t ω - B t ω))
    (h2T : MemLp (M T) 2 P) {ε : ℝ} (hε : 0 < ε) (r : ℕ) :
    Integrable (largeStoppingIncrementCount M σ ε r) P ∧
      ε ^ 2 * (∫ ω, largeStoppingIncrementCount M σ ε r ω ∂P) ≤
        ∫ ω, stoppedValue B (σ r) ω - stoppedValue B (σ 0) ω ∂P := by
  let X : ℕ → Ω → ℝ := fun k ω =>
    stoppedValue M (σ (k + 1)) ω - stoppedValue M (σ k) ω
  let A : ℕ → Set Ω := fun k => {ω | ε ≤ |X k ω|}
  have hpair (k : ℕ) := bounded_stopping_bracket_increment_integral
    hM hC (hσ k) (hσ (k + 1)) T (hmono k) (hT (k + 1)) hrM hrC h2T
  have hA (k : ℕ) : NullMeasurableSet (A k) P := by
    have hsq : AEMeasurable (fun ω => (X k ω) ^ 2) P :=
      (hpair k).1.aestronglyMeasurable.aemeasurable
    have heq : A k = (fun ω => (X k ω) ^ 2) ⁻¹' Ici (ε ^ 2) := by
      ext ω
      simp only [A, X, mem_ofPred_eq, mem_preimage, mem_Ici]
      simpa only [sq_abs] using
        (sq_le_sq₀ hε.le (abs_nonneg (X k ω))).symm
    rw [heq]
    exact hsq.nullMeasurableSet_preimage measurableSet_Ici
  have hind (k : ℕ) : Integrable ((A k).indicator (fun _ => (1 : ℝ))) P :=
    (integrable_const (1 : ℝ)).indicator₀ (hA k)
  have hcount : Integrable (largeStoppingIncrementCount M σ ε r) P := by
    unfold largeStoppingIncrementCount
    exact integrable_finsetSum _ fun k hk => hind k
  refine ⟨hcount, ?_⟩
  have hpoint (ω : Ω) :
      ε ^ 2 * largeStoppingIncrementCount M σ ε r ω ≤
        ∑ k ∈ Finset.range r, (X k ω) ^ 2 := by
    unfold largeStoppingIncrementCount
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro k hk
    by_cases hω : ω ∈ A k
    · rw [Set.indicator_of_mem hω]
      change ε ≤ |X k ω| at hω
      simpa only [mul_one, sq_abs] using
        (sq_le_sq₀ hε.le (abs_nonneg (X k ω))).2 hω
    · rw [Set.indicator_of_notMem hω]
      simpa only [mul_zero] using sq_nonneg (X k ω)
  have hsumint : Integrable (fun ω => ∑ k ∈ Finset.range r, (X k ω) ^ 2) P :=
    integrable_finsetSum _ fun k hk => (hpair k).1
  calc
    ε ^ 2 * (∫ ω, largeStoppingIncrementCount M σ ε r ω ∂P) =
        ∫ ω, ε ^ 2 * largeStoppingIncrementCount M σ ε r ω ∂P := by
          rw [integral_const_mul]
    _ ≤ ∫ ω, ∑ k ∈ Finset.range r, (X k ω) ^ 2 ∂P :=
      integral_mono (hcount.const_mul _) hsumint hpoint
    _ = ∑ k ∈ Finset.range r, ∫ ω, (X k ω) ^ 2 ∂P := by
      rw [integral_finsetSum]
      intro k hk
      exact (hpair k).1
    _ = _ := (bounded_stopping_sq_increment_integral_sum hM hC σ hσ T hmono
      hT hrM hrC h2T r).2.2

/-- Markov's inequality in the precise real-valued form used for excursion
counts. -/
theorem measure_count_ge_le_of_mul_integral_le
    {P : Measure Ω} {C : Ω → ℝ} (hC : Integrable C P)
    (hC0 : ∀ ω, 0 ≤ C ω) {a K R : ℝ} (ha : 0 < a) (hK : 0 < K)
    (hmean : a * (∫ ω, C ω ∂P) ≤ R) :
    P {ω | K ≤ C ω} ≤ ENNReal.ofReal (R / (a * K)) := by
  have hf : Integrable (fun ω => C ω / K) P := hC.div_const K
  have hf0 : 0 ≤ᵐ[P] fun ω => C ω / K :=
    Eventually.of_forall fun ω => div_nonneg (hC0 ω) hK.le
  have hmarkov :
      P {ω | K ≤ C ω} ≤ ENNReal.ofReal (∫ ω, C ω / K ∂P) := by
    apply hf.measure_le_integral hf0
    intro ω hω
    change K ≤ C ω at hω
    apply (le_div_iff₀ hK).2
    simpa only [one_mul] using hω
  refine hmarkov.trans ?_
  apply ENNReal.ofReal_le_ofReal
  rw [integral_div]
  apply (le_div_iff₀ (mul_pos ha hK)).2
  have heq : (∫ ω, C ω ∂P) / K * (a * K) =
      a * (∫ ω, C ω ∂P) := by
    field_simp [ne_of_gt hK]
    <;> ring
  rw [heq]
  exact hmean

/-- Tail bound for the number of large increments along an increasing bounded
sequence of stopping times. -/
theorem large_stopping_increment_count_tail_le
    {P : Measure Ω} [IsProbabilityMeasure P]
    {F : Filtration ℝ≥0 m} {M B : ℝ≥0 → Ω → ℝ}
    (hM : Martingale M F P)
    (hC : Martingale (fun t ω => M t ω * M t ω - B t ω) F P)
    (σ : ℕ → Ω → WithTop ℝ≥0)
    (hσ : ∀ k, IsStoppingTime F (σ k))
    (T : ℝ≥0) (hmono : ∀ k ω, σ k ω ≤ σ (k + 1) ω)
    (hT : ∀ k ω, σ k ω ≤ T)
    (hrM : ∀ᵐ ω ∂P, IsRightContinuous (fun t => M t ω))
    (hrC : ∀ᵐ ω ∂P,
      IsRightContinuous (fun t => M t ω * M t ω - B t ω))
    (h2T : MemLp (M T) 2 P) {ε K : ℝ} (hε : 0 < ε) (hK : 0 < K)
    (r : ℕ) :
    P {ω | K ≤ largeStoppingIncrementCount M σ ε r ω} ≤
      ENNReal.ofReal
        ((∫ ω, stoppedValue B (σ r) ω - stoppedValue B (σ 0) ω ∂P) /
          (ε ^ 2 * K)) := by
  have hcount := large_stopping_increment_count_integrable_and_expectation_le
    hM hC σ hσ T hmono hT hrM hrC h2T hε r
  apply measure_count_ge_le_of_mul_integral_le hcount.1 _ (sq_pos_of_pos hε) hK
    hcount.2
  intro ω
  unfold largeStoppingIncrementCount
  exact Finset.sum_nonneg fun k hk => Set.indicator_nonneg (fun _ _ => zero_le_one) _

/-- Uniform-in-`r` expected-count and tail bounds obtained from the terminal
second moment. -/
theorem large_stopping_increment_count_uniform_terminal_bounds
    {P : Measure Ω} [IsProbabilityMeasure P]
    {F : Filtration ℝ≥0 m} {M B : ℝ≥0 → Ω → ℝ}
    (hM : Martingale M F P)
    (hC : Martingale (fun t ω => M t ω * M t ω - B t ω) F P)
    (σ : ℕ → Ω → WithTop ℝ≥0)
    (hσ : ∀ k, IsStoppingTime F (σ k))
    (T : ℝ≥0) (hmono : ∀ k ω, σ k ω ≤ σ (k + 1) ω)
    (hT : ∀ k ω, σ k ω ≤ T)
    (hrM : ∀ᵐ ω ∂P, IsRightContinuous (fun t => M t ω))
    (hrC : ∀ᵐ ω ∂P,
      IsRightContinuous (fun t => M t ω * M t ω - B t ω))
    (h2T : MemLp (M T) 2 P) {ε K : ℝ} (hε : 0 < ε) (hK : 0 < K)
    (r : ℕ) :
    ε ^ 2 * (∫ ω, largeStoppingIncrementCount M σ ε r ω ∂P) ≤
        ∫ ω, (M T ω) ^ 2 ∂P ∧
      P {ω | K ≤ largeStoppingIncrementCount M σ ε r ω} ≤
        ENNReal.ofReal ((∫ ω, (M T ω) ^ 2 ∂P) / (ε ^ 2 * K)) := by
  have h0r : ∀ ω, σ 0 ω ≤ σ r ω := by
    intro ω
    induction r with
    | zero => exact le_rfl
    | succ r ihr => exact ihr.trans (hmono r ω)
  have hterminal := bounded_stopping_bracket_increment_integral_nonneg_le
    hM hC (hσ 0) (hσ r) T h0r (hT r) hrM hrC h2T
  constructor
  · exact (large_stopping_increment_count_integrable_and_expectation_le
      hM hC σ hσ T hmono hT hrM hrC h2T hε r).2.trans hterminal.2
  · refine (large_stopping_increment_count_tail_le hM hC σ hσ T hmono hT
      hrM hrC h2T hε hK r).trans ?_
    apply ENNReal.ofReal_le_ofReal
    exact div_le_div_of_nonneg_right hterminal.2 (mul_nonneg (sq_nonneg ε) hK.le)

end ReflectedGMS.MartingaleLimit
