/-
The maximal ergodic theorem.

For a measure-preserving `T` and an integrable `f`, write `S_n` for the Birkhoff
sums of `f` along `T` and `M_N` for the largest of `0, S_1, …, S_N`.  On the set
where `M_N` is positive the integral of `f` is nonnegative.

Garsia's proof.  Where `M_N` is positive it is one of `S_1, …, S_N`, and
`S_n(x) = f(x) + S_{n-1}(T x) ≤ f(x) + M_N(T x)`, so `f ≥ M_N - M_N ∘ T` there.
Integrating, the first term contributes all of `∫ M_N`, because `M_N` vanishes
off the set, and the second contributes at most `∫ M_N ∘ T = ∫ M_N`, because
`M_N ∘ T` is nonnegative and `T` preserves the measure.  The two cancel.

This is the step Mathlib does not have and the pointwise ergodic theorem needs.
-/
import Mathlib

noncomputable section

namespace LatticeProb

open MeasureTheory Filter

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {T : Ω → Ω} {f : Ω → ℝ}

/-- The largest of the Birkhoff sums `0, S_1, …, S_N`. -/
noncomputable def maxBirkhoff (T : Ω → Ω) (f : Ω → ℝ) : ℕ → Ω → ℝ
  | 0 => fun _ => 0
  | N + 1 => fun x => max (maxBirkhoff T f N x) (birkhoffSum T f (N + 1) x)

omit [MeasurableSpace Ω] in
@[simp] theorem maxBirkhoff_zero (T : Ω → Ω) (f : Ω → ℝ) (x : Ω) :
    maxBirkhoff T f 0 x = 0 := rfl

omit [MeasurableSpace Ω] in
theorem maxBirkhoff_succ (T : Ω → Ω) (f : Ω → ℝ) (N : ℕ) (x : Ω) :
    maxBirkhoff T f (N + 1) x
      = max (maxBirkhoff T f N x) (birkhoffSum T f (N + 1) x) := rfl

omit [MeasurableSpace Ω] in
theorem maxBirkhoff_nonneg (T : Ω → Ω) (f : Ω → ℝ) (N : ℕ) (x : Ω) :
    0 ≤ maxBirkhoff T f N x := by
  induction N with
  | zero => exact le_rfl
  | succ N ih => exact le_trans ih (le_max_left _ _)

omit [MeasurableSpace Ω] in
theorem maxBirkhoff_mono (T : Ω → Ω) (f : Ω → ℝ) {M N : ℕ} (h : M ≤ N) (x : Ω) :
    maxBirkhoff T f M x ≤ maxBirkhoff T f N x := by
  induction N with
  | zero => rw [Nat.le_zero.mp h]
  | succ N ih =>
      rcases Nat.lt_or_ge M (N + 1) with hlt | hge
      · exact le_trans (ih (Nat.lt_succ_iff.mp hlt)) (le_max_left _ _)
      · rw [le_antisymm h hge]

omit [MeasurableSpace Ω] in
theorem birkhoffSum_le_maxBirkhoff (T : Ω → Ω) (f : Ω → ℝ) {n N : ℕ} (h : n ≤ N) (x : Ω) :
    birkhoffSum T f n x ≤ maxBirkhoff T f N x := by
  cases n with
  | zero => simpa [birkhoffSum] using maxBirkhoff_nonneg T f N x
  | succ n =>
      have h1 : birkhoffSum T f (n + 1) x ≤ maxBirkhoff T f (n + 1) x := le_max_right _ _
      exact le_trans h1 (maxBirkhoff_mono T f h x)

omit [MeasurableSpace Ω] in
/-- **The pointwise step of Garsia's proof.**  Where the maximal sum is
positive, it is at most `f` plus the maximal sum one step along. -/
theorem maxBirkhoff_le_add (T : Ω → Ω) (f : Ω → ℝ) (N : ℕ) (x : Ω)
    (hx : 0 < maxBirkhoff T f N x) :
    maxBirkhoff T f N x ≤ f x + maxBirkhoff T f N (T x) := by
  induction N with
  | zero => exact absurd hx (by simp)
  | succ N ih =>
      have hstep : birkhoffSum T f (N + 1) x ≤ f x + maxBirkhoff T f (N + 1) (T x) := by
        rw [birkhoffSum_succ']
        linarith [birkhoffSum_le_maxBirkhoff T f (Nat.le_succ N) (T x)]
      rcases max_cases (maxBirkhoff T f N x) (birkhoffSum T f (N + 1) x) with
        ⟨hmax, hle⟩ | ⟨hmax, hlt⟩
      · rw [maxBirkhoff_succ, hmax] at hx ⊢
        linarith [ih hx, maxBirkhoff_mono T f (Nat.le_succ N) (T x)]
      · rw [maxBirkhoff_succ, hmax]
        exact hstep

/-! ### Measurability and integrability -/

theorem measurable_maxBirkhoff (hT : Measurable T) (hf : Measurable f) (N : ℕ) :
    Measurable (maxBirkhoff T f N) := by
  induction N with
  | zero => exact measurable_const
  | succ N ih =>
      refine ih.max ?_
      exact Finset.measurable_sum _ fun k _ => hf.comp (hT.iterate k)

theorem integrable_birkhoffSum (hT : MeasurePreserving T μ μ) (hf : Integrable f μ) (n : ℕ) :
    Integrable (birkhoffSum T f n) μ := by
  refine integrable_finsetSum _ fun k _ => ?_
  have : Integrable (f ∘ T^[k]) μ := by
    rw [← (hT.iterate k).map_eq] at hf
    exact (integrable_map_measure hf.aestronglyMeasurable
      (hT.measurable.iterate k).aemeasurable).mp hf
  exact this

theorem integrable_maxBirkhoff (hT : MeasurePreserving T μ μ) (hfm : Measurable f)
    (hf : Integrable f μ) (N : ℕ) : Integrable (maxBirkhoff T f N) μ := by
  induction N with
  | zero => simp only [maxBirkhoff]; exact integrable_zero Ω ℝ μ
  | succ N ih =>
      have h2 := integrable_birkhoffSum hT hf (N + 1)
      have hmeas : Measurable (maxBirkhoff T f (N + 1)) :=
        measurable_maxBirkhoff hT.measurable hfm (N + 1)
      refine Integrable.mono' (ih.norm.add h2.norm) hmeas.aestronglyMeasurable ?_
      filter_upwards with x
      rw [maxBirkhoff_succ, Real.norm_eq_abs]
      rcases max_cases (maxBirkhoff T f N x) (birkhoffSum T f (N + 1) x) with
        ⟨h, -⟩ | ⟨h, -⟩ <;> rw [h] <;>
        simp only [Pi.add_apply, Real.norm_eq_abs] <;>
        [linarith [abs_nonneg (birkhoffSum T f (N + 1) x), le_abs_self
          (maxBirkhoff T f N x), neg_abs_le (maxBirkhoff T f N x)];
         linarith [abs_nonneg (maxBirkhoff T f N x), le_abs_self
          (birkhoffSum T f (N + 1) x), neg_abs_le (birkhoffSum T f (N + 1) x)]]

/-! ### The theorem -/

/-- **The maximal ergodic theorem** (Garsia's proof).  For a measure-preserving
transformation and an integrable function, the integral of the function over the
set where some Birkhoff sum of length at most `N` is positive is nonnegative. -/
theorem maximal_ergodic [IsFiniteMeasure μ] (hT : MeasurePreserving T μ μ)
    (hfm : Measurable f) (hf : Integrable f μ) (N : ℕ) :
    0 ≤ ∫ x in {x | 0 < maxBirkhoff T f N x}, f x ∂μ := by
  set M : Ω → ℝ := maxBirkhoff T f N with hM
  set E : Set Ω := {x | 0 < M x} with hE
  have hMmeas : Measurable M := measurable_maxBirkhoff hT.measurable hfm N
  have hMint : Integrable M μ := integrable_maxBirkhoff hT hfm hf N
  have hEmeas : MeasurableSet E := measurableSet_lt measurable_const hMmeas
  have hMT : Integrable (fun x => M (T x)) μ := by
    have := hMint
    rw [← hT.map_eq] at this
    exact (integrable_map_measure this.aestronglyMeasurable hT.measurable.aemeasurable).mp this
  -- pointwise, on `E`
  have hpt : ∀ x ∈ E, M x - M (T x) ≤ f x := by
    intro x hx
    have := maxBirkhoff_le_add T f N x hx
    linarith
  -- the two integrals
  have h1 : ∫ x in E, (M x - M (T x)) ∂μ ≤ ∫ x in E, f x ∂μ :=
    setIntegral_mono_on (hMint.sub hMT).integrableOn hf.integrableOn hEmeas hpt
  have h2 : ∫ x in E, (M x - M (T x)) ∂μ = (∫ x in E, M x ∂μ) - ∫ x in E, M (T x) ∂μ :=
    integral_sub hMint.integrableOn hMT.integrableOn
  have h3 : ∫ x in E, M x ∂μ = ∫ x, M x ∂μ := by
    refine setIntegral_eq_integral_of_forall_compl_eq_zero fun x hx => ?_
    have hle : ¬ (0 < M x) := hx
    have := maxBirkhoff_nonneg T f N x
    push Not at hle
    linarith
  have h4 : ∫ x in E, M (T x) ∂μ ≤ ∫ x, M (T x) ∂μ :=
    setIntegral_le_integral hMT (Filter.Eventually.of_forall fun x =>
      maxBirkhoff_nonneg T f N (T x))
  have h5 : ∫ x, M (T x) ∂μ = ∫ x, M x ∂μ := by
    conv_rhs => rw [← hT.map_eq]
    rw [integral_map hT.measurable.aemeasurable
      (by rw [hT.map_eq]; exact hMint.aestronglyMeasurable)]
  linarith

end LatticeProb

end
