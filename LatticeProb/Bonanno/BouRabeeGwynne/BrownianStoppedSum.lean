/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module BouRabeeGwynne.BrownianStoppedSum at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.BouRabeeGwynne.BrownianStoppedStep
import LatticeProb.Bonanno.BouRabeeGwynne.BrownianStoppingApprox

/-!
# Exact stopped dyadic telescoping and its harmonic expectation bound

The step decision is the genuine event that the unrounded stopping time is
still in the future. The endpoint is its upper dyadic approximation, including
the step that crosses the stopping time.
-/

open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal
namespace BouRabeeGwynne

lemma sum_stopped_differences (g : ℕ → ℝ) (m k : ℕ) :
    (∑ j ∈ Finset.range m, if j < k then g (j + 1) - g j else 0) =
      g (min m k) - g 0 := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Finset.sum_range_succ, ih]
    by_cases h : m < k
    · rw [if_pos h, Nat.min_eq_left h.le, Nat.min_eq_left (Nat.succ_le_of_lt h)]
      ring
    · have hk : k ≤ m := Nat.le_of_not_gt h
      rw [if_neg h, Nat.min_eq_right hk, Nat.min_eq_right (hk.trans (Nat.le_succ m))]
      ring

lemma dyadic_stopped_difference_eq_sum {Ω : Type*}
    (g : Ω → ℝ≥0 → ℝ) (σ : Ω → ℝ≥0) {N : ℝ≥0}
    (hN : ∀ ω, σ ω ≤ N) (n : ℕ) (ω : Ω) :
    g ω (dyadicStoppingTime σ n ω) - g ω 0 =
      ∑ j ∈ Finset.range ⌈N * (2 : ℝ≥0) ^ n⌉₊,
        if (j : ℝ≥0) / (2 : ℝ≥0) ^ n < σ ω then
          g ω ((j + 1 : ℕ) / (2 : ℝ≥0) ^ n) - g ω ((j : ℝ≥0) / (2 : ℝ≥0) ^ n)
        else 0 := by
  have hk : ⌈σ ω * (2 : ℝ≥0) ^ n⌉₊ ≤ ⌈N * (2 : ℝ≥0) ^ n⌉₊ :=
    Nat.ceil_mono (mul_le_mul_of_nonneg_right (hN ω) (by positivity))
  have hthreshold (j : ℕ) : j < ⌈σ ω * (2 : ℝ≥0) ^ n⌉₊ ↔
      (j : ℝ≥0) / (2 : ℝ≥0) ^ n < σ ω := by
    rw [Nat.lt_ceil, div_lt_iff₀ (by positivity : 0 < (2 : ℝ≥0) ^ n)]
  have h := sum_stopped_differences (fun j ↦ g ω ((j : ℝ≥0) / (2 : ℝ≥0) ^ n))
    ⌈N * (2 : ℝ≥0) ^ n⌉₊ ⌈σ ω * (2 : ℝ≥0) ^ n⌉₊
  simpa only [Nat.min_eq_right hk, hthreshold, Nat.cast_zero, zero_div, dyadicStoppingTime]
    using h.symm

lemma measurableSet_before_nnreal_stopping {d : ℕ} {σ : BrownianPath d → ℝ≥0}
    (hσ : IsStoppingTime (brownianNaturalFiltration d) (fun ω ↦ (σ ω : ℝ≥0∞)))
    (t : ℝ≥0) : MeasurableSet[brownianNaturalFiltration d t] {ω | t < σ ω} := by
  have h := (hσ t).compl
  change MeasurableSet[brownianNaturalFiltration d t]
    ({ω : BrownianPath d | (σ ω : ℝ≥0∞) ≤ (t : ℝ≥0∞)}ᶜ) at h
  simpa only [compl_setOf, not_le, ENNReal.coe_lt_coe] using h

/-- Summing the proved one-step bounds up to an actual bounded stopping time.
The constant is uniform over the stopping time, starting point, and dyadic mesh. -/
theorem standardBrownianLaw_dyadic_stopped_harmonic_bound {d : ℕ}
    {μ : Measure (BrownianPath d)} (hμ : IsStandardBrownianLaw μ)
    {f : Euc d → ℝ} (hf : ContDiff ℝ 2 f) (hsupp : HasCompactSupport f)
    {U : Set (Euc d)} (hh : IsHarmonicOn f U) {ε : ℝ} (hε : 0 < ε) :
    ∃ C ≥ 0, ∀ (σ : BrownianPath d → ℝ≥0),
      IsStoppingTime (brownianNaturalFiltration d) (fun ω ↦ (σ ω : ℝ≥0∞)) →
      ∀ N : ℝ≥0, (∀ ω, σ ω ≤ N) → ∀ z : Euc d,
      (∀ ω t, t < σ ω → z + ω t ∈ U) → ∀ n : ℕ,
      Integrable (fun ω ↦ f (z + ω (dyadicStoppingTime σ n ω)) - f (z + ω 0)) μ ∧
      |∫ ω, f (z + ω (dyadicStoppingTime σ n ω)) - f (z + ω 0) ∂μ| ≤
        (⌈N * (2 : ℝ≥0) ^ n⌉₊ : ℝ) *
          (ε * (d : ℝ) * ((1 / (2 : ℝ≥0) ^ n : ℝ≥0) : ℝ) +
            C * ((1 / (2 : ℝ≥0) ^ n : ℝ≥0) : ℝ) ^ 2) := by
  obtain ⟨C, hC, hstep⟩ := standardBrownianLaw_stopped_harmonic_step_bound hμ hf hsupp hh hε
  refine ⟨C, hC, fun σ hσ N hN z hstay n ↦ ?_⟩
  let D : ℕ → BrownianPath d → ℝ := fun j ω ↦
    if (j : ℝ≥0) / (2 : ℝ≥0) ^ n < σ ω then
      f (z + ω ((j + 1 : ℕ) / (2 : ℝ≥0) ^ n)) - f (z + ω ((j : ℝ≥0) / (2 : ℝ≥0) ^ n))
    else 0
  let B : ℝ := ε * (d : ℝ) * ((1 / (2 : ℝ≥0) ^ n : ℝ≥0) : ℝ) +
    C * ((1 / (2 : ℝ≥0) ^ n : ℝ≥0) : ℝ) ^ 2
  have hD (j : ℕ) : Integrable (D j) μ ∧ |∫ ω, D j ω ∂μ| ≤ B := by
    let t : ℝ≥0 := (j : ℝ≥0) / (2 : ℝ≥0) ^ n
    let s : ℝ≥0 := 1 / (2 : ℝ≥0) ^ n
    have htime : t + s = (j + 1 : ℕ) / (2 : ℝ≥0) ^ n := by
      dsimp [t, s]
      rw [← add_div, Nat.cast_add, Nat.cast_one]
    have hXm : Measurable[brownianNaturalFiltration d t]
        (fun ω : BrownianPath d ↦ z + ω t) := by
      apply measurable_const.add
      exact (comap_measurable (fun ω : BrownianPath d ↦ ω t)).mono
        (le_iSup₂_of_le t le_rfl le_rfl) le_rfl
    have h := hstep t s (fun ω ↦ z + ω t) {ω | t < σ ω} hXm
      (measurableSet_before_nnreal_stopping hσ t) (fun ω hω ↦ hstay ω t hω)
    have heq : {ω | t < σ ω}.indicator
        (fun ω ↦ f ((z + ω t) + (ω (t + s) - ω t)) - f (z + ω t)) = D j := by
      funext ω
      by_cases hω : t < σ ω
      · rw [indicator_of_mem (show ω ∈ {ω | t < σ ω} from hω)]
        dsimp [D]
        rw [if_pos hω, ← htime]
        congr 2
        abel
      · rw [indicator_of_notMem (show ω ∉ {ω | t < σ ω} from hω)]
        exact (if_neg hω).symm
    rw [heq] at h
    exact h
  have heq : (fun ω ↦ f (z + ω (dyadicStoppingTime σ n ω)) - f (z + ω 0)) =
      fun ω ↦ ∑ j ∈ Finset.range ⌈N * (2 : ℝ≥0) ^ n⌉₊, D j ω := by
    funext ω
    exact dyadic_stopped_difference_eq_sum (fun ω t ↦ f (z + ω t)) σ hN n ω
  rw [heq]
  refine ⟨integrable_finset_sum _ (fun j _ ↦ (hD j).1), ?_⟩
  rw [integral_finset_sum _ (fun j _ ↦ (hD j).1)]
  calc
    |∑ j ∈ Finset.range ⌈N * (2 : ℝ≥0) ^ n⌉₊, ∫ ω, D j ω ∂μ| ≤
        ∑ j ∈ Finset.range ⌈N * (2 : ℝ≥0) ^ n⌉₊, |∫ ω, D j ω ∂μ| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ j ∈ Finset.range ⌈N * (2 : ℝ≥0) ^ n⌉₊, B :=
      Finset.sum_le_sum (fun j _ ↦ (hD j).2)
    _ = _ := by simp [B, mul_add]

end BouRabeeGwynne
