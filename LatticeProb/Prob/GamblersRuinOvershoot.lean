/-
Gambler's ruin for an exponential martingale with a controlled overshoot.

Let `M k = exp (-a * Y k)` be a martingale for a filtration `𝒢` with `E M 0 = 1`, and let `δ, η > 0`.
Following the walk `Y` until it first drops to `-δ`, the martingale property on the survival
events telescopes:
`∫_{survival up to n} M n = ∫_{survival up to 0} M 0 - ∑_{i < n} ∫_{first passage at i+1} M (i+1)`.
At a first passage the value of `M` is at most `exp (a (δ + η))` unless the last step was
smaller than `-η`, and that overshoot is paid for by one explicit term.  The conclusion is the
lower bound
`exp (-a (δ + η)) (1 - n q - ρ) ≤ P (the walk is at most -δ at some time ≤ n)`,
where `q` bounds the contribution of one large downward step and `ρ` bounds `∫_{survival} M n`.
-/
import Mathlib

open MeasureTheory ProbabilityTheory Filter MeasurableSpace
open scoped ENNReal NNReal

noncomputable section

namespace LatticeProb

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {𝒢 : Filtration ℕ mΩ}
  {Y M : ℕ → Ω → ℝ}

/-- The event that the walk has stayed above `-δ` up to time `k`. -/
def survivalSet (Y : ℕ → Ω → ℝ) (δ : ℝ) (k : ℕ) : Set Ω := {ω | ∀ j ≤ k, -δ < Y j ω}

/-- The event of first passage at time `k + 1`. -/
def firstPassageSet (Y : ℕ → Ω → ℝ) (δ : ℝ) (k : ℕ) : Set Ω :=
  survivalSet Y δ k \ {ω | -δ < Y (k + 1) ω}

theorem survivalSet_succ (Y : ℕ → Ω → ℝ) (δ : ℝ) (k : ℕ) :
    survivalSet Y δ (k + 1) = survivalSet Y δ k ∩ {ω | -δ < Y (k + 1) ω} := by
  ext ω
  constructor
  · intro h
    exact ⟨fun j hj => h j (by omega), h _ le_rfl⟩
  · rintro ⟨h1, h2⟩ j hj
    rcases Nat.lt_or_ge j (k + 1) with h | h
    · exact h1 j (by omega)
    · have : j = k + 1 := by omega
      subst this
      exact h2

theorem measurableSet_survivalSet (hY : ∀ k, Measurable[𝒢 k] (Y k)) (δ : ℝ) (k : ℕ) :
    MeasurableSet[𝒢 k] (survivalSet Y δ k) := by
  have : survivalSet Y δ k = ⋂ j ∈ Finset.range (k + 1), {ω | -δ < Y j ω} := by
    ext ω
    simp [survivalSet]
  rw [this]
  refine Finset.measurableSet_biInter _ fun j hj => ?_
  have hjk : j ≤ k := Nat.lt_succ_iff.1 (Finset.mem_range.1 hj)
  exact measurableSet_lt measurable_const ((hY j).mono (𝒢.mono hjk) le_rfl)

/-- One step of the telescoping identity. -/
theorem setIntegral_survivalSet_succ [IsFiniteMeasure P] (hM : Martingale M 𝒢 P)
    (hY : ∀ k, Measurable[𝒢 k] (Y k)) (δ : ℝ) (k : ℕ) :
    ∫ ω in survivalSet Y δ (k + 1), M (k + 1) ω ∂P =
      ∫ ω in survivalSet Y δ k, M k ω ∂P - ∫ ω in firstPassageSet Y δ k, M (k + 1) ω ∂P := by
  have hGk : MeasurableSet (survivalSet Y δ k) := 𝒢.le k _ (measurableSet_survivalSet hY δ k)
  have hYm : ∀ j, Measurable (Y j) := fun j => (hY j).mono (𝒢.le j) le_rfl
  have ht : MeasurableSet {ω | -δ < Y (k + 1) ω} :=
    measurableSet_lt measurable_const (hYm (k + 1))
  have h1 := integral_inter_add_sdiff (μ := P) (f := M (k + 1)) ht
    (hM.integrable (k + 1)).integrableOn (s := survivalSet Y δ k)
  have h2 : ∫ ω in survivalSet Y δ k, M k ω ∂P = ∫ ω in survivalSet Y δ k, M (k + 1) ω ∂P :=
    hM.setIntegral_eq (Nat.le_succ k) (measurableSet_survivalSet hY δ k)
  rw [survivalSet_succ]
  simp only [firstPassageSet]
  linarith


/-- The telescoping identity over `n` steps. -/
theorem setIntegral_survivalSet_eq [IsFiniteMeasure P] (hM : Martingale M 𝒢 P)
    (hY : ∀ k, Measurable[𝒢 k] (Y k)) (δ : ℝ) (n : ℕ) :
    ∫ ω in survivalSet Y δ n, M n ω ∂P = ∫ ω in survivalSet Y δ 0, M 0 ω ∂P -
      ∑ i ∈ Finset.range n, ∫ ω in firstPassageSet Y δ i, M (i + 1) ω ∂P := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [setIntegral_survivalSet_succ hM hY, ih, Finset.sum_range_succ]
    ring

/-- One first passage costs at most `exp (a (δ + η))` times its probability plus the
overshoot term `q`. -/
theorem setIntegral_firstPassageSet_le [IsFiniteMeasure P] (hM : Martingale M 𝒢 P)
    (hY : ∀ k, Measurable[𝒢 k] (Y k)) {a : ℝ} (hMY : ∀ k ω, M k ω = Real.exp (-a * Y k ω))
    (ha : 0 ≤ a) (δ η q : ℝ) (k : ℕ)
    (hq : ∫ ω in {ω | Y (k + 1) ω - Y k ω < -η}, M (k + 1) ω ∂P ≤ q) :
    ∫ ω in firstPassageSet Y δ k, M (k + 1) ω ∂P ≤
      Real.exp (a * (δ + η)) * P.real (firstPassageSet Y δ k) + q := by
  have hYm : ∀ j, Measurable (Y j) := fun j => (hY j).mono (𝒢.le j) le_rfl
  have hGk : MeasurableSet (survivalSet Y δ k) := 𝒢.le k _ (measurableSet_survivalSet hY δ k)
  have ht : MeasurableSet {ω | -δ < Y (k + 1) ω} :=
    measurableSet_lt measurable_const (hYm (k + 1))
  have hD : MeasurableSet (firstPassageSet Y δ k) := hGk.diff ht
  have hbad : MeasurableSet {ω | Y (k + 1) ω - Y k ω < -η} :=
    measurableSet_lt ((hYm (k + 1)).sub (hYm k)) measurable_const
  have hint := (hM.integrable (k + 1)).integrableOn (s := firstPassageSet Y δ k)
  have hsplit := integral_inter_add_sdiff (μ := P) (f := M (k + 1)) hbad hint
  have hnn : ∀ ω, 0 ≤ M (k + 1) ω := fun ω => by rw [hMY]; exact (Real.exp_pos _).le
  -- the part with a small last step
  have h1 : ∫ ω in firstPassageSet Y δ k \ {ω | Y (k + 1) ω - Y k ω < -η}, M (k + 1) ω ∂P ≤
      Real.exp (a * (δ + η)) * P.real (firstPassageSet Y δ k) := by
    calc ∫ ω in firstPassageSet Y δ k \ {ω | Y (k + 1) ω - Y k ω < -η}, M (k + 1) ω ∂P
        ≤ ∫ ω in firstPassageSet Y δ k \ {ω | Y (k + 1) ω - Y k ω < -η},
            Real.exp (a * (δ + η)) ∂P := by
          refine setIntegral_mono_on (hint.mono_set Set.sdiff_subset) (integrableOn_const
            (by simp)) (hD.diff hbad) fun ω hω => ?_
          obtain ⟨hD1, hD2⟩ := hω
          have h1 : -δ < Y k ω := hD1.1 k le_rfl
          have h2 : -η ≤ Y (k + 1) ω - Y k ω := not_lt.1 hD2
          rw [hMY]
          refine Real.exp_le_exp.2 ?_
          nlinarith [mul_nonneg ha (show 0 ≤ Y (k + 1) ω + (δ + η) by linarith)]
      _ = P.real (firstPassageSet Y δ k \ {ω | Y (k + 1) ω - Y k ω < -η}) *
            Real.exp (a * (δ + η)) := by rw [setIntegral_const, smul_eq_mul]
      _ ≤ P.real (firstPassageSet Y δ k) * Real.exp (a * (δ + η)) := by
          exact mul_le_mul_of_nonneg_right (measureReal_mono Set.sdiff_subset)
            (Real.exp_pos _).le
      _ = _ := mul_comm _ _
  have h2 : ∫ ω in firstPassageSet Y δ k ∩ {ω | Y (k + 1) ω - Y k ω < -η}, M (k + 1) ω ∂P ≤ q := by
    refine le_trans (setIntegral_mono_set (hM.integrable (k + 1)).integrableOn
      (Filter.Eventually.of_forall hnn) (Set.inter_subset_right.eventuallyLE)) hq
  linarith


/-- **Gambler's ruin with overshoot control.**  See the module docstring. -/
theorem exp_mul_mul_le_measureReal_exists_le [IsProbabilityMeasure P] (hM : Martingale M 𝒢 P)
    (hY : ∀ k, Measurable[𝒢 k] (Y k)) {a : ℝ} (hMY : ∀ k ω, M k ω = Real.exp (-a * Y k ω))
    (ha : 0 < a) (hM0 : ∫ ω, M 0 ω ∂P = 1) {δ : ℝ} (hY0 : ∀ᵐ ω ∂P, -δ < Y 0 ω)
    (η q ρ : ℝ) (n : ℕ)
    (hq : ∀ k < n, ∫ ω in {ω | Y (k + 1) ω - Y k ω < -η}, M (k + 1) ω ∂P ≤ q)
    (hρ : ∫ ω in survivalSet Y δ n, M n ω ∂P ≤ ρ) :
    Real.exp (-(a * (δ + η))) * (1 - n * q - ρ) ≤ P.real {ω | ∃ k ≤ n, Y k ω ≤ -δ} := by
  have hG0 : ∀ᵐ ω ∂P, ω ∈ survivalSet Y δ 0 := by
    filter_upwards [hY0] with ω hω j hj
    have : j = 0 := by omega
    subst this
    exact hω
  have hrestr : P.restrict (survivalSet Y δ 0) = P := Measure.restrict_eq_self_of_ae_mem hG0
  have hYm : ∀ j, Measurable (Y j) := fun j => (hY j).mono (𝒢.le j) le_rfl
  have hGn : MeasurableSet (survivalSet Y δ n) := 𝒢.le n _ (measurableSet_survivalSet hY δ n)
  -- telescoping for `M`
  have hT := setIntegral_survivalSet_eq hM hY δ n
  rw [hrestr, hM0] at hT
  -- telescoping for the constant martingale: the probabilities of the first passages
  have hone : ∀ s : Set Ω, ∫ ω in s, (1 : ℝ) ∂P = P.real s := fun s => by
    rw [setIntegral_const, smul_eq_mul, mul_one]
  have hT1 := setIntegral_survivalSet_eq (martingale_const 𝒢 P (1 : ℝ)) hY δ n
  beta_reduce at hT1
  rw [hrestr] at hT1
  simp only [hone] at hT1
  simp only [integral_const, probReal_univ, smul_eq_mul, mul_one] at hT1
  have hcompl : P.real {ω | ∃ k ≤ n, Y k ω ≤ -δ} = 1 - P.real (survivalSet Y δ n) := by
    have : {ω | ∃ k ≤ n, Y k ω ≤ -δ} = (survivalSet Y δ n)ᶜ := by
      ext ω
      simp [survivalSet, not_lt]
    rw [this, probReal_compl_eq_one_sub hGn]
  have hsum : ∑ i ∈ Finset.range n, ∫ ω in firstPassageSet Y δ i, M (i + 1) ω ∂P ≤
      Real.exp (a * (δ + η)) * ∑ i ∈ Finset.range n, P.real (firstPassageSet Y δ i) + n * q := by
    calc _ ≤ ∑ i ∈ Finset.range n, (Real.exp (a * (δ + η)) * P.real (firstPassageSet Y δ i) + q) :=
          Finset.sum_le_sum fun i hi => setIntegral_firstPassageSet_le hM hY hMY ha.le δ η q i
            (hq i (Finset.mem_range.1 hi))
      _ = _ := by rw [Finset.sum_add_distrib, ← Finset.mul_sum]; simp
  have hprob : ∑ i ∈ Finset.range n, P.real (firstPassageSet Y δ i) =
      P.real {ω | ∃ k ≤ n, Y k ω ≤ -δ} := by
    rw [hcompl]
    linarith
  rw [hprob] at hsum
  have hE : 0 < Real.exp (a * (δ + η)) := Real.exp_pos _
  have hkey : 1 - n * q - ρ ≤ Real.exp (a * (δ + η)) * P.real {ω | ∃ k ≤ n, Y k ω ≤ -δ} := by
    linarith
  calc Real.exp (-(a * (δ + η))) * (1 - n * q - ρ)
      ≤ Real.exp (-(a * (δ + η))) *
          (Real.exp (a * (δ + η)) * P.real {ω | ∃ k ≤ n, Y k ω ≤ -δ}) :=
        mul_le_mul_of_nonneg_left hkey (Real.exp_pos _).le
    _ = _ := by rw [← mul_assoc, ← Real.exp_add]; simp

end LatticeProb
