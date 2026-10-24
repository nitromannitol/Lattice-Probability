import LatticeProb.Prob.JumpChain.Memoryless
import LatticeProb.Prob.JumpChain.ClockLaw
import LatticeProb.Prob.JumpChain.RingCount

/-!
# Finite-dimensional clock-ring laws

Residual clock sums identify ring windows after a deterministic shift. The exponential
product law gives Poisson ring probabilities and their finite-dimensional factorization.
-/

namespace LatticeProb.JumpChain

open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal

noncomputable section

/-- Exactly `n` clock rings have occurred at time `t`. -/
def ring (n : ℕ) (t : ℝ) (e : ℕ → ℝ) : Prop :=
  clockSum e n ≤ t ∧ t < clockSum e (n + 1)

/-- A ring window is measurable in the clock sequence. -/
theorem measurableSet_ring (n : ℕ) (t : ℝ) : MeasurableSet {e | ring n t e} :=
  (measurableSet_le (measurable_clockSum n) measurable_const).inter
    (measurableSet_lt measurable_const (measurable_clockSum (n + 1)))

/-- Positive-index residual sums are the original sums minus the shift time. -/
theorem clockSum_clockShift_succ (e : ℕ → ℝ) (n m : ℕ) (s : ℝ) :
    clockSum (clockShift n s e) (m + 1) = clockSum e (n + (m + 1)) - s := by
  induction m with
  | zero => simp [clockSum, clockShift]
  | succ m ih =>
    rw [clockSum_succ, ih]
    simp only [clockShift, Nat.add_eq_zero_iff, Nat.one_ne_zero, and_false, if_false]
    rw [show n + (m + 1 + 1) = (n + (m + 1)) + 1 by omega, clockSum_succ]
    ring

/-- A ring window becomes a residual ring window after shifting at an earlier window. -/
theorem ring_shift_iff {e : ℕ → ℝ} {n : ℕ} {s t : ℝ}
    (hn : ring n s e) (hst : s ≤ t) (m : ℕ) :
    ring (n + m) t e ↔ ring m (t - s) (clockShift n s e) := by
  cases m with
  | zero =>
    simp only [ring, Nat.add_zero, clockSum_clockShift_succ]
    have hz : clockSum (clockShift n s e) 0 = 0 := by simp [clockSum]
    rw [hz]
    constructor
    · intro h
      exact ⟨sub_nonneg.mpr hst, by linarith [h.2]⟩
    · intro h
      exact ⟨hn.1.trans hst, by linarith [h.2]⟩
  | succ m =>
    simp only [ring, clockSum_clockShift_succ, Nat.add_assoc]
    constructor <;> intro h <;> constructor <;> linarith [h.1, h.2]

/-- The canonical exponential clock law has Poisson single-time ring probabilities. -/
theorem infinitePi_ring {R : ℝ} (hR : 0 < R) (n : ℕ) {t : ℝ} (ht : 0 ≤ t) :
    (Measure.infinitePi (fun _ : ℕ ↦ expMeasure R)) {e | ring n t e} =
      ENNReal.ofReal (Real.exp (-(R * t)) * (R * t) ^ n / n.factorial) := by
  let rates : BoundedRates Unit :=
    { q := fun _ _ ↦ 0
      q_nonneg := fun _ _ ↦ le_rfl
      q_self := fun _ ↦ rfl
      summable := fun _ ↦ summable_zero
      R := R
      R_pos := hR
      total_le := fun _ ↦ by simpa only [tsum_zero] using hR.le }
  have hm := rates.historyLaw_map_clocks (Measure.dirac ())
  rw [rates.clockLaw_eq_expMeasure] at hm
  rw [← hm, Measure.map_apply (by fun_prop) (measurableSet_ring n t)]
  exact rates.historyLaw_jumpTime_window (Measure.dirac ()) ⟨t, ht⟩ n

/-- Joint ring windows factor into the Poisson probabilities of successive increments. -/
theorem infinitePi_ring_fdd {R : ℝ} (hR : 0 < R) (k : ℕ)
    (t : Fin (k + 1) → ℝ) (ht : Monotone t) (ht0 : t 0 = 0)
    (n : Fin (k + 1) → ℕ) (hn : Monotone n) (hn0 : n 0 = 0) :
    (Measure.infinitePi (fun _ : ℕ ↦ expMeasure R))
      {e | ∀ i : Fin k, ring (n i.succ) (t i.succ) e} =
      ∏ i : Fin k, ENNReal.ofReal
        (Real.exp (-(R * (t i.succ - t i.castSucc))) *
          (R * (t i.succ - t i.castSucc)) ^ (n i.succ - n i.castSucc) /
            (n i.succ - n i.castSucc).factorial) := by
  letI := isProbabilityMeasure_expMeasure hR
  induction k with
  | zero => simp only [Fin.forall_fin_zero, Set.setOf_true, measure_univ, Fin.prod_univ_zero]
  | succ k ih =>
    let u : Fin (k + 1) → ℝ := fun i ↦ t i.succ - t 1
    let v : Fin (k + 1) → ℕ := fun i ↦ n i.succ - n 1
    have hu : Monotone u := fun i j hij ↦ sub_le_sub_right (ht (by simpa using hij)) _
    have hv : Monotone v := fun i j hij ↦ Nat.sub_le_sub_right
      (hn (by simpa using hij)) _
    have hu0 : u 0 = 0 := sub_self _
    have hv0 : v 0 = 0 := Nat.sub_self _
    let C : Set (ℕ → ℝ) := {e | ∀ i : Fin k, ring (v i.succ) (u i.succ) e}
    have hC : MeasurableSet C := by
      simpa only [C, Set.setOf_forall] using
        (MeasurableSet.iInter fun i : Fin k ↦
          measurableSet_ring (v i.succ) (u i.succ))
    have hshift := infinitePi_clockShift hR (n 1) MeasurableSet.univ hC (t 1)
    simp only [Set.mem_univ, true_and] at hshift
    have hset : {e | ∀ i : Fin (k + 1), ring (n i.succ) (t i.succ) e} =
        {e | clockSum e (n 1) ≤ t 1 ∧ t 1 < clockSum e (n 1 + 1) ∧
          clockShift (n 1) (t 1) e ∈ C} := by
      ext e
      simp only [Set.mem_setOf_eq]
      rw [Fin.forall_fin_succ]
      change (ring (n 1) (t 1) e ∧
        ∀ i : Fin k, ring (n i.succ.succ) (t i.succ.succ) e) ↔ _
      constructor
      · rintro ⟨hfirst, hrest⟩
        refine ⟨hfirst.1, hfirst.2, ?_⟩
        intro i
        have hle : n 1 ≤ n i.succ.succ := hn (by
          simp only [Fin.le_iff_val_le_val, Fin.val_one, Fin.val_succ]
          omega)
        have htime : t 1 ≤ t i.succ.succ := ht (by
          simp only [Fin.le_iff_val_le_val, Fin.val_one, Fin.val_succ]
          omega)
        have h := (ring_shift_iff hfirst htime (v i.succ)).mp
          (by simpa only [v, Nat.add_sub_of_le hle] using hrest i)
        exact h
      · rintro ⟨hlo, hhi, hrest⟩
        refine ⟨⟨hlo, hhi⟩, ?_⟩
        intro i
        have hle : n 1 ≤ n i.succ.succ := hn (by
          simp only [Fin.le_iff_val_le_val, Fin.val_one, Fin.val_succ]
          omega)
        have htime : t 1 ≤ t i.succ.succ := ht (by
          simp only [Fin.le_iff_val_le_val, Fin.val_one, Fin.val_succ]
          omega)
        have h := (ring_shift_iff ⟨hlo, hhi⟩ htime (v i.succ)).mpr (hrest i)
        simpa only [v, Nat.add_sub_of_le hle] using h
    rw [hset, hshift]
    change (Measure.infinitePi (fun _ : ℕ ↦ expMeasure R))
      {e | ring (n 1) (t 1) e} *
        (Measure.infinitePi (fun _ : ℕ ↦ expMeasure R)) C = _
    have ht1 : 0 ≤ t 1 := by simpa only [ht0] using ht (Fin.zero_le 1)
    rw [infinitePi_ring hR (n 1) ht1,
      ih u hu hu0 v hv hv0, Fin.prod_univ_succ]
    congr 1
    · simp only [Fin.castSucc_zero, ht0, hn0, sub_zero, Nat.sub_zero, Fin.succ_zero_eq_one]
    · apply Finset.prod_congr rfl
      intro i _
      have heq : v i.succ - v i.castSucc =
          n i.succ.succ - n i.succ.castSucc := by
        dsimp [v]
        have hbase : n 1 ≤ n i.castSucc.succ := hn (by
          simp only [Fin.le_iff_val_le_val, Fin.val_one, Fin.val_succ, Fin.val_castSucc]
          omega)
        have hstep : n i.castSucc.succ ≤ n i.succ.succ := hn (by
          simp only [Fin.le_iff_val_le_val, Fin.val_succ, Fin.val_castSucc]
          omega)
        omega
      have htime : u i.succ - u i.castSucc =
          t i.succ.succ - t i.succ.castSucc := by
        dsimp [u]
        ring
      rw [heq, htime]

namespace BoundedRates

variable {S : Type*} [MeasurableSpace S] [Countable S] [MeasurableSingletonClass S]

/-- Joint ring-time windows on histories have independent Poisson increments. -/
theorem historyLaw_jumpTime_fdd (rates : BoundedRates S) (μ : Measure S)
    [IsProbabilityMeasure μ] (k : ℕ) (t : Fin (k + 1) → ℝ)
    (ht : Monotone t) (ht0 : t 0 = 0) (n : Fin (k + 1) → ℕ)
    (hn : Monotone n) (hn0 : n 0 = 0) :
    rates.historyLaw μ {h | ∀ i : Fin k,
      jumpTime h (n i.succ) ≤ t i.succ ∧ t i.succ < jumpTime h (n i.succ + 1)} =
      ∏ i : Fin k, ENNReal.ofReal
        (Real.exp (-(rates.R * (t i.succ - t i.castSucc))) *
          (rates.R * (t i.succ - t i.castSucc)) ^ (n i.succ - n i.castSucc) /
            (n i.succ - n i.castSucc).factorial) := by
  have hm := rates.historyLaw_map_clocks μ
  rw [rates.clockLaw_eq_expMeasure] at hm
  have h := infinitePi_ring_fdd rates.R_pos k t ht ht0 n hn hn0
  rw [← hm, Measure.map_apply (by fun_prop)
    (by simpa only [Set.setOf_forall] using
      (MeasurableSet.iInter fun i : Fin k ↦
        measurableSet_ring (n i.succ) (t i.succ)))] at h
  exact h

/-- Regular-history ring-time windows retain the finite-dimensional Poisson law. -/
theorem regularLaw_jumpTime_fdd (rates : BoundedRates S) (μ : Measure S)
    [IsProbabilityMeasure μ] (k : ℕ) (t : Fin (k + 1) → ℝ)
    (ht : Monotone t) (ht0 : t 0 = 0) (n : Fin (k + 1) → ℕ)
    (hn : Monotone n) (hn0 : n 0 = 0) :
    rates.regularLaw μ {h | ∀ i : Fin k,
      jumpTime h.val (n i.succ) ≤ t i.succ ∧
        t i.succ < jumpTime h.val (n i.succ + 1)} =
      ∏ i : Fin k, ENNReal.ofReal
        (Real.exp (-(rates.R * (t i.succ - t i.castSucc))) *
          (rates.R * (t i.succ - t i.castSucc)) ^ (n i.succ - n i.castSucc) /
            (n i.succ - n i.castSucc).factorial) := by
  have h := rates.historyLaw_jumpTime_fdd μ k t ht ht0 n hn hn0
  rw [← rates.regularLaw_map_val μ, Measure.map_apply measurable_subtype_coe
    (by simpa only [Set.setOf_forall, Set.setOf_and] using (MeasurableSet.iInter fun i : Fin k ↦
      (measurableSet_le (measurable_jumpTime (n i.succ)) measurable_const).inter
        (measurableSet_lt measurable_const (measurable_jumpTime (n i.succ + 1)))))] at h
  exact h

/-- The actual regular-history counts have the Poisson finite-dimensional law. -/
theorem regularLaw_ringCount_fdd (rates : BoundedRates S) (μ : Measure S)
    [IsProbabilityMeasure μ] (k : ℕ) (t : Fin (k + 1) → ℝ≥0)
    (ht : Monotone t) (ht0 : t 0 = 0) (n : Fin (k + 1) → ℕ)
    (hn : Monotone n) (hn0 : n 0 = 0) :
    rates.regularLaw μ {h | ∀ i : Fin k, h.ringCount (t i.succ) = n i.succ} =
      ∏ i : Fin k, ENNReal.ofReal
        (Real.exp (-(rates.R * ((t i.succ : ℝ) - t i.castSucc))) *
          (rates.R * ((t i.succ : ℝ) - t i.castSucc)) ^ (n i.succ - n i.castSucc) /
            (n i.succ - n i.castSucc).factorial) := by
  have hset : {h : RegularHistory S |
      ∀ i : Fin k, h.ringCount (t i.succ) = n i.succ} =
      {h | ∀ i : Fin k, jumpTime h.val (n i.succ) ≤ t i.succ ∧
        (t i.succ : ℝ) < jumpTime h.val (n i.succ + 1)} := by
    ext h
    exact forall_congr' fun i ↦ h.ringCount_eq_iff (t i.succ) (n i.succ)
  rw [hset]
  exact rates.regularLaw_jumpTime_fdd μ k (fun i ↦ (t i : ℝ))
    (fun i j hij ↦ ht hij) (by simp only [ht0, NNReal.coe_zero]) n hn hn0

end BoundedRates

end

end LatticeProb.JumpChain
