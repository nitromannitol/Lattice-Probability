import LatticeProb.Prob.JumpChain.StateChain
import LatticeProb.Analysis.KernelPowersCS

/-!
# Killed finite-dimensional state laws

Killing removes transitions whose destination lies outside the prescribed set.
Finite set cylinders are obtained by summing the exact singleton path masses.
Arbitrary finite prefix events propagate through killed powers, which gives the
finite-dimensional laws at monotone observation times, including repeated times.
-/

namespace LatticeProb.JumpChain

open MeasureTheory ProbabilityTheory Set Function

noncomputable section

attribute [local instance] Classical.propDecidable

namespace BoundedRates

variable {S : Type*}

/-- The embedded transition matrix killed on arrival outside `U`. -/
def killedP (rates : BoundedRates S) (U : Set S) : S → S → ℝ := by
  classical
  exact fun x y ↦ if y ∈ U then rates.p x y else 0

/-- Every killed transition mass is nonnegative. -/
theorem killedP_nonneg (rates : BoundedRates S) (U : Set S) (x y : S) :
    0 ≤ rates.killedP U x y := by
  classical
  simp only [killedP]
  split <;> simp_all only [rates.p_nonneg, le_refl]

/-- Killing decreases each transition mass. -/
theorem killedP_le_p (rates : BoundedRates S) (U : Set S) (x y : S) :
    rates.killedP U x y ≤ rates.p x y := by
  classical
  simp only [killedP]
  split
  · exact le_rfl
  · exact rates.p_nonneg x y

/-- Each row of the killed transition matrix is summable. -/
theorem killedP_summable (rates : BoundedRates S) (U : Set S) (x : S) :
    Summable (rates.killedP U x) :=
  (rates.hasSum_p x).summable.of_nonneg_of_le (rates.killedP_nonneg U x)
    (rates.killedP_le_p U x)

/-- Each killed row has total mass at most one. -/
theorem killedP_tsum_le_one (rates : BoundedRates S) (U : Set S) (x : S) :
    ∑' y, rates.killedP U x y ≤ 1 := by
  rw [← (rates.hasSum_p x).tsum_eq]
  exact (rates.killedP_summable U x).tsum_le_tsum (rates.killedP_le_p U x)
    (rates.hasSum_p x).summable

/-- Killing on the full state space leaves the transition matrix unchanged. -/
@[simp] theorem killedP_univ (rates : BoundedRates S) : rates.killedP univ = rates.p := by
  classical
  funext x y
  simp only [killedP, mem_univ, ite_true]

/-- Killed powers are bounded by the corresponding unrestricted powers. -/
theorem kernelPow_killedP_le (rates : BoundedRates S) (U : Set S)
    (m : ℕ) (x z : S) : kernelPow (rates.killedP U) m x z ≤ kernelPow rates.p m x z := by
  induction m generalizing x z with
  | zero => exact le_rfl
  | succ m ih =>
    apply Summable.tsum_le_tsum
      (fun y ↦ mul_le_mul (ih x y) (rates.killedP_le_p U y z)
        (rates.killedP_nonneg U y z) (kernelPow_nonneg rates.p_nonneg m x y))
    · apply ((kernelPow_summable rates.p_nonneg rates.hasSum_p m x).of_nonneg_of_le
        (fun y ↦ mul_nonneg (kernelPow_nonneg (rates.killedP_nonneg U) m x y)
          (rates.killedP_nonneg U y z)))
      intro y
      exact (mul_le_mul (ih x y) (rates.killedP_le_p U y z)
        (rates.killedP_nonneg U y z) (kernelPow_nonneg rates.p_nonneg m x y)).trans
        (mul_le_of_le_one_right (kernelPow_nonneg rates.p_nonneg m x y)
          (kernel_entry_le_one rates.p_nonneg rates.hasSum_p y z))
    · apply (kernelPow_summable rates.p_nonneg rates.hasSum_p m x).of_nonneg_of_le
        (fun y ↦ mul_nonneg (kernelPow_nonneg rates.p_nonneg m x y) (rates.p_nonneg y z))
      intro y
      exact mul_le_of_le_one_right (kernelPow_nonneg rates.p_nonneg m x y)
        (kernel_entry_le_one rates.p_nonneg rates.hasSum_p y z)

/-- Killed powers have summable rows. -/
theorem kernelPow_killedP_summable (rates : BoundedRates S) (U : Set S)
    (m : ℕ) (x : S) : Summable (kernelPow (rates.killedP U) m x) :=
  (kernelPow_summable rates.p_nonneg rates.hasSum_p m x).of_nonneg_of_le
    (kernelPow_nonneg (rates.killedP_nonneg U) m x) (rates.kernelPow_killedP_le U m x)

/-- A killed power step becomes convolution of nonnegative extended-real masses. -/
theorem ofReal_kernelPow_killedP_succ (rates : BoundedRates S) (U : Set S)
    (m : ℕ) (x z : S) :
    ENNReal.ofReal (kernelPow (rates.killedP U) (m + 1) x z) =
      ∑' y, ENNReal.ofReal (kernelPow (rates.killedP U) m x y) *
        ENNReal.ofReal (rates.killedP U y z) := by
  have hs : Summable (fun y ↦ kernelPow (rates.killedP U) m x y *
      rates.killedP U y z) := by
    apply (rates.kernelPow_killedP_summable U m x).of_nonneg_of_le
      (fun y ↦ mul_nonneg (kernelPow_nonneg (rates.killedP_nonneg U) m x y)
        (rates.killedP_nonneg U y z))
    intro y
    exact mul_le_of_le_one_right (kernelPow_nonneg (rates.killedP_nonneg U) m x y)
      ((rates.killedP_le_p U y z).trans
        (kernel_entry_le_one rates.p_nonneg rates.hasSum_p y z))
  rw [kernelPow, kernelComp, ENNReal.ofReal_tsum_of_nonneg
    (fun y ↦ mul_nonneg (kernelPow_nonneg (rates.killedP_nonneg U) m x y)
      (rates.killedP_nonneg U y z)) hs]
  exact tsum_congr fun y ↦ ENNReal.ofReal_mul
    (kernelPow_nonneg (rates.killedP_nonneg U) m x y)

/-- A killed power sums exactly the paths whose arrivals remain in the killing set. -/
theorem ofReal_kernelPow_killedP (rates : BoundedRates S) (U : Set S)
    (m : ℕ) (x z : S) :
    ENNReal.ofReal (kernelPow (rates.killedP U) m x z) =
      ∑' y : Fin (m + 1) → S,
        if y 0 = x ∧ y (Fin.last m) = z ∧ ∀ k : Fin m, y k.succ ∈ U then
          ∏ k : Fin m, ENNReal.ofReal (rates.p (y k.castSucc) (y k.succ))
        else 0 := by
  classical
  induction m generalizing x z with
  | zero =>
    rw [← (Equiv.funUnique (Fin 1) S).symm.tsum_eq]
    simp only [Equiv.funUnique_symm_apply, uniqueElim_const, Fin.last_zero,
      Fin.prod_univ_zero, Fin.forall_fin_zero, and_true, kernelPow]
    rw [tsum_eq_single x]
    · by_cases hx : x = z <;>
        simp only [hx, true_and, ite_true, ite_false,
          ENNReal.ofReal_one, ENNReal.ofReal_zero]
    · intro a ha
      simp only [ha, false_and, ite_false]
  | succ m ih =>
    rw [rates.ofReal_kernelPow_killedP_succ]
    simp only [ih, ← ENNReal.tsum_mul_right]
    rw [ENNReal.tsum_comm]
    have hleft (y : Fin (m + 1) → S) :
        (∑' a, (if y 0 = x ∧ y (Fin.last m) = a ∧
            ∀ k : Fin m, y k.succ ∈ U then
            ∏ k : Fin m, ENNReal.ofReal (rates.p (y k.castSucc) (y k.succ))
          else 0) * ENNReal.ofReal (rates.killedP U a z)) =
        if y 0 = x ∧ (∀ k : Fin m, y k.succ ∈ U) ∧ z ∈ U then
          (∏ k : Fin m, ENNReal.ofReal (rates.p (y k.castSucc) (y k.succ))) *
            ENNReal.ofReal (rates.p (y (Fin.last m)) z)
        else 0 := by
      rw [tsum_eq_single (y (Fin.last m))]
      · by_cases h0 : y 0 = x <;>
          by_cases hU : ∀ k : Fin m, y k.succ ∈ U <;> by_cases hz : z ∈ U <;>
          simp [h0, hU, hz, killedP]
      · intro a ha
        have hne : y (Fin.last m) ≠ a := Ne.symm ha
        simp only [hne, false_and, and_false, ite_false, zero_mul]
    simp_rw [hleft]
    rw [← (Fin.snocEquiv (fun _ : Fin (m + 1 + 1) ↦ S)).tsum_eq,
      ENNReal.tsum_prod', ENNReal.tsum_comm]
    apply tsum_congr
    intro y
    rw [tsum_eq_single z]
    · have harr : (∀ k : Fin (m + 1), Fin.snoc (α := fun _ ↦ S) y z k.succ ∈ U) ↔
          (∀ k : Fin m, y k.succ ∈ U) ∧ z ∈ U := by
        rw [Fin.forall_iff_castSucc]
        simp only [← Fin.castSucc_succ, Fin.snoc_castSucc, Fin.succ_last, Fin.snoc_last]
        exact and_comm
      simp only [Fin.snocEquiv_apply, Fin.snoc_apply_zero, Fin.snoc_last,
        true_and, harr, Fin.prod_univ_castSucc,
        ← Fin.castSucc_succ, Fin.snoc_castSucc, Fin.succ_last]
    · intro a ha
      simp only [Fin.snocEquiv_apply, Fin.snoc_last, ha, false_and, and_false,
        ite_false]

variable [MeasurableSpace S] [Countable S] [MeasurableSingletonClass S]

/-- The singleton cylinder formula expressed using finite path coordinates. -/
theorem historyLaw_state_fin_cylinder (rates : BoundedRates S) (μ : Measure S)
    [IsProbabilityMeasure μ] (n : ℕ) (y : Fin (n + 1) → S) :
    rates.historyLaw μ {h | ∀ k : Fin (n + 1), (h k).1 = y k} =
      μ {y 0} * ∏ k : Fin n, ENNReal.ofReal (rates.p (y k.castSucc) (y k.succ)) := by
  let x : ℕ → S := fun k ↦ y ⟨min k n, by omega⟩
  have hevent : {h : History S | ∀ k : Fin (n + 1), (h k).1 = y k} =
      {h | ∀ k ≤ n, (h k).1 = x k} := by
    ext h
    constructor
    · intro hh k hk
      simpa only [x, min_eq_left hk] using hh ⟨k, by omega⟩
    · intro hh k
      simpa only [x, min_eq_left (show k.val ≤ n by omega)] using hh k (by omega)
  rw [hevent, rates.historyLaw_state_cylinder μ n x, ← Fin.prod_univ_eq_prod_range]
  congr 1
  apply Finset.prod_congr rfl
  intro k _
  simp only [x, min_eq_left (show k.val ≤ n by omega),
    min_eq_left (show k.val + 1 ≤ n by omega)]
  rfl

/-- Any event determined by a finite state prefix is a sum of singleton path masses. -/
theorem historyLaw_state_prefix_event (rates : BoundedRates S) (μ : Measure S)
    [IsProbabilityMeasure μ] (n : ℕ) (C : (Fin (n + 1) → S) → Prop) :
    rates.historyLaw μ {h | C (fun k ↦ (h k).1)} =
      ∑' y : Fin (n + 1) → S, if C y then
        μ {y 0} * ∏ k : Fin n, ENNReal.ofReal (rates.p (y k.castSucc) (y k.succ))
      else 0 := by
  let f : History S → (Fin (n + 1) → S) := fun h k ↦ (h k).1
  have hf : Measurable f := by fun_prop
  have hC : MeasurableSet {y | C y} := (Set.to_countable _).measurableSet
  change rates.historyLaw μ (f ⁻¹' {y | C y}) = _
  rw [← Measure.map_apply hf hC, ← Measure.tsum_indicator_apply_singleton _ _ hC]
  apply tsum_congr
  intro y
  simp only [Set.indicator_apply, Set.mem_setOf_eq]
  split
  · rw [Measure.map_apply hf (measurableSet_singleton y)]
    have heq : f ⁻¹' {y} =
        {h : History S | ∀ k : Fin (n + 1), (h k).1 = y k} := by
      ext h
      exact funext_iff
    rw [heq, rates.historyLaw_state_fin_cylinder]
  · rfl

/-- Extending an arbitrary finite state event by one specified state uses one transition. -/
theorem historyLaw_state_prefix_succ (rates : BoundedRates S) (μ : Measure S)
    [IsProbabilityMeasure μ] (n : ℕ) (C : (Fin (n + 1) → S) → Prop) (z : S) :
    rates.historyLaw μ {h | C (fun k ↦ (h k).1) ∧ (h (n + 1)).1 = z} =
      ∑' a, rates.historyLaw μ {h | C (fun k ↦ (h k).1) ∧ (h n).1 = a} *
        ENNReal.ofReal (rates.p a z) := by
  have hfull : {h : History S | C (fun k ↦ (h k).1) ∧ (h (n + 1)).1 = z} =
      {h | (fun y : Fin (n + 1 + 1) → S ↦
        C (Fin.init y) ∧ y (Fin.last (n + 1)) = z) (fun k ↦ (h k).1)} := rfl
  rw [hfull, rates.historyLaw_state_prefix_event μ (n + 1)
    (fun y ↦ C (Fin.init y) ∧ y (Fin.last (n + 1)) = z),
    ← (Fin.snocEquiv (fun _ : Fin (n + 1 + 1) ↦ S)).tsum_eq,
    ENNReal.tsum_prod', ENNReal.tsum_comm]
  trans ∑' y : Fin (n + 1) → S,
    (if C y then μ {y 0} * ∏ k : Fin n,
      ENNReal.ofReal (rates.p (y k.castSucc) (y k.succ)) else 0) *
        ENNReal.ofReal (rates.p (y (Fin.last n)) z)
  · apply tsum_congr
    intro y
    rw [tsum_eq_single z]
    · simp only [Fin.snocEquiv, Equiv.coe_fn_mk, Fin.init_snoc, Fin.snoc_last,
        and_true, Fin.snoc_apply_zero, Fin.prod_univ_castSucc, Fin.snoc_castSucc,
        ← Fin.castSucc_succ, Fin.succ_last, Fin.snoc_castSucc]
      by_cases hc : C y <;> simp only [hc, ite_true, ite_false, mul_assoc, zero_mul]
    · intro a ha
      simp only [Fin.snocEquiv, Equiv.coe_fn_mk, Fin.snoc_last, ha, and_false, ite_false]
  · have hprefix (a : S) :
        rates.historyLaw μ {h | C (fun k ↦ (h k).1) ∧ (h n).1 = a} =
          ∑' y : Fin (n + 1) → S, if C y ∧ y (Fin.last n) = a then
            μ {y 0} * ∏ k : Fin n,
              ENNReal.ofReal (rates.p (y k.castSucc) (y k.succ)) else 0 :=
      by
        convert rates.historyLaw_state_prefix_event μ n
          (fun y ↦ C y ∧ y (Fin.last n) = a) using 1
        · simp only [Fin.val_last]
        · apply tsum_congr
          intro y
          by_cases hy : C y ∧ y (Fin.last n) = a <;> simp only [hy, ite_false]
    simp_rw [hprefix, ← ENNReal.tsum_mul_right]
    rw [ENNReal.tsum_comm]
    apply tsum_congr
    intro y
    rw [tsum_eq_single (y (Fin.last n))]
    · simp only [and_true]
    · intro a ha
      simp only [Ne.symm ha, and_false, ite_false, zero_mul]

/-- A finite prefix event propagates across a gap by the killed matrix power. -/
theorem historyLaw_state_prefix_gap (rates : BoundedRates S) (μ : Measure S)
    [IsProbabilityMeasure μ] (U : Set S) (a b : ℕ)
    (C : (Fin (a + 1) → S) → Prop) (z : S) :
    rates.historyLaw μ {h | C (fun k ↦ (h k).1) ∧ (h (a + b)).1 = z ∧
      ∀ j, a < j → j ≤ a + b → (h j).1 ∈ U} =
      ∑' y, rates.historyLaw μ {h | C (fun k ↦ (h k).1) ∧ (h a).1 = y} *
        ENNReal.ofReal (kernelPow (rates.killedP U) b y z) := by
  induction b generalizing z with
  | zero =>
    simp only [Nat.add_zero, kernelPow]
    have hevent : {h : History S | C (fun k ↦ (h k).1) ∧ (h a).1 = z ∧
        ∀ j, a < j → j ≤ a → (h j).1 ∈ U} =
        {h | C (fun k ↦ (h k).1) ∧ (h a).1 = z} := by
      ext h
      exact ⟨fun hh ↦ ⟨hh.1, hh.2.1⟩,
        fun hh ↦ ⟨hh.1, hh.2, fun j hj hja ↦ (Nat.not_lt_of_ge hja hj).elim⟩⟩
    rw [hevent, tsum_eq_single z]
    · simp only [ite_true, ENNReal.ofReal_one, mul_one]
    · intro y hy
      simp only [hy, ite_false, ENNReal.ofReal_zero, mul_zero]
  | succ b ih =>
    let D : (Fin (a + b + 1) → S) → Prop := fun y ↦
      C (fun k ↦ y ⟨k, by omega⟩) ∧
        ∀ j : Fin (a + b + 1), a < j.val → y j ∈ U
    have hD (h : History S) : D (fun k ↦ (h k).1) ↔
        C (fun k ↦ (h k).1) ∧ ∀ j, a < j → j ≤ a + b → (h j).1 ∈ U := by
      constructor
      · rintro ⟨hc, hu⟩
        exact ⟨hc, fun j hj hjb ↦ hu ⟨j, by omega⟩ hj⟩
      · rintro ⟨hc, hu⟩
        exact ⟨hc, fun j hj ↦ hu j hj (by omega)⟩
    have hpre (y : S) :
        {h : History S | D (fun k ↦ (h k).1) ∧ (h (a + b)).1 = y} =
        {h | C (fun k ↦ (h k).1) ∧ (h (a + b)).1 = y ∧
          ∀ j, a < j → j ≤ a + b → (h j).1 ∈ U} := by
      ext h
      rw [Set.mem_setOf_eq, Set.mem_setOf_eq, hD]
      exact ⟨fun hh ↦ ⟨hh.1.1, hh.2, hh.1.2⟩,
        fun hh ↦ ⟨⟨hh.1, hh.2.2⟩, hh.2.1⟩⟩
    by_cases hz : z ∈ U
    · have hevent : {h : History S | C (fun k ↦ (h k).1) ∧
          (h (a + (b + 1))).1 = z ∧ ∀ j, a < j → j ≤ a + (b + 1) → (h j).1 ∈ U} =
          {h | D (fun k ↦ (h k).1) ∧ (h (a + b + 1)).1 = z} := by
        ext h
        simp only [Set.mem_setOf_eq, hD]
        constructor
        · rintro ⟨hc, hx, hu⟩
          exact ⟨⟨hc, fun j hj hjb ↦ hu j hj (by omega)⟩, hx⟩
        · rintro ⟨⟨hc, hu⟩, hx⟩
          refine ⟨hc, hx, fun j hj hjb ↦ ?_⟩
          by_cases hjpre : j ≤ a + b
          · exact hu j hj hjpre
          · have hjlast : j = a + b + 1 := by omega
            simpa only [hjlast, hx] using hz
      rw [hevent, rates.historyLaw_state_prefix_succ μ (a + b) D z]
      simp only [hpre, ih, ← ENNReal.tsum_mul_right]
      rw [ENNReal.tsum_comm]
      apply tsum_congr
      intro y
      rw [rates.ofReal_kernelPow_killedP_succ, ← ENNReal.tsum_mul_left]
      apply tsum_congr
      intro v
      simp only [killedP, hz, ite_true, mul_assoc]
    · have hevent : {h : History S | C (fun k ↦ (h k).1) ∧
          (h (a + (b + 1))).1 = z ∧ ∀ j, a < j → j ≤ a + (b + 1) → (h j).1 ∈ U} =
          ∅ := by
        apply Set.eq_empty_iff_forall_notMem.mpr
        rintro h ⟨_, hx, hu⟩
        exact hz (hx ▸ hu (a + (b + 1)) (by omega) le_rfl)
      rw [hevent, measure_empty]
      simp only [rates.ofReal_kernelPow_killedP_succ, killedP, hz, ite_false,
        ENNReal.ofReal_zero, mul_zero, tsum_zero]

/-- Set cylinders are the countable sum of their singleton path masses. -/
theorem historyLaw_state_set_cylinder (rates : BoundedRates S) (μ : Measure S)
    [IsProbabilityMeasure μ] (n : ℕ) (A : ℕ → Set S) :
    rates.historyLaw μ {h | ∀ k ≤ n, (h k).1 ∈ A k} =
      ∑' y : Fin (n + 1) → S,
        if ∀ k : Fin (n + 1), y k ∈ A k then
          μ {y 0} * ∏ k : Fin n, ENNReal.ofReal (rates.p (y k.castSucc) (y k.succ))
        else 0 := by
  have hevent : {h : History S | ∀ k ≤ n, (h k).1 ∈ A k} =
      {h | (fun y : Fin (n + 1) → S ↦ ∀ k : Fin (n + 1), y k ∈ A k)
        (fun k ↦ (h k).1)} := by
    ext h
    exact ⟨fun hh k ↦ hh k (by omega), fun hh k hk ↦ hh ⟨k, by omega⟩⟩
  rw [hevent, rates.historyLaw_state_prefix_event μ n
    (fun y ↦ ∀ k : Fin (n + 1), y k ∈ A k)]
  apply tsum_congr
  intro y
  by_cases hy : ∀ k : Fin (n + 1), y k ∈ A k <;> simp only [hy, ite_false]

/-- Fixing the initial state gives a product of killed powers at monotone observation times. -/
theorem historyLaw_killed_fdd_initial (rates : BoundedRates S) (μ : Measure S)
    [IsProbabilityMeasure μ] (U : Set S) (k : ℕ) (n : Fin (k + 1) → ℕ)
    (hn : Monotone n) (hn0 : n 0 = 0) (x : Fin (k + 1) → S) :
    rates.historyLaw μ {h | (∀ i : Fin (k + 1), (h (n i)).1 = x i) ∧
      ∀ j ≤ n (Fin.last k), (h j).1 ∈ U} =
      (if x 0 ∈ U then μ {x 0} else 0) *
        ∏ i : Fin k, ENNReal.ofReal (kernelPow (rates.killedP U)
          (n i.succ - n i.castSucc) (x i.castSucc) (x i.succ)) := by
  induction k with
  | zero =>
    have hevent : {h : History S | (∀ i : Fin 1, (h (n i)).1 = x i) ∧
        ∀ j ≤ n (Fin.last 0), (h j).1 ∈ U} =
        if x 0 ∈ U then {h | (h 0).1 = x 0} else ∅ := by
      ext h
      simp only [Fin.forall_fin_one, Fin.last_zero, hn0, Nat.le_zero, forall_eq]
      by_cases hx : x 0 ∈ U <;> simp only [hx, ite_true, ite_false, Set.mem_setOf_eq,
        Set.mem_empty_iff_false]
      · exact ⟨fun hh ↦ hh.1, fun hh ↦ ⟨hh, hh ▸ hx⟩⟩
      · exact ⟨fun hh ↦ hx (hh.1 ▸ hh.2), False.elim⟩
    rw [hevent]
    have hzero := rates.historyLaw_state_cylinder μ 0 (fun _ ↦ x 0)
    simp only [Nat.le_zero, forall_eq, Finset.range_zero, Finset.prod_empty,
      mul_one] at hzero
    split <;> simp only [measure_empty, hzero, Fin.prod_univ_zero, mul_one]
  | succ k ih =>
    let a := n (Fin.last k).castSucc
    let b := n (Fin.last (k + 1)) - a
    have hle : a ≤ n (Fin.last (k + 1)) := hn (Fin.le_last _)
    have hab : a + b = n (Fin.last (k + 1)) := Nat.add_sub_of_le hle
    let C : (Fin (a + 1) → S) → Prop := fun y ↦
      (∀ i : Fin (k + 1), y ⟨n i.castSucc, by
        have hi := hn (Fin.castSucc_le_castSucc_iff.mpr (Fin.le_last i))
        change n i.castSucc < a + 1
        omega⟩ = x i.castSucc) ∧ ∀ j : Fin (a + 1), y j ∈ U
    have hC (h : History S) : C (fun j ↦ (h j).1) ↔
        (∀ i : Fin (k + 1), (h (n i.castSucc)).1 = x i.castSucc) ∧
          ∀ j ≤ a, (h j).1 ∈ U := by
      constructor
      · rintro ⟨ho, hu⟩
        exact ⟨ho, fun j hj ↦ hu ⟨j, by omega⟩⟩
      · rintro ⟨ho, hu⟩
        exact ⟨ho, fun j ↦ hu j (by omega)⟩
    have hevent : {h : History S | (∀ i : Fin (k + 1 + 1), (h (n i)).1 = x i) ∧
        ∀ j ≤ n (Fin.last (k + 1)), (h j).1 ∈ U} =
        {h | C (fun j ↦ (h j).1) ∧ (h (a + b)).1 = x (Fin.last (k + 1)) ∧
          ∀ j, a < j → j ≤ a + b → (h j).1 ∈ U} := by
      ext h
      simp only [Set.mem_setOf_eq, hC, hab]
      rw [Fin.forall_iff_castSucc]
      constructor
      · rintro ⟨⟨hx, ho⟩, hu⟩
        exact ⟨⟨ho, fun j hj ↦ hu j (hj.trans hle)⟩, hx, fun j _ hj ↦ hu j hj⟩
      · rintro ⟨⟨ho, hu⟩, hx, hv⟩
        refine ⟨⟨hx, ho⟩, fun j hj ↦ ?_⟩
        by_cases hja : j ≤ a
        · exact hu j hja
        · exact hv j (by omega) hj
    rw [hevent, rates.historyLaw_state_prefix_gap, tsum_eq_single (x (Fin.last k).castSucc)]
    · have hsame : {h : History S | C (fun j ↦ (h j).1) ∧
          (h a).1 = x (Fin.last k).castSucc} = {h | C (fun j ↦ (h j).1)} := by
        ext h
        exact ⟨fun hh ↦ hh.1, fun hh ↦ ⟨hh, ((hC h).mp hh).1 (Fin.last k)⟩⟩
      rw [hsame]
      have hpre : {h : History S | C (fun j ↦ (h j).1)} =
          {h | (∀ i : Fin (k + 1), (h ((fun i ↦ n i.castSucc) i)).1 =
              (fun i ↦ x i.castSucc) i) ∧ ∀ j ≤ (fun i ↦ n i.castSucc) (Fin.last k),
                (h j).1 ∈ U} := by
        ext h
        exact hC h
      rw [hpre, ih (fun i ↦ n i.castSucc)
        (fun i j hij ↦ hn (Fin.castSucc_le_castSucc_iff.mpr hij)) hn0,
        Fin.prod_univ_castSucc]
      simp only [Fin.castSucc_zero, Fin.castSucc_succ, Fin.succ_last]
      exact mul_assoc _ _ _
    · intro y hy
      have hempty : {h : History S | C (fun j ↦ (h j).1) ∧ (h a).1 = y} = ∅ := by
        apply Set.eq_empty_iff_forall_notMem.mpr
        rintro h ⟨hc, hx⟩
        exact hy (hx.symm.trans (((hC h).mp hc).1 (Fin.last k)))
      rw [hempty, measure_empty, zero_mul]

/-- The killed state law at monotone observation times, with the initial state integrated out. -/
theorem historyLaw_killed_fdd (rates : BoundedRates S) (μ : Measure S)
    [IsProbabilityMeasure μ] (U : Set S) (k : ℕ) (n : Fin (k + 1) → ℕ)
    (hn : Monotone n) (hn0 : n 0 = 0) (x : Fin (k + 1) → S) :
    rates.historyLaw μ {h | (∀ i : Fin (k + 1), 0 < i → (h (n i)).1 = x i) ∧
      ∀ j ≤ n (Fin.last k), (h j).1 ∈ U} =
      ∑' x₀, (if x₀ ∈ U then μ {x₀} else 0) *
        ∏ i : Fin k, ENNReal.ofReal (kernelPow (rates.killedP U)
          (n i.succ - n i.castSucc)
          (Function.update x 0 x₀ i.castSucc) (Function.update x 0 x₀ i.succ)) := by
  let E : S → Set (History S) := fun x₀ ↦
    {h | (∀ i : Fin (k + 1), (h (n i)).1 = Function.update x 0 x₀ i) ∧
      ∀ j ≤ n (Fin.last k), (h j).1 ∈ U}
  have hE (x₀ : S) : MeasurableSet (E x₀) := by
    dsimp only [E]
    simp only [setOf_and, setOf_forall]
    apply MeasurableSet.inter
    · exact MeasurableSet.iInter fun i ↦ measurableSet_eq_fun (by fun_prop) measurable_const
    · exact MeasurableSet.iInter fun j ↦ MeasurableSet.iInter fun _ ↦
        (show Measurable (fun h : History S ↦ (h j).1) by fun_prop)
          ((Set.to_countable U).measurableSet)
  have hdisj : Pairwise (Disjoint on E) := by
    intro v w hvw
    apply Set.disjoint_left.mpr
    rintro h ⟨hv, _⟩ ⟨hw, _⟩
    have h0 := (hv 0).symm.trans (hw 0)
    simp only [Function.update_self] at h0
    exact hvw h0
  have hevent : {h : History S |
        (∀ i : Fin (k + 1), 0 < i → (h (n i)).1 = x i) ∧
          ∀ j ≤ n (Fin.last k), (h j).1 ∈ U} = ⋃ x₀, E x₀ := by
    ext h
    simp only [Set.mem_setOf_eq, Set.mem_iUnion, E]
    constructor
    · rintro ⟨ho, hu⟩
      refine ⟨(h 0).1, ?_, hu⟩
      intro i
      by_cases hi : i = 0
      · subst i
        simp only [hn0, Function.update_self]
      · rw [Function.update_of_ne hi]
        exact ho i (Fin.pos_iff_ne_zero.mpr hi)
    · rintro ⟨x₀, ho, hu⟩
      refine ⟨fun i hi ↦ ?_, hu⟩
      simpa only [Function.update_of_ne (ne_of_gt hi)] using ho i
  rw [hevent, measure_iUnion hdisj hE]
  apply tsum_congr
  intro x₀
  simpa only [E, Function.update_self] using
    rates.historyLaw_killed_fdd_initial μ U k n hn hn0 (Function.update x 0 x₀)

/-- The unrestricted state finite-dimensional law is the specialization to the full space. -/
theorem historyLaw_fdd (rates : BoundedRates S) (μ : Measure S)
    [IsProbabilityMeasure μ] (k : ℕ) (n : Fin (k + 1) → ℕ)
    (hn : Monotone n) (hn0 : n 0 = 0) (x : Fin (k + 1) → S) :
    rates.historyLaw μ {h | ∀ i : Fin (k + 1), 0 < i → (h (n i)).1 = x i} =
      ∑' x₀, μ {x₀} * ∏ i : Fin k, ENNReal.ofReal (kernelPow rates.p
        (n i.succ - n i.castSucc)
        (Function.update x 0 x₀ i.castSucc) (Function.update x 0 x₀ i.succ)) := by
  simpa only [mem_univ, implies_true, forall_const, and_true, ite_true, killedP_univ] using
    rates.historyLaw_killed_fdd μ univ k n hn hn0 x

end BoundedRates

end

end LatticeProb.JumpChain
