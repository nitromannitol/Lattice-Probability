import LatticeProb.Prob.JumpChain.StateFdd
import LatticeProb.Prob.JumpChain.ClockLaw
import LatticeProb.Prob.JumpChain.PoissonFdd
import LatticeProb.Analysis.KernelPowerBridge

/-!
# Finite-dimensional killed position laws

The killed position kernel is the Poisson average of the killed embedded transition
powers. Staying in a set up to a fixed time is exactly a finite embedded-state event.
Disjoint count cylinders and state-clock independence give the killed position law;
resumming over count increments gives a product of killed kernels.
-/

namespace LatticeProb.JumpChain

open MeasureTheory ProbabilityTheory Set Function
open scoped NNReal ENNReal

noncomputable section

attribute [local instance] Classical.propDecidable

namespace BoundedRates

variable {S : Type*}

/-- The Poisson average of the embedded transition powers killed on arrival outside `U`. -/
def killedKernel (rates : BoundedRates S) (U : Set S) (t : ℝ≥0) (x y : S) : ℝ :=
  ∑' m, Real.exp (-(rates.R * t)) * (rates.R * t) ^ m / m.factorial *
    kernelPow (rates.killedP U) m x y

/-- Each summand in the killed position kernel is nonnegative. -/
theorem killedKernel_term_nonneg (rates : BoundedRates S) (U : Set S)
    (t : ℝ≥0) (x y : S) (m : ℕ) :
    0 ≤ Real.exp (-(rates.R * t)) * (rates.R * t) ^ m / m.factorial *
      kernelPow (rates.killedP U) m x y := by
  have hR := rates.R_pos
  exact mul_nonneg (by positivity) (kernelPow_nonneg (rates.killedP_nonneg U) m x y)

/-- The series defining each killed position mass converges. -/
theorem killedKernel_summable (rates : BoundedRates S) (U : Set S)
    (t : ℝ≥0) (x y : S) :
    Summable (fun m ↦ Real.exp (-(rates.R * t)) * (rates.R * t) ^ m /
      m.factorial * kernelPow (rates.killedP U) m x y) := by
  have hR := rates.R_pos
  have hs := (hasSum_one_poissonMeasure
    (⟨rates.R * t, mul_nonneg rates.R_pos.le t.coe_nonneg⟩ : ℝ≥0)).summable
  apply hs.of_nonneg_of_le (rates.killedKernel_term_nonneg U t x y)
  intro m
  exact mul_le_of_le_one_right (by positivity)
    ((rates.kernelPow_killedP_le U m x y).trans
      (kernel_entry_le_one (kernelPow_nonneg rates.p_nonneg m)
        (kernelPow_hasSum rates.p_nonneg rates.hasSum_p m) x y))

/-- Every killed position mass is nonnegative. -/
theorem killedKernel_nonneg (rates : BoundedRates S) (U : Set S)
    (t : ℝ≥0) (x y : S) : 0 ≤ rates.killedKernel U t x y :=
  tsum_nonneg (rates.killedKernel_term_nonneg U t x y)

/-- At time zero the killed kernel is the identity matrix, even outside the killing set. -/
@[simp] theorem killedKernel_zero (rates : BoundedRates S) (U : Set S) (x y : S) :
    rates.killedKernel U 0 x y = if x = y then 1 else 0 := by
  classical
  unfold killedKernel
  rw [tsum_eq_single 0]
  · simp only [NNReal.coe_zero, mul_zero, neg_zero, Real.exp_zero, pow_zero,
      mul_one, Nat.factorial_zero, Nat.cast_one, div_one, one_mul, kernelPow]
  · intro m hm
    simp only [NNReal.coe_zero, mul_zero, zero_pow hm, mul_zero, zero_div, zero_mul]

variable [MeasurableSpace S] [Countable S] [MeasurableSingletonClass S]

/-- Killing on the full space recovers the transition kernel singleton mass. -/
@[simp] theorem killedKernel_univ (rates : BoundedRates S) (t : ℝ≥0) (x y : S) :
    rates.killedKernel univ t x y = (rates.transitionKernel t x).real {y} := by
  rw [rates.transitionKernel_real_singleton_eq_kernelPow]
  simp only [killedKernel, killedP_univ]

/-- Killing can only decrease a transition singleton mass. -/
theorem killedKernel_le_transitionKernel (rates : BoundedRates S) (U : Set S)
    (t : ℝ≥0) (x y : S) :
    rates.killedKernel U t x y ≤ (rates.transitionKernel t x).real {y} := by
  have hR := rates.R_pos
  rw [← rates.killedKernel_univ]
  apply (rates.killedKernel_summable U t x y).tsum_le_tsum
    _ (rates.killedKernel_summable univ t x y)
  intro m
  simp only [killedP_univ]
  exact mul_le_mul_of_nonneg_left (rates.kernelPow_killedP_le U m x y) (by positivity)

end BoundedRates

namespace RegularHistory

variable {S : Type*}

/-- Staying in `U` up to time `t` means every embedded state through its count lies in `U`. -/
theorem position_mem_iff (h : RegularHistory S) (U : Set S) (t : ℝ≥0) :
    (∀ s ≤ t, h.position s ∈ U) ↔ ∀ j ≤ h.ringCount t, (h.val j).1 ∈ U := by
  constructor
  · intro hp j hj
    let s : ℝ≥0 := ⟨jumpTime h.val j, h.jumpTime_nonneg j⟩
    have hst : s ≤ t := (h.strictMono_jumpTime.monotone hj).trans
      (h.jumpTime_ringCount_le t)
    have heq := h.position_eq_of_interval s j le_rfl
      (h.strictMono_jumpTime (Nat.lt_succ_self j))
    rw [← heq]
    exact hp s hst
  · intro hp s hs
    exact hp (h.ringCount s) (h.ringCount_le hs)

end RegularHistory

namespace BoundedRates

variable {S : Type*} [MeasurableSpace S] [Countable S] [MeasurableSingletonClass S]

/-- A killed state observation event and fixed clock windows factor by independence. -/
theorem historyLaw_killed_fdd_clock_windows (rates : BoundedRates S) (μ : Measure S)
    [IsProbabilityMeasure μ] (U : Set S) (k : ℕ) (t : Fin (k + 1) → ℝ)
    (ht : Monotone t) (ht0 : t 0 = 0) (n : Fin (k + 1) → ℕ)
    (hn : Monotone n) (hn0 : n 0 = 0) (x : Fin (k + 1) → S) :
    rates.historyLaw μ {h |
      ((∀ i : Fin (k + 1), 0 < i → (h (n i)).1 = x i) ∧
        ∀ j ≤ n (Fin.last k), (h j).1 ∈ U) ∧
      ∀ i : Fin k, jumpTime h (n i.succ) ≤ t i.succ ∧
        t i.succ < jumpTime h (n i.succ + 1)} =
      (∑' x₀, (if x₀ ∈ U then μ {x₀} else 0) *
        ∏ i : Fin k, ENNReal.ofReal (kernelPow (rates.killedP U)
          (n i.succ - n i.castSucc)
          (Function.update x 0 x₀ i.castSucc) (Function.update x 0 x₀ i.succ))) *
      ∏ i : Fin k, ENNReal.ofReal
        (Real.exp (-(rates.R * (t i.succ - t i.castSucc))) *
          (rates.R * (t i.succ - t i.castSucc)) ^ (n i.succ - n i.castSucc) /
            (n i.succ - n i.castSucc).factorial) := by
  classical
  let A : Set (ℕ → S) := {y |
    (∀ i : Fin (k + 1), 0 < i → y (n i) = x i) ∧
      ∀ j ≤ n (Fin.last k), y j ∈ U}
  let B : Set (ℕ → ℝ) := {e | ∀ i : Fin k, ring (n i.succ) (t i.succ) e}
  have hA : MeasurableSet A := by
    dsimp only [A]
    simp only [setOf_and, setOf_forall]
    refine MeasurableSet.inter ?_ ?_
    · exact MeasurableSet.iInter fun i ↦ MeasurableSet.iInter fun _ ↦
        measurableSet_eq_fun (measurable_pi_apply _) measurable_const
    · exact MeasurableSet.iInter fun j ↦ MeasurableSet.iInter fun _ ↦
        (measurable_pi_apply j) (Set.to_countable U).measurableSet
  have hB : MeasurableSet B := by
    simpa only [B, setOf_forall] using
      MeasurableSet.iInter (fun i : Fin k ↦ measurableSet_ring (n i.succ) (t i.succ))
  have h := (rates.indepFun_states_clocks μ).measure_inter_preimage_eq_mul A B hA hB
  change rates.historyLaw μ {h |
      ((∀ i : Fin (k + 1), 0 < i → (h (n i)).1 = x i) ∧
        ∀ j ≤ n (Fin.last k), (h j).1 ∈ U) ∧
      ∀ i : Fin k, jumpTime h (n i.succ) ≤ t i.succ ∧
        t i.succ < jumpTime h (n i.succ + 1)} = _ at h
  change _ = rates.historyLaw μ {h |
    (∀ i : Fin (k + 1), 0 < i → (h (n i)).1 = x i) ∧
      ∀ j ≤ n (Fin.last k), (h j).1 ∈ U} *
    rates.historyLaw μ {h | ∀ i : Fin k, jumpTime h (n i.succ) ≤ t i.succ ∧
      t i.succ < jumpTime h (n i.succ + 1)} at h
  rw [rates.historyLaw_killed_fdd μ U k n hn hn0 x,
    rates.historyLaw_jumpTime_fdd μ k t ht ht0 n hn hn0] at h
  exact h

/-- The killed position event on one fixed count cylinder factors into state and clock laws. -/
theorem regularLaw_killed_position_count_fdd (rates : BoundedRates S) (μ : Measure S)
    [IsProbabilityMeasure μ] (U : Set S) (k : ℕ) (t : Fin (k + 1) → ℝ≥0)
    (ht : Monotone t) (ht0 : t 0 = 0) (n : Fin (k + 1) → ℕ)
    (hn : Monotone n) (hn0 : n 0 = 0) (x : Fin (k + 1) → S) :
    rates.regularLaw μ {h |
      ((∀ i : Fin (k + 1), 0 < i → h.position (t i) = x i) ∧
        ∀ s ≤ t (Fin.last k), h.position s ∈ U) ∧
      ∀ i : Fin k, h.ringCount (t i.succ) = n i.succ} =
      (∑' x₀, (if x₀ ∈ U then μ {x₀} else 0) *
        ∏ i : Fin k, ENNReal.ofReal (kernelPow (rates.killedP U)
          (n i.succ - n i.castSucc)
          (Function.update x 0 x₀ i.castSucc) (Function.update x 0 x₀ i.succ))) *
      ∏ i : Fin k, ENNReal.ofReal
        (Real.exp (-(rates.R * ((t i.succ : ℝ) - t i.castSucc))) *
          (rates.R * ((t i.succ : ℝ) - t i.castSucc)) ^
            (n i.succ - n i.castSucc) / (n i.succ - n i.castSucc).factorial) := by
  let E : Set (History S) := {h |
    ((∀ i : Fin (k + 1), 0 < i → (h (n i)).1 = x i) ∧
      ∀ j ≤ n (Fin.last k), (h j).1 ∈ U) ∧
    ∀ i : Fin k, jumpTime h (n i.succ) ≤ t i.succ ∧
      (t i.succ : ℝ) < jumpTime h (n i.succ + 1)}
  have hE : MeasurableSet E := by
    dsimp only [E]
    simp only [setOf_and, setOf_forall]
    refine (MeasurableSet.inter ?_ ?_).inter ?_
    · exact MeasurableSet.iInter fun i ↦ MeasurableSet.iInter fun _ ↦
        measurableSet_eq_fun (by fun_prop) measurable_const
    · exact MeasurableSet.iInter fun j ↦ MeasurableSet.iInter fun _ ↦
        (show Measurable (fun h : History S ↦ (h j).1) by fun_prop)
          (Set.to_countable U).measurableSet
    · exact MeasurableSet.iInter fun i ↦
        (measurableSet_le (measurable_jumpTime _) measurable_const).inter
          (measurableSet_lt measurable_const (measurable_jumpTime _))
  have hevent : {h : RegularHistory S |
      ((∀ i : Fin (k + 1), 0 < i → h.position (t i) = x i) ∧
        ∀ s ≤ t (Fin.last k), h.position s ∈ U) ∧
      ∀ i : Fin k, h.ringCount (t i.succ) = n i.succ} = Subtype.val ⁻¹' E := by
    ext h
    have hcount : (∀ i : Fin k, h.ringCount (t i.succ) = n i.succ) ↔
        ∀ i : Fin k, jumpTime h.val (n i.succ) ≤ t i.succ ∧
          (t i.succ : ℝ) < jumpTime h.val (n i.succ + 1) :=
      forall_congr' fun i ↦ h.ringCount_eq_iff (t i.succ) (n i.succ)
    have hall (hc : ∀ i : Fin k, h.ringCount (t i.succ) = n i.succ)
        (i : Fin (k + 1)) : h.ringCount (t i) = n i := by
      refine Fin.cases ?_ (fun j ↦ hc j) i
      rw [ht0, h.ringCount_zero, hn0]
    simp only [mem_setOf_eq, mem_preimage, E]
    constructor
    · rintro ⟨⟨hx, hu⟩, hc⟩
      refine ⟨⟨?_, ?_⟩, hcount.mp hc⟩
      · intro i hi
        simpa only [RegularHistory.position, hall hc i] using hx i hi
      · simpa only [hall hc (Fin.last k)] using (h.position_mem_iff U _).mp hu
    · rintro ⟨⟨hx, hu⟩, hw⟩
      have hc := hcount.mpr hw
      refine ⟨⟨?_, ?_⟩, hc⟩
      · intro i hi
        simpa only [RegularHistory.position, hall hc i] using hx i hi
      · apply (h.position_mem_iff U _).mpr
        simpa only [hall hc (Fin.last k)] using hu
  rw [hevent, ← Measure.map_apply measurable_subtype_coe hE, rates.regularLaw_map_val]
  exact rates.historyLaw_killed_fdd_clock_windows μ U k (fun i ↦ (t i : ℝ))
    (fun i j hij ↦ ht hij) (by simp only [ht0, NNReal.coe_zero]) n hn hn0 x

/-- Nonnegative finite partial sums increase with the observation index. -/
private theorem monotone_partialSum (k : ℕ) (m : Fin k → ℕ) :
    Monotone (Fin.partialSum m) := by
  apply Fin.monotone_iff_le_succ.mpr
  intro i
  rw [Fin.partialSum_succ]
  exact Nat.le_add_right _ _

/-- Successive differences recover the increments of natural-number partial sums. -/
private theorem partialSum_sub (k : ℕ) (m : Fin k → ℕ) (i : Fin k) :
    Fin.partialSum m i.succ - Fin.partialSum m i.castSucc = m i := by
  rw [Fin.partialSum_succ, Nat.add_sub_cancel_left]

/-- A monotone natural-number tuple starting at zero is the partial sum of its increments. -/
private theorem partialSum_differences (k : ℕ) (n : Fin (k + 1) → ℕ)
    (hn : Monotone n) (hn0 : n 0 = 0) :
    Fin.partialSum (fun i : Fin k ↦ n i.succ - n i.castSucc) = n := by
  funext i
  refine Fin.induction ?_ ?_ i
  · rw [Fin.partialSum_zero, hn0]
  · intro j hj
    rw [Fin.partialSum_succ, hj, Nat.add_sub_of_le (hn (Fin.castSucc_le_succ j))]

/-- A finite product of nonnegative series is the series over all tuples of indices. -/
private theorem tsum_fin_prod (k : ℕ) (f : Fin k → ℕ → ℝ≥0∞) :
    (∑' m : Fin k → ℕ, ∏ i : Fin k, f i (m i)) = ∏ i : Fin k, ∑' j, f i j := by
  induction k with
  | zero => simp [tsum_fintype]
  | succ k ih =>
    rw [← (Fin.consEquiv (fun _ : Fin (k + 1) ↦ ℕ)).tsum_eq,
      ENNReal.tsum_prod']
    simp only [Fin.consEquiv_apply, Fin.prod_univ_succ, Fin.cons_zero, Fin.cons_succ]
    simp_rw [ENNReal.tsum_mul_left, ih]
    rw [ENNReal.tsum_mul_right]

/-- The count cylinders indexed by successive increments exhaust a killed position event. -/
theorem regularLaw_killed_position_sum_counts (rates : BoundedRates S) (μ : Measure S)
    [IsProbabilityMeasure μ] (U : Set S) (k : ℕ) (t : Fin (k + 1) → ℝ≥0)
    (ht : Monotone t) (ht0 : t 0 = 0) (x : Fin (k + 1) → S) :
    rates.regularLaw μ {h |
      (∀ i : Fin (k + 1), 0 < i → h.position (t i) = x i) ∧
        ∀ s ≤ t (Fin.last k), h.position s ∈ U} =
      ∑' m : Fin k → ℕ, rates.regularLaw μ {h |
        ((∀ i : Fin (k + 1), 0 < i → h.position (t i) = x i) ∧
          ∀ s ≤ t (Fin.last k), h.position s ∈ U) ∧
        ∀ i : Fin k, h.ringCount (t i.succ) = Fin.partialSum m i.succ} := by
  classical
  let E : (Fin k → ℕ) → Set (RegularHistory S) := fun m ↦ {h |
    ((∀ i : Fin (k + 1), 0 < i → h.position (t i) = x i) ∧
      ∀ s ≤ t (Fin.last k), h.position s ∈ U) ∧
    ∀ i : Fin k, h.ringCount (t i.succ) = Fin.partialSum m i.succ}
  have hcounts (h : RegularHistory S) (m : Fin k → ℕ)
      (hc : ∀ i : Fin k, h.ringCount (t i.succ) = Fin.partialSum m i.succ)
      (i : Fin (k + 1)) : h.ringCount (t i) = Fin.partialSum m i := by
    refine Fin.cases ?_ (fun j ↦ hc j) i
    rw [ht0, h.ringCount_zero, Fin.partialSum_zero]
  have hdisj : Pairwise (Disjoint on E) := by
    intro m v hmv
    apply Set.disjoint_left.mpr
    rintro h ⟨_, hm⟩ ⟨_, hv⟩
    apply hmv
    funext i
    have hs := (hcounts h m hm i.succ).symm.trans (hcounts h v hv i.succ)
    have hp := (hcounts h m hm i.castSucc).symm.trans (hcounts h v hv i.castSucc)
    have hd := congrArg₂ (fun a b : ℕ ↦ a - b) hs hp
    simpa only [partialSum_sub] using hd
  have hE (m : Fin k → ℕ) : MeasurableSet (E m) := by
    have heq : E m = {h |
        ((∀ i : Fin (k + 1), 0 < i → h.position (t i) = x i) ∧
          ∀ j ≤ Fin.partialSum m (Fin.last k), (h.val j).1 ∈ U) ∧
        ∀ i : Fin k, h.ringCount (t i.succ) = Fin.partialSum m i.succ} := by
      ext h
      simp only [E, mem_setOf_eq]
      constructor
      · rintro ⟨⟨hx, hu⟩, hc⟩
        refine ⟨⟨hx, ?_⟩, hc⟩
        simpa only [hcounts h m hc (Fin.last k)] using (h.position_mem_iff U _).mp hu
      · rintro ⟨⟨hx, hu⟩, hc⟩
        refine ⟨⟨hx, (h.position_mem_iff U _).mpr ?_⟩, hc⟩
        simpa only [hcounts h m hc (Fin.last k)] using hu
    rw [heq]
    simp only [setOf_and, setOf_forall]
    refine (MeasurableSet.inter ?_ ?_).inter ?_
    · exact MeasurableSet.iInter fun i ↦ MeasurableSet.iInter fun _ ↦
        measurableSet_eq_fun (by fun_prop) measurable_const
    · exact MeasurableSet.iInter fun j ↦ MeasurableSet.iInter fun _ ↦
        (((measurable_pi_apply (X := fun _ : ℕ ↦ S × ℝ) j).comp
          measurable_subtype_coe).fst)
          (Set.to_countable U).measurableSet
    · exact MeasurableSet.iInter fun i ↦
        measurableSet_eq_fun (by fun_prop) measurable_const
  have hevent : {h : RegularHistory S |
      (∀ i : Fin (k + 1), 0 < i → h.position (t i) = x i) ∧
        ∀ s ≤ t (Fin.last k), h.position s ∈ U} = ⋃ m, E m := by
    ext h
    simp only [mem_setOf_eq, mem_iUnion, E]
    constructor
    · intro hh
      let n : Fin (k + 1) → ℕ := fun i ↦ h.ringCount (t i)
      have hn : Monotone n := fun i j hij ↦ h.ringCount_le (ht hij)
      have hn0 : n 0 = 0 := by simp only [n, ht0, h.ringCount_zero]
      refine ⟨(fun i : Fin k ↦ n i.succ - n i.castSucc), hh, ?_⟩
      intro i
      rw [partialSum_differences k n hn hn0]
    · rintro ⟨m, hh, _⟩
      exact hh
  rw [hevent]
  exact measure_iUnion hdisj hE

/-- Killed position observations have the product law of the Poisson-averaged killed kernels. -/
theorem regularLaw_killed_position_fdd (rates : BoundedRates S) (μ : Measure S)
    [IsProbabilityMeasure μ] (U : Set S) (k : ℕ) (t : Fin (k + 1) → ℝ≥0)
    (ht : Monotone t) (ht0 : t 0 = 0) (x : Fin (k + 1) → S) :
    rates.regularLaw μ {h |
      (∀ i : Fin (k + 1), 0 < i → h.position (t i) = x i) ∧
        ∀ s ≤ t (Fin.last k), h.position s ∈ U} =
      ∑' x₀, (if x₀ ∈ U then μ {x₀} else 0) *
        ∏ i : Fin k, ENNReal.ofReal (rates.killedKernel U (t i.succ - t i.castSucc)
          (Function.update x 0 x₀ i.castSucc) (Function.update x 0 x₀ i.succ)) := by
  classical
  have hR := rates.R_pos
  rw [rates.regularLaw_killed_position_sum_counts μ U k t ht ht0 x]
  simp_rw [rates.regularLaw_killed_position_count_fdd μ U k t ht ht0
    _ (monotone_partialSum k _) (Fin.partialSum_zero _) x, partialSum_sub,
    ← ENNReal.tsum_mul_right]
  rw [ENNReal.tsum_comm]
  apply tsum_congr
  intro x₀
  simp_rw [mul_assoc]
  rw [ENNReal.tsum_mul_left]
  congr 1
  let a : Fin k → ℕ → ℝ := fun i m ↦
    Real.exp (-(rates.R * ((t i.succ : ℝ) - t i.castSucc))) *
      (rates.R * ((t i.succ : ℝ) - t i.castSucc)) ^ m / m.factorial
  let b : Fin k → ℕ → ℝ := fun i m ↦ kernelPow (rates.killedP U) m
    (Function.update x 0 x₀ i.castSucc) (Function.update x 0 x₀ i.succ)
  have hterm (m : Fin k → ℕ) :
      (∏ i : Fin k, ENNReal.ofReal (b i (m i))) *
        (∏ i : Fin k, ENNReal.ofReal (a i (m i))) =
      ∏ i : Fin k, ENNReal.ofReal (a i (m i) * b i (m i)) := by
    rw [← Finset.prod_mul_distrib]
    apply Finset.prod_congr rfl
    intro i _
    rw [mul_comm, ENNReal.ofReal_mul]
    dsimp only [a]
    have htime : 0 ≤ (t i.succ : ℝ) - t i.castSucc := sub_nonneg.mpr
      (ht (Fin.castSucc_le_succ i))
    positivity
  change (∑' m : Fin k → ℕ,
    (∏ i : Fin k, ENNReal.ofReal (b i (m i))) *
      ∏ i : Fin k, ENNReal.ofReal (a i (m i))) = _
  simp_rw [hterm]
  rw [tsum_fin_prod k (fun i m ↦ ENNReal.ofReal (a i m * b i m))]
  apply Finset.prod_congr rfl
  intro i _
  have hle : t i.castSucc ≤ t i.succ := ht (Fin.castSucc_le_succ i)
  have hcoe : ((t i.succ - t i.castSucc : ℝ≥0) : ℝ) =
      (t i.succ : ℝ) - t i.castSucc := NNReal.coe_sub hle
  rw [killedKernel, ENNReal.ofReal_tsum_of_nonneg
    (rates.killedKernel_term_nonneg U _ _ _) (rates.killedKernel_summable U _ _ _)]
  apply tsum_congr
  intro m
  simp only [a, b, hcoe]

/-- Unrestricted position observations have the product law of transition singleton masses. -/
theorem regularLaw_position_fdd (rates : BoundedRates S) (μ : Measure S)
    [IsProbabilityMeasure μ] (k : ℕ) (t : Fin (k + 1) → ℝ≥0)
    (ht : Monotone t) (ht0 : t 0 = 0) (x : Fin (k + 1) → S) :
    rates.regularLaw μ {h | ∀ i : Fin (k + 1), 0 < i → h.position (t i) = x i} =
      ∑' x₀, μ {x₀} * ∏ i : Fin k,
        rates.transitionKernel (t i.succ - t i.castSucc)
          (Function.update x 0 x₀ i.castSucc) {Function.update x 0 x₀ i.succ} := by
  have hmass (s : ℝ≥0) (a b : S) :
      ENNReal.ofReal ((rates.transitionKernel s a).real {b}) =
        rates.transitionKernel s a {b} := ofReal_measureReal (measure_ne_top _ _)
  simpa only [mem_univ, implies_true, forall_const, and_true, ite_true,
    killedKernel_univ, hmass]
    using rates.regularLaw_killed_position_fdd μ univ k t ht ht0 x

end BoundedRates

end

end LatticeProb.JumpChain
