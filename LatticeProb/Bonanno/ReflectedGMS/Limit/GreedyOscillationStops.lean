/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module ReflectedGMS.Limit.GreedyOscillationStops at commit fdb5cad; only the module paths of local imports are changed. -/
import Mathlib.Probability.Process.HittingTime

/-!
# Greedy oscillation stopping times on a finite grid

This file constructs the successive first times at which a real-valued discrete
process has moved by at least a prescribed amount from its value at the
previous stopping time.  The finite horizon is retained as the value in the
no-hit case.
-/

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Set

namespace ReflectedGMS.MartingaleLimit

variable {Ω : Type*} {m : MeasurableSpace Ω}

/-- Successive greedy oscillation times, capped at the deterministic horizon
`N`.  The search starts at zero; stopping the reference process at the previous
time makes the searched increment zero before that time. -/
noncomputable def greedyOscillationStop
    (X : ℕ → Ω → ℝ) (ε : ℝ) (N : ℕ) : ℕ → Ω → ℕ
  | 0 => fun _ => 0
  | k + 1 =>
      hittingBtwn
        (X - stoppedProcess X
          (fun ω => (greedyOscillationStop X ε N k ω : WithTop ℕ)))
        {x | ε ≤ |x|} 0 N

@[simp]
theorem greedyOscillationStop_zero
    (X : ℕ → Ω → ℝ) (ε : ℝ) (N : ℕ) (ω : Ω) :
    greedyOscillationStop X ε N 0 ω = 0 := rfl

@[simp]
theorem greedyOscillationStop_succ
    (X : ℕ → Ω → ℝ) (ε : ℝ) (N k : ℕ) (ω : Ω) :
    greedyOscillationStop X ε N (k + 1) ω =
      hittingBtwn
        (X - stoppedProcess X
          (fun ω => (greedyOscillationStop X ε N k ω : WithTop ℕ)))
        {x | ε ≤ |x|} 0 N ω := rfl

/-- Every greedy oscillation time, coerced to `WithTop ℕ`, is a stopping time. -/
theorem greedyOscillationStop_isStoppingTime
    {F : Filtration ℕ m} {X : ℕ → Ω → ℝ}
    (hX : StronglyAdapted F X) {ε : ℝ} (N k : ℕ) :
    IsStoppingTime F
      (fun ω => (greedyOscillationStop X ε N k ω : WithTop ℕ)) := by
  induction k with
  | zero => simpa using isStoppingTime_const F (0 : ℕ)
  | succ k ih =>
      rw [show (fun ω => (greedyOscillationStop X ε N (k + 1) ω : WithTop ℕ)) =
          fun ω =>
            ((hittingBtwn
              (X - stoppedProcess X
                (fun ω => (greedyOscillationStop X ε N k ω : WithTop ℕ)))
              {x | ε ≤ |x|} 0 N ω : ℕ) : WithTop ℕ) by
        funext ω
        simp]
      apply Adapted.isStoppingTime_hittingBtwn
      · exact (hX.sub (hX.stoppedProcess_of_discrete ih)).adapted
      · exact measurableSet_Ici.preimage continuous_abs.measurable

/-- Greedy oscillation times never exceed their deterministic horizon. -/
theorem greedyOscillationStop_le
    (X : ℕ → Ω → ℝ) (ε : ℝ) (N k : ℕ) (ω : Ω) :
    greedyOscillationStop X ε N k ω ≤ N := by
  cases k with
  | zero => simp
  | succ k => exact hittingBtwn_le ω

/-- Successive greedy oscillation times are increasing when `ε > 0`. -/
theorem greedyOscillationStop_mono_step
    (X : ℕ → Ω → ℝ) {ε : ℝ} (hε : 0 < ε) (N k : ℕ) (ω : Ω) :
    greedyOscillationStop X ε N k ω ≤
      greedyOscillationStop X ε N (k + 1) ω := by
  let τ := greedyOscillationStop X ε N k ω
  let σ := greedyOscillationStop X ε N (k + 1) ω
  have hτN : τ ≤ N := greedyOscillationStop_le X ε N k ω
  by_contra hnot
  have hστ : σ < τ := Nat.lt_of_not_ge hnot
  have hσN : σ < N := hστ.trans_le hτN
  have hmem :
      (X - stoppedProcess X
        (fun ω => (greedyOscillationStop X ε N k ω : WithTop ℕ))) σ ω ∈
        {x | ε ≤ |x|} := by
    exact hittingBtwn_mem_set_of_hittingBtwn_lt hσN
  have hzero :
      (X - stoppedProcess X
        (fun ω => (greedyOscillationStop X ε N k ω : WithTop ℕ))) σ ω = 0 := by
    have hstop : stoppedProcess X
        (fun ω => (greedyOscillationStop X ε N k ω : WithTop ℕ)) σ ω = X σ ω :=
      stoppedProcess_eq_of_le (u := X)
        (τ := fun ω => (greedyOscillationStop X ε N k ω : WithTop ℕ))
        (i := σ) (ω := ω) (WithTop.coe_le_coe.mpr hστ.le)
    rw [Pi.sub_apply, Pi.sub_apply, hstop]
    exact sub_self _
  rw [hzero] at hmem
  exact (not_le_of_gt hε) (by simpa using hmem)

/-- Before the horizon, the greedy construction advances strictly. -/
theorem greedyOscillationStop_strict_step
    (X : ℕ → Ω → ℝ) {ε : ℝ} (hε : 0 < ε) (N k : ℕ) (ω : Ω)
    (hk : greedyOscillationStop X ε N k ω < N) :
    greedyOscillationStop X ε N k ω <
      greedyOscillationStop X ε N (k + 1) ω := by
  refine lt_of_le_of_ne (greedyOscillationStop_mono_step X hε N k ω) ?_
  intro heq
  have hnextN : greedyOscillationStop X ε N (k + 1) ω < N := heq ▸ hk
  have hmem :
      (X - stoppedProcess X
        (fun ω => (greedyOscillationStop X ε N k ω : WithTop ℕ)))
          (greedyOscillationStop X ε N (k + 1) ω) ω ∈
        {x | ε ≤ |x|} := by
    exact hittingBtwn_mem_set_of_hittingBtwn_lt hnextN
  have hzero :
      (X - stoppedProcess X
        (fun ω => (greedyOscillationStop X ε N k ω : WithTop ℕ)))
          (greedyOscillationStop X ε N (k + 1) ω) ω = 0 := by
    have hstop : stoppedProcess X
        (fun ω => (greedyOscillationStop X ε N k ω : WithTop ℕ))
          (greedyOscillationStop X ε N (k + 1) ω) ω =
        X (greedyOscillationStop X ε N (k + 1) ω) ω :=
      stoppedProcess_eq_of_le (u := X)
        (τ := fun ω => (greedyOscillationStop X ε N k ω : WithTop ℕ))
        (i := greedyOscillationStop X ε N (k + 1) ω) (ω := ω)
        (WithTop.coe_le_coe.mpr heq.symm.le)
    rw [Pi.sub_apply, Pi.sub_apply, hstop]
    exact sub_self _
  rw [hzero] at hmem
  exact (not_le_of_gt hε) (by simpa using hmem)

/-- Between two successive greedy times the displacement from the earlier
stopped value is strictly below `ε`. -/
theorem abs_sub_lt_of_between_greedyOscillationStops
    (X : ℕ → Ω → ℝ) {ε : ℝ} (hε : 0 < ε) (N k j : ℕ) (ω : Ω)
    (hleft : greedyOscillationStop X ε N k ω ≤ j)
    (hright : j < greedyOscillationStop X ε N (k + 1) ω) :
    |X j ω - X (greedyOscillationStop X ε N k ω) ω| < ε := by
  have hnotmem :
      (X - stoppedProcess X
        (fun ω => (greedyOscillationStop X ε N k ω : WithTop ℕ))) j ω ∉
        {x | ε ≤ |x|} :=
    notMem_of_lt_hittingBtwn hright (Nat.zero_le j)
  have heval :
      (X - stoppedProcess X
        (fun ω => (greedyOscillationStop X ε N k ω : WithTop ℕ))) j ω =
        X j ω - X (greedyOscillationStop X ε N k ω) ω := by
    have hstop : stoppedProcess X
        (fun ω => (greedyOscillationStop X ε N k ω : WithTop ℕ)) j ω =
        X (greedyOscillationStop X ε N k ω) ω := by
      rw [stoppedProcess_eq_of_ge (u := X)
        (τ := fun ω => (greedyOscillationStop X ε N k ω : WithTop ℕ))
        (i := j) (ω := ω) (WithTop.coe_le_coe.mpr hleft),
        show (greedyOscillationStop X ε N k ω : WithTop ℕ).untopA =
          greedyOscillationStop X ε N k ω by rfl]
    rw [Pi.sub_apply, Pi.sub_apply, hstop]
  rw [heval] at hnotmem
  exact lt_of_not_ge hnotmem

/-- If a successor greedy time lies strictly before the horizon, its endpoint
increment has reached the threshold. -/
theorem le_abs_sub_at_greedyOscillationStop_succ
    (X : ℕ → Ω → ℝ) {ε : ℝ} (hε : 0 < ε) (N k : ℕ) (ω : Ω)
    (hk : greedyOscillationStop X ε N (k + 1) ω < N) :
    ε ≤ |X (greedyOscillationStop X ε N (k + 1) ω) ω -
      X (greedyOscillationStop X ε N k ω) ω| := by
  have hmono := greedyOscillationStop_mono_step X hε N k ω
  have hmem :
      (X - stoppedProcess X
        (fun ω => (greedyOscillationStop X ε N k ω : WithTop ℕ)))
          (greedyOscillationStop X ε N (k + 1) ω) ω ∈
        {x | ε ≤ |x|} :=
    hittingBtwn_mem_set_of_hittingBtwn_lt hk
  have hstop : stoppedProcess X
      (fun ω => (greedyOscillationStop X ε N k ω : WithTop ℕ))
        (greedyOscillationStop X ε N (k + 1) ω) ω =
      X (greedyOscillationStop X ε N k ω) ω := by
    rw [stoppedProcess_eq_of_ge (u := X)
      (τ := fun ω => (greedyOscillationStop X ε N k ω : WithTop ℕ))
      (i := greedyOscillationStop X ε N (k + 1) ω) (ω := ω)
      (WithTop.coe_le_coe.mpr hmono),
      show (greedyOscillationStop X ε N k ω : WithTop ℕ).untopA =
        greedyOscillationStop X ε N k ω by rfl]
  simpa only [Pi.sub_apply, hstop, Set.mem_ofPred_eq] using hmem

/-- With grid jumps bounded by `b`, a greedy endpoint can overshoot its
threshold by at most one grid jump. -/
theorem abs_sub_at_greedyOscillationStop_succ_le
    (X : ℕ → Ω → ℝ) {ε b : ℝ} (hε : 0 < ε) (_hb : 0 ≤ b)
    (N k : ℕ) (ω : Ω)
    (hjump : ∀ i < N, |X (i + 1) ω - X i ω| ≤ b)
    (hk : greedyOscillationStop X ε N (k + 1) ω < N) :
    |X (greedyOscillationStop X ε N (k + 1) ω) ω -
      X (greedyOscillationStop X ε N k ω) ω| ≤ ε + b := by
  let τ := greedyOscillationStop X ε N k ω
  let σ := greedyOscillationStop X ε N (k + 1) ω
  have hτN : τ < N := (greedyOscillationStop_mono_step X hε N k ω).trans_lt hk
  have hτσ : τ < σ := greedyOscillationStop_strict_step X hε N k ω hτN
  have hσpos : 0 < σ := (Nat.zero_le τ).trans_lt hτσ
  have hpred : τ ≤ σ - 1 := Nat.le_sub_one_of_lt hτσ
  have hpredσ : σ - 1 < σ := Nat.sub_one_lt hσpos.ne'
  have hbelow : |X (σ - 1) ω - X τ ω| < ε :=
    abs_sub_lt_of_between_greedyOscillationStops X hε N k (σ - 1) ω hpred hpredσ
  have hj : |X σ ω - X (σ - 1) ω| ≤ b := by
    have hj' := hjump (σ - 1) (hpredσ.trans hk)
    rw [Nat.sub_add_cancel hσpos] at hj'
    exact hj'
  calc
    |X σ ω - X τ ω| =
        |(X σ ω - X (σ - 1) ω) + (X (σ - 1) ω - X τ ω)| := by ring_nf
    _ ≤ |X σ ω - X (σ - 1) ω| + |X (σ - 1) ω - X τ ω| := abs_add_le _ _
    _ ≤ b + ε := add_le_add hj hbelow.le
    _ = ε + b := add_comm _ _

end ReflectedGMS.MartingaleLimit
