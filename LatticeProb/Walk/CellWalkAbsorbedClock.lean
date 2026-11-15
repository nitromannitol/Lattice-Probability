import LatticeProb.Walk.WalkSelectedClockStrict
import LatticeProb.Walk.CellConfigKnotComparison
import LatticeProb.Walk.CellConfigFiniteExit

/-! # Physical clocks of finite selected walk skeletons -/

set_option autoImplicit false

noncomputable section

open ReflectedGMS ReflectedGMS.GMS
open scoped NNReal
open LatticeProb.CellConfigInterpolation

namespace BouRabeeGwynne.FiniteConductanceNetwork

/-- A finite selected walk skeleton has a monotone physical clock, strict
before its terminal value, whose knots are the interpolated walk vertices. -/
theorem actualWalkStage_physical_absorbed_clock
    {V J : Type*} [Fintype V] [MeasurableSpace V] [MeasurableSingletonClass V]
    [Countable J] [MeasurableSpace (Option J)] [MeasurableSingletonClass (Option J)]
    (H : CellConfig) (p : H.cells → Plane) (cell : V → H.cells)
    (pos : V → Euc 2) (B : J → Set V) (initial : J)
    (select : ℕ → V → Option J) (ω : ℕ → V) (K : ℕ) (k : ℕ → ℕ)
    (hpos : ∀ C, 0 < H.holding C) (hunb : H.JumpTimesUnbounded (cell ∘ ω))
    {ε : ℝ≥0} (hε : 0 < ε)
    (hclock : ∀ i ≤ K, (actualWalkStage pos B initial select i ω).1 = k i)
    (hinit : ω 0 ∈ B initial)
    (hselect : ∀ n v j, select n v = some j → v ∈ B j) :
    let T : ℕ → ℝ≥0 := fun n => Nat.casesOn n 0
      (fun i => scaledJumpTime H (cell ∘ ω) hpos ε (k (min i K)))
    T 0 = 0 ∧ Monotone T ∧
      (∀ i ≤ K, T (i + 1) = scaledJumpTime H (cell ∘ ω) hpos ε (k i)) ∧
      (∀ n < K + 1, T n < T (K + 1) → T n < T (n + 1)) ∧
      (∀ i ≤ K, H.interpolatedWalk p ε (cell ∘ ω) (T (i + 1)) =
        (ε : ℝ) • p (cell (ω (k i)))) ∧
      H.interpolatedWalk p ε (cell ∘ ω) (T 0) = (ε : ℝ) • p (cell (ω 0)) := by
  let q := scaledJumpTime H (cell ∘ ω) hpos ε
  let T : ℕ → ℝ≥0 := fun n => Nat.casesOn n 0 (fun i => q (k (min i K)))
  have hq : StrictMono q := by
    intro a b hab
    apply NNReal.coe_lt_coe.mp
    exact mul_lt_mul_of_pos_left (H.jumpTime_strictMono hpos hab)
      (sq_pos_of_pos (by exact_mod_cast hε))
  have hq0 : q 0 = 0 := by
    apply NNReal.coe_injective
    change (ε : ℝ) ^ 2 * H.jumpTime (cell ∘ ω) 0 = 0
    rw [H.jumpTime_zero, mul_zero]
  obtain ⟨S, hS0, hSmono, hSmatch, hSstrict⟩ :=
    actualWalkStage_exists_absorbed_comparison_clock_of_select_mem
      pos B initial select ω K k hclock hinit hselect
  have hkmono : ∀ i j, i ≤ j → j ≤ K → k i ≤ k j := by
    intro i j hij hj
    have h := hSmono (show i + 1 ≤ j + 1 by omega)
    rw [hSmatch i (hij.trans hj), hSmatch j hj] at h
    exact_mod_cast h
  have hmatch : ∀ i ≤ K, T (i + 1) = q (k i) := by
    intro i hi
    simp only [T, min_eq_left hi]
  have hmono : Monotone T := by
    apply monotone_nat_of_le_succ
    intro n
    cases n with
    | zero => exact zero_le
    | succ n =>
      change q (k (min n K)) ≤ q (k (min (n + 1) K))
      exact hq.monotone (hkmono _ _ (min_le_min_right K (Nat.le_succ n)) (min_le_right _ _))
  have hstrict : ∀ n < K + 1, T n < T (K + 1) → T n < T (n + 1) := by
    intro n hn ht
    cases n with
    | zero =>
      have hk0 : 0 < k 0 := by
        have h := exitTime_pos_of_mem hinit
        change 0 < (actualWalkStage pos B initial select 0 ω).1 at h
        rw [hclock 0 (Nat.zero_le K)] at h
        exact WithTop.coe_lt_coe.mp h
      rw [hmatch 0 (Nat.zero_le K)]
      change 0 < q (k 0)
      rw [← hq0]
      exact hq hk0
    | succ i =>
      have hi : i < K := by omega
      rw [hmatch i (by omega), hmatch K le_rfl] at ht
      have hki : k i < k K := hq.lt_iff_lt.mp ht
      have hs : S (i + 1) < S (K + 1) := by
        rw [hSmatch i (by omega), hSmatch K le_rfl]
        exact_mod_cast hki
      have hs' := hSstrict (i + 1) (by omega) hs
      rw [hSmatch i (by omega), hSmatch (i + 1) (by omega)] at hs'
      have hki' : k i < k (i + 1) := by exact_mod_cast hs'
      rw [hmatch i (by omega), hmatch (i + 1) (by omega)]
      exact hq hki'
  change T 0 = 0 ∧ Monotone T ∧ _
  refine ⟨rfl, hmono, hmatch, hstrict, ?_, ?_⟩
  · intro i hi
    change H.interpolatedWalk p ε (cell ∘ ω) (T (i + 1)) = _
    rw [hmatch i hi]
    exact interpolatedWalk_at_jumpTime H p (cell ∘ ω) hpos hunb (k i) hε
  · have h := interpolatedWalk_at_jumpTime H p (cell ∘ ω) hpos hunb 0 hε
    change H.interpolatedWalk p ε (cell ∘ ω) 0 = _
    change H.interpolatedWalk p ε (cell ∘ ω) (q 0) = _ at h
    rw [hq0] at h
    exact h

end BouRabeeGwynne.FiniteConductanceNetwork
end
