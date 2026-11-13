/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module ReflectedGMS.Forms.UpcrossingSampling at commit fdb5cad; only the module paths of local imports are changed. -/
import Mathlib.Probability.Martingale.Upcrossing

/-!
# Upcrossings under deterministic subsampling

Every completed upcrossing visible along a strictly increasing deterministic
subsample is also a completed upcrossing of the ambient sequence before the
corresponding ambient horizon.
-/

set_option autoImplicit false

open MeasureTheory Set

namespace ReflectedGMS

variable {Ω : Type*}

/-- An ambient sequence completes its `k`-th upper crossing no later than the
ambient image of the corresponding completed sampled crossing. -/
theorem upperCrossingTime_comp_le
    (f : ℕ → Ω → ℝ) (φ : ℕ → ℕ) (hφ : StrictMono φ)
    (a b : ℝ) (N k : ℕ) (ω : Ω)
    (hk : upperCrossingTime a b (fun n ω ↦ f (φ n) ω) N k ω < N) :
    upperCrossingTime a b f (φ N) k ω ≤
      φ (upperCrossingTime a b (fun n ω ↦ f (φ n) ω) N k ω) := by
  induction k with
  | zero => simp
  | succ k ih =>
      let g : ℕ → Ω → ℝ := fun n ω ↦ f (φ n) ω
      have hl_lt : lowerCrossingTime a b g N k ω < N :=
        lt_of_le_of_lt lowerCrossingTime_le_upperCrossingTime_succ hk
      have hu_lt : upperCrossingTime a b g N k ω < N :=
        lt_of_le_of_lt upperCrossingTime_le_lowerCrossingTime hl_lt
      have hu_le := ih hu_lt
      have hl_mem : g (lowerCrossingTime a b g N k ω) ω ∈ Set.Iic a := by
        simpa only [lowerCrossingTime] using
          (hittingBtwn_mem_set_of_hittingBtwn_lt hl_lt)
      have hl_ambient : lowerCrossingTime a b f (φ N) k ω ≤
          φ (lowerCrossingTime a b g N k ω) := by
        rw [lowerCrossingTime]
        apply hittingBtwn_le_of_mem
        · exact hu_le.trans (hφ.monotone upperCrossingTime_le_lowerCrossingTime)
        · exact hφ.monotone lowerCrossingTime_le
        · exact hl_mem
      have hu_mem : g (upperCrossingTime a b g N (k + 1) ω) ω ∈ Set.Ici b := by
        rw [upperCrossingTime_succ_eq] at hk ⊢
        exact hittingBtwn_mem_set_of_hittingBtwn_lt hk
      rw [upperCrossingTime_succ_eq]
      apply hittingBtwn_le_of_mem
      · exact hl_ambient.trans
          (hφ.monotone lowerCrossingTime_le_upperCrossingTime_succ)
      · exact hφ.monotone hk.le
      · exact hu_mem

/-- Increasing deterministic subsampling cannot create upcrossings that are
absent from the ambient sequence before the corresponding ambient horizon. -/
theorem upcrossingsBefore_comp_le
    (f : ℕ → Ω → ℝ) (φ : ℕ → ℕ) (hφ : StrictMono φ)
    {a b : ℝ} (hab : a < b) (N : ℕ) (ω : Ω) :
    upcrossingsBefore a b (fun n ω ↦ f (φ n) ω) N ω ≤
      upcrossingsBefore a b f (φ N) ω := by
  by_cases hN : N = 0
  · subst N
    simp only [upcrossingsBefore_zero, zero_le]
  · have hs_lt : upperCrossingTime a b (fun n ω ↦ f (φ n) ω) N
        (upcrossingsBefore a b (fun n ω ↦ f (φ n) ω) N ω) ω < N :=
      upperCrossingTime_lt_of_le_upcrossingsBefore (Nat.pos_of_ne_zero hN) hab le_rfl
    apply le_csSup (upperCrossingTime_lt_bddAbove hab)
    exact lt_of_le_of_lt (upperCrossingTime_comp_le f φ hφ a b N _ ω hs_lt)
      (hφ hs_lt)

end ReflectedGMS
