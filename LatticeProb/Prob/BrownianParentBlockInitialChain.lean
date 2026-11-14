import LatticeProb.Prob.BrownianParentBlockActivePrefix

/-!
# Parent-block chains from active clocks

An initial excursion and an active clock prefix form a full chain of excursions.
-/

set_option autoImplicit false

open Set
open scoped NNReal ENNReal

namespace BouRabeeGwynne

/-- Prepending the initial excursion to an active clock prefix gives a chain with
one more interval. The initial excursion conditions are stated explicitly. -/
theorem brownianSkeletonClock_active_parentBlock_chain {J : Type*} [Countable J]
    [MeasurableSpace (Option J)] [MeasurableSingletonClass (Option J)]
    (centres : J → ℂ) (s : ℝ) (hs : 0 < s) (outer : Set ℂ)
    (z : Euc 2) (j₀ : J) (selector : ℕ → Euc 2 → Option J)
    (hselector : ∀ n x j, selector n x = some j →
      Complex.orthonormalBasisOneI.repr.symm x ∈ outer ∧
      Complex.orthonormalBasisOneI.repr.symm x ∈
        LatticeProb.ParentBlock.closedSquare (centres j) s)
    (K : ℕ) (ω : BrownianPath 2)
    (hactive : (brownianSkeletonClock
      (fun j => Complex.orthonormalBasisOneI.repr.symm ⁻¹'
        interior (LatticeProb.ParentBlock.parentBlock (centres j) s)) z j₀ selector K ω).1 = false)
    (hfinite : (brownianSkeletonClock
      (fun j => Complex.orthonormalBasisOneI.repr.symm ⁻¹'
        interior (LatticeProb.ParentBlock.parentBlock (centres j) s)) z j₀ selector K ω).2 ≠ ∞)
    (hinitial :
      let t₀ := (brownianSkeletonClock
        (fun j => Complex.orthonormalBasisOneI.repr.symm ⁻¹'
          interior (LatticeProb.ParentBlock.parentBlock (centres j) s)) z j₀ selector 0 ω).2.toNNReal
      Complex.orthonormalBasisOneI.repr.symm (z + ω 0) ∈ outer ∧
      Complex.orthonormalBasisOneI.repr.symm (z + ω 0) ∈
        LatticeProb.ParentBlock.closedSquare (centres j₀) s ∧
      Complex.orthonormalBasisOneI.repr.symm (z + ω t₀) ∉
        interior (LatticeProb.ParentBlock.parentBlock (centres j₀) s) ∧
      ∀ t ∈ Icc 0 t₀,
        ‖Complex.orthonormalBasisOneI.repr.symm (z + ω t) -
          Complex.orthonormalBasisOneI.repr.symm (z + ω 0)‖ ≤ 4 * s) :
    ∃ (T : ℕ → ℝ≥0) (selected : ℕ → J), Monotone T ∧ T 0 = 0 ∧
      ∀ n < K + 1,
        Complex.orthonormalBasisOneI.repr.symm (z + ω (T n)) ∈ outer ∧
        Complex.orthonormalBasisOneI.repr.symm (z + ω (T n)) ∈
          LatticeProb.ParentBlock.closedSquare (centres (selected n)) s ∧
        Complex.orthonormalBasisOneI.repr.symm (z + ω (T (n + 1))) ∉
          interior (LatticeProb.ParentBlock.parentBlock (centres (selected n)) s) ∧
        ∀ t ∈ Icc (T n) (T (n + 1)),
          ‖Complex.orthonormalBasisOneI.repr.symm (z + ω t) -
            Complex.orthonormalBasisOneI.repr.symm (z + ω (T n))‖ ≤ 4 * s := by
  obtain ⟨τ, selected, hmono, htime, hsteps⟩ :=
    brownianSkeletonClock_active_parentBlock_prefix centres s hs outer z j₀ selector
      hselector K ω hactive hfinite
  let T : ℕ → ℝ≥0 := fun n => Nat.casesOn n 0 τ
  let selected' : ℕ → J := fun n => Nat.casesOn n j₀ selected
  have hT : Monotone T := by
    apply monotone_nat_of_le_succ
    intro n
    cases n with
    | zero => exact zero_le
    | succ n => exact hmono (Nat.le_succ n)
  refine ⟨T, selected', hT, rfl, ?_⟩
  intro n hn
  cases n with
  | zero =>
    have ht := htime 0 (Nat.zero_le K)
    dsimp only [T, selected']
    rw [ht]
    exact hinitial
  | succ n =>
    have hn' : n < K := by omega
    have h := hsteps n hn'
    simpa only [T, selected', Nat.succ_eq_add_one] using h.2

end BouRabeeGwynne
